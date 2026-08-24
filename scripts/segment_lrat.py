"""Split one LRAT trace into restartable proof-producing Lean modules."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import TypedDict


class SegmentRecord(TypedDict):
    index: int
    additions: int
    actions: int
    ids_before: int
    initial_ids: int
    text_file: str
    text_sha256: str
    binary_file: str
    binary_sha256: str
    binary_bytes: int
    ids_file: str | None
    ids_sha256: str | None
    initial_ids_file: str
    initial_ids_sha256: str
    final: bool


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def lean_case_name(case_name: str) -> str:
    pieces = re.split(r"[^A-Za-z0-9]+", case_name)
    return "".join(piece[:1].upper() + piece[1:] for piece in pieces if piece)


def is_deletion(fields: list[str]) -> bool:
    return len(fields) > 1 and fields[1] == "d"


def is_empty_addition(fields: list[str]) -> bool:
    return not is_deletion(fields) and len(fields) > 1 and fields[1] == "0"


def update_live_derived(fields: list[str], live: set[int]) -> None:
    if is_deletion(fields):
        for field in fields[2:-1]:
            live.discard(int(field))
    elif not is_empty_addition(fields):
        live.add(int(fields[0]))


def write_module(
    path: Path,
    import_name: str,
    namespace_name: str,
    declaration_name: str,
    formula_name: str,
    initial_bundle_name: str,
    proof_relative: str,
    initial_ids_relative: str,
    initial_clause_count: int,
    prior_name: str | None,
    ids_relative: str | None,
) -> None:
    lines = [
        f"import {import_name}",
        "",
        f"namespace {namespace_name}",
        "",
    ]
    if prior_name is None:
        lines.extend(
            [
                f"lrat_initial_segment_from_bundle_binary {declaration_name}",
                f"  {formula_name}",
                f"  {initial_bundle_name}",
                f'  (include_str "{initial_ids_relative}")',
                f"  {initial_clause_count}",
                f'  "{proof_relative}"',
            ]
        )
    else:
        assert ids_relative is not None
        lines.extend(
            [
                f"lrat_segment_from_bundle_binary {declaration_name}",
                f"  {formula_name}",
                f"  {initial_bundle_name}",
                f'  (include_str "{initial_ids_relative}")',
                f"  {initial_clause_count}",
                f"  {prior_name}",
                f'  (include_str "{ids_relative}")',
                f'  "{proof_relative}"',
            ]
        )
    lines.extend(["", f"end {namespace_name}", ""])
    path.write_text("\n".join(lines), encoding="utf-8", newline="\n")


def segment_trace(
    repository: Path,
    case_name: str,
    additions_per_segment: int,
    max_text_bytes: int,
    lake_command: str | None,
) -> None:
    if additions_per_segment <= 0:
        raise ValueError("additions per segment must be positive")
    if max_text_bytes <= 0:
        raise ValueError("maximum text bytes must be positive")
    source = repository / "Certificates" / "lrat" / f"{case_name}.lrat"
    binary_source = repository / "Certificates" / "lratb" / f"{case_name}.lratb"
    cnf = repository / "Certificates" / "cnf" / f"{case_name}.cnf"
    if not source.is_file() or not binary_source.is_file() or not cnf.is_file():
        raise FileNotFoundError(f"missing source for {case_name}")
    cnf_header = cnf.open(encoding="ascii").readline().split()
    if len(cnf_header) != 4 or cnf_header[:2] != ["p", "cnf"]:
        raise ValueError(f"malformed DIMACS header in {cnf}")
    initial_clause_count = int(cnf_header[3])

    case_lean = lean_case_name(case_name)
    namespace_name = f"TuzaRankFour.Certificates.Segmented.{case_lean}"
    module_root = repository / "TuzaRankFour" / "Certificates" / "Segmented" / case_lean
    text_root = repository / "Certificates" / "segments-text" / case_name
    binary_root = repository / "Certificates" / "segments" / case_name
    state_root = repository / "Certificates" / "segment-state" / case_name
    for directory in (module_root, text_root, binary_root, state_root):
        directory.mkdir(parents=True, exist_ok=True)
    for pattern, directory in (
        ("Segment*.lean", module_root),
        ("segment*.lrat", text_root),
        ("segment*.lratb", binary_root),
        ("segment*.ids", state_root),
    ):
        for generated_file in directory.glob(pattern):
            generated_file.unlink()

    module_prefix = f"TuzaRankFour.Certificates.Segmented.{case_lean}"
    formula_name = f"{namespace_name}.formula"
    initial_bundle_name = f"{namespace_name}.initialClauses"
    relative_root = "../../../../"
    cnf_relative = f"{relative_root}Certificates/cnf/{case_name}.cnf"

    base_module = module_root / "Base.lean"
    base_module.write_text(
        "\n".join(
            [
                "import TuzaRankFour.Certificates.CheckpointLRAT",
                "",
                f"namespace {namespace_name}",
                "",
                "dimacs_formula_binary formula",
                f'  (include_str "{cnf_relative}")',
                "",
                "dimacs_initial_clause_bundle initialClauses",
                "  formula",
                f'  (include_str "{cnf_relative}")',
                "",
                f"end {namespace_name}",
                "",
            ]
        ),
        encoding="utf-8",
        newline="\n",
    )

    live: set[int] = set()
    segments: list[tuple[list[str], list[int], list[int], int, bool]] = []
    lines: list[str] = []
    ids_before = sorted(live)
    additions = 0
    text_bytes = 0
    initial_ids: set[int] = set()
    saw_refutation = False
    with source.open(encoding="ascii") as stream:
        for raw_line in stream:
            stripped = raw_line.strip()
            if not stripped:
                continue
            fields = stripped.split()
            normalized_line = stripped + "\n"
            lines.append(normalized_line)
            text_bytes += len(normalized_line.encode("ascii"))
            final = is_empty_addition(fields)
            if not is_deletion(fields):
                additions += 1
                first_zero = fields.index("0", 1)
                for hint in fields[first_zero + 1 : -1]:
                    hint_id = abs(int(hint))
                    if hint_id <= initial_clause_count:
                        initial_ids.add(hint_id)
            update_live_derived(fields, live)
            if final or (
                additions > 0
                and (
                    additions == additions_per_segment
                    or text_bytes >= max_text_bytes
                )
            ):
                segments.append(
                    (lines, ids_before, sorted(initial_ids), additions, final)
                )
                lines = []
                ids_before = sorted(live)
                additions = 0
                text_bytes = 0
                initial_ids = set()
                if final:
                    saw_refutation = True
                    break
    if lines:
        segments.append((lines, ids_before, sorted(initial_ids), additions, False))
    if not saw_refutation or not segments[-1][4]:
        raise ValueError(f"{source} does not end in an empty-clause addition")

    pending_records: list[tuple[SegmentRecord, Path]] = []
    previous_module = f"{module_prefix}.Base"
    previous_declaration: str | None = None
    for index, (
        segment_lines,
        prior_ids,
        segment_initial_ids,
        segment_additions,
        final,
    ) in enumerate(segments):
        stem = f"Segment{index:04d}"
        text_path = text_root / f"segment{index:04d}.lrat"
        text_path.write_text("".join(segment_lines), encoding="ascii", newline="\n")
        ids_path: Path | None = None
        ids_sha: str | None = None
        if index > 0:
            ids_path = state_root / f"segment{index:04d}.ids"
            ids_path.write_text(" ".join(map(str, prior_ids)) + "\n", encoding="ascii")
            ids_sha = sha256_file(ids_path)
        initial_ids_path = state_root / f"segment{index:04d}.initial.ids"
        initial_ids_path.write_text(
            " ".join(map(str, segment_initial_ids)) + "\n", encoding="ascii"
        )
        declaration = "refutation" if final else f"checkpoint{index:04d}"
        proof_relative = (
            f"{relative_root}Certificates/segments/{case_name}/segment{index:04d}.lratb"
        )
        ids_relative = None
        if ids_path is not None:
            ids_relative = (
                f"{relative_root}Certificates/segment-state/{case_name}/"
                f"segment{index:04d}.ids"
            )
        initial_ids_relative = (
            f"{relative_root}Certificates/segment-state/{case_name}/"
            f"segment{index:04d}.initial.ids"
        )
        write_module(
            module_root / f"{stem}.lean",
            previous_module,
            namespace_name,
            declaration,
            formula_name,
            initial_bundle_name,
            proof_relative,
            initial_ids_relative,
            initial_clause_count,
            previous_declaration,
            ids_relative,
        )
        binary_path = binary_root / f"segment{index:04d}.lratb"
        pending_records.append(
            ({
                "index": index,
                "additions": segment_additions,
                "actions": len(segment_lines),
                "ids_before": len(prior_ids),
                "initial_ids": len(segment_initial_ids),
                "text_file": text_path.relative_to(repository).as_posix(),
                "text_sha256": sha256_file(text_path),
                "binary_file": binary_path.relative_to(repository).as_posix(),
                "binary_sha256": "",
                "binary_bytes": 0,
                "ids_file": None if ids_path is None else ids_path.relative_to(repository).as_posix(),
                "ids_sha256": ids_sha,
                "initial_ids_file": initial_ids_path.relative_to(repository).as_posix(),
                "initial_ids_sha256": sha256_file(initial_ids_path),
                "final": final,
            }, binary_path)
        )
        previous_module = f"{module_prefix}.{stem}"
        previous_declaration = f"{namespace_name}.{declaration}"

    (module_root / "All.lean").write_text(
        f"import {previous_module}\n",
        encoding="utf-8",
        newline="\n",
    )
    if lake_command is not None:
        subprocess.run(
            [
                lake_command,
                "env",
                "lean",
                "--run",
                str(repository / "scripts" / "convert_lrat_binary.lean"),
                str(text_root),
                str(binary_root),
            ],
            cwd=repository,
            check=True,
        )
    records: list[SegmentRecord] = []
    concatenated_digest = hashlib.sha256()
    concatenated_bytes = 0
    for record, binary_path in pending_records:
        if not binary_path.is_file():
            raise FileNotFoundError(
                f"missing {binary_path}; rerun with --lake or convert the text segments"
            )
        record["binary_sha256"] = sha256_file(binary_path)
        record["binary_bytes"] = binary_path.stat().st_size
        with binary_path.open("rb") as stream:
            while block := stream.read(1024 * 1024):
                concatenated_digest.update(block)
                concatenated_bytes += len(block)
        records.append(record)

    source_binary_sha256 = sha256_file(binary_source)
    if (
        concatenated_digest.hexdigest() != source_binary_sha256
        or concatenated_bytes != binary_source.stat().st_size
    ):
        raise ValueError("concatenated binary segments do not reproduce the source LRAT")

    manifest = {
        "schema": "tuza-checkpoint-lrat-segments-v1",
        "case": case_name,
        "source": source.relative_to(repository).as_posix(),
        "source_sha256": sha256_file(source),
        "binary_source": binary_source.relative_to(repository).as_posix(),
        "binary_source_sha256": source_binary_sha256,
        "binary_source_bytes": binary_source.stat().st_size,
        "concatenated_binary_sha256": concatenated_digest.hexdigest(),
        "concatenated_binary_bytes": concatenated_bytes,
        "cnf": cnf.relative_to(repository).as_posix(),
        "cnf_sha256": sha256_file(cnf),
        "additions_per_segment": additions_per_segment,
        "max_text_bytes": max_text_bytes,
        "segment_count": len(records),
        "segments": records,
    }
    (state_root / "manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(f"{case_name}: wrote {len(records)} segments")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("case")
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    parser.add_argument("--additions-per-segment", type=int, default=10_000)
    parser.add_argument("--max-text-bytes", type=int, default=1_000_000)
    parser.add_argument(
        "--lake",
        help="lake executable used to convert generated text segments to binary LRAT",
    )
    arguments = parser.parse_args()
    segment_trace(
        arguments.repository.resolve(),
        arguments.case,
        arguments.additions_per_segment,
        arguments.max_text_bytes,
        arguments.lake,
    )


if __name__ == "__main__":
    main()
