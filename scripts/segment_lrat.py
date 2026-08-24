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
    text_file: str
    text_sha256: str
    binary_file: str
    binary_sha256: str
    binary_bytes: int
    ids_file: str | None
    ids_sha256: str | None
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
    cnf_relative: str,
    proof_relative: str,
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
                f"lrat_initial_segment_binary {declaration_name}",
                f"  {formula_name}",
                f'  (include_str "{cnf_relative}")',
                f'  "{proof_relative}"',
            ]
        )
    else:
        assert ids_relative is not None
        lines.extend(
            [
                f"lrat_segment_binary {declaration_name}",
                f"  {formula_name}",
                f"  {prior_name}",
                f'  (include_str "{ids_relative}")',
                f'  (include_str "{cnf_relative}")',
                f'  "{proof_relative}"',
            ]
        )
    lines.extend(["", f"end {namespace_name}", ""])
    path.write_text("\n".join(lines), encoding="utf-8", newline="\n")


def segment_trace(
    repository: Path,
    case_name: str,
    additions_per_segment: int,
    lake_command: str | None,
) -> None:
    if additions_per_segment <= 0:
        raise ValueError("additions per segment must be positive")
    source = repository / "Certificates" / "lrat" / f"{case_name}.lrat"
    binary_source = repository / "Certificates" / "lratb" / f"{case_name}.lratb"
    cnf = repository / "Certificates" / "cnf" / f"{case_name}.cnf"
    if not source.is_file() or not binary_source.is_file() or not cnf.is_file():
        raise FileNotFoundError(f"missing source for {case_name}")

    case_lean = lean_case_name(case_name)
    namespace_name = f"TuzaRankFour.Certificates.Segmented.{case_lean}"
    module_root = repository / "TuzaRankFour" / "Certificates" / "Segmented" / case_lean
    text_root = repository / "Certificates" / "segments-text" / case_name
    binary_root = repository / "Certificates" / "segments" / case_name
    state_root = repository / "Certificates" / "segment-state" / case_name
    for directory in (module_root, text_root, binary_root, state_root):
        directory.mkdir(parents=True, exist_ok=True)

    module_prefix = f"TuzaRankFour.Certificates.Segmented.{case_lean}"
    formula_name = f"{namespace_name}.formula"
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
                f"end {namespace_name}",
                "",
            ]
        ),
        encoding="utf-8",
        newline="\n",
    )

    live: set[int] = set()
    segments: list[tuple[list[str], list[int], int, bool]] = []
    lines: list[str] = []
    ids_before = sorted(live)
    additions = 0
    saw_refutation = False
    with source.open(encoding="ascii") as stream:
        for raw_line in stream:
            stripped = raw_line.strip()
            if not stripped:
                continue
            fields = stripped.split()
            lines.append(stripped + "\n")
            final = is_empty_addition(fields)
            if not is_deletion(fields):
                additions += 1
            update_live_derived(fields, live)
            if final or additions == additions_per_segment:
                segments.append((lines, ids_before, additions, final))
                lines = []
                ids_before = sorted(live)
                additions = 0
                if final:
                    saw_refutation = True
                    break
    if lines:
        segments.append((lines, ids_before, additions, False))
    if not saw_refutation or not segments[-1][3]:
        raise ValueError(f"{source} does not end in an empty-clause addition")

    pending_records: list[tuple[SegmentRecord, Path]] = []
    previous_module = f"{module_prefix}.Base"
    previous_declaration: str | None = None
    for index, (segment_lines, prior_ids, segment_additions, final) in enumerate(segments):
        stem = f"Segment{index:04d}"
        text_path = text_root / f"segment{index:04d}.lrat"
        text_path.write_text("".join(segment_lines), encoding="ascii", newline="\n")
        ids_path: Path | None = None
        ids_sha: str | None = None
        if index > 0:
            ids_path = state_root / f"segment{index:04d}.ids"
            ids_path.write_text(" ".join(map(str, prior_ids)) + "\n", encoding="ascii")
            ids_sha = sha256_file(ids_path)
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
        write_module(
            module_root / f"{stem}.lean",
            previous_module,
            namespace_name,
            declaration,
            formula_name,
            cnf_relative,
            proof_relative,
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
                "text_file": text_path.relative_to(repository).as_posix(),
                "text_sha256": sha256_file(text_path),
                "binary_file": binary_path.relative_to(repository).as_posix(),
                "binary_sha256": "",
                "binary_bytes": 0,
                "ids_file": None if ids_path is None else ids_path.relative_to(repository).as_posix(),
                "ids_sha256": ids_sha,
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
    parser.add_argument("--additions-per-segment", type=int, default=1000)
    parser.add_argument(
        "--lake",
        help="lake executable used to convert generated text segments to binary LRAT",
    )
    arguments = parser.parse_args()
    segment_trace(
        arguments.repository.resolve(),
        arguments.case,
        arguments.additions_per_segment,
        arguments.lake,
    )


if __name__ == "__main__":
    main()
