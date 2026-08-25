"""Build the large proof environment in bounded-concurrency phases.

Lake launches independent module jobs concurrently.  That is desirable for an
ordinary project, but the generated LRAT and semantic modules can collectively
exceed the memory of a standard hosted runner.  This script materializes the
same dependency graph one chain and one semantic case at a time.  Comparator
then exports and kernel-checks the already-built Solution environment.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path
from typing import TypedDict, cast


class LaneRecord(TypedDict):
    index: int
    cases: list[str]


class LaneManifest(TypedDict):
    schema: str
    lane_count: int
    lanes: list[LaneRecord]


def lean_case_name(case_name: str) -> str:
    pieces = re.split(r"[^A-Za-z0-9]+", case_name)
    return "".join(piece[:1].upper() + piece[1:] for piece in pieces if piece)


def load_manifest(repository: Path) -> LaneManifest:
    path = repository / "Certificates" / "segment-state" / "lane-manifest.json"
    raw = cast(dict[str, object], json.loads(path.read_text(encoding="utf-8")))
    manifest = cast(LaneManifest, raw)
    if manifest["schema"] != "tuza-certificate-build-lanes-v1":
        raise ValueError(f"unexpected lane-manifest schema in {path}")
    if manifest["lane_count"] != len(manifest["lanes"]):
        raise ValueError(f"lane count mismatch in {path}")
    cases = [case for lane in manifest["lanes"] for case in lane["cases"]]
    if len(cases) != 66 or len(set(cases)) != 66:
        raise ValueError(f"expected 66 unique cases in {path}, found {len(set(cases))}")
    return manifest


def run_build(repository: Path, module: str, dry_run: bool) -> None:
    command = ["lake", "build", f"+{module}"]
    print(" ".join(command), flush=True)
    if not dry_run:
        subprocess.run(command, cwd=repository, check=True)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repository",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
    )
    parser.add_argument("--dry-run", action="store_true")
    return parser.parse_args()


def main() -> None:
    arguments = parse_args()
    repository = cast(Path, arguments.repository).resolve()
    dry_run = cast(bool, arguments.dry_run)
    manifest = load_manifest(repository)

    print("Prebuilding certificate lanes sequentially", flush=True)
    for lane in sorted(manifest["lanes"], key=lambda item: item["index"]):
        if not lane["cases"]:
            continue
        final_case = lean_case_name(lane["cases"][-1])
        run_build(
            repository,
            f"TuzaRankFour.Certificates.Segmented.{final_case}.All",
            dry_run,
        )
    run_build(
        repository,
        "TuzaRankFour.Certificates.Segmented.AllCases",
        dry_run,
    )

    print("Prebuilding semantic cases sequentially", flush=True)
    case_names = sorted(
        lean_case_name(case) for lane in manifest["lanes"] for case in lane["cases"]
    )
    for case_name in case_names:
        prefix = f"TuzaRankFour.Certificates.Semantic.{case_name}"
        run_build(repository, f"{prefix}Data", dry_run)
        run_build(repository, f"{prefix}Validity", dry_run)
        run_build(repository, prefix, dry_run)
    run_build(
        repository,
        "TuzaRankFour.Certificates.Semantic.AllCases",
        dry_run,
    )

    print("Completing the Solution environment", flush=True)
    run_build(repository, "Solution", dry_run)


if __name__ == "__main__":
    main()
