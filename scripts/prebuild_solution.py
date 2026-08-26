"""Build the large proof environment in addressable, bounded-memory phases.

Lake launches independent module jobs concurrently.  That is desirable for an
ordinary project, but the generated LRAT and semantic modules can collectively
exceed the memory of a standard hosted runner.  The phase selectors let a
release job build the four certificate lanes and the semantic cases in
separate GitHub Actions steps.  Comparator then exports and kernel-checks the
already-built Solution environment.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import TypedDict, cast


class LaneRecord(TypedDict):
    index: int
    cases: list[str]


class LaneManifest(TypedDict):
    schema: str
    lane_count: int
    lanes: list[LaneRecord]


@dataclass(frozen=True)
class Arguments:
    repository: Path
    dry_run: bool
    phase: str
    lane: int | None
    shard: tuple[int, int] | None


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


def parse_shard(value: str) -> tuple[int, int]:
    match = re.fullmatch(r"(\d+)/(\d+)", value)
    if match is None:
        raise argparse.ArgumentTypeError("shard must have the form INDEX/COUNT")
    index, count = (int(part) for part in match.groups())
    if count == 0 or index >= count:
        raise argparse.ArgumentTypeError(
            "shard must satisfy 0 <= INDEX < COUNT"
        )
    return index, count


def parse_args() -> Arguments:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repository",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument(
        "--phase",
        choices=(
            "all",
            "certificate-lane",
            "certificate-aggregate",
            "semantic-shard",
            "semantic-aggregate",
            "solution",
        ),
        default="all",
    )
    parser.add_argument("--lane", type=int)
    parser.add_argument("--shard", type=parse_shard, metavar="INDEX/COUNT")
    namespace = parser.parse_args()
    phase = cast(str, namespace.phase)
    lane = cast(int | None, namespace.lane)
    shard = cast(tuple[int, int] | None, namespace.shard)
    if (phase == "certificate-lane") != (lane is not None):
        parser.error("--lane is required exactly for --phase certificate-lane")
    if (phase == "semantic-shard") != (shard is not None):
        parser.error("--shard is required exactly for --phase semantic-shard")
    return Arguments(
        repository=cast(Path, namespace.repository).resolve(),
        dry_run=cast(bool, namespace.dry_run),
        phase=phase,
        lane=lane,
        shard=shard,
    )


def certificate_lane(
    repository: Path,
    manifest: LaneManifest,
    lane_index: int,
    dry_run: bool,
) -> None:
    lanes = [lane for lane in manifest["lanes"] if lane["index"] == lane_index]
    if len(lanes) != 1:
        raise ValueError(f"certificate lane {lane_index} is not in the manifest")
    lane = lanes[0]
    if not lane["cases"]:
        raise ValueError(f"certificate lane {lane_index} is empty")
    final_case = lean_case_name(lane["cases"][-1])
    print(f"Prebuilding certificate lane {lane_index}", flush=True)
    run_build(
        repository,
        f"TuzaRankFour.Certificates.Segmented.{final_case}.All",
        dry_run,
    )


def certificate_aggregate(repository: Path, dry_run: bool) -> None:
    print("Joining certificate lanes", flush=True)
    run_build(
        repository,
        "TuzaRankFour.Certificates.Segmented.AllCases",
        dry_run,
    )


def semantic_case_names(manifest: LaneManifest) -> list[str]:
    return sorted(
        lean_case_name(case)
        for lane in manifest["lanes"]
        for case in lane["cases"]
    )


def semantic_cases(
    repository: Path,
    case_names: list[str],
    dry_run: bool,
) -> None:
    for case_name in case_names:
        prefix = f"TuzaRankFour.Certificates.Semantic.{case_name}"
        run_build(repository, f"{prefix}Data", dry_run)
        run_build(repository, prefix, dry_run)


def semantic_aggregate(repository: Path, dry_run: bool) -> None:
    print("Joining semantic cases", flush=True)
    run_build(
        repository,
        "TuzaRankFour.Certificates.Semantic.AllCases",
        dry_run,
    )


def solution(repository: Path, dry_run: bool) -> None:
    print("Completing the Solution environment", flush=True)
    run_build(repository, "Solution", dry_run)


def main() -> None:
    arguments = parse_args()
    manifest = load_manifest(arguments.repository)

    if arguments.phase == "certificate-lane":
        assert arguments.lane is not None
        certificate_lane(
            arguments.repository, manifest, arguments.lane, arguments.dry_run
        )
    elif arguments.phase == "certificate-aggregate":
        certificate_aggregate(arguments.repository, arguments.dry_run)
    elif arguments.phase == "semantic-shard":
        assert arguments.shard is not None
        shard_index, shard_count = arguments.shard
        selected = semantic_case_names(manifest)[shard_index::shard_count]
        print(
            f"Prebuilding semantic shard {shard_index}/{shard_count} "
            f"({len(selected)} cases)",
            flush=True,
        )
        semantic_cases(arguments.repository, selected, arguments.dry_run)
    elif arguments.phase == "semantic-aggregate":
        semantic_aggregate(arguments.repository, arguments.dry_run)
    elif arguments.phase == "solution":
        solution(arguments.repository, arguments.dry_run)
    else:
        print("Prebuilding certificate lanes sequentially", flush=True)
        for lane in sorted(manifest["lanes"], key=lambda item: item["index"]):
            certificate_lane(
                arguments.repository, manifest, lane["index"], arguments.dry_run
            )
        certificate_aggregate(arguments.repository, arguments.dry_run)
        print("Prebuilding semantic cases sequentially", flush=True)
        semantic_cases(
            arguments.repository,
            semantic_case_names(manifest),
            arguments.dry_run,
        )
        semantic_aggregate(arguments.repository, arguments.dry_run)
        solution(arguments.repository, arguments.dry_run)


if __name__ == "__main__":
    main()
