"""Assign segmented certificate cases to deterministic memory-safe build lanes."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import TypedDict, cast


class CaseManifest(TypedDict):
    case: str
    binary_source_bytes: int
    segment_count: int


class LaneRecord(TypedDict):
    index: int
    binary_bytes: int
    segments: int
    cases: list[str]


def lean_case_name(case_name: str) -> str:
    pieces = re.split(r"[^A-Za-z0-9]+", case_name)
    return "".join(piece[:1].upper() + piece[1:] for piece in pieces if piece)


def case_module(case_name: str) -> str:
    return f"TuzaRankFour.Certificates.Segmented.{lean_case_name(case_name)}"


def load_cases(repository: Path) -> list[CaseManifest]:
    state_root = repository / "Certificates" / "segment-state"
    output: list[CaseManifest] = []
    for path in sorted(state_root.glob("*/manifest.json")):
        raw = cast(dict[str, object], json.loads(path.read_text(encoding="utf-8")))
        output.append(
            {
                "case": cast(str, raw["case"]),
                "binary_source_bytes": cast(int, raw["binary_source_bytes"]),
                "segment_count": cast(int, raw["segment_count"]),
            }
        )
    return output


def assign_lanes(cases: list[CaseManifest], lane_count: int) -> list[LaneRecord]:
    lanes: list[LaneRecord] = [
        {"index": index, "binary_bytes": 0, "segments": 0, "cases": []}
        for index in range(lane_count)
    ]
    for case in sorted(
        cases, key=lambda item: (-item["binary_source_bytes"], item["case"])
    ):
        lane = min(lanes, key=lambda item: (item["binary_bytes"], item["index"]))
        lane["cases"].append(case["case"])
        lane["binary_bytes"] += case["binary_source_bytes"]
        lane["segments"] += case["segment_count"]
    return lanes


def add_predecessor_import(base_path: Path, predecessor: str | None) -> None:
    lines = base_path.read_text(encoding="utf-8").splitlines()
    lines = [
        line
        for line in lines
        if not line.startswith("import TuzaRankFour.Certificates.Segmented.")
    ]
    if predecessor is not None:
        lines.insert(1, f"import {case_module(predecessor)}.All")
    base_path.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")


def write_aggregate_modules(repository: Path, lanes: list[LaneRecord]) -> None:
    lean_root = repository / "TuzaRankFour" / "Certificates" / "Segmented"
    lane_ends = [lane["cases"][-1] for lane in lanes if lane["cases"]]
    imports = [f"import {case_module(case)}.All" for case in lane_ends]
    (lean_root / "AllCases.lean").write_text(
        "\n".join(imports) + "\n", encoding="utf-8", newline="\n"
    )
    audit_lines = ["import TuzaRankFour.Certificates.Segmented.AllCases", ""]
    for case in sorted(case for lane in lanes for case in lane["cases"]):
        audit_lines.append(f"#print axioms {case_module(case)}.refutation")
    audit_lines.append("")
    (lean_root / "Audit.lean").write_text(
        "\n".join(audit_lines), encoding="utf-8", newline="\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    parser.add_argument("--lanes", type=int, default=4)
    arguments = parser.parse_args()
    if arguments.lanes <= 0:
        raise ValueError("lane count must be positive")
    repository = arguments.repository.resolve()
    cases = load_cases(repository)
    if len(cases) != 66:
        raise ValueError(f"expected 66 certificate cases, found {len(cases)}")
    lanes = assign_lanes(cases, arguments.lanes)
    for lane in lanes:
        predecessor: str | None = None
        for case in lane["cases"]:
            base_path = (
                repository
                / "TuzaRankFour"
                / "Certificates"
                / "Segmented"
                / lean_case_name(case)
                / "Base.lean"
            )
            add_predecessor_import(base_path, predecessor)
            predecessor = case
    write_aggregate_modules(repository, lanes)
    manifest = {
        "schema": "tuza-certificate-build-lanes-v1",
        "lane_count": len(lanes),
        "assignment_rule": "descending binary size, greedily assigned to the lightest lane",
        "lanes": lanes,
    }
    output_path = repository / "Certificates" / "segment-state" / "lane-manifest.json"
    output_path.write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    for lane in lanes:
        print(
            f"lane {lane['index']}: {len(lane['cases'])} cases, "
            f"{lane['segments']} segments, {lane['binary_bytes']} bytes"
        )


if __name__ == "__main__":
    main()
