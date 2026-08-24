"""Materialize an adaptive LRAT tree as kernel-checkable Lean modules."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path
from typing import Any, TypedDict, cast


class NodeRecord(TypedDict):
    node_id: str
    assignment: list[int]


class InternalRecord(NodeRecord):
    split_variable: int
    negative_child: str
    positive_child: str


class LeafRecord(NodeRecord):
    lrat_path: str
    lrat_sha256: str
    lrat_bytes: int


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def lean_suffix(node_id: str) -> str:
    return node_id if node_id else "Root"


def leaf_name(node_id: str) -> str:
    return f"leaf{lean_suffix(node_id)}"


def node_name(node_id: str) -> str:
    return f"node{lean_suffix(node_id)}"


def unit_literal(literal: int) -> str:
    constructor = "pos" if literal > 0 else "neg"
    return f"Sat.Literal.{constructor} {abs(literal) - 1}"


def context_expr(assignment: list[int]) -> str:
    expression = "formula"
    for literal in assignment:
        expression = (
            f"({expression}).and (Sat.Fmla.one [{unit_literal(literal)}])"
        )
    return expression


def unit_dimacs(assignment: list[int]) -> str:
    return "".join(f"{literal} 0\\n" for literal in assignment)


def validate_tree(
    internal_rows: list[InternalRecord], leaf_rows: list[LeafRecord]
) -> None:
    internal = {row["node_id"]: row for row in internal_rows}
    leaves = {row["node_id"]: row for row in leaf_rows}
    if len(internal) != len(internal_rows) or len(leaves) != len(leaf_rows):
        raise ValueError("duplicate adaptive-tree node identifier")
    overlap = set(internal) & set(leaves)
    if overlap:
        raise ValueError(f"nodes are both internal and leaves: {sorted(overlap)}")
    all_nodes = set(internal) | set(leaves)
    if "" not in all_nodes:
        raise ValueError("adaptive tree has no root")

    reached: set[str] = set()
    frontier = [""]
    while frontier:
        node_id = frontier.pop()
        if node_id in reached:
            raise ValueError(f"adaptive tree revisits node {node_id}")
        reached.add(node_id)
        if node_id in leaves:
            continue
        row = internal[node_id]
        negative = row["negative_child"]
        positive = row["positive_child"]
        if negative != node_id + "0" or positive != node_id + "1":
            raise ValueError(f"noncanonical children at node {node_id}")
        split = row["split_variable"]
        expected_negative = [*row["assignment"], -split]
        expected_positive = [*row["assignment"], split]
        for child, expected in (
            (negative, expected_negative),
            (positive, expected_positive),
        ):
            child_row = internal.get(child) or leaves.get(child)
            if child_row is None:
                raise ValueError(f"missing child {child} of node {node_id}")
            if child_row["assignment"] != expected:
                raise ValueError(f"assignment mismatch at child {child}")
            frontier.append(child)
    if reached != all_nodes:
        raise ValueError(f"orphan adaptive-tree nodes: {sorted(all_nodes - reached)}")


def load_manifest(path: Path) -> tuple[dict[str, Any], list[InternalRecord], list[LeafRecord]]:
    raw = cast(dict[str, Any], json.loads(path.read_text(encoding="utf-8")))
    if raw.get("schema") != "tuza-q4-adaptive-cube-lrat-v1":
        raise ValueError("unexpected adaptive-cube manifest schema")
    internal = cast(list[InternalRecord], raw.get("internal_nodes"))
    leaves = cast(list[LeafRecord], raw.get("leaves"))
    validate_tree(internal, leaves)
    return raw, internal, leaves


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--binary-dir", type=Path, required=True)
    parser.add_argument("--case-stem", required=True)
    parser.add_argument("--module", required=True)
    arguments = parser.parse_args()

    repo = arguments.repo_root.resolve()
    certificate_target = (repo / "Certificates" / "cubes" / arguments.case_stem).resolve()
    lean_target = (
        repo / "TuzaRankFour" / "Certificates" / arguments.module
    ).resolve()
    for target in (certificate_target, lean_target):
        if repo not in target.parents:
            raise ValueError(f"target lies outside repository: {target}")
        if target.exists():
            raise FileExistsError(f"refusing to overwrite existing target: {target}")

    raw, internal_rows, leaf_rows = load_manifest(arguments.manifest)
    cnf_name = f"{arguments.case_stem.removesuffix('-adaptive')}.cnf"
    cnf_path = repo / "Certificates" / "cnf" / cnf_name
    if not cnf_path.is_file():
        raise FileNotFoundError(cnf_path)
    if sha256_file(cnf_path) != raw["source_cnf_sha256"]:
        raise ValueError("source CNF hash does not match adaptive manifest")

    certificate_target.mkdir(parents=True)
    lean_target.mkdir(parents=True)
    namespace = f"TuzaRankFour.Certificates.{arguments.module}"
    module_prefix = f"TuzaRankFour.Certificates.{arguments.module}"
    cnf_relative = f"../../../Certificates/cnf/{cnf_name}"
    certificate_relative = f"../../../Certificates/cubes/{arguments.case_stem}"

    formula_text = f'''import TuzaRankFour.Certificates.FromBinaryLRAT

namespace {namespace}

dimacs_formula_binary formula
  (include_str "{cnf_relative}")

end {namespace}
'''
    (lean_target / "Formula.lean").write_text(formula_text, encoding="utf-8")

    materialized_leaves: list[dict[str, Any]] = []
    for leaf in sorted(leaf_rows, key=lambda row: row["node_id"]):
        source_name = Path(leaf["lrat_path"]).stem + ".lratb"
        binary_source = arguments.binary_dir / source_name
        if not binary_source.is_file():
            raise FileNotFoundError(binary_source)
        target_name = f"leaf-{lean_suffix(leaf['node_id']).lower()}.lratb"
        binary_target = certificate_target / target_name
        shutil.copyfile(binary_source, binary_target)

        theorem = leaf_name(leaf["node_id"])
        module_name = f"Leaf{lean_suffix(leaf['node_id'])}"
        leaf_text = f'''import {module_prefix}.Formula

set_option maxHeartbeats 0

namespace {namespace}

lrat_cube_core_proof_binary {theorem}
  formula
  (include_str "{cnf_relative}")
  "{unit_dimacs(leaf['assignment'])}"
  "{certificate_relative}/{target_name}"

end {namespace}
'''
        (lean_target / f"{module_name}.lean").write_text(
            leaf_text, encoding="utf-8"
        )
        materialized_leaves.append(
            {
                **leaf,
                "binary_lrat_path": target_name,
                "binary_lrat_bytes": binary_target.stat().st_size,
                "binary_lrat_sha256": sha256_file(binary_target),
                "lean_module": f"{module_prefix}.{module_name}",
                "lean_theorem": f"{namespace}.{theorem}",
            }
        )

    imports = ["import TuzaRankFour.Certificates.Cube", f"import {module_prefix}.Formula"]
    imports.extend(
        f"import {row['lean_module']}" for row in materialized_leaves
    )
    declarations: list[str] = []
    for row in sorted(internal_rows, key=lambda item: len(item["node_id"]), reverse=True):
        assignment = row["assignment"]
        declarations.append(
            f"theorem {node_name(row['node_id'])} : ({context_expr(assignment)}).proof [] :=\n"
            f"  Sat.Fmla.proof_empty_of_split ({context_expr(assignment)}) "
            f"{row['split_variable'] - 1}\n"
            f"    {node_name(row['negative_child']) if row['negative_child'] in {r['node_id'] for r in internal_rows} else leaf_name(row['negative_child'])}\n"
            f"    {node_name(row['positive_child']) if row['positive_child'] in {r['node_id'] for r in internal_rows} else leaf_name(row['positive_child'])}"
        )
    root_reference = node_name("") if any(row["node_id"] == "" for row in internal_rows) else leaf_name("")
    declarations.append(
        f"theorem refutation : formula.proof [] := {root_reference}"
    )
    all_text = "\n".join(imports) + f"\n\nnamespace {namespace}\n\n"
    all_text += "\n\n".join(declarations)
    all_text += f"\n\nend {namespace}\n"
    (lean_target / "All.lean").write_text(all_text, encoding="utf-8")

    materialized_manifest = {
        **raw,
        "schema": "tuza-q4-adaptive-cube-lean-v1",
        "source_cnf": f"../../cnf/{cnf_name}",
        "leaves": materialized_leaves,
        "lean": {
            "formula_module": f"{module_prefix}.Formula",
            "aggregate_module": f"{module_prefix}.All",
            "refutation_theorem": f"{namespace}.refutation",
        },
    }
    (certificate_target / "manifest.json").write_text(
        json.dumps(materialized_manifest, indent=2) + "\n", encoding="utf-8"
    )
    print(
        json.dumps(
            {
                "internal_nodes": len(internal_rows),
                "leaves": len(leaf_rows),
                "binary_lrat_bytes": sum(
                    int(row["binary_lrat_bytes"]) for row in materialized_leaves
                ),
                "aggregate_module": f"{module_prefix}.All",
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
