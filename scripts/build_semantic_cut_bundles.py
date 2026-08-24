"""Build compact Lean-side witnesses from the frozen ambient q4 streams.

This producer is outside the trusted base.  Each generated Lean module checks
the decoded witnesses and their exact equality with the imported DIMACS
formula inside the kernel.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
from typing import Any, BinaryIO, cast

MAGIC = b"TCUT0001"
EXPECTED_COUNTS: dict[int, int] = {6: 1, 7: 3, 8: 6, 9: 11, 10: 14, 11: 15, 12: 16}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require_dict(value: object, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError(f"{label} must be an object")
    return cast(dict[str, Any], value)


def require_list(value: object, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise ValueError(f"{label} must be a list")
    return cast(list[Any], value)


def require_int(value: object, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{label} must be a nonnegative integer")
    return value


def require_pair(value: object, order: int, label: str) -> tuple[int, int]:
    items = require_list(value, label)
    if len(items) != 2:
        raise ValueError(f"{label} must have two entries")
    pair = (require_int(items[0], label), require_int(items[1], label))
    if not 0 <= pair[0] < pair[1] < order:
        raise ValueError(f"{label} is not a normalized edge")
    return pair


def require_triple(value: object, order: int, label: str) -> tuple[int, int, int]:
    items = require_list(value, label)
    if len(items) != 3:
        raise ValueError(f"{label} must have three entries")
    triple = tuple(require_int(item, label) for item in items)
    if not 0 <= triple[0] < triple[1] < triple[2] < order:
        raise ValueError(f"{label} is not a normalized triangle")
    return cast(tuple[int, int, int], triple)


def require_int_list(value: object, label: str) -> list[int]:
    return [require_int(item, label) for item in require_list(value, label)]


def write_varnat(stream: BinaryIO, value: int) -> None:
    if value < 0:
        raise ValueError("cannot encode a negative varint")
    while True:
        byte = value & 0x7F
        value >>= 7
        stream.write(bytes([byte | (0x80 if value else 0)]))
        if not value:
            return


def semantic_indices(
    record: dict[str, Any],
    *,
    order: int,
    skeleton: int,
    edge_indices: dict[tuple[int, int], int],
    triangle_indices: dict[tuple[int, int, int], int],
) -> tuple[int, list[int]]:
    if require_int(record.get("order"), "record.order") != order:
        raise ValueError("record order mismatch")
    if require_int(record.get("skeleton_index"), "record.skeleton_index") != skeleton:
        raise ValueError("record skeleton mismatch")
    category = record.get("category")
    clause_raw = require_list(record.get("clause"), "record.clause")
    if not all(isinstance(literal, int) and not isinstance(literal, bool) for literal in clause_raw):
        raise ValueError("record.clause must contain integers")
    clause = cast(list[int], clause_raw)
    edge_count = len(edge_indices)
    if category == "five-packing":
        packing = [
            require_triple(item, order, "record.packing")
            for item in require_list(record.get("packing"), "record.packing")
        ]
        indices = [triangle_indices[triangle] for triangle in packing]
        expected = [-(edge_count + index + 1) for index in indices]
        if clause != expected:
            raise ValueError("five-packing clause does not match its witness")
        return 0, indices
    if category == "small-cover":
        cover = [
            require_pair(item, order, "record.cover")
            for item in require_list(record.get("cover"), "record.cover")
        ]
        indices = [edge_indices[edge] for edge in cover]
        cover_set = set(cover)
        expected: list[int] = []
        for triangle, index in triangle_indices.items():
            a, b, c = triangle
            if {(a, b), (a, c), (b, c)}.isdisjoint(cover_set):
                expected.append(edge_count + index + 1)
        if clause != expected:
            raise ValueError("small-cover clause does not match its witness")
        return 1, indices
    raise ValueError(f"unknown semantic category {category!r}")


def build_case(artifact_root: Path, output_root: Path, order: int, skeleton: int) -> dict[str, object]:
    case_dir = artifact_root / f"ambient-maplesat-order{order}"
    stem = f"skeleton-{skeleton:02d}"
    report_path = case_dir / f"{stem}.json"
    stream_path = case_dir / f"{stem}.jsonl"
    report = require_dict(json.loads(report_path.read_text(encoding="utf-8")), "report")
    if report.get("schema") != "tuza-q4-reduced-kernel-exact-search-v1":
        raise ValueError(f"wrong schema in {report_path}")
    if report.get("target") != "nu=4,tau>=9" or report.get("cover_limit") != 8:
        raise ValueError(f"wrong target in {report_path}")
    if report.get("k4_free") is not False or report.get("normal_form") is not False:
        raise ValueError(f"wrong ambient flags in {report_path}")
    if report.get("normal_form_nogoods") != 0:
        raise ValueError(f"normal-form nogoods are not permitted in {report_path}")
    expected_stream_hash = report.get("certificate_stream_sha256")
    actual_stream_hash = sha256_file(stream_path)
    if expected_stream_hash != actual_stream_hash:
        raise ValueError(f"certificate stream hash mismatch in {stream_path}")
    skeletons = require_list(report.get("skeletons"), "report.skeletons")
    if len(skeletons) != 1:
        raise ValueError(f"expected one skeleton in {report_path}")
    skeleton_record = require_dict(skeletons[0], "report.skeletons[0]")
    if require_int(skeleton_record.get("skeleton_index"), "skeleton_index") != skeleton:
        raise ValueError(f"skeleton index mismatch in {report_path}")
    marked_triangles = [
        require_triple(item, order, "report.packing")
        for item in require_list(skeleton_record.get("packing"), "report.packing")
    ]
    if len(marked_triangles) != 4:
        raise ValueError(f"marked packing must have four triangles in {report_path}")
    edges = list(itertools.combinations(range(order), 2))
    triangles = list(itertools.combinations(range(order), 3))
    edge_indices = {edge: index for index, edge in enumerate(edges)}
    triangle_indices = {triangle: index for index, triangle in enumerate(triangles)}
    marked = [triangle_indices[triangle] for triangle in marked_triangles]
    cuts: list[tuple[int, list[int]]] = []
    with stream_path.open("r", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, start=1):
            if not line.strip():
                raise ValueError(f"blank record at {stream_path}:{line_number}")
            record = require_dict(json.loads(line), f"record {line_number}")
            cuts.append(
                semantic_indices(
                    record,
                    order=order,
                    skeleton=skeleton,
                    edge_indices=edge_indices,
                    triangle_indices=triangle_indices,
                )
            )
    expected_records = require_int(
        skeleton_record.get("certificate_record_count"), "certificate_record_count"
    )
    clause_count = require_int(skeleton_record.get("clause_count"), "clause_count")
    if len(cuts) != expected_records or report.get("models") != len(cuts):
        raise ValueError(f"certificate record count mismatch in {stream_path}")
    output_root.mkdir(parents=True, exist_ok=True)
    output_path = output_root / f"order{order:02d}-skeleton{skeleton:02d}.cutb"
    with output_path.open("wb") as output:
        output.write(MAGIC)
        write_varnat(output, order)
        write_varnat(output, skeleton)
        write_varnat(output, len(marked))
        for index in marked:
            write_varnat(output, index)
        write_varnat(output, len(cuts))
        for tag, indices in cuts:
            output.write(bytes([tag]))
            write_varnat(output, len(indices))
            for index in indices:
                write_varnat(output, index)
    return {
        "case": f"order{order:02d}-skeleton{skeleton:02d}",
        "order": order,
        "skeleton": skeleton,
        "marked_triangle_indices": marked,
        "cut_count": len(cuts),
        "clause_count": clause_count,
        "packing_cut_count": sum(tag == 0 for tag, _ in cuts),
        "cover_cut_count": sum(tag == 1 for tag, _ in cuts),
        "source": stream_path.relative_to(artifact_root).as_posix(),
        "source_sha256": actual_stream_hash,
        "bundle": output_path.name,
        "bundle_bytes": output_path.stat().st_size,
        "bundle_sha256": sha256_file(output_path),
    }


def chunk_tree(start: int, stop: int, maximum_size: int) -> tuple[int, int] | tuple[object, object]:
    if stop - start <= maximum_size:
        return (start, stop)
    middle = start + (stop - start) // 2
    return (chunk_tree(start, middle, maximum_size), chunk_tree(middle, stop, maximum_size))


def tree_leaves(tree: tuple[int, int] | tuple[object, object]) -> list[tuple[int, int]]:
    left, right = tree
    if isinstance(left, int) and isinstance(right, int):
        return [(left, right)]
    return tree_leaves(cast(tuple[object, object], left)) + tree_leaves(
        cast(tuple[object, object], right)
    )


def satisfaction_expression(
    tree: tuple[int, int] | tuple[object, object],
    leaf_indices: dict[tuple[int, int], int],
) -> str:
    left, right = tree
    if isinstance(left, int) and isinstance(right, int):
        return f"hChunk{leaf_indices[(left, right)]}"
    return (
        "satisfies_fmla_append "
        f"({satisfaction_expression(cast(tuple[object, object], left), leaf_indices)}) "
        f"({satisfaction_expression(cast(tuple[object, object], right), leaf_indices)})"
    )


def write_lean_modules(lean_root: Path, case: dict[str, object], maximum_size: int) -> None:
    order = cast(int, case["order"])
    skeleton = cast(int, case["skeleton"])
    cut_count = cast(int, case["cut_count"])
    clause_count = cast(int, case["clause_count"])
    module = f"Order{order:02d}Skeleton{skeleton:02d}"
    namespace = f"TuzaRankFour.Certificates.Semantic.{module}"
    segmented = f"TuzaRankFour.Certificates.Segmented.{module}"
    stem = f"order{order:02d}-skeleton{skeleton:02d}"
    base_count = 4 * len(list(itertools.combinations(range(order), 3))) + len(
        list(itertools.combinations(range(order), 2))
    ) + order + 4
    if base_count + cut_count != clause_count:
        raise ValueError(f"base/cut clause count mismatch for {stem}")
    tree = chunk_tree(0, clause_count, maximum_size)
    leaves = tree_leaves(tree)
    leaf_indices = {leaf: index for index, leaf in enumerate(leaves)}
    lean_root.mkdir(parents=True, exist_ok=True)
    data_source = f"""import TuzaRankFour.Certificates.SemanticCutBinary

namespace {namespace}

semantic_cut_bundle_binary markedPacking cuts {order} {skeleton}
  \"../../../Certificates/semantic-cuts/{stem}.cutb\"

dimacs_formula_chunks formulaChunk {maximum_size}
  (include_str \"../../../Certificates/cnf/{stem}.cnf\")

semantic_cut_slices_binary cutChunk {order} {skeleton} {base_count} {maximum_size}
  \"../../../Certificates/semantic-cuts/{stem}.cutb\"

end {namespace}
"""
    (lean_root / f"{module}Data.lean").write_text(data_source, encoding="utf-8", newline="\n")
    validity_source = f"""import TuzaRankFour.Certificates.Semantic.{module}Data

namespace {namespace}

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open TuzaRankFour.SemanticEncoding

theorem cuts_valid : cutsValidBool {order} cuts = true := by decide

end {namespace}
"""
    (lean_root / f"{module}Validity.lean").write_text(
        validity_source, encoding="utf-8", newline="\n"
    )
    formula_group_size = 8
    group_count = (len(leaves) + formula_group_size - 1) // formula_group_size
    for group in range(group_count):
        first = group * formula_group_size
        stop_index = min(len(leaves), first + formula_group_size)
        dependency = (
            f"TuzaRankFour.Certificates.Semantic.{module}Data"
            if group == 0
            else f"TuzaRankFour.Certificates.Semantic.{module}Formula{group - 1:02d}"
        )
        group_lines = [
            f"import {dependency}",
            "",
            f"namespace {namespace}",
            "",
            "set_option maxHeartbeats 0",
            "set_option maxRecDepth 1000000",
            "",
            "open TuzaRankFour.SemanticEncoding",
            "",
        ]
        if group == 0:
            group_lines.extend(
                [
                    "deriving instance DecidableEq for Sat.Literal",
                    "deriving instance DecidableEq for Sat.Clause",
                    "",
                ]
            )
        for index in range(first, stop_index):
            start, stop = leaves[index]
            base_start = min(start, base_count)
            base_stop = min(stop, base_count)
            base_length = base_stop - base_start
            cut_start = max(0, start - base_count)
            cut_stop = max(0, stop - base_count)
            cut_length = cut_stop - cut_start
            group_lines.extend(
                [
                    f"theorem cutChunk{index}_valid : cutsValidBool {order} cutChunk{index} = true := by",
                    "  decide",
                    "",
                    f"theorem formulaChunk{index}_eq :",
                    f"    formulaChunk{index} =",
                    f"      ((baseFormula {order} markedPacking).drop {base_start}).take {base_length} ++",
                    f"        cutFormula {order} cutChunk{index} := by",
                    "  decide",
                    "",
                ]
            )
        group_lines.extend([f"end {namespace}", ""])
        (lean_root / f"{module}Formula{group:02d}.lean").write_text(
            "\n".join(group_lines), encoding="utf-8", newline="\n"
        )
    lines = [
        f"import TuzaRankFour.Certificates.Semantic.{module}Validity",
        f"import TuzaRankFour.Certificates.Semantic.{module}Formula{group_count - 1:02d}",
        f"import TuzaRankFour.Certificates.Segmented.{module}.All",
        "",
        f"namespace {namespace}",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 1000000",
        "",
        "open TuzaRankFour.FiniteEncoding",
        "open TuzaRankFour.SemanticEncoding",
        "",
    ]
    lines.extend(
        [
            f"theorem no_counterexample (G : SimpleGraph (Fin {order}))",
            "    (hSupport : G.triangleSupport = G)",
            f"    (hVertices : ∀ v : Fin {order}, v ∈ G.triangleSupportVertices)",
            "    (hMarked : ∀ i, List.Mem i markedPacking →",
            f"      ∃ t, (orderedTriangles {order})[i]? = some t ∧",
            "        triangleFinset t ∈ G.triangles)",
            "    (hν : G.trianglePackingNumber ≤ 4)",
            "    (hτ : 8 < G.triangleTransversalNumber) : False := by",
            "  let v := graphValuation G",
            f"  have hBaseConditions : BaseConditions {order} v markedPacking :=",
            "    graphValuation_baseConditions G markedPacking hSupport hVertices hMarked",
            f"  have hCutConditions : CutConditions {order} v :=",
            "    graphValuation_cutConditions G hν hτ",
            f"  have hBase : v.satisfies_fmla (baseFormula {order} markedPacking) :=",
            "    satisfies_baseFormula hBaseConditions",
        ]
    )
    for index, (start, stop) in enumerate(leaves):
        base_start = min(start, base_count)
        base_stop = min(stop, base_count)
        base_length = base_stop - base_start
        cut_start = max(0, start - base_count)
        cut_stop = max(0, stop - base_count)
        cut_length = cut_stop - cut_start
        lines.extend(
            [
                f"  have hChunk{index} : v.satisfies_fmla formulaChunk{index} := by",
                f"    rw [formulaChunk{index}_eq]",
                "    apply satisfies_fmla_append",
                f"    · exact satisfies_fmla_drop_take hBase {base_start} {base_length}",
                "    · exact satisfies_cutFormula hCutConditions _",
                f"        (valid_of_cutsValidBool cutChunk{index}_valid)",
            ]
        )
    expression = satisfaction_expression(tree, leaf_indices)
    lines.extend(
        [
            f"  have hFormula : v.satisfies_fmla {segmented}.formula := by",
            f"    exact {expression}",
            f"  exact {segmented}.refutation v hFormula",
            "",
            f"end {namespace}",
            "",
        ]
    )
    (lean_root / f"{module}.lean").write_text("\n".join(lines), encoding="utf-8", newline="\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact-root", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--lean-root", type=Path)
    parser.add_argument("--formula-chunk-size", type=int, default=512)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    artifact_root = cast(Path, args.artifact_root).resolve()
    output_root = cast(Path, args.output_root).resolve()
    cases = [
        build_case(artifact_root, output_root, order, skeleton)
        for order, count in EXPECTED_COUNTS.items()
        for skeleton in range(count)
    ]
    lean_root_value = cast(Path | None, args.lean_root)
    if lean_root_value is not None:
        lean_root = lean_root_value.resolve()
        maximum_size = cast(int, args.formula_chunk_size)
        if maximum_size <= 0:
            raise ValueError("formula chunk size must be positive")
        for case in cases:
            write_lean_modules(lean_root, case, maximum_size)
    if len(cases) != 66 or sum(cast(int, case["cut_count"]) for case in cases) != 331_430:
        raise ValueError("aggregate ambient campaign count mismatch")
    manifest = {
        "schema": "tuza-semantic-cut-bundles-v1",
        "campaign": "ambient rank-four endpoint: nu<=4 and tau>=9",
        "encoding": "TCUT0001",
        "case_count": len(cases),
        "cut_count": sum(cast(int, case["cut_count"]) for case in cases),
        "packing_cut_count": sum(cast(int, case["packing_cut_count"]) for case in cases),
        "cover_cut_count": sum(cast(int, case["cover_cut_count"]) for case in cases),
        "cases": cases,
    }
    manifest_path = output_root / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: manifest[key] for key in ("case_count", "cut_count", "packing_cut_count", "cover_cut_count")}))


if __name__ == "__main__":
    main()
