"""Partition a certified UNSAT formula into a small LRAT decision tree.

The producer is deliberately outside the trusted base.  Every retained leaf
contains the original DIMACS formula plus its path's unit clauses, and every
leaf LRAT trace is checked by ``drat-trim`` before it enters the manifest.
Lean subsequently imports the leaf traces as ordinary proof terms and combines
the exhaustive binary decision tree by propositional case analysis.
"""

from __future__ import annotations

import argparse
import ctypes
import hashlib
import json
import os
import subprocess
import time
from concurrent.futures import ProcessPoolExecutor
from dataclasses import asdict, dataclass
from pathlib import Path

from pysat.solvers import Solver

type Clause = list[int]
type Assignment = tuple[int, ...]


@dataclass(frozen=True)
class NodeSpec:
    node_id: str
    assignment: Assignment


@dataclass(frozen=True)
class NodeResult:
    node_id: str
    assignment: Assignment
    cnf_path: str
    drat_path: str
    lrat_path: str
    cnf_sha256: str
    drat_sha256: str
    lrat_sha256: str
    drat_bytes: int
    lrat_bytes: int
    solve_seconds: float
    trim_seconds: float


@dataclass(frozen=True)
class InternalRecord:
    node_id: str
    assignment: Assignment
    split_variable: int
    negative_child: str
    positive_child: str
    discarded_lrat_bytes: int
    solve_seconds: float
    trim_seconds: float


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def parse_dimacs(path: Path) -> tuple[int, list[Clause]]:
    variables = -1
    declared = -1
    clauses: list[Clause] = []
    for raw_line in path.read_text(encoding="ascii").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            fields = line.split()
            if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                raise ValueError(f"bad DIMACS header in {path}")
            variables, declared = int(fields[2]), int(fields[3])
            continue
        values = [int(value) for value in line.split()]
        if not values or values[-1] != 0 or 0 in values[:-1]:
            raise ValueError(f"bad DIMACS clause in {path}")
        clauses.append(values[:-1])
    if variables < 0 or declared != len(clauses):
        raise ValueError(f"DIMACS count mismatch in {path}")
    return variables, clauses


def write_dimacs(path: Path, variables: int, clauses: list[Clause]) -> None:
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(f"p cnf {variables} {len(clauses)}\n")
        for clause in clauses:
            stream.write(" ".join(str(literal) for literal in clause))
            stream.write(" 0\n")


def flush_native_streams() -> None:
    result = (
        ctypes.CDLL("ucrtbase")._flushall()
        if os.name == "nt"
        else ctypes.CDLL(None).fflush(None)
    )
    if result < 0:
        raise RuntimeError("native proof stream flush failed")


def solve_node(
    job: tuple[NodeSpec, int, list[Clause], str, str]
) -> NodeResult:
    spec, variables, base_clauses, output_text, drat_trim_text = job
    output = Path(output_text)
    drat_trim = Path(drat_trim_text)
    stem = "root" if not spec.node_id else f"node-{spec.node_id}"
    cnf_path = output / "cnf" / f"{stem}.cnf"
    drat_path = output / "drat" / f"{stem}.drat"
    lrat_path = output / "lrat" / f"{stem}.lrat"
    clauses = [*base_clauses, *([literal] for literal in spec.assignment)]
    write_dimacs(cnf_path, variables, clauses)

    solve_started = time.perf_counter()
    solver = Solver(name="cadical195", bootstrap_with=clauses, with_proof=True)
    try:
        if solver.solve():
            raise RuntimeError(f"node {spec.node_id or 'root'} is satisfiable")
        flush_native_streams()
        try:
            proof = solver.get_proof()
        except AssertionError:
            flush_native_streams()
            proof = solver.get_proof()
        if proof is None or not proof or "0" not in proof:
            raise RuntimeError(f"node {spec.node_id or 'root'} proof lacks the empty clause")
        with drat_path.open("w", encoding="ascii", newline="\n") as stream:
            for line in proof:
                stream.write(line)
                stream.write("\n")
    finally:
        solver.delete()
    solve_seconds = time.perf_counter() - solve_started

    trim_started = time.perf_counter()
    completed = subprocess.run(
        [str(drat_trim), str(cnf_path), str(drat_path), "-L", str(lrat_path)],
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    trim_seconds = time.perf_counter() - trim_started
    if completed.returncode not in (0, 1) or "s VERIFIED" not in (
        completed.stdout + completed.stderr
    ):
        raise RuntimeError(f"drat-trim rejected node {spec.node_id or 'root'}")

    return NodeResult(
        node_id=spec.node_id,
        assignment=spec.assignment,
        cnf_path=str(cnf_path.relative_to(output)),
        drat_path=str(drat_path.relative_to(output)),
        lrat_path=str(lrat_path.relative_to(output)),
        cnf_sha256=sha256_file(cnf_path),
        drat_sha256=sha256_file(drat_path),
        lrat_sha256=sha256_file(lrat_path),
        drat_bytes=drat_path.stat().st_size,
        lrat_bytes=lrat_path.stat().st_size,
        solve_seconds=solve_seconds,
        trim_seconds=trim_seconds,
    )


def unforced_edge_variables(
    clauses: list[Clause], edge_variables: int
) -> list[int]:
    assignment: dict[int, bool] = {}
    changed = True
    while changed:
        changed = False
        for clause in clauses:
            unresolved: list[int] = []
            satisfied = False
            for literal in clause:
                value = assignment.get(abs(literal))
                if value is None:
                    unresolved.append(literal)
                elif value == (literal > 0):
                    satisfied = True
                    break
            if satisfied:
                continue
            if not unresolved:
                raise ValueError("base CNF is already refuted by unit propagation")
            if len(unresolved) == 1:
                literal = unresolved[0]
                old = assignment.get(abs(literal))
                value = literal > 0
                if old is not None and old != value:
                    raise ValueError("base CNF has conflicting unit propagation")
                if old is None:
                    assignment[abs(literal)] = value
                    changed = True
    return [
        variable
        for variable in range(1, edge_variables + 1)
        if variable not in assignment
    ]


def remove_internal_artifacts(output: Path, result: NodeResult) -> None:
    for relative in (result.cnf_path, result.drat_path, result.lrat_path):
        target = (output / relative).resolve()
        if output.resolve() not in target.parents:
            raise RuntimeError(f"refusing to remove artifact outside {output}: {target}")
        target.unlink()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--drat-trim", type=Path, required=True)
    parser.add_argument("--order", type=int, required=True)
    parser.add_argument("--max-lrat-bytes", type=int, required=True)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--skip-variables", type=int, default=0)
    parser.add_argument("--max-depth", type=int, default=64)
    arguments = parser.parse_args()

    variables, clauses = parse_dimacs(arguments.cnf)
    edge_variables = arguments.order * (arguments.order - 1) // 2
    choices = unforced_edge_variables(clauses, edge_variables)[arguments.skip_variables :]
    if not choices:
        raise ValueError("no unforced edge variables remain for splitting")
    arguments.output.mkdir(parents=True, exist_ok=False)
    for directory in ("cnf", "drat", "lrat"):
        (arguments.output / directory).mkdir()

    frontier = [NodeSpec(node_id="", assignment=())]
    leaves: list[NodeResult] = []
    internal: list[InternalRecord] = []
    depth = 0
    started = time.perf_counter()
    with ProcessPoolExecutor(max_workers=arguments.workers) as pool:
        while frontier:
            jobs = [
                (
                    spec,
                    variables,
                    clauses,
                    str(arguments.output),
                    str(arguments.drat_trim),
                )
                for spec in frontier
            ]
            results = list(pool.map(solve_node, jobs))
            next_frontier: list[NodeSpec] = []
            for result in results:
                if result.lrat_bytes <= arguments.max_lrat_bytes:
                    leaves.append(result)
                    continue
                if depth >= arguments.max_depth or depth >= len(choices):
                    raise RuntimeError(
                        f"oversized leaf {result.node_id or 'root'} remains at depth {depth}"
                    )
                split_variable = choices[depth]
                assigned = {abs(literal) for literal in result.assignment}
                if split_variable in assigned:
                    raise RuntimeError(f"split variable {split_variable} is already assigned")
                negative_id = result.node_id + "0"
                positive_id = result.node_id + "1"
                internal.append(
                    InternalRecord(
                        node_id=result.node_id,
                        assignment=result.assignment,
                        split_variable=split_variable,
                        negative_child=negative_id,
                        positive_child=positive_id,
                        discarded_lrat_bytes=result.lrat_bytes,
                        solve_seconds=result.solve_seconds,
                        trim_seconds=result.trim_seconds,
                    )
                )
                remove_internal_artifacts(arguments.output, result)
                next_frontier.extend(
                    [
                        NodeSpec(negative_id, (*result.assignment, -split_variable)),
                        NodeSpec(positive_id, (*result.assignment, split_variable)),
                    ]
                )
            depth += 1
            frontier = next_frontier

    manifest = {
        "schema": "tuza-q4-adaptive-cube-lrat-v1",
        "source_cnf": arguments.cnf.name,
        "source_cnf_sha256": sha256_file(arguments.cnf),
        "order": arguments.order,
        "edge_variables": edge_variables,
        "max_lrat_bytes": arguments.max_lrat_bytes,
        "workers": arguments.workers,
        "skip_variables": arguments.skip_variables,
        "candidate_variables": choices,
        "internal_nodes": [asdict(record) for record in internal],
        "leaves": [asdict(result) for result in leaves],
        "summary": {
            "internal_nodes": len(internal),
            "leaves": len(leaves),
            "maximum_depth": max((len(leaf.node_id) for leaf in leaves), default=0),
            "retained_lrat_bytes": sum(leaf.lrat_bytes for leaf in leaves),
            "largest_leaf_lrat_bytes": max(
                (leaf.lrat_bytes for leaf in leaves), default=0
            ),
            "elapsed_seconds": time.perf_counter() - started,
        },
    }
    (arguments.output / "manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(manifest["summary"], sort_keys=True))


if __name__ == "__main__":
    main()
