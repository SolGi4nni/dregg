#!/usr/bin/env python3
"""Semantics-first comparison harness for direct logic arithmetizations.

This is deliberately a relation evaluator and symbolic cost ledger, not a ZK
prover benchmark.  A lane is timed only after its semantic result is recorded,
and only passing, supported lane pairs are used to compute timing ratios.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import os
import platform
import random
import statistics
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Iterable, Sequence


BABY_BEAR = 2_013_265_921
BABY_BEAR_SQRT_NEG_ONE = 1_728_404_513
SEED = 0xD4E66
SUITE_VERSION = "direct-logic-v1"

BITLOGIC_SOURCE = {
    "title": "BitLogic from Modulus: zkFOL Bitcoin",
    "date": "2025-11-21",
    "repository": "https://github.com/ModulusZK/BitLogic-from-Modulus-zkFOL-Bitcoin",
    "commit": "26f125b37f0442d92991e3066095b1dfeb1b0ce4d",
    "pdf_sha256": "ea0e483ec9c7a3acfaae52ef0dfc0e07d141b760c2ce4b14461c1b89f324ba0c",
    "transcription": {
        "zero_means_true": True,
        "and": "P * Q",
        "or": "P + Q",
        "not": "1 - P",
        "forall": "product over H",
        "exists": "sum over H",
        "swap": "(A'-A+k)*(B'-B-f(k,s))*(A*B-A'*B')",
    },
}


@dataclass(frozen=True)
class Formula:
    kind: str
    atom: int | None = None
    children: tuple["Formula", ...] = ()

    def to_json(self) -> dict:
        out: dict[str, object] = {"kind": self.kind}
        if self.atom is not None:
            out["atom"] = self.atom
        if self.children:
            out["children"] = [child.to_json() for child in self.children]
        return out


def atom(index: int) -> Formula:
    return Formula("atom", atom=index)


def top() -> Formula:
    return Formula("top")


def bottom() -> Formula:
    return Formula("bottom")


def not_(p: Formula) -> Formula:
    return Formula("not", children=(p,))


def and_(left: Formula, right: Formula) -> Formula:
    return Formula("and", children=(left, right))


def or_(left: Formula, right: Formula) -> Formula:
    return Formula("or", children=(left, right))


def all_(children: Sequence[Formula]) -> Formula:
    return Formula("all", children=tuple(children))


def any_(children: Sequence[Formula]) -> Formula:
    return Formula("any", children=tuple(children))


@dataclass(frozen=True)
class Workload:
    workload_id: str
    formula: Formula
    residuals: tuple[int, ...]
    expected: bool
    family: str
    tags: tuple[str, ...]
    note: str = ""

    def to_json(self) -> dict:
        return {
            "workload_id": self.workload_id,
            "formula": self.formula.to_json(),
            "residuals": list(self.residuals),
            "expected": self.expected,
            "family": self.family,
            "tags": list(self.tags),
            "note": self.note,
        }


@dataclass(frozen=True)
class LaneOutcome:
    status: str
    accepted: bool | None
    output: int | None
    reason: str | None = None
    max_integer_accumulator: int | None = None


@dataclass(frozen=True)
class Cost:
    equations: int
    multiplications: int
    witnesses: int
    max_degree: int
    representation: str
    evidence: str


class Unsupported(Exception):
    def __init__(self, reason: str, max_accumulator: int | None = None):
        super().__init__(reason)
        self.reason = reason
        self.max_accumulator = max_accumulator


def reference_eval(formula: Formula, residuals: Sequence[int], modulus: int = BABY_BEAR) -> bool:
    kind = formula.kind
    if kind == "atom":
        assert formula.atom is not None
        return residuals[formula.atom] % modulus == 0
    if kind == "top":
        return True
    if kind == "bottom":
        return False
    if kind == "not":
        return not reference_eval(formula.children[0], residuals, modulus)
    values = [reference_eval(child, residuals, modulus) for child in formula.children]
    if kind in ("and", "all"):
        return all(values)
    if kind in ("or", "any"):
        return any(values)
    raise ValueError(f"unknown formula kind {kind!r}")


def _m_spec_residual(formula: Formula, residuals: Sequence[int], modulus: int) -> int:
    """Exact transcription of the operations printed in the BitLogic PDF."""
    kind = formula.kind
    if kind == "atom":
        assert formula.atom is not None
        return residuals[formula.atom] % modulus
    if kind == "top":
        return 0
    if kind == "bottom":
        return 1
    values = [_m_spec_residual(child, residuals, modulus) for child in formula.children]
    if kind == "not":
        return (1 - values[0]) % modulus
    if kind in ("and", "all"):
        return math.prod(values) % modulus
    if kind in ("or", "any"):
        return sum(values) % modulus
    raise ValueError(f"unknown formula kind {kind!r}")


def _g_field_residual(formula: Formula, residuals: Sequence[int], modulus: int) -> int:
    """Gabbay-style positive residuals, naively interpreted in a field."""
    kind = formula.kind
    if kind == "atom":
        assert formula.atom is not None
        value = residuals[formula.atom] % modulus
        return (value * value) % modulus
    if kind == "top":
        return 0
    if kind == "bottom":
        return 1
    if kind == "not":
        raise Unsupported("positive_fragment_has_no_general_negation")
    values = [_g_field_residual(child, residuals, modulus) for child in formula.children]
    if kind in ("and", "all"):
        return sum(values) % modulus
    if kind in ("or", "any"):
        return math.prod(values) % modulus
    raise ValueError(f"unknown formula kind {kind!r}")


def _d_nowrap_residual(formula: Formula, residuals: Sequence[int], modulus: int) -> tuple[int, int]:
    """Positive integer residual evaluation with a checked cast to the field."""
    kind = formula.kind
    if kind == "atom":
        assert formula.atom is not None
        value = residuals[formula.atom]
        squared = value * value
        if squared >= modulus:
            raise Unsupported("atom_square_not_below_modulus", squared)
        return squared, squared
    if kind == "top":
        return 0, 0
    if kind == "bottom":
        return 1, 1
    if kind == "not":
        raise Unsupported("positive_fragment_has_no_general_negation")
    evaluated = [_d_nowrap_residual(child, residuals, modulus) for child in formula.children]
    values = [value for value, _ in evaluated]
    prior_max = max((bound for _, bound in evaluated), default=0)
    if kind in ("and", "all"):
        result = sum(values)
    elif kind in ("or", "any"):
        result = math.prod(values)
    else:
        raise ValueError(f"unknown formula kind {kind!r}")
    maximum = max(prior_max, result)
    if result >= modulus:
        raise Unsupported("partial_accumulator_not_below_modulus", maximum)
    return result, maximum


def _falsebit_output(formula: Formula, residuals: Sequence[int], modulus: int) -> int:
    """Independent executable model of one-means-true Boolean graph gates."""
    kind = formula.kind
    if kind == "atom":
        assert formula.atom is not None
        return int(residuals[formula.atom] % modulus == 0)
    if kind == "top":
        return 1
    if kind == "bottom":
        return 0
    values = [_falsebit_output(child, residuals, modulus) for child in formula.children]
    if kind == "not":
        return 1 - values[0]
    if kind == "and":
        return values[0] * values[1]
    if kind == "or":
        return values[0] + values[1] - values[0] * values[1]
    if kind == "all":
        out = 1
        for value in values:
            out = out * value
        return out
    if kind == "any":
        out = 0
        for value in values:
            out = out + value - out * value
        return out
    raise ValueError(f"unknown formula kind {kind!r}")


def _conventional_output(formula: Formula, residuals: Sequence[int], modulus: int) -> int:
    """A separately written gate-by-gate arithmetic-circuit evaluator."""
    kind = formula.kind
    if kind == "atom":
        assert formula.atom is not None
        residual = residuals[formula.atom] % modulus
        return 1 if residual == 0 else 0
    if kind == "top":
        return 1
    if kind == "bottom":
        return 0
    if kind == "not":
        return 1 - _conventional_output(formula.children[0], residuals, modulus)
    child_bits = [_conventional_output(child, residuals, modulus) for child in formula.children]
    if kind in ("and", "all"):
        result = 1
        for bit in child_bits:
            result *= bit
        return result
    if kind in ("or", "any"):
        result = 0
        for bit in child_bits:
            result = 1 - ((1 - result) * (1 - bit))
        return result
    raise ValueError(f"unknown formula kind {kind!r}")


LANES = ("M-SPEC", "G-FIELD-NAIVE", "D-NOWRAP", "D-BOOLGRAPH", "C-AIR")


def evaluate_lane(lane: str, workload: Workload, modulus: int = BABY_BEAR) -> LaneOutcome:
    try:
        if lane == "M-SPEC":
            output = _m_spec_residual(workload.formula, workload.residuals, modulus)
            return LaneOutcome("supported", output == 0, output)
        if lane == "G-FIELD-NAIVE":
            output = _g_field_residual(workload.formula, workload.residuals, modulus)
            return LaneOutcome("supported", output == 0, output)
        if lane == "D-NOWRAP":
            output, maximum = _d_nowrap_residual(workload.formula, workload.residuals, modulus)
            return LaneOutcome("supported", output == 0, output % modulus, max_integer_accumulator=maximum)
        if lane == "D-BOOLGRAPH":
            output = _falsebit_output(workload.formula, workload.residuals, modulus)
            return LaneOutcome("supported", output == 1, output)
        if lane == "C-AIR":
            output = _conventional_output(workload.formula, workload.residuals, modulus)
            return LaneOutcome("supported", output == 1, output)
    except Unsupported as error:
        return LaneOutcome(
            "unsupported",
            None,
            None,
            reason=error.reason,
            max_integer_accumulator=error.max_accumulator,
        )
    raise ValueError(f"unknown lane {lane!r}")


def _left_associative(kind: str, count: int) -> Formula:
    assert count >= 1
    result = atom(0)
    constructor = and_ if kind == "and" else or_
    for index in range(1, count):
        result = constructor(result, atom(index))
    return result


def pinned_workloads() -> list[Workload]:
    cases: list[Workload] = [
        Workload("constant.top", top(), (), True, "semantic", ("constant",)),
        Workload("constant.bottom", bottom(), (), False, "semantic", ("constant",)),
        Workload("not.true", not_(atom(0)), (0,), False, "semantic", ("negation",)),
        Workload("not.false", not_(atom(0)), (7,), True, "semantic", ("negation",)),
        Workload(
            "gabbay.babybear-cancellation",
            and_(atom(0), atom(1)),
            (1, BABY_BEAR_SQRT_NEG_ONE),
            False,
            "adversarial",
            ("cancellation", "lean-regression"),
            "Mirrors babyBear_false_and_false_accepted: both squared residuals are nonzero but sum to zero in BabyBear.",
        ),
        Workload(
            "bitlogic.swap.honest",
            all_((atom(0), atom(1), atom(2))),
            (0, 0, 0),
            True,
            "transaction",
            ("swap", "public-equation"),
        ),
        Workload(
            "bitlogic.swap.output-mutation",
            all_((atom(0), atom(1), atom(2))),
            (0, 1, 0),
            False,
            "transaction",
            ("swap", "public-equation", "mutation"),
        ),
        Workload(
            "bitlogic.swap.invariant-mutation",
            all_((atom(0), atom(1), atom(2))),
            (0, 0, 1),
            False,
            "transaction",
            ("swap", "public-equation", "mutation"),
        ),
        Workload(
            "bitlogic.swap.published-invalid-witness",
            all_((atom(0), atom(1), atom(2))),
            (0, 988, -8_891),
            False,
            "transaction",
            ("swap", "public-equation", "lean-regression", "multi-fault"),
            "A=10, B=10, k=1, quotedOutput=1, A'=9, B'=999 from published_swap_accepts_invalid_witness.",
        ),
    ]

    for size in (1, 2, 4, 16, 64, 256, 1024):
        patterns = (
            ("all-true", (0,) * size),
            ("one-false", ((7,) + (0,) * (size - 1))),
            ("all-false", (7,) * size),
        )
        for label, residuals in patterns:
            cases.append(
                Workload(
                    f"forall.n{size}.{label}",
                    all_(tuple(atom(i) for i in range(size))),
                    residuals,
                    all(value % BABY_BEAR == 0 for value in residuals),
                    "quantifier",
                    ("forall", f"n={size}", label),
                )
            )
        any_patterns = (
            ("one-true", ((0,) + (7,) * (size - 1))),
            ("all-false", (7,) * size),
            ("all-true", (0,) * size),
        )
        for label, residuals in any_patterns:
            cases.append(
                Workload(
                    f"exists.n{size}.{label}",
                    any_(tuple(atom(i) for i in range(size))),
                    residuals,
                    any(value % BABY_BEAR == 0 for value in residuals),
                    "quantifier",
                    ("exists", f"n={size}", label),
                )
            )

    # Keep the deliberately left-associated depth below Python's recursion
    # limit.  The n=1024 homogeneous folds above use the n-ary representation
    # and still exercise the full cardinality requested by the protocol.
    for size in (2, 4, 16, 64, 256):
        residuals = tuple(0 if i % 3 else 5 for i in range(size))
        for connective in ("and", "or"):
            formula = _left_associative(connective, size)
            expected = all(r == 0 for r in residuals) if connective == "and" else any(r == 0 for r in residuals)
            cases.append(
                Workload(
                    f"{connective}.n{size}.mixed",
                    formula,
                    residuals,
                    expected,
                    "connective",
                    (connective, f"n={size}", "left-associated"),
                )
            )
    return cases


def _random_formula(rng: random.Random, depth: int, atom_count: int) -> Formula:
    if depth <= 0 or rng.random() < 0.28:
        choice = rng.randrange(atom_count + 2)
        if choice == atom_count:
            return top()
        if choice == atom_count + 1:
            return bottom()
        return atom(choice)
    kind = rng.choice(("not", "and", "or", "all", "any"))
    if kind == "not":
        return not_(_random_formula(rng, depth - 1, atom_count))
    if kind in ("and", "or"):
        left = _random_formula(rng, depth - 1, atom_count)
        right = _random_formula(rng, depth - 1, atom_count)
        return and_(left, right) if kind == "and" else or_(left, right)
    count = rng.randrange(0, 5)
    children = tuple(_random_formula(rng, depth - 1, atom_count) for _ in range(count))
    return all_(children) if kind == "all" else any_(children)


def random_workloads(count: int, seed: int = SEED) -> Iterable[Workload]:
    rng = random.Random(seed)
    for index in range(count):
        atom_count = rng.randrange(1, 9)
        residuals = tuple(rng.choice((-11, -3, -2, -1, 0, 1, 2, 3, 11)) for _ in range(atom_count))
        formula = _random_formula(rng, rng.randrange(1, 5), atom_count)
        expected = reference_eval(formula, residuals)
        yield Workload(
            f"generated.{index:05d}",
            formula,
            residuals,
            expected,
            "generated",
            (f"seed={seed}",),
        )


def semantic_conformance(workloads: Iterable[Workload]) -> tuple[dict, list[dict]]:
    counters = {
        lane: {
            "gate_status": "pass",
            "supported": 0,
            "unsupported": 0,
            "mismatches": 0,
            "unsupported_reasons": {},
        }
        for lane in LANES
    }
    records: list[dict] = []
    for workload in workloads:
        reference = reference_eval(workload.formula, workload.residuals)
        if reference != workload.expected:
            raise AssertionError(f"pinned expectation drift for {workload.workload_id}")
        for lane in LANES:
            outcome = evaluate_lane(lane, workload)
            match = outcome.accepted == reference if outcome.status == "supported" else None
            if outcome.status == "supported":
                counters[lane]["supported"] += 1
                if not match:
                    counters[lane]["mismatches"] += 1
                    counters[lane]["gate_status"] = "fail"
            else:
                counters[lane]["unsupported"] += 1
                reasons = counters[lane]["unsupported_reasons"]
                assert isinstance(reasons, dict)
                reasons[outcome.reason] = reasons.get(outcome.reason, 0) + 1
            records.append(
                {
                    "workload_id": workload.workload_id,
                    "family": workload.family,
                    "lane": lane,
                    "reference": reference,
                    "status": outcome.status,
                    "accepted": outcome.accepted,
                    "match": match,
                    "output": outcome.output,
                    "reason": outcome.reason,
                    "max_integer_accumulator": outcome.max_integer_accumulator,
                }
            )
    for lane in LANES:
        if counters[lane]["supported"] == 0:
            counters[lane]["gate_status"] = "unknown"
    gates = {
        "rule": "A semantic mismatch fails the lane. Explicitly unsupported formulas are counted, not treated as acceptance.",
        "modulus": BABY_BEAR,
        "seed": SEED,
        "lanes": counters,
    }
    return gates, records


def _formula_counts(formula: Formula) -> dict[str, int]:
    counts = {"atoms": 0, "not": 0, "and": 0, "or": 0, "all_items": 0, "any_items": 0}

    def visit(node: Formula) -> None:
        if node.kind == "atom":
            counts["atoms"] += 1
        elif node.kind in ("not", "and", "or"):
            counts[node.kind] += 1
        elif node.kind == "all":
            counts["all_items"] += len(node.children)
        elif node.kind == "any":
            counts["any_items"] += len(node.children)
        for child in node.children:
            visit(child)

    visit(formula)
    return counts


def _only_conjunction_of_atoms(formula: Formula) -> bool:
    if formula.kind == "atom":
        return True
    return formula.kind in ("and", "all") and all(_only_conjunction_of_atoms(c) for c in formula.children)


def _single_polynomial_degree(formula: Formula, lane: str) -> int:
    """Total degree of the inlined printed expression for the two spec lanes."""
    if formula.kind == "atom":
        return 1 if lane == "M-SPEC" else 2
    if formula.kind in ("top", "bottom"):
        return 0
    child_degrees = [_single_polynomial_degree(child, lane) for child in formula.children]
    if formula.kind == "not":
        return child_degrees[0]
    product_kinds = ("and", "all") if lane == "M-SPEC" else ("or", "any")
    if formula.kind in product_kinds:
        return sum(child_degrees)
    return max(child_degrees, default=0)


def _single_polynomial_multiplications(formula: Formula, lane: str) -> int:
    child_cost = sum(_single_polynomial_multiplications(child, lane) for child in formula.children)
    if formula.kind == "atom":
        return 0 if lane == "M-SPEC" else 1  # Gabbay equality residual is squared.
    product_kinds = ("and", "all") if lane == "M-SPEC" else ("or", "any")
    if formula.kind not in product_kinds:
        return child_cost
    if formula.kind in ("and", "or"):
        return child_cost + 1
    return child_cost + max(0, len(formula.children) - 1)


def symbolic_cost(lane: str, formula: Formula) -> Cost:
    c = _formula_counts(formula)
    binary = c["and"] + c["or"]
    folds = c["all_items"] + c["any_items"]
    if lane == "M-SPEC":
        # This is the public single-expression presentation, not a constraint graph.
        return Cost(
            1,
            _single_polynomial_multiplications(formula, lane),
            0,
            _single_polynomial_degree(formula, lane),
            "single_polynomial_expression",
            "E1 transcription",
        )
    if lane == "G-FIELD-NAIVE":
        return Cost(
            1,
            _single_polynomial_multiplications(formula, lane),
            0,
            _single_polynomial_degree(formula, lane),
            "single_polynomial_expression",
            "E1 transcription",
        )
    if lane == "D-NOWRAP":
        # Instantiate Positive.cost with one materialized square per signed
        # equality residual, then add one root-acceptance equation.
        equations = c["atoms"] + c["and"] + c["or"] + folds + 1
        multiplications = c["atoms"] + c["or"] + c["any_items"]
        witnesses = c["atoms"] + c["and"] + c["or"] + folds
        return Cost(equations, multiplications, witnesses, 2, "materialized_positive_graph", "E4 Lean recurrence + E2 mirror")
    if lane == "D-BOOLGRAPH":
        equations = 3 * c["atoms"] + 2 * c["not"] + 2 * (binary + folds) + 1
        multiplications = 3 * c["atoms"] + c["not"] + 2 * (binary + folds)
        witnesses = 2 * c["atoms"] + c["not"] + binary + folds
        return Cost(equations, multiplications, witnesses, 2, "materialized_boolean_graph", "E4 Lean recurrence + E2 mirror")
    if lane == "C-AIR":
        if _only_conjunction_of_atoms(formula):
            # Production optimization: constrain each externally supplied residual directly.
            return Cost(c["atoms"], 0, 0, 1, "optimized_conjunction_constraints", "E1 conventional baseline model")
        equations = 3 * c["atoms"] + 2 * c["not"] + 2 * (binary + folds) + 1
        multiplications = 3 * c["atoms"] + c["not"] + 2 * (binary + folds)
        witnesses = 2 * c["atoms"] + c["not"] + binary + folds
        return Cost(equations, multiplications, witnesses, 2, "materialized_boolean_graph", "E1 conventional baseline model")
    raise ValueError(lane)


def _percentile(values: Sequence[float], q: float) -> float:
    ordered = sorted(values)
    return ordered[min(len(ordered) - 1, max(0, math.ceil(q * len(ordered)) - 1))]


def _bootstrap_mean_ci(values: Sequence[float], seed: int, resamples: int = 1000) -> tuple[float, float]:
    rng = random.Random(seed)
    means = []
    for _ in range(resamples):
        means.append(statistics.fmean(rng.choice(values) for _ in values))
    return _percentile(means, 0.025), _percentile(means, 0.975)


def _timed_sample(lane: str, workload: Workload, iterations: int) -> tuple[float, int]:
    checksum = 0
    start = time.perf_counter_ns()
    for _ in range(iterations):
        result = evaluate_lane(lane, workload)
        checksum = ((checksum * 131) + (result.output or 0) + (1 if result.accepted else 0)) & 0xFFFFFFFF
    elapsed = time.perf_counter_ns() - start
    return elapsed / iterations, checksum


def microbench(
    workloads: Sequence[Workload], gates: dict, samples: int, iterations: int, warmups: int
) -> tuple[list[dict], list[dict]]:
    raw: list[dict] = []
    stats: list[dict] = []
    for workload_index, workload in enumerate(workloads):
        for lane_index, lane in enumerate(LANES):
            outcome = evaluate_lane(lane, workload)
            if outcome.status != "supported":
                continue
            for _ in range(warmups):
                _timed_sample(lane, workload, max(1, iterations // 10))
            values: list[float] = []
            checksum = 0
            for sample in range(samples):
                ns_per_eval, sample_checksum = _timed_sample(lane, workload, iterations)
                checksum ^= sample_checksum
                values.append(ns_per_eval)
                raw.append(
                    {
                        "workload_id": workload.workload_id,
                        "lane": lane,
                        "sample": sample,
                        "iterations": iterations,
                        "ns_per_relation_evaluation": ns_per_eval,
                        "semantic_gate_status": gates["lanes"][lane]["gate_status"],
                        "workload_conformant": outcome.accepted == workload.expected,
                    }
                )
            ci_low, ci_high = _bootstrap_mean_ci(values, SEED + workload_index * 17 + lane_index)
            stats.append(
                {
                    "workload_id": workload.workload_id,
                    "lane": lane,
                    "samples": samples,
                    "iterations_per_sample": iterations,
                    "median_ns": statistics.median(values),
                    "p95_ns": _percentile(values, 0.95),
                    "mean_ns": statistics.fmean(values),
                    "stdev_ns": statistics.stdev(values) if len(values) > 1 else 0.0,
                    "bootstrap_mean_ci95_low_ns": ci_low,
                    "bootstrap_mean_ci95_high_ns": ci_high,
                    "checksum": checksum,
                    "eligible_for_speedup": gates["lanes"][lane]["gate_status"] == "pass"
                    and outcome.accepted == workload.expected,
                }
            )
    return raw, stats


def _sha256_json(value: object) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def _git_head(cwd: Path) -> str | None:
    try:
        return subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=cwd, check=True, capture_output=True, text=True
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def _write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def _write_csv(path: Path, rows: Sequence[dict]) -> None:
    if not rows:
        path.write_text("")
        return
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def _build_summary(gates: dict, stats: Sequence[dict], cost_rows: Sequence[dict]) -> dict:
    by_workload_lane = {(row["workload_id"], row["lane"]): row for row in stats}
    timing_ratios: list[dict] = []
    for (workload_id, lane), row in sorted(by_workload_lane.items()):
        if lane not in ("D-NOWRAP", "D-BOOLGRAPH") or not row["eligible_for_speedup"]:
            continue
        baseline = by_workload_lane.get((workload_id, "C-AIR"))
        if not baseline or not baseline["eligible_for_speedup"]:
            continue
        timing_ratios.append(
            {
                "workload_id": workload_id,
                "candidate": lane,
                "baseline": "C-AIR",
                "baseline_over_candidate_evaluator_ratio": baseline["median_ns"] / row["median_ns"],
                "scope": "Python relation evaluator only; not proving, verification, finality, or monetary cost",
            }
        )
    return {
        "suite_version": SUITE_VERSION,
        "gate_status": {lane: data["gate_status"] for lane, data in gates["lanes"].items()},
        "timing_ratios": timing_ratios,
        "symbolic_cost_rows": list(cost_rows),
        "excluded_from_speedups": [
            lane for lane, data in gates["lanes"].items() if data["gate_status"] != "pass"
        ],
        "claim_boundary": (
            "This run measures Python relation-evaluator throughput and backend-neutral symbolic costs. "
            "It contains no proof generation, proof verification, FHE, deployment, finality, or monetary-cost measurement."
        ),
    }


def _summary_markdown(meta: dict, gates: dict, summary: dict, stats: Sequence[dict]) -> str:
    lines = [
        "# Direct logic benchmark run",
        "",
        f"- Suite: `{SUITE_VERSION}`",
        f"- Run: `{meta['run_id']}`",
        f"- BabyBear modulus: `{BABY_BEAR}`",
        f"- Deterministic generated-case seed: `{SEED}`",
        "",
        "## Semantic admission gate",
        "",
        "| lane | gate | supported | unsupported | mismatches |",
        "|---|---:|---:|---:|---:|",
    ]
    for lane in LANES:
        data = gates["lanes"][lane]
        lines.append(
            f"| `{lane}` | {data['gate_status']} | {data['supported']} | {data['unsupported']} | {data['mismatches']} |"
        )
    lines.extend(
        [
            "",
            "A failing lane is retained as a falsification artifact but excluded from every speedup.",
            "An unsupported D-NOWRAP row means the required integer accumulator bound was not established; it is not silently cast.",
            "",
            "## Measurement boundary",
            "",
            summary["claim_boundary"],
            "The public `M-SPEC` lane is an executable transcription of equations, not a public Modulus prover implementation.",
            "",
            f"Aggregate timing rows: {len(stats)}; see `samples.csv` and `samples.jsonl` for raw samples.",
            "See `summary.json` for eligible per-workload evaluator ratios; they are intentionally not called prover speedups.",
            "",
        ]
    )
    return "\n".join(lines)


def run(args: argparse.Namespace) -> Path:
    script_dir = Path(__file__).resolve().parent
    repo_root = script_dir.parents[1]
    pinned = pinned_workloads()
    generated = list(random_workloads(args.random_cases, args.seed))
    all_workloads = pinned + generated
    gates, conformance_rows = semantic_conformance(all_workloads)

    cost_rows: list[dict] = []
    for workload in pinned:
        for lane in LANES:
            cost = symbolic_cost(lane, workload.formula)
            cost_rows.append({"workload_id": workload.workload_id, "lane": lane, **asdict(cost)})

    raw_samples: list[dict] = []
    stats: list[dict] = []
    if not args.no_timing:
        raw_samples, stats = microbench(pinned, gates, args.samples, args.iterations, args.warmups)

    inputs = [workload.to_json() for workload in all_workloads]
    run_id = args.run_id or datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + _sha256_json(inputs)[:12]
    output = Path(args.output) if args.output else script_dir / "artifacts" / run_id
    output.mkdir(parents=True, exist_ok=False)

    meta = {
        "suite_version": SUITE_VERSION,
        "run_id": run_id,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "command": sys.argv,
        "repository_head": _git_head(repo_root),
        "workload_sha256": _sha256_json(inputs),
        "harness_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "seed": args.seed,
        "random_cases": args.random_cases,
        "modulus": BABY_BEAR,
        "timing": {
            "enabled": not args.no_timing,
            "samples": args.samples,
            "iterations_per_sample": args.iterations,
            "warmups": args.warmups,
            "clock": "time.perf_counter_ns",
            "scope": "Python relation evaluator; no prover or verifier",
        },
        "environment": {
            "python": sys.version,
            "platform": platform.platform(),
            "machine": platform.machine(),
            "processor": platform.processor(),
            "cpu_count": os.cpu_count(),
        },
        "external_specification": BITLOGIC_SOURCE,
        "formal_cost_sources": [
            "metatheory/Dregg2/Metatheory/ArithmetizationCost.lean",
            "metatheory/Dregg2/Logic/BoolGraph.lean",
            "metatheory/Dregg2/Metatheory/FOLArithmetizationCorrected.lean",
        ],
    }
    summary = _build_summary(gates, stats, cost_rows)

    _write_json(output / "META.json", meta)
    _write_json(output / "workloads.json", inputs)
    _write_json(output / "gates.json", {**gates, "results": conformance_rows})
    _write_json(output / "costs.json", cost_rows)
    _write_csv(output / "costs.csv", cost_rows)
    _write_csv(output / "samples.csv", raw_samples)
    with (output / "samples.jsonl").open("w") as handle:
        for row in raw_samples:
            handle.write(json.dumps(row, sort_keys=True) + "\n")
    _write_json(output / "stats.json", stats)
    _write_json(output / "summary.json", summary)
    (output / "SUMMARY.md").write_text(_summary_markdown(meta, gates, summary, stats))
    return output


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="new output directory (default: artifacts/<run-id>)")
    parser.add_argument("--run-id", help="explicit run identifier")
    parser.add_argument("--seed", type=int, default=SEED)
    parser.add_argument("--random-cases", type=int, default=10_000)
    parser.add_argument("--samples", type=int, default=9)
    parser.add_argument("--iterations", type=int, default=250)
    parser.add_argument("--warmups", type=int, default=2)
    parser.add_argument("--no-timing", action="store_true")
    args = parser.parse_args(argv)
    if args.random_cases < 0 or args.samples < 1 or args.iterations < 1 or args.warmups < 0:
        parser.error("counts must be nonnegative; samples and iterations must be positive")
    return args


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    output = run(args)
    gates = json.loads((output / "gates.json").read_text())["lanes"]
    print(output)
    for lane in LANES:
        data = gates[lane]
        print(
            f"{lane:14s} gate={data['gate_status']:4s} "
            f"supported={data['supported']:5d} unsupported={data['unsupported']:5d} mismatches={data['mismatches']:5d}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
