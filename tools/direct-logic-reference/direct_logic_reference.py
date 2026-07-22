#!/usr/bin/env python3
"""Canonical reference compiler for DREGG's corrected direct-logic plans.

This is an executable specification, not a prover benchmark.  It compiles a
bounded, finite source formula and one concrete model to two independently
checkable witness plans:

* ``nowrap``: squared nonnegative equality residuals, addition for conjunction
  and multiplication for disjunction, with a static ``< modulus`` certificate
  attached to every materialized value before projection to the field;
* ``boolean``: one-means-true Boolean wires with inverse-witness zero tests and
  quadratic Boolean gates over a checked prime field.

The output is canonical JSON.  The outer hash commits to the canonical bytes of
the inner artifact, avoiding any self-referential hash convention.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence


SOURCE_SCHEMA = "dregg.direct-logic.source.v1"
ARTIFACT_SCHEMA = "dregg.direct-logic.artifact.v1"
HYBRID_ARTIFACT_SCHEMA = "dregg.direct-logic.hybrid-artifact.v1"
EVALUATION_SCHEMA = "dregg.direct-logic.evaluation.v1"
CHECK_SCHEMA = "dregg.direct-logic.check.v1"
COMPILER_ID = "dregg-direct-logic-reference/1"
OPTIMIZER_ID = "dregg-direct-logic-hybrid/1"
DEFAULT_MODULUS = 2_013_265_921
MAX_INPUT_INTEGER = (1 << 63) - 1
MAX_EXPANDED_NODES = 10_000


class ReferenceError(ValueError):
    """A fail-closed source, artifact, or plan validation error."""


def canonical_bytes(value: object) -> bytes:
    """The repository's canonical JSON profile: sorted compact ASCII + LF."""
    return (
        json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("ascii")


def sha256_json(value: object) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def _object(value: object, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ReferenceError(f"{where}: expected object")
    if not all(isinstance(key, str) for key in value):
        raise ReferenceError(f"{where}: object keys must be strings")
    return value


def _array(value: object, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise ReferenceError(f"{where}: expected array")
    return value


def _keys(obj: Mapping[str, object], allowed: set[str], required: set[str], where: str) -> None:
    missing = required - set(obj)
    extra = set(obj) - allowed
    if missing:
        raise ReferenceError(f"{where}: missing keys {sorted(missing)!r}")
    if extra:
        raise ReferenceError(f"{where}: unknown keys {sorted(extra)!r}")


def _string(value: object, where: str) -> str:
    if not isinstance(value, str) or not value:
        raise ReferenceError(f"{where}: expected nonempty string")
    return value


def _nat(value: object, where: str, maximum: int = MAX_INPUT_INTEGER) -> int:
    # bool is an int subclass and is deliberately rejected.
    if isinstance(value, bool) or not isinstance(value, int):
        raise ReferenceError(f"{where}: expected natural number")
    if value < 0 or value > maximum:
        raise ReferenceError(f"{where}: expected 0 <= value <= {maximum}")
    return value


def _is_prime(n: int) -> bool:
    """Deterministic Miller-Rabin for the accepted unsigned 63-bit range."""
    if n < 2:
        return False
    small_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for prime in small_primes:
        if n == prime:
            return True
        if n % prime == 0:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2
    # This base set is deterministic for every n < 2^64.
    for base in (2, 325, 9_375, 28_178, 450_775, 9_780_504, 1_795_265_022):
        if base % n == 0:
            continue
        x = pow(base, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _normalize_term(raw: object, where: str, counter: list[int]) -> dict[str, Any]:
    counter[0] += 1
    if counter[0] > MAX_EXPANDED_NODES:
        raise ReferenceError("source exceeds node limit")
    obj = _object(raw, where)
    op = _string(obj.get("op"), f"{where}.op")
    if op == "lit":
        _keys(obj, {"op", "value"}, {"op", "value"}, where)
        return {"op": "lit", "value": _nat(obj["value"], f"{where}.value")}
    if op == "var":
        _keys(obj, {"op", "name"}, {"op", "name"}, where)
        return {"name": _string(obj["name"], f"{where}.name"), "op": "var"}
    if op in ("add", "mul"):
        _keys(obj, {"op", "args"}, {"op", "args"}, where)
        args = _array(obj["args"], f"{where}.args")
        if len(args) != 2:
            raise ReferenceError(f"{where}.args: {op} requires exactly two terms")
        return {
            "args": [
                _normalize_term(args[0], f"{where}.args[0]", counter),
                _normalize_term(args[1], f"{where}.args[1]", counter),
            ],
            "op": op,
        }
    raise ReferenceError(f"{where}.op: unsupported term operation {op!r}")


def _normalize_formula(raw: object, where: str, counter: list[int]) -> dict[str, Any]:
    counter[0] += 1
    if counter[0] > MAX_EXPANDED_NODES:
        raise ReferenceError("source exceeds node limit")
    obj = _object(raw, where)
    op = _string(obj.get("op"), f"{where}.op")
    if op in ("top", "bottom"):
        _keys(obj, {"op"}, {"op"}, where)
        return {"op": op}
    if op == "eq":
        _keys(obj, {"op", "lhs", "rhs"}, {"op", "lhs", "rhs"}, where)
        return {
            "lhs": _normalize_term(obj["lhs"], f"{where}.lhs", counter),
            "op": "eq",
            "rhs": _normalize_term(obj["rhs"], f"{where}.rhs", counter),
        }
    if op == "not":
        _keys(obj, {"op", "arg"}, {"op", "arg"}, where)
        return {"arg": _normalize_formula(obj["arg"], f"{where}.arg", counter), "op": "not"}
    if op in ("and", "or"):
        _keys(obj, {"op", "args"}, {"op", "args"}, where)
        args = _array(obj["args"], f"{where}.args")
        if len(args) != 2:
            raise ReferenceError(f"{where}.args: {op} requires exactly two formulae")
        return {
            "args": [
                _normalize_formula(args[0], f"{where}.args[0]", counter),
                _normalize_formula(args[1], f"{where}.args[1]", counter),
            ],
            "op": op,
        }
    if op in ("forall", "exists"):
        _keys(obj, {"op", "binder", "domain", "body"}, {"op", "binder", "domain", "body"}, where)
        binder = _string(obj["binder"], f"{where}.binder")
        domain = [_nat(x, f"{where}.domain[{i}]") for i, x in enumerate(_array(obj["domain"], f"{where}.domain"))]
        if domain != sorted(set(domain)):
            raise ReferenceError(f"{where}.domain: canonical domains are strictly increasing")
        return {
            "binder": binder,
            "body": _normalize_formula(obj["body"], f"{where}.body", counter),
            "domain": domain,
            "op": op,
        }
    raise ReferenceError(f"{where}.op: unsupported formula operation {op!r}")


def normalize_source(raw: object) -> dict[str, Any]:
    obj = _object(raw, "source")
    _keys(obj, {"schema", "modulus", "model", "formula"}, {"schema", "model", "formula"}, "source")
    if obj["schema"] != SOURCE_SCHEMA:
        raise ReferenceError(f"source.schema: expected {SOURCE_SCHEMA!r}")
    modulus = _nat(obj.get("modulus", DEFAULT_MODULUS), "source.modulus")
    if not _is_prime(modulus):
        raise ReferenceError("source.modulus: Boolean zero tests require a prime field")
    model_raw = _array(obj["model"], "source.model")
    model: list[dict[str, Any]] = []
    names: set[str] = set()
    for index, raw_entry in enumerate(model_raw):
        where = f"source.model[{index}]"
        entry = _object(raw_entry, where)
        _keys(entry, {"name", "value", "bound"}, {"name", "value", "bound"}, where)
        name = _string(entry["name"], f"{where}.name")
        if name in names:
            raise ReferenceError(f"{where}.name: duplicate model variable {name!r}")
        names.add(name)
        value = _nat(entry["value"], f"{where}.value")
        bound = _nat(entry["bound"], f"{where}.bound")
        if value > bound:
            raise ReferenceError(f"{where}: model value exceeds declared bound")
        model.append({"bound": bound, "name": name, "value": value})
    model.sort(key=lambda entry: entry["name"])
    counter = [0]
    formula = _normalize_formula(obj["formula"], "source.formula", counter)
    normalized = {"formula": formula, "model": model, "modulus": modulus, "schema": SOURCE_SCHEMA}
    _validate_names(normalized)
    return normalized


def _validate_names(source: Mapping[str, Any]) -> None:
    free = {entry["name"] for entry in source["model"]}

    def term(t: Mapping[str, Any], bound: set[str], where: str) -> None:
        if t["op"] == "var":
            if t["name"] not in free and t["name"] not in bound:
                raise ReferenceError(f"{where}: unbound variable {t['name']!r}")
        for index, child in enumerate(t.get("args", [])):
            term(child, bound, f"{where}.args[{index}]")

    def formula(f: Mapping[str, Any], bound: set[str], where: str) -> None:
        op = f["op"]
        if op == "eq":
            term(f["lhs"], bound, f"{where}.lhs")
            term(f["rhs"], bound, f"{where}.rhs")
        elif op == "not":
            formula(f["arg"], bound, f"{where}.arg")
        elif op in ("and", "or"):
            for index, child in enumerate(f["args"]):
                formula(child, bound, f"{where}.args[{index}]")
        elif op in ("forall", "exists"):
            name = f["binder"]
            if name in free or name in bound:
                raise ReferenceError(f"{where}.binder: shadowing is forbidden in canonical source")
            formula(f["body"], bound | {name}, f"{where}.body")

    formula(source["formula"], set(), "source.formula")


@dataclass(frozen=True)
class TermResult:
    value: int
    bound: int
    additions: int
    multiplications: int


def _term_eval(term: Mapping[str, Any], values: Mapping[str, int], bounds: Mapping[str, int]) -> TermResult:
    op = term["op"]
    if op == "lit":
        return TermResult(term["value"], term["value"], 0, 0)
    if op == "var":
        return TermResult(values[term["name"]], bounds[term["name"]], 0, 0)
    left = _term_eval(term["args"][0], values, bounds)
    right = _term_eval(term["args"][1], values, bounds)
    if op == "add":
        return TermResult(
            left.value + right.value,
            left.bound + right.bound,
            left.additions + right.additions + 1,
            left.multiplications + right.multiplications,
        )
    if op == "mul":
        return TermResult(
            left.value * right.value,
            left.bound * right.bound,
            left.additions + right.additions,
            left.multiplications + right.multiplications + 1,
        )
    raise AssertionError(op)


def evaluate_source(source: Mapping[str, Any]) -> bool:
    values = {entry["name"]: entry["value"] for entry in source["model"]}
    bounds = {entry["name"]: entry["bound"] for entry in source["model"]}

    def evaluate(formula: Mapping[str, Any], local_values: dict[str, int], local_bounds: dict[str, int]) -> bool:
        op = formula["op"]
        if op == "top":
            return True
        if op == "bottom":
            return False
        if op == "eq":
            return _term_eval(formula["lhs"], local_values, local_bounds).value == _term_eval(
                formula["rhs"], local_values, local_bounds
            ).value
        if op == "not":
            return not evaluate(formula["arg"], local_values, local_bounds)
        if op == "and":
            # Deliberately evaluate both sides: plans are relations, not short-circuit programs.
            results = [evaluate(child, local_values, local_bounds) for child in formula["args"]]
            return all(results)
        if op == "or":
            results = [evaluate(child, local_values, local_bounds) for child in formula["args"]]
            return any(results)
        identity = op == "forall"
        results = []
        for value in formula["domain"]:
            next_values = dict(local_values)
            next_bounds = dict(local_bounds)
            next_values[formula["binder"]] = value
            next_bounds[formula["binder"]] = value
            results.append(evaluate(formula["body"], next_values, next_bounds))
        return all(results) if op == "forall" else any(results)

    return evaluate(source["formula"], values, bounds)


class PlanBuilder:
    def __init__(self, prefix: str, modulus: int):
        self.prefix = prefix
        self.modulus = modulus
        self.nodes: list[dict[str, Any]] = []
        self.term_additions = 0
        self.term_multiplications = 0

    def add(self, node: dict[str, Any]) -> str:
        node_id = f"{self.prefix}{len(self.nodes)}"
        self.nodes.append({"id": node_id, **node})
        if len(self.nodes) > MAX_EXPANDED_NODES:
            raise ReferenceError("grounded plan exceeds node limit")
        return node_id

    def node(self, node_id: str) -> dict[str, Any]:
        index = int(node_id[len(self.prefix) :])
        if index >= len(self.nodes) or self.nodes[index]["id"] != node_id:
            raise ReferenceError(f"plan contains invalid node reference {node_id!r}")
        return self.nodes[index]


def _base_env(source: Mapping[str, Any]) -> tuple[dict[str, int], dict[str, int]]:
    return (
        {entry["name"]: entry["value"] for entry in source["model"]},
        {entry["name"]: entry["bound"] for entry in source["model"]},
    )


def _ground_fold(
    builder: PlanBuilder,
    roots: Sequence[str],
    empty_node: dict[str, Any],
    gate: str,
    combine: Any,
) -> str:
    if not roots:
        return builder.add(empty_node)
    level = list(roots)
    # Deterministic balanced reduction keeps relation depth logarithmic.
    while len(level) > 1:
        next_level: list[str] = []
        for index in range(0, len(level), 2):
            if index + 1 == len(level):
                next_level.append(level[index])
            else:
                next_level.append(combine(level[index], level[index + 1], gate))
        level = next_level
    return level[0]


class BooleanUnsupported(Exception):
    def __init__(self, reason: str, bound: int):
        super().__init__(reason)
        self.reason = reason
        self.bound = bound


def _compile_boolean(source: Mapping[str, Any]) -> dict[str, Any]:
    modulus = source["modulus"]
    builder = PlanBuilder("b", modulus)
    free_values, free_bounds = _base_env(source)

    def binary(left_id: str, right_id: str, kind: str) -> str:
        left = builder.node(left_id)["out"]
        right = builder.node(right_id)["out"]
        out = left * right if kind == "and" else left + right - left * right
        return builder.add({"inputs": [left_id, right_id], "kind": kind, "out": out % modulus})

    def compile_formula(formula: Mapping[str, Any], values: dict[str, int], bounds: dict[str, int], scope: list[dict[str, int]]) -> str:
        op = formula["op"]
        if op in ("top", "bottom"):
            return builder.add({"kind": "constant", "out": 1 if op == "top" else 0})
        if op == "eq":
            lhs = _term_eval(formula["lhs"], values, bounds)
            rhs = _term_eval(formula["rhs"], values, bounds)
            difference_bound = max(lhs.bound, rhs.bound)
            # The zero gate is exact over the field only after proving that a
            # nonzero integer difference cannot be a multiple of the modulus.
            if difference_bound >= modulus:
                raise BooleanUnsupported("term_difference_bound_not_below_modulus", difference_bound)
            builder.term_additions += lhs.additions + rhs.additions
            builder.term_multiplications += lhs.multiplications + rhs.multiplications
            signed = lhs.value - rhs.value
            residual = signed % modulus
            out = 1 if residual == 0 else 0
            inverse = 0 if residual == 0 else pow(residual, modulus - 2, modulus)
            return builder.add(
                {
                    "inverse": inverse,
                    "kind": "zero_test",
                    "integer_difference_bound": difference_bound,
                    "lhs_bound": lhs.bound,
                    "lhs_value": lhs.value,
                    "out": out,
                    "residual": residual,
                    "rhs_bound": rhs.bound,
                    "rhs_value": rhs.value,
                    "scope": scope,
                    "signed_residual": signed,
                }
            )
        if op == "not":
            child_id = compile_formula(formula["arg"], values, bounds, scope)
            return builder.add({"input": child_id, "kind": "not", "out": 1 - builder.node(child_id)["out"]})
        if op in ("and", "or"):
            left = compile_formula(formula["args"][0], values, bounds, scope)
            right = compile_formula(formula["args"][1], values, bounds, scope)
            return binary(left, right, op)
        roots = []
        for value in formula["domain"]:
            next_values = dict(values)
            next_bounds = dict(bounds)
            next_values[formula["binder"]] = value
            next_bounds[formula["binder"]] = value
            roots.append(
                compile_formula(
                    formula["body"],
                    next_values,
                    next_bounds,
                    scope + [{"name": formula["binder"], "value": value}],
                )
            )
        gate = "and" if op == "forall" else "or"
        return _ground_fold(
            builder,
            roots,
            {"kind": "constant", "out": 1 if op == "forall" else 0},
            gate,
            binary,
        )

    try:
        root = compile_formula(source["formula"], free_values, free_bounds, [])
    except BooleanUnsupported as error:
        return {
            "certificate": {
                "modulus": modulus,
                "required_minimum_modulus": error.bound + 1,
                "term_difference_bound": error.bound,
            },
            "reason": error.reason,
            "status": "unsupported",
        }
    root_value = builder.node(root)["out"]
    counts = {kind: sum(node["kind"] == kind for node in builder.nodes) for kind in ("zero_test", "not", "and", "or")}
    equations = 3 * counts["zero_test"] + 2 * (counts["not"] + counts["and"] + counts["or"]) + 1
    multiplications = 3 * counts["zero_test"] + counts["not"] + 2 * (counts["and"] + counts["or"])
    witnesses = 2 * counts["zero_test"] + counts["not"] + counts["and"] + counts["or"]
    max_degree = 2 if any(counts.values()) else 1
    return {
        "acceptance": {"expected_root": 1, "satisfied": root_value == 1},
        "certificate": {
            "field_prime": True,
            "integer_atom_projection_exact": True,
            "gate_counts": counts,
            "logic_cost": {
                "equations": equations,
                "max_degree": max_degree,
                "multiplications": multiplications,
                "witnesses": witnesses,
            },
            "representation": "materialized_one_true_boolean_graph",
            "term_evaluation_cost": {
                "additions": builder.term_additions,
                "multiplications": builder.term_multiplications,
                "scope": "reference evaluation of equality terms; separate from logic graph cost",
            },
            "zero_test": "b*(b-1)=0; x*b=0; x*inv=1-b",
        },
        "nodes": builder.nodes,
        "root": root,
        "status": "admitted",
    }


class NoWrapUnsupported(Exception):
    def __init__(self, reason: str):
        super().__init__(reason)
        self.reason = reason


def _compile_nowrap(source: Mapping[str, Any]) -> dict[str, Any]:
    modulus = source["modulus"]
    builder = PlanBuilder("n", modulus)
    free_values, free_bounds = _base_env(source)

    def combine(left_id: str, right_id: str, kind: str) -> str:
        left = builder.node(left_id)
        right = builder.node(right_id)
        if kind == "add":
            integer_value = left["integer_value"] + right["integer_value"]
            static_bound = left["static_bound"] + right["static_bound"]
        else:
            integer_value = left["integer_value"] * right["integer_value"]
            static_bound = left["static_bound"] * right["static_bound"]
        return builder.add(
            {
                "field_value": integer_value % modulus,
                "inputs": [left_id, right_id],
                "integer_value": integer_value,
                "kind": kind,
                "static_bound": static_bound,
            }
        )

    def compile_formula(formula: Mapping[str, Any], values: dict[str, int], bounds: dict[str, int], scope: list[dict[str, int]]) -> str:
        op = formula["op"]
        if op in ("top", "bottom"):
            value = 0 if op == "top" else 1
            return builder.add({"field_value": value, "integer_value": value, "kind": "constant", "static_bound": value})
        if op == "eq":
            lhs = _term_eval(formula["lhs"], values, bounds)
            rhs = _term_eval(formula["rhs"], values, bounds)
            builder.term_additions += lhs.additions + rhs.additions
            builder.term_multiplications += lhs.multiplications + rhs.multiplications
            signed = lhs.value - rhs.value
            integer_value = signed * signed
            static_bound = max(lhs.bound, rhs.bound) ** 2
            return builder.add(
                {
                    "field_value": integer_value % modulus,
                    "integer_value": integer_value,
                    "kind": "square",
                    "lhs_bound": lhs.bound,
                    "lhs_value": lhs.value,
                    "rhs_bound": rhs.bound,
                    "rhs_value": rhs.value,
                    "scope": scope,
                    "signed_residual": signed,
                    "static_bound": static_bound,
                }
            )
        if op == "not":
            raise NoWrapUnsupported("negation_outside_positive_fragment")
        if op in ("and", "or"):
            left = compile_formula(formula["args"][0], values, bounds, scope)
            right = compile_formula(formula["args"][1], values, bounds, scope)
            return combine(left, right, "add" if op == "and" else "mul")
        roots = []
        for value in formula["domain"]:
            next_values = dict(values)
            next_bounds = dict(bounds)
            next_values[formula["binder"]] = value
            next_bounds[formula["binder"]] = value
            roots.append(
                compile_formula(
                    formula["body"],
                    next_values,
                    next_bounds,
                    scope + [{"name": formula["binder"], "value": value}],
                )
            )
        gate = "add" if op == "forall" else "mul"
        empty_value = 0 if op == "forall" else 1
        return _ground_fold(
            builder,
            roots,
            {
                "field_value": empty_value % modulus,
                "integer_value": empty_value,
                "kind": "constant",
                "static_bound": empty_value,
            },
            gate,
            combine,
        )

    try:
        root = compile_formula(source["formula"], free_values, free_bounds, [])
    except NoWrapUnsupported as error:
        return {"reason": error.reason, "status": "unsupported"}

    max_static_bound = max(node["static_bound"] for node in builder.nodes)
    violating = [node["id"] for node in builder.nodes if node["static_bound"] >= modulus]
    if violating:
        return {
            "certificate": {
                "max_static_bound": max_static_bound,
                "modulus": modulus,
                "required_minimum_modulus": max_static_bound + 1,
                "violating_nodes": violating,
            },
            "reason": "static_residual_bound_not_below_modulus",
            "status": "unsupported",
        }
    root_value = builder.node(root)["integer_value"]
    counts = {kind: sum(node["kind"] == kind for node in builder.nodes) for kind in ("square", "add", "mul")}
    equations = counts["square"] + counts["add"] + counts["mul"] + 1
    multiplications = counts["square"] + counts["mul"]
    witnesses = counts["square"] + counts["add"] + counts["mul"]
    max_degree = 2 if counts["square"] + counts["mul"] else 1
    return {
        "acceptance": {"expected_root": 0, "satisfied": root_value == 0},
        "certificate": {
            "bound_rule": "every nonnegative materialized residual and partial accumulator is strictly below modulus before projection",
            "field_projection_exact": True,
            "gate_counts": counts,
            "logic_cost": {
                "equations": equations,
                "max_degree": max_degree,
                "multiplications": multiplications,
                "witnesses": witnesses,
            },
            "max_static_bound": max_static_bound,
            "modulus": modulus,
            "representation": "materialized_positive_residual_graph",
            "term_evaluation_cost": {
                "additions": builder.term_additions,
                "multiplications": builder.term_multiplications,
                "scope": "reference evaluation of equality terms; separate from logic graph cost",
            },
        },
        "nodes": builder.nodes,
        "root": root,
        "status": "admitted",
    }


# ---------------------------------------------------------------------------
# Hybrid presentation optimizer
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class HybridCost:
    equations: int = 0
    multiplications: int = 0
    witnesses: int = 0
    conversions: int = 0
    materialized_nodes: int = 0
    max_degree: int = 0

    def plus(self, other: "HybridCost") -> "HybridCost":
        return HybridCost(
            equations=self.equations + other.equations,
            multiplications=self.multiplications + other.multiplications,
            witnesses=self.witnesses + other.witnesses,
            conversions=self.conversions + other.conversions,
            materialized_nodes=self.materialized_nodes + other.materialized_nodes,
            max_degree=max(self.max_degree, other.max_degree),
        )

    def with_acceptance(self) -> "HybridCost":
        return self.plus(HybridCost(equations=1, max_degree=1))

    def objective(self) -> tuple[int, int, int, int, int]:
        # Multiplications lead because this optimizer targets symbolic
        # algebraic work; the complete vector is still emitted and never
        # called wall-clock time.
        return (
            self.multiplications,
            self.equations,
            self.witnesses,
            self.conversions,
            self.materialized_nodes,
        )

    def to_json(self) -> dict[str, int]:
        return {
            "conversions": self.conversions,
            "equations": self.equations,
            "materialized_nodes": self.materialized_nodes,
            "max_degree": self.max_degree,
            "multiplications": self.multiplications,
            "witnesses": self.witnesses,
        }


HYBRID_GATE_COSTS = {
    "constant": HybridCost(materialized_nodes=1),
    "residual_square": HybridCost(1, 1, 1, 0, 1, 2),
    "residual_add": HybridCost(1, 0, 1, 0, 1, 1),
    "residual_mul": HybridCost(1, 1, 1, 0, 1, 2),
    "boolean_zero_test": HybridCost(3, 3, 2, 0, 1, 2),
    "boolean_not": HybridCost(2, 1, 1, 0, 1, 2),
    "boolean_and": HybridCost(2, 2, 1, 0, 1, 2),
    "boolean_or": HybridCost(2, 2, 1, 0, 1, 2),
    "residual_to_boolean": HybridCost(3, 3, 2, 1, 1, 2),
    "boolean_to_residual": HybridCost(1, 0, 1, 1, 1, 1),
}


@dataclass(frozen=True)
class HybridCandidate:
    representation: str
    kind: str
    value: int
    bound: int
    cost: HybridCost
    children: tuple["HybridCandidate", ...] = ()
    metadata: Mapping[str, Any] | None = None


def _candidate(
    representation: str,
    kind: str,
    value: int,
    bound: int,
    children: Sequence[HybridCandidate] = (),
    metadata: Mapping[str, Any] | None = None,
) -> HybridCandidate:
    cost = HYBRID_GATE_COSTS[kind]
    for child in children:
        cost = cost.plus(child.cost)
    return HybridCandidate(representation, kind, value, bound, cost, tuple(children), metadata)


def _choose(candidates: Sequence[HybridCandidate | None]) -> HybridCandidate | None:
    admitted = [candidate for candidate in candidates if candidate is not None]
    if not admitted:
        return None
    # Python's stable min implements the documented native-before-conversion,
    # residual-before-Boolean tie break supplied by each caller's list order.
    return min(admitted, key=lambda candidate: candidate.cost.objective())


def _balanced_ground(kind: str, children: Sequence[dict[str, Any]]) -> dict[str, Any]:
    if not children:
        return {"op": "top" if kind == "and" else "bottom"}
    level = list(children)
    while len(level) > 1:
        next_level: list[dict[str, Any]] = []
        for index in range(0, len(level), 2):
            if index + 1 == len(level):
                next_level.append(level[index])
            else:
                next_level.append({"args": [level[index], level[index + 1]], "op": kind})
        level = next_level
    return level[0]


def _ground_source(source: Mapping[str, Any]) -> dict[str, Any]:
    values, bounds = _base_env(source)
    count = [0]

    def ground(
        formula: Mapping[str, Any],
        local_values: dict[str, int],
        local_bounds: dict[str, int],
        scope: list[dict[str, int]],
    ) -> dict[str, Any]:
        count[0] += 1
        if count[0] > MAX_EXPANDED_NODES:
            raise ReferenceError("grounded formula exceeds node limit")
        op = formula["op"]
        if op in ("top", "bottom"):
            return {"op": op}
        if op == "eq":
            lhs = _term_eval(formula["lhs"], local_values, local_bounds)
            rhs = _term_eval(formula["rhs"], local_values, local_bounds)
            return {
                "lhs_bound": lhs.bound,
                "lhs_value": lhs.value,
                "op": "eq",
                "rhs_bound": rhs.bound,
                "rhs_value": rhs.value,
                "scope": scope,
                "signed_residual": lhs.value - rhs.value,
                "term_additions": lhs.additions + rhs.additions,
                "term_multiplications": lhs.multiplications + rhs.multiplications,
            }
        if op == "not":
            return {"arg": ground(formula["arg"], local_values, local_bounds, scope), "op": "not"}
        if op in ("and", "or"):
            return {
                "args": [
                    ground(formula["args"][0], local_values, local_bounds, scope),
                    ground(formula["args"][1], local_values, local_bounds, scope),
                ],
                "op": op,
            }
        children = []
        for value in formula["domain"]:
            next_values = dict(local_values)
            next_bounds = dict(local_bounds)
            next_values[formula["binder"]] = value
            next_bounds[formula["binder"]] = value
            children.append(
                ground(
                    formula["body"],
                    next_values,
                    next_bounds,
                    scope + [{"name": formula["binder"], "value": value}],
                )
            )
        return _balanced_ground("and" if op == "forall" else "or", children)

    return ground(source["formula"], values, bounds, [])


@dataclass(frozen=True)
class HybridState:
    residual_candidates: tuple[HybridCandidate, ...]
    boolean_candidates: tuple[HybridCandidate, ...]
    pure_residual: HybridCandidate | None
    pure_boolean: HybridCandidate | None

    @property
    def best_residual(self) -> HybridCandidate | None:
        return _choose(self.residual_candidates)

    @property
    def best_boolean(self) -> HybridCandidate | None:
        return _choose(self.boolean_candidates)


def _prune_residual(candidates: Sequence[HybridCandidate]) -> tuple[HybridCandidate, ...]:
    """Keep the cost/bound Pareto frontier needed by enclosing residuals."""
    kept: list[HybridCandidate] = []
    for index, candidate in enumerate(candidates):
        dominated = False
        for other_index, other in enumerate(candidates):
            if other_index == index:
                continue
            cheaper = other.cost.objective() < candidate.cost.objective()
            same_but_earlier = (
                other.cost.objective() == candidate.cost.objective()
                and other.bound == candidate.bound
                and other_index < index
            )
            if other.bound <= candidate.bound and (cheaper or same_but_earlier):
                dominated = True
                break
        if not dominated:
            kept.append(candidate)
    return tuple(kept)


def _prune_boolean(candidates: Sequence[HybridCandidate]) -> tuple[HybridCandidate, ...]:
    best = _choose(candidates)
    return () if best is None else (best,)


def _as_boolean(residual: HybridCandidate, modulus: int) -> HybridCandidate:
    x = residual.value % modulus
    out = 1 if x == 0 else 0
    inverse = 0 if x == 0 else pow(x, modulus - 2, modulus)
    return _candidate(
        "boolean",
        "residual_to_boolean",
        out,
        1,
        [residual],
        {"inverse": inverse, "residual": x},
    )


def _as_residual(boolean: HybridCandidate) -> HybridCandidate:
    return _candidate(
        "residual",
        "boolean_to_residual",
        1 - boolean.value,
        1,
        [boolean],
    )


def _solve_hybrid(ground: Mapping[str, Any], modulus: int) -> tuple[HybridState, int]:
    states = 0

    def solve(node: Mapping[str, Any]) -> HybridState:
        nonlocal states
        states += 1
        op = node["op"]
        native_residuals: list[HybridCandidate] = []
        native_booleans: list[HybridCandidate] = []
        pure_residual: HybridCandidate | None = None
        pure_boolean: HybridCandidate | None = None

        if op in ("top", "bottom"):
            truth = op == "top"
            native_residuals.append(
                _candidate("residual", "constant", 0 if truth else 1, 0 if truth else 1)
            )
            native_booleans.append(_candidate("boolean", "constant", 1 if truth else 0, 1))
            pure_residual = native_residuals[0]
            pure_boolean = native_booleans[0]
        elif op == "eq":
            signed = node["signed_residual"]
            difference_bound = max(node["lhs_bound"], node["rhs_bound"])
            metadata = dict(node)
            metadata.pop("op")
            if difference_bound**2 < modulus:
                native_residuals.append(
                    _candidate(
                        "residual",
                        "residual_square",
                        signed * signed,
                        difference_bound**2,
                        metadata=metadata,
                    )
                )
                pure_residual = native_residuals[0]
            if difference_bound < modulus:
                residual = signed % modulus
                native_booleans.append(
                    _candidate(
                        "boolean",
                        "boolean_zero_test",
                        1 if residual == 0 else 0,
                        1,
                        metadata={
                            **metadata,
                            "integer_difference_bound": difference_bound,
                            "inverse": 0 if residual == 0 else pow(residual, modulus - 2, modulus),
                            "residual": residual,
                        },
                    )
                )
                pure_boolean = native_booleans[0]
        elif op == "not":
            child = solve(node["arg"])
            for child_boolean in child.boolean_candidates:
                native_booleans.append(
                    _candidate("boolean", "boolean_not", 1 - child_boolean.value, 1, [child_boolean])
                )
            if child.pure_boolean is not None:
                pure_boolean = _candidate(
                    "boolean", "boolean_not", 1 - child.pure_boolean.value, 1, [child.pure_boolean]
                )
        else:
            left = solve(node["args"][0])
            right = solve(node["args"][1])
            residual_kind = "residual_add" if op == "and" else "residual_mul"
            boolean_kind = "boolean_and" if op == "and" else "boolean_or"

            def residual_binary(a: HybridCandidate, b: HybridCandidate) -> HybridCandidate | None:
                value = a.value + b.value if op == "and" else a.value * b.value
                bound = a.bound + b.bound if op == "and" else a.bound * b.bound
                if bound >= modulus:
                    return None
                return _candidate("residual", residual_kind, value, bound, [a, b])

            def boolean_binary(a: HybridCandidate, b: HybridCandidate) -> HybridCandidate:
                value = a.value * b.value if op == "and" else a.value + b.value - a.value * b.value
                return _candidate("boolean", boolean_kind, value, 1, [a, b])

            for left_residual in left.residual_candidates:
                for right_residual in right.residual_candidates:
                    candidate = residual_binary(left_residual, right_residual)
                    if candidate is not None:
                        native_residuals.append(candidate)
            for left_boolean in left.boolean_candidates:
                for right_boolean in right.boolean_candidates:
                    native_booleans.append(boolean_binary(left_boolean, right_boolean))
            if left.pure_residual is not None and right.pure_residual is not None:
                pure_residual = residual_binary(left.pure_residual, right.pure_residual)
            if left.pure_boolean is not None and right.pure_boolean is not None:
                pure_boolean = boolean_binary(left.pure_boolean, right.pure_boolean)

        residual_candidates = _prune_residual(
            native_residuals + [_as_residual(candidate) for candidate in native_booleans]
        )
        boolean_candidates = _prune_boolean(
            native_booleans + [_as_boolean(candidate, modulus) for candidate in native_residuals]
        )
        return HybridState(residual_candidates, boolean_candidates, pure_residual, pure_boolean)

    return solve(ground), states


def _candidate_summary(candidate: HybridCandidate | None) -> dict[str, Any]:
    if candidate is None:
        return {
            "reason": "no_pure_presentation_under_single_field_bounds",
            "status": "unsupported",
        }
    cost = candidate.cost.with_acceptance()
    return {
        "cost": cost.to_json(),
        "objective_score": list(cost.objective()),
        "representation": candidate.representation,
        "status": "admitted",
    }


def _emit_hybrid(candidate: HybridCandidate, modulus: int) -> tuple[list[dict[str, Any]], str]:
    nodes: list[dict[str, Any]] = []

    def emit(current: HybridCandidate) -> str:
        child_ids = [emit(child) for child in current.children]
        node_id = f"h{len(nodes)}"
        node: dict[str, Any] = {
            "id": node_id,
            "kind": current.kind,
            "representation": current.representation,
        }
        if child_ids:
            node["inputs"] = child_ids
        if current.representation == "boolean":
            node["out"] = current.value
        else:
            node.update(
                {
                    "field_value": current.value % modulus,
                    "integer_value": current.value,
                    "static_bound": current.bound,
                }
            )
        if current.metadata:
            node.update(current.metadata)
        nodes.append(node)
        return node_id

    root = emit(candidate)
    return nodes, root


def _ground_metrics(ground: Mapping[str, Any]) -> dict[str, int]:
    metrics = {"atoms": 0, "formula_nodes": 0, "term_additions": 0, "term_multiplications": 0}

    def visit(node: Mapping[str, Any]) -> None:
        metrics["formula_nodes"] += 1
        if node["op"] == "eq":
            metrics["atoms"] += 1
            metrics["term_additions"] += node["term_additions"]
            metrics["term_multiplications"] += node["term_multiplications"]
        elif node["op"] == "not":
            visit(node["arg"])
        elif node["op"] in ("and", "or"):
            visit(node["args"][0])
            visit(node["args"][1])

    visit(ground)
    return metrics


def optimize_source(raw_source: object) -> dict[str, Any]:
    source = normalize_source(raw_source)
    ground = _ground_source(source)
    state, state_count = _solve_hybrid(ground, source["modulus"])
    selected = _choose([*state.residual_candidates, *state.boolean_candidates])
    pure_boolean = _candidate_summary(state.pure_boolean)
    pure_nowrap = _candidate_summary(state.pure_residual)
    metrics = _ground_metrics(ground)
    if selected is None:
        plan: dict[str, Any] = {
            "baselines": {"all_boolean": pure_boolean, "all_nowrap": pure_nowrap},
            "reason": "no_faithful_single_field_presentation",
            "status": "unsupported",
        }
    else:
        nodes, root = _emit_hybrid(selected, source["modulus"])
        selected_cost = selected.cost.with_acceptance()
        source_value = evaluate_source(source)
        observed = selected.value == (1 if selected.representation == "boolean" else 0)
        boolean_score = (
            tuple(pure_boolean["objective_score"]) if pure_boolean["status"] == "admitted" else None
        )
        plan = {
            "acceptance": {
                "expected_root": 1 if selected.representation == "boolean" else 0,
                "satisfied": observed,
            },
            "baselines": {"all_boolean": pure_boolean, "all_nowrap": pure_nowrap},
            "certificate": {
                "cost": selected_cost.to_json(),
                "field_prime": True,
                "ground_metrics": metrics,
                "objective_order": [
                    "multiplications",
                    "equations",
                    "witnesses",
                    "conversions",
                    "materialized_nodes",
                ],
                "objective_score": list(selected_cost.objective()),
                "optimal_over_enumerated_presentations": True,
                "strictly_cheaper_than_all_boolean":
                    boolean_score is not None and selected_cost.objective() < boolean_score,
                "term_evaluation_scope": "reported separately; identical grounded equality terms for every presentation",
            },
            "nodes": nodes,
            "root": root,
            "root_representation": selected.representation,
            "status": "admitted",
        }
        if observed != source_value:
            raise AssertionError("hybrid optimizer violated source semantics")
    artifact = {
        "compiler": COMPILER_ID,
        "optimizer": {
            "dp_states": state_count * 2,
            "id": OPTIMIZER_ID,
            "search": "exhaustive dynamic program over residual/boolean representation at every grounded subformula",
            "tie_break": "native before conversion; residual before boolean at the root",
        },
        "plan": plan,
        "schema": HYBRID_ARTIFACT_SCHEMA,
        "source": source,
        "source_semantics": {"value": evaluate_source(source)},
        "source_sha256": sha256_json(source),
    }
    return {"artifact": artifact, "sha256": sha256_json(artifact)}


def compile_source(raw_source: object) -> dict[str, Any]:
    source = normalize_source(raw_source)
    artifact = {
        "compiler": COMPILER_ID,
        "plans": {"boolean": _compile_boolean(source), "nowrap": _compile_nowrap(source)},
        "schema": ARTIFACT_SCHEMA,
        "source": source,
        "source_semantics": {"value": evaluate_source(source)},
        "source_sha256": sha256_json(source),
    }
    return {"artifact": artifact, "sha256": sha256_json(artifact)}


def _check_boolean_plan(plan: Mapping[str, Any], modulus: int) -> bool:
    if plan.get("status") == "unsupported":
        return plan.get("reason") == "term_difference_bound_not_below_modulus"
    if plan.get("status") != "admitted":
        return False
    values: dict[str, int] = {}
    for node in plan["nodes"]:
        kind = node["kind"]
        out = node["out"]
        if out not in (0, 1):
            return False
        if kind == "constant":
            pass
        elif kind == "zero_test":
            x = node["residual"]
            inv = node["inverse"]
            if node["integer_difference_bound"] >= modulus:
                return False
            if x * out % modulus != 0 or x * inv % modulus != (1 - out) % modulus:
                return False
        elif kind == "not":
            if out != 1 - values[node["input"]]:
                return False
        elif kind in ("and", "or"):
            left, right = (values[node_id] for node_id in node["inputs"])
            expected = left * right if kind == "and" else left + right - left * right
            if out != expected % modulus:
                return False
        else:
            return False
        values[node["id"]] = out
    acceptance = plan["acceptance"]
    if acceptance["expected_root"] != 1:
        return False
    return acceptance["satisfied"] == (values.get(plan["root"]) == 1)


def _check_nowrap_plan(plan: Mapping[str, Any], modulus: int) -> bool:
    if plan.get("status") == "unsupported":
        return plan.get("reason") in {
            "negation_outside_positive_fragment",
            "static_residual_bound_not_below_modulus",
        }
    if plan.get("status") != "admitted":
        return False
    values: dict[str, tuple[int, int]] = {}
    for node in plan["nodes"]:
        kind = node["kind"]
        value = node["integer_value"]
        bound = node["static_bound"]
        if value < 0 or value > bound or bound >= modulus or node["field_value"] != value % modulus:
            return False
        if kind == "constant":
            pass
        elif kind == "square":
            if value != node["signed_residual"] ** 2:
                return False
        elif kind in ("add", "mul"):
            left, right = (values[node_id] for node_id in node["inputs"])
            expected_value = left[0] + right[0] if kind == "add" else left[0] * right[0]
            expected_bound = left[1] + right[1] if kind == "add" else left[1] * right[1]
            if (value, bound) != (expected_value, expected_bound):
                return False
        else:
            return False
        values[node["id"]] = (value, bound)
    root_value = values[plan["root"]][0]
    acceptance = plan["acceptance"]
    if acceptance["expected_root"] != 0:
        return False
    return acceptance["satisfied"] == (root_value == 0)


def _check_hybrid_plan(plan: Mapping[str, Any], modulus: int, source_value: bool) -> bool:
    if plan.get("status") == "unsupported":
        return plan.get("reason") == "no_faithful_single_field_presentation"
    if plan.get("status") != "admitted":
        return False
    values: dict[str, tuple[str, int, int]] = {}
    reconstructed_cost = HybridCost()
    for index, node in enumerate(plan["nodes"]):
        if node.get("id") != f"h{index}":
            return False
        kind = node.get("kind")
        representation = node.get("representation")
        if kind not in HYBRID_GATE_COSTS or representation not in ("residual", "boolean"):
            return False
        reconstructed_cost = reconstructed_cost.plus(HYBRID_GATE_COSTS[kind])
        inputs = node.get("inputs", [])
        if any(node_id not in values for node_id in inputs):
            return False

        if representation == "boolean":
            out = node.get("out")
            if out not in (0, 1):
                return False
            value, bound = out, 1
        else:
            value = node.get("integer_value")
            bound = node.get("static_bound")
            if not isinstance(value, int) or not isinstance(bound, int):
                return False
            if value < 0 or value > bound or bound >= modulus:
                return False
            if node.get("field_value") != value % modulus:
                return False

        if kind == "constant":
            if inputs or value not in (0, 1):
                return False
        elif kind == "residual_square":
            if representation != "residual" or inputs:
                return False
            signed = node.get("signed_residual")
            expected_bound = max(node.get("lhs_bound"), node.get("rhs_bound")) ** 2
            if signed != node.get("lhs_value") - node.get("rhs_value"):
                return False
            if value != signed * signed or bound != expected_bound:
                return False
        elif kind == "boolean_zero_test":
            if representation != "boolean" or inputs:
                return False
            signed = node.get("signed_residual")
            difference_bound = max(node.get("lhs_bound"), node.get("rhs_bound"))
            residual = signed % modulus
            if signed != node.get("lhs_value") - node.get("rhs_value"):
                return False
            if node.get("integer_difference_bound") != difference_bound or difference_bound >= modulus:
                return False
            if node.get("residual") != residual:
                return False
            if residual * out % modulus != 0:
                return False
            if residual * node.get("inverse") % modulus != (1 - out) % modulus:
                return False
        elif kind == "residual_add" or kind == "residual_mul":
            if representation != "residual" or len(inputs) != 2:
                return False
            left = values[inputs[0]]
            right = values[inputs[1]]
            if left[0] != "residual" or right[0] != "residual":
                return False
            expected_value = left[1] + right[1] if kind == "residual_add" else left[1] * right[1]
            expected_bound = left[2] + right[2] if kind == "residual_add" else left[2] * right[2]
            if (value, bound) != (expected_value, expected_bound):
                return False
        elif kind in ("boolean_not", "boolean_and", "boolean_or"):
            if representation != "boolean":
                return False
            if kind == "boolean_not":
                if len(inputs) != 1 or values[inputs[0]][0] != "boolean":
                    return False
                expected = 1 - values[inputs[0]][1]
            else:
                if len(inputs) != 2 or any(values[node_id][0] != "boolean" for node_id in inputs):
                    return False
                left, right = values[inputs[0]][1], values[inputs[1]][1]
                expected = left * right if kind == "boolean_and" else left + right - left * right
            if out != expected:
                return False
        elif kind == "residual_to_boolean":
            if representation != "boolean" or len(inputs) != 1 or values[inputs[0]][0] != "residual":
                return False
            residual = values[inputs[0]][1] % modulus
            if node.get("residual") != residual:
                return False
            if residual * out % modulus != 0:
                return False
            if residual * node.get("inverse") % modulus != (1 - out) % modulus:
                return False
        elif kind == "boolean_to_residual":
            if representation != "residual" or len(inputs) != 1 or values[inputs[0]][0] != "boolean":
                return False
            if (value, bound) != (1 - values[inputs[0]][1], 1):
                return False
        else:
            return False
        values[node["id"]] = (representation, value, bound)

    root = plan.get("root")
    if root not in values:
        return False
    root_representation, root_value, _ = values[root]
    if plan.get("root_representation") != root_representation:
        return False
    expected_root = 1 if root_representation == "boolean" else 0
    acceptance = plan.get("acceptance", {})
    satisfied = root_value == expected_root
    if acceptance.get("expected_root") != expected_root or acceptance.get("satisfied") != satisfied:
        return False
    if satisfied != source_value:
        return False
    reconstructed_cost = reconstructed_cost.with_acceptance()
    certificate = plan.get("certificate", {})
    if certificate.get("cost") != reconstructed_cost.to_json():
        return False
    if certificate.get("objective_score") != list(reconstructed_cost.objective()):
        return False
    return True


def check_hybrid_wrapper(raw_wrapper: object) -> tuple[bool, str]:
    try:
        wrapper = _object(raw_wrapper, "wrapper")
        _keys(wrapper, {"artifact", "sha256"}, {"artifact", "sha256"}, "wrapper")
        if not isinstance(wrapper["sha256"], str) or wrapper["sha256"] != sha256_json(wrapper["artifact"]):
            return False, "artifact_hash_mismatch"
        artifact = _object(wrapper["artifact"], "wrapper.artifact")
        if artifact.get("schema") != HYBRID_ARTIFACT_SCHEMA:
            return False, "artifact_version_mismatch"
        if artifact.get("compiler") != COMPILER_ID or artifact.get("optimizer", {}).get("id") != OPTIMIZER_ID:
            return False, "artifact_version_mismatch"
        expected = optimize_source(artifact.get("source"))
        if wrapper != expected:
            return False, "artifact_recompilation_mismatch"
        if not _check_hybrid_plan(
            artifact["plan"], artifact["source"]["modulus"], artifact["source_semantics"]["value"]
        ):
            return False, "hybrid_plan_invalid"
        return True, "ok"
    except (KeyError, IndexError, TypeError, ReferenceError, ValueError):
        return False, "malformed_artifact"


def check_wrapper(raw_wrapper: object) -> tuple[bool, str]:
    try:
        wrapper = _object(raw_wrapper, "wrapper")
        _keys(wrapper, {"artifact", "sha256"}, {"artifact", "sha256"}, "wrapper")
        artifact_probe = _object(wrapper["artifact"], "wrapper.artifact")
        if artifact_probe.get("schema") == HYBRID_ARTIFACT_SCHEMA:
            return check_hybrid_wrapper(raw_wrapper)
        if not isinstance(wrapper["sha256"], str) or wrapper["sha256"] != sha256_json(wrapper["artifact"]):
            return False, "artifact_hash_mismatch"
        artifact = artifact_probe
        if artifact.get("schema") != ARTIFACT_SCHEMA or artifact.get("compiler") != COMPILER_ID:
            return False, "artifact_version_mismatch"
        expected = compile_source(artifact.get("source"))
        if wrapper != expected:
            return False, "artifact_recompilation_mismatch"
        modulus = artifact["source"]["modulus"]
        if not _check_boolean_plan(artifact["plans"]["boolean"], modulus):
            return False, "boolean_plan_invalid"
        if not _check_nowrap_plan(artifact["plans"]["nowrap"], modulus):
            return False, "nowrap_plan_invalid"
        boolean = artifact["plans"]["boolean"]
        if boolean["status"] == "admitted":
            boolean_accepts = boolean["acceptance"]["satisfied"]
            if boolean_accepts != artifact["source_semantics"]["value"]:
                return False, "boolean_semantics_mismatch"
        nowrap = artifact["plans"]["nowrap"]
        if nowrap["status"] == "admitted" and nowrap["acceptance"]["satisfied"] != artifact["source_semantics"]["value"]:
            return False, "nowrap_semantics_mismatch"
        return True, "ok"
    except (KeyError, IndexError, TypeError, ReferenceError, ValueError):
        return False, "malformed_artifact"


def _read_json(path: str) -> object:
    data = sys.stdin.buffer.read() if path == "-" else Path(path).read_bytes()
    try:
        return json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ReferenceError(f"invalid JSON: {error}") from error


def _write_json(value: object, path: str | None) -> None:
    data = canonical_bytes(value)
    if path is None or path == "-":
        sys.stdout.buffer.write(data)
    else:
        destination = Path(path)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    compile_parser = subparsers.add_parser("compile", help="compile source JSON to a hashed canonical artifact")
    compile_parser.add_argument("input", help="source JSON path, or - for stdin")
    compile_parser.add_argument("-o", "--output", help="artifact path; stdout by default")
    optimize_parser = subparsers.add_parser(
        "optimize", help="search residual/Boolean presentations and emit a hashed hybrid artifact"
    )
    optimize_parser.add_argument("input", help="source JSON path, or - for stdin")
    optimize_parser.add_argument("-o", "--output", help="artifact path; stdout by default")
    evaluate_parser = subparsers.add_parser("evaluate", help="evaluate source semantics without compiling plans")
    evaluate_parser.add_argument("input", help="source JSON path, or - for stdin")
    evaluate_parser.add_argument("-o", "--output", help="result path; stdout by default")
    check_parser = subparsers.add_parser("check", help="recompile and validate a hashed artifact")
    check_parser.add_argument("input", help="artifact JSON path, or - for stdin")
    check_parser.add_argument("-o", "--output", help="check result path; stdout by default")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        raw = _read_json(args.input)
        if args.command == "compile":
            result = compile_source(raw)
        elif args.command == "optimize":
            result = optimize_source(raw)
        elif args.command == "evaluate":
            source = normalize_source(raw)
            result = {
                "schema": EVALUATION_SCHEMA,
                "source_sha256": sha256_json(source),
                "value": evaluate_source(source),
            }
        else:
            ok, reason = check_wrapper(raw)
            result = {"ok": ok, "reason": reason, "schema": CHECK_SCHEMA}
            _write_json(result, args.output)
            return 0 if ok else 1
        _write_json(result, args.output)
        return 0
    except (OSError, ReferenceError) as error:
        sys.stderr.buffer.write(canonical_bytes({"error": str(error), "ok": False}))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
