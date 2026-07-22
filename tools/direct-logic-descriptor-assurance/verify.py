#!/usr/bin/env python3
"""Independent JSON/evaluator checks for Lean direct-logic descriptors.

This is executable translation-validation evidence, not a proof that Python or
Rust refines the Lean denotation.  The Rust companion exercises the production
parser and prover; this script supplies a second parser/evaluator implementation
using only Python's standard library.
"""

from __future__ import annotations

import ast
import hashlib
import itertools
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
BABY_BEAR = 2_013_265_921

GABBAY_SOURCE = ROOT / "metatheory/Dregg2/Metatheory/GabbayDescriptorIR2PublicBinding.lean"
GABBAY_MARKER = "#guard publicDescriptorBytes =="
GABBAY_SHA256 = "fcdd33cbe483ea145c5f5e6aa736ab9192b98fd14b08f7db121a62b8cec53776"

BOOLGRAPH_SOURCE = (
    ROOT / "metatheory/Dregg2/Metatheory/DirectLogicBoolGraphDescriptorIR2.lean"
)
BOOLGRAPH_MARKER = "def factorPublicDescriptorJsonLiteral : String :="
BOOLGRAPH_SHA256 = "c0d3ccf8025cba07e7f79e1082eaa30836bc99d74502ad15daf7d6dac6433af9"


def guarded_lean_literal(path: Path, marker: str) -> str:
    source = path.read_text(encoding="utf-8")
    if source.count(marker) != 1:
        raise AssertionError(f"expected one marker {marker!r} in {path}")
    suffix = source.split(marker, 1)[1].lstrip()
    if not suffix.startswith('"'):
        raise AssertionError(f"marker {marker!r} is not followed by a string")

    escaped = False
    for end, character in enumerate(suffix[1:], start=1):
        if escaped:
            escaped = False
        elif character == "\\":
            escaped = True
        elif character == '"':
            literal = suffix[: end + 1]
            value = ast.literal_eval(literal)
            if not isinstance(value, str):
                raise AssertionError("Lean wire literal did not decode to text")
            return value
    raise AssertionError(f"unterminated string after marker {marker!r}")


def load_pinned(path: Path, marker: str, sha256: str) -> tuple[str, dict[str, Any]]:
    wire = guarded_lean_literal(path, marker)
    actual = hashlib.sha256(wire.encode()).hexdigest()
    if actual != sha256:
        raise AssertionError(f"descriptor byte pin changed: {actual} != {sha256}")
    decoded = json.loads(wire)
    if not isinstance(decoded, dict):
        raise AssertionError("descriptor JSON is not an object")
    return wire, decoded


def eval_expression(expression: dict[str, Any], row: list[int], next_row: list[int]) -> int:
    tag = expression["t"]
    if tag == "loc":
        return row[expression["c"]]
    if tag == "nxt":
        return next_row[expression["c"]]
    if tag == "const":
        return expression["v"] % BABY_BEAR
    if tag == "add":
        return (
            eval_expression(expression["l"], row, next_row)
            + eval_expression(expression["r"], row, next_row)
        ) % BABY_BEAR
    if tag == "mul":
        return (
            eval_expression(expression["l"], row, next_row)
            * eval_expression(expression["r"], row, next_row)
        ) % BABY_BEAR
    raise AssertionError(f"unsupported expression tag {tag!r}")


def accepts(descriptor: dict[str, Any], row: list[int], public: list[int]) -> bool:
    if len(row) != descriptor["trace_width"]:
        return False
    if len(public) != descriptor["public_input_count"]:
        return False
    for constraint in descriptor["constraints"]:
        tag = constraint["t"]
        if tag == "pi_binding":
            if constraint["row"] not in ("first", "last"):
                return False
            if (row[constraint["col"]] - public[constraint["pi_index"]]) % BABY_BEAR:
                return False
        elif tag == "window_gate":
            # Both committed specimens are one-row, always-on relations.
            if constraint["on_transition"]:
                return False
            if eval_expression(constraint["body"], row, row) % BABY_BEAR:
                return False
        else:
            raise AssertionError(f"unexpected constraint form {tag!r}")
    return True


def assert_identity_pi_layout(descriptor: dict[str, Any], count: int) -> None:
    for index, constraint in enumerate(descriptor["constraints"][:count]):
        assert constraint == {
            "t": "pi_binding",
            "row": "first",
            "col": index,
            "pi_index": index,
        }


def check_gabbay() -> int:
    wire, descriptor = load_pinned(GABBAY_SOURCE, GABBAY_MARKER, GABBAY_SHA256)
    assert len(wire.encode()) == 1_740
    assert descriptor["name"] == "dregg-gabbay-public-three-entry-direct-v2"
    assert descriptor["ir"] == 2
    assert descriptor["trace_width"] == 6
    assert descriptor["public_input_count"] == 6
    assert descriptor["tables"] == [{"id": 0, "name": "main", "arity": 6, "sem": "main"}]
    assert len(descriptor["constraints"]) == 7
    assert_identity_pi_layout(descriptor, 6)
    assert descriptor["hash_sites"] == []
    assert descriptor["ranges"] == []

    cases = 0
    for inputs in itertools.product(range(4), repeat=3):
        for outputs in itertools.product(range(5), repeat=3):
            row = [*inputs, *outputs]
            expected = all(output == input_ + 1 for input_, output in zip(inputs, outputs))
            assert accepts(descriptor, row, row) == expected, row
            cases += 1
    assert cases == 8_000

    honest = [5, 9, 17, 6, 10, 18]
    assert accepts(descriptor, honest, honest)
    tampered_public = honest.copy()
    tampered_public[4] += 1
    assert not accepts(descriptor, honest, tampered_public)

    for old, new in [('"trace_width":6', '"trace_width":7'), ('"v":1', '"v":2')]:
        tampered = wire.replace(old, new, 1)
        json.loads(tampered)  # still valid JSON; the pin, rather than syntax, refuses it
        assert hashlib.sha256(tampered.encode()).hexdigest() != GABBAY_SHA256
    return cases


def boolgraph_canonical(mask: int) -> tuple[list[int], list[int], bool]:
    truth = [bool(mask & (1 << atom)) for atom in range(4)]
    t0, t1, t2, t3 = truth
    or12 = t1 or t2
    output = t0 and or12
    public = [int(not t0), int(not t1), int(not t2), int(not t3)]
    row = [
        *public,
        int(t0),
        int(not t0),
        int(t1),
        int(not t1),
        int(t2),
        int(not t2),
        int(or12),
        int(output),
    ]
    source = (t0 and t1) or (t0 and t2)
    return row, public, source


def check_boolgraph() -> int:
    wire, descriptor = load_pinned(
        BOOLGRAPH_SOURCE, BOOLGRAPH_MARKER, BOOLGRAPH_SHA256
    )
    assert len(wire.encode()) == 2_654
    assert descriptor["name"] == "dregg-public-materialized-boolgraph-v2-4"
    assert descriptor["ir"] == 2
    assert descriptor["trace_width"] == 12
    assert descriptor["public_input_count"] == 4
    assert descriptor["tables"] == [{"id": 0, "name": "main", "arity": 12, "sem": "main"}]
    assert len(descriptor["constraints"]) == 18
    assert_identity_pi_layout(descriptor, 4)
    assert descriptor["hash_sites"] == []
    assert descriptor["ranges"] == []

    accepted = 0
    for mask in range(16):
        row, public, expected = boolgraph_canonical(mask)
        actual = accepts(descriptor, row, public)
        assert actual == expected, (mask, row)
        accepted += int(actual)
    assert accepted == 6

    honest, public, expected = boolgraph_canonical(0b0011)
    assert expected and accepts(descriptor, honest, public)
    tampered_public = public.copy()
    tampered_public[0] = 1
    assert not accepts(descriptor, honest, tampered_public)

    for old, new in [('"trace_width":12', '"trace_width":13'), ('"v":-1', '"v":-2')]:
        tampered = wire.replace(old, new, 1)
        json.loads(tampered)
        assert hashlib.sha256(tampered.encode()).hexdigest() != BOOLGRAPH_SHA256
    return 16


def main() -> None:
    gabbay_cases = check_gabbay()
    boolgraph_cases = check_boolgraph()
    print(
        "direct-logic descriptor translation validation: "
        f"Gabbay {gabbay_cases} exhaustive rows; "
        f"BoolGraph {boolgraph_cases} exhaustive truth assignments; all checks passed"
    )


if __name__ == "__main__":
    main()
