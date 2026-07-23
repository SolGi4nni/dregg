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
# Pinned to the REPAIRED descriptor (three linear acceptance atoms plus six
# 30-bit range lookups).  The retired pin
# `fcdd33cbe483ea145c5f5e6aa736ab9192b98fd14b08f7db121a62b8cec53776` named the
# unsound sum-of-squares shape.
GABBAY_SHA256 = "9f5ef0608f6088f992292736d91cd9a7bec235b9868d55f3065350e3434f6dd5"
GABBAY_BYTES = 1_580

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


def range_table_bits(descriptor: dict[str, Any], table_id: int) -> int:
    """Width of a declared `range` table, fail-closed.

    A lookup bounds a column only against the table it looks INTO.  The
    deployed assembly does not read a prover-supplied table: it constructs the
    limb decomposition for the declared width.  This evaluator models that
    honest table, which is exactly the Lean-side `HonestRangeTable` premise
    (`t.tf .range = rangeRows 30`) -- see
    `Dregg2.Verify.DirectLogicAdversarialFalsifierV2` section 0.
    """
    for table in descriptor["tables"]:
        if table["id"] != table_id:
            continue
        if table["sem"] != "range" or table["arity"] != 1:
            raise AssertionError(f"lookup target table {table_id} is not a range table")
        bits = table["bits"]
        if not isinstance(bits, int) or bits <= 0:
            raise AssertionError(f"range table {table_id} has no usable width")
        return bits
    raise AssertionError(f"lookup names undeclared table {table_id}")


def accepts(descriptor: dict[str, Any], row: list[int], public: list[int]) -> bool:
    if len(row) != descriptor["trace_width"]:
        return False
    if len(public) != descriptor["public_input_count"]:
        return False
    for constraint in descriptor["constraints"]:
        tag = constraint["t"]
        if tag == "lookup":
            bits = range_table_bits(descriptor, constraint["table"])
            tuple_ = constraint["tuple"]
            if len(tuple_) != 1 or tuple_[0]["t"] != "var":
                raise AssertionError("unsupported lookup tuple shape")
            value = row[tuple_[0]["v"]]
            if not 0 <= value < (1 << bits):
                return False
        elif tag == "pi_binding":
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
    assert len(wire.encode()) == GABBAY_BYTES
    assert descriptor["name"] == "dregg-gabbay-public-three-entry-direct-v2"
    assert descriptor["ir"] == 2
    assert descriptor["trace_width"] == 6
    assert descriptor["public_input_count"] == 6
    assert descriptor["tables"] == [
        {"id": 0, "name": "main", "arity": 6, "sem": "main"},
        {"id": 2, "name": "range", "arity": 1, "sem": "range", "bits": 30},
    ]
    # The repaired shape: 6 PI bindings, 3 LINEAR acceptance atoms, 6 range
    # lookups.  The retired shape was 7 constraints whose single arithmetic
    # gate was the sum of three squared residuals.
    assert len(descriptor["constraints"]) == 15
    assert_identity_pi_layout(descriptor, 6)
    assert [c["t"] for c in descriptor["constraints"][6:9]] == ["window_gate"] * 3
    assert descriptor["constraints"][9:] == [
        {"t": "lookup", "table": 2, "tuple": [{"t": "var", "v": column}]}
        for column in range(6)
    ]
    assert descriptor["hash_sites"] == []
    # `ranges` is EMPTY by construction: the no-wrap bound is enforced by the
    # six lookups above against range table 2, not by the v1 `ranges` carrier.
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

    # Both halves of the wire-hole repair, checked independently here.  Lean
    # twins: `DirectLogicAdversarialFalsifierV2.wrapClaim_direct_trace_refused`
    # and `.borderWrap_direct_trace_refused`.
    #
    # (a) The BabyBear cancellation table the RETIRED sum-of-squares gate
    #     accepted: every cell canonical and inside the 30-bit tooth, so only
    #     the linear atoms can refuse it.
    wrap = [0, 0, 0, 2, 284_861_409, 1]
    assert sum((wrap[3 + j] - wrap[j] - 1) ** 2 for j in range(3)) % BABY_BEAR == 0
    assert all(0 <= value < (1 << 30) for value in wrap)
    assert (wrap[4] - wrap[1] - 1) % BABY_BEAR != 0
    assert not accepts(descriptor, wrap, wrap)

    # (b) The residual canonical wrap the linear atoms ACCEPT: every successor
    #     equation is a genuine field zero, so only the range lookups refuse it.
    border = [2_013_265_920, 0, 0, 0, 1, 1]
    assert all((border[3 + j] - border[j] - 1) % BABY_BEAR == 0 for j in range(3))
    assert border[3] != border[0] + 1
    assert not accepts(descriptor, border, border)
    # ...and it is the range tooth, not an atom, that does the refusing.
    without_lookups = dict(descriptor)
    without_lookups["constraints"] = [
        c for c in descriptor["constraints"] if c["t"] != "lookup"
    ]
    assert accepts(without_lookups, border, border)
    assert not accepts(without_lookups, wrap, wrap)

    for old, new in [
        ('"trace_width":6', '"trace_width":7'),
        ('"v":1', '"v":2'),
        ('"table":2', '"table":0'),
    ]:
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
