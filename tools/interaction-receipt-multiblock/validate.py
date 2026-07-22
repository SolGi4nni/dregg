#!/usr/bin/env python3
"""Validate the exact emitted depth-25 multi-block interaction descriptor."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys


HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[1]
METATHEORY = REPO / "metatheory"
EMITTER = HERE / "emit.lean"


def emitted_descriptor() -> dict:
    subprocess.run(
        ["lake", "build", "Dregg2.Calculus.IntensionalCCCInteractionMultiBlockDescriptorIR2"],
        cwd=METATHEORY,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    proc = subprocess.run(
        ["lake", "env", "lean", str(EMITTER)],
        cwd=METATHEORY,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    lines = [line for line in proc.stdout.splitlines() if line.startswith("{")]
    if len(lines) != 1:
        raise AssertionError(
            f"expected one emitted JSON object, got {len(lines)}\n{proc.stdout}\n{proc.stderr}"
        )
    return json.loads(lines[0])


def col(index: int) -> dict:
    return {"t": "col", "c": index}


ZERO = {"t": "zero"}


def expected_payload(start: int) -> list[dict]:
    return [col(k) if k < 26 else ZERO for k in range(start, start + 11)]


def expected_site(digest_col: int, domain_col: int, prior_col: int | None, start: int) -> dict:
    return {
        "digest_col": digest_col,
        "arity": 15,
        "inputs": [col(domain_col), col(28), col(29), ZERO if prior_col is None else col(prior_col)]
        + expected_payload(start),
    }


def validate(doc: dict) -> None:
    assert doc["name"] == "dregg-intensional-ccc-local-receipt-v2-multiblock-depth-25"
    assert doc["ir"] == 2
    assert doc["trace_width"] == 36
    assert doc["public_input_count"] == 36
    assert doc["tables"] == [{"id": 0, "name": "main", "arity": 36, "sem": "main"}]
    assert doc["ranges"] == []

    constraints = doc["constraints"]
    assert len(constraints) == 36
    assert constraints == [
        {"t": "pi_binding", "row": "first", "col": i, "pi_index": i}
        for i in range(36)
    ]

    assert doc["hash_sites"] == [
        expected_site(30, 26, None, 0),
        expected_site(31, 26, 30, 11),
        expected_site(32, 26, 31, 22),
        expected_site(33, 27, None, 0),
        expected_site(34, 27, 33, 11),
        expected_site(35, 27, 34, 22),
    ]

    # The deep case really crosses the old one-site depth-14 boundary.
    assert 25 > 14
    assert all(len(site["inputs"]) == site["arity"] == 15 for site in doc["hash_sites"])


def main() -> int:
    validate(emitted_descriptor())
    print("interaction-receipt multiblock descriptor: 1/1 exact wire validation green")
    return 0


if __name__ == "__main__":
    sys.exit(main())
