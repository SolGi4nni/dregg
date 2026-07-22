#!/usr/bin/env python3
"""Narrow wire-image check for the typed interchain predicate descriptor."""

from __future__ import annotations

import json
import pathlib
import subprocess


ROOT = pathlib.Path(__file__).resolve().parents[2]
EMITTER = ROOT / "tools" / "typed-linear-predicate-descriptor" / "Emit.lean"


def main() -> None:
    emitted = subprocess.run(
        ["lake", "env", "lean", "--run", str(EMITTER)],
        cwd=ROOT / "metatheory",
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    descriptor = json.loads(emitted)

    assert descriptor["name"] == "dregg-typed-linear-predicate-v2-p2-s0-a4"
    assert descriptor["ir"] == 2
    assert descriptor["trace_width"] == 18
    assert descriptor["public_input_count"] == 2
    assert len(descriptor["constraints"]) == 27
    assert descriptor["hash_sites"] == []
    assert descriptor["ranges"] == []

    pins = descriptor["constraints"][:2]
    assert pins == [
        {"t": "pi_binding", "row": "first", "col": 4, "pi_index": 0},
        {"t": "pi_binding", "row": "first", "col": 5, "pi_index": 1},
    ]
    # Public inputs bind raw tag/payload columns, never atom-truth columns 0..3.
    assert all(pin["col"] not in range(4) for pin in pins)
    assert all(c["t"] == "window_gate" for c in descriptor["constraints"][2:])

    print(
        "typed-linear descriptor: ok "
        f"({len(emitted)} bytes, 18 columns, 27 constraints, raw PI columns 4/5)"
    )


if __name__ == "__main__":
    main()
