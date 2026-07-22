#!/usr/bin/env python3
"""Stage/check the unregistered exact-nullifier FNSP-v3 IR-v2 descriptor.

Lean is the only constraint author.  This tool runs the dedicated Lean emitter, validates the
runtime-consumed IR-v2 envelope and exact geometry, pins SHA-256 over the byte-exact JSON, and
writes an additive staging artifact.  It does not touch the deployed descriptor directory,
registry, fingerprint constants, provenance stamp, verifier key, or epoch selector.

Usage:
  python3 scripts/emit-exact-nullifier-aafi-rotated-state.py --inspect
  python3 scripts/emit-exact-nullifier-aafi-rotated-state.py --write
  python3 scripts/emit-exact-nullifier-aafi-rotated-state.py --check   # default
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
META = ROOT / "metatheory"
EMITTER = "EmitExactNullifierAafiRotatedState.lean"

STAGED_DIR = ROOT / "circuit" / "staged-descriptors" / "fnsp-v3"
DESCRIPTOR = STAGED_DIR / "faithful-note-spend-exact-aafi-fns3-rotated-wide-state.json"
MANIFEST = STAGED_DIR / "faithful-note-spend-exact-aafi-fns3-rotated-wide-state.manifest.json"

EXPECTED_NAME = "faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state"
EXPECTED_TRACE_WIDTH = 3760
EXPECTED_PUBLIC_INPUT_COUNT = 76
EXPECTED_TABLE_IDS = [0, 9, 1, 84, 85]

# Filled from `--inspect` after the first Lean emission, then deliberately pinned.  A descriptor
# byte change must update this reviewed constant; `--write` never silently blesses new bytes.
EXPECTED_CONSTRAINT_COUNT = 1258
EXPECTED_SHA256 = "dac87d07f12ec01cc32e34ec131db0786244b2492d5bc153f90bbf062e577b6e"


def emit_from_lean() -> bytes:
    proc = subprocess.run(
        ["lake", "env", "lean", "--run", EMITTER],
        cwd=META,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        sys.stderr.buffer.write(proc.stderr)
        raise SystemExit(
            f"exact-nullifier emitter failed with status {proc.returncode}: {EMITTER}"
        )
    if not proc.stdout or proc.stdout[-1:] != b"}":
        raise SystemExit(
            "exact-nullifier emitter did not produce one newline-free JSON object"
        )
    return proc.stdout


def inspect_wire(blob: bytes) -> tuple[dict[str, object], str]:
    try:
        descriptor = json.loads(blob)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SystemExit(f"Lean emitter output is not valid JSON: {exc}") from exc

    expected = {
        "name": EXPECTED_NAME,
        "ir": 2,
        "trace_width": EXPECTED_TRACE_WIDTH,
        "public_input_count": EXPECTED_PUBLIC_INPUT_COUNT,
    }
    for key, want in expected.items():
        got = descriptor.get(key)
        if got != want:
            raise SystemExit(f"descriptor {key} drift: got {got!r}, expected {want!r}")

    tables = descriptor.get("tables")
    if not isinstance(tables, list):
        raise SystemExit("descriptor tables is not an array")
    table_ids = [table.get("id") if isinstance(table, dict) else None for table in tables]
    if table_ids != EXPECTED_TABLE_IDS:
        raise SystemExit(
            f"descriptor table-id geometry drift: got {table_ids!r}, "
            f"expected {EXPECTED_TABLE_IDS!r}"
        )

    constraints = descriptor.get("constraints")
    if not isinstance(constraints, list) or not constraints:
        raise SystemExit("descriptor constraints is absent, non-array, or vacuous")

    for empty_carrier in ("hash_sites", "ranges"):
        if descriptor.get(empty_carrier) != []:
            raise SystemExit(f"graduated IR-v2 carrier {empty_carrier} must remain empty")

    digest = hashlib.sha256(blob).hexdigest()
    return descriptor, digest


def manifest_bytes(descriptor: dict[str, object], digest: str) -> bytes:
    tables = descriptor["tables"]
    constraints = descriptor["constraints"]
    manifest = {
        "artifact": str(DESCRIPTOR.relative_to(ROOT)),
        "constraint_count": len(constraints),
        "descriptor_sha256": digest,
        "emitter": f"metatheory/{EMITTER}",
        "ir": descriptor["ir"],
        "lean_definition": (
            "Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld."
            "exactNullifierAafiRotatedStateDescriptor"
        ),
        "name": descriptor["name"],
        "public_input_count": descriptor["public_input_count"],
        "status": "staged-unregistered-no-vk",
        "table_ids": [table["id"] for table in tables],
        "trace_width": descriptor["trace_width"],
    }
    return (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()


def require_pins(descriptor: dict[str, object], digest: str) -> None:
    constraints = descriptor["constraints"]
    if len(constraints) != EXPECTED_CONSTRAINT_COUNT:
        raise SystemExit(
            f"descriptor constraint-count drift: got {len(constraints)}, "
            f"expected {EXPECTED_CONSTRAINT_COUNT}"
        )
    if digest != EXPECTED_SHA256:
        raise SystemExit(
            f"descriptor SHA-256 drift: got {digest}, expected {EXPECTED_SHA256}"
        )


def write_if_changed(path: Path, blob: bytes) -> bool:
    if path.exists() and path.read_bytes() == blob:
        return False
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(blob)
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--inspect", action="store_true", help="print emitted pins without writing")
    mode.add_argument("--write", action="store_true", help="install pinned staged artifacts")
    mode.add_argument("--check", action="store_true", help="check staged bytes (default)")
    args = parser.parse_args()

    blob = emit_from_lean()
    descriptor, digest = inspect_wire(blob)

    if args.inspect:
        print(f"name={descriptor['name']}")
        print(f"trace_width={descriptor['trace_width']}")
        print(f"public_input_count={descriptor['public_input_count']}")
        print(f"table_ids={[table['id'] for table in descriptor['tables']]}")
        print(f"constraint_count={len(descriptor['constraints'])}")
        print(f"bytes={len(blob)}")
        print(f"sha256={digest}")
        return

    require_pins(descriptor, digest)
    manifest = manifest_bytes(descriptor, digest)

    if args.write:
        descriptor_changed = write_if_changed(DESCRIPTOR, blob)
        manifest_changed = write_if_changed(MANIFEST, manifest)
        state = "updated" if descriptor_changed or manifest_changed else "byte-identical no-op"
        print(f"exact-nullifier staged emission: {state}; sha256={digest}")
        return

    failures: list[str] = []
    for path, want in ((DESCRIPTOR, blob), (MANIFEST, manifest)):
        if not path.exists():
            failures.append(f"missing {path.relative_to(ROOT)}")
        elif path.read_bytes() != want:
            failures.append(f"drifted {path.relative_to(ROOT)}")
    if failures:
        raise SystemExit(
            "exact-nullifier staged descriptor check failed:\n  "
            + "\n  ".join(failures)
            + "\nrun with --write after reviewing the pinned Lean change"
        )
    print(f"exact-nullifier staged descriptor check: PASS; sha256={digest}")


if __name__ == "__main__":
    main()
