#!/usr/bin/env python3
"""emit_descriptors.py — regenerate every circuit descriptor JSON from the Lean
emit (the SOURCE OF TRUTH) and re-pin the sha256 fingerprints in the Rust registry.

Lean is authoritative: the `circuit/descriptors/*.json` files and the `*_FP`
fingerprint constants are MACHINE-GENERATED projections of the verified Lean
`EffectVmDescriptor` objects. This script is the ONE command that closes the
Lean->JSON->FP loop, so the checked-in artifacts can never silently drift from
the Lean emission.

Pipeline:
  1. Run each Lean emitter executable (`lake env lean --run <file>`), capturing
     its `key<TAB>name<TAB>json` (or manifest) TSV stdout.
  2. Split each emitter's stdout into `circuit/descriptors/<file>.json` via the
     per-emitter routing below. The routing is reconstructed from the Rust
     registry tables (so it stays in lockstep with how the prover consumes them).
  3. Recompute sha256 of every emitted file and rewrite the matching `*_FP`
     constant in the Rust sources.

Idempotent: on a freshly-emitted tree it writes byte-identical content and
leaves no diff. Run `scripts/check-descriptor-drift.sh` to GATE on drift.
"""
from __future__ import annotations

import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
META = ROOT / "metatheory"
DESC = ROOT / "circuit" / "descriptors"

# The Rust sources that carry `include_str!(...descriptors/<file>)` + a matching
# `*_FP` sha256 constant for it.
RUST_FP_FILES = [
    ROOT / "circuit" / "src" / "effect_vm_descriptors.rs",
    ROOT / "circuit" / "src" / "cap_delegation_nonamp_descriptor.rs",
    ROOT / "circuit" / "src" / "cap_reshape_descriptor.rs",
    ROOT / "circuit" / "src" / "bilateral_aggregation_air.rs",
    ROOT / "circuit" / "src" / "lean_descriptor_air.rs",
]

# The Lean emitter executables (run via `lake env lean --run`), in a stable order.
EMITTERS = [
    "Dregg2/Circuit/Emit/EmitAllJson.lean",  # v1: name-keyed
    "EmitAllJsonV2.lean",                    # ir2: defName-keyed (V2_DESCRIPTORS)
    "EmitRotationV3.lean",                   # rotation v3-staged artifacts + registry tsv
    "EmitBilateralLegs.lean",                # bilateral-aggregation legs
]


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, capture_output=True, text=True, **kw)


def emit(lean_file: str) -> str:
    """Run a Lean emitter, return its raw stdout."""
    r = subprocess.run(
        ["lake", "env", "lean", "--run", lean_file],
        cwd=META, capture_output=True, text=True,
    )
    if r.returncode != 0:
        sys.stderr.write(
            f"\nEMIT FAILED: lake env lean --run {lean_file}\n"
            f"--- stderr ---\n{r.stderr}\n"
        )
        sys.exit(2)
    return r.stdout


# ---- defName/const routing reconstructed from the Rust registry -------------

def const_to_file(rust_text: str) -> dict[str, str]:
    """`pub const NAME: &str = include_str!("../descriptors/FILE");` -> {NAME: FILE}."""
    out = {}
    for m in re.finditer(
        r'pub const (\w+):\s*&str\s*=\s*\n?\s*include_str!\("\.\./descriptors/([^"]+)"\)',
        rust_text,
    ):
        out[m.group(1)] = m.group(2)
    return out


def ir2_defname_to_file(rust_text: str, c2f: dict[str, str]) -> dict[str, str]:
    """V2_DESCRIPTORS: (defName, CONST_JSON, CONST_FP) -> {defName: file}."""
    out = {}
    block = re.search(r'V2_DESCRIPTORS:\s*&\[.*?\];', rust_text, re.S)
    if not block:
        sys.exit("emit_descriptors: V2_DESCRIPTORS table not found in effect_vm_descriptors.rs")
    for dn, cj, _cfp in re.findall(
        r'\(\s*"([^"]+)",\s*(\w+),\s*(\w+),?\s*\)', block.group(0)
    ):
        if cj in c2f:
            out[dn] = c2f[cj]
    return out


def write_file(name: str, content: str, written: dict[str, str]):
    """Write content to circuit/descriptors/<name>, asserting no two emitters
    disagree on a shared file (the attenuate fan-out emits the same bytes N times)."""
    if name in written and written[name] != content:
        sys.exit(f"emit_descriptors: CONFLICT — two emissions disagree on {name}")
    written[name] = content
    (DESC / name).write_text(content)


def split_v1(stdout: str, written):
    # key\tname\tjson  ->  <name>.json  (the .name IS the wire identity / filename)
    for line in stdout.splitlines():
        p = line.split("\t")
        if len(p) < 3:
            continue
        write_file(p[1] + ".json", p[2], written)


def split_ir2(stdout: str, dn2file, written):
    # key\tname\tjson  ->  file via V2_DESCRIPTORS (defName-keyed; .name collides)
    for line in stdout.splitlines():
        p = line.split("\t")
        if len(p) < 3:
            continue
        f = dn2file.get(p[0])
        if not f:
            sys.exit(f"emit_descriptors: ir2 defName {p[0]!r} has no V2_DESCRIPTORS entry")
        write_file(f, p[2], written)


# rotation routing: key -> (column index of payload, target file).
# Manifest lines are `key\tjson` (payload col 1); probe lines `key\tname\tjson` (col 2).
ROTATION_SINGLE = {
    "rotationLayoutManifest": (1, "rotation-layout-v3-staged.json"),
    "rotationCaveatLayoutManifest": (1, "rotation-caveat-layout-v3-staged.json"),
    "rotationProbeVmDescriptor2": (2, "dregg-effectvm-rotation-state-v3-staged.json"),
    "rotationProbeVmDescriptorR24": (2, "dregg-effectvm-rotation-state-v3-staged-r24.json"),
    "rotationProbeVmDescriptorR32": (2, "dregg-effectvm-rotation-state-v3-staged-r32.json"),
    "rotationCaveatProbeVmDescriptor2": (2, "dregg-effectvm-rotation-caveat-v3-staged-r24.json"),
}
ROTATION_TSV = "rotation-v3-staged-registry.tsv"


def split_rotation(stdout: str, written):
    v3rot = []
    for line in stdout.splitlines():
        p = line.split("\t")
        key = p[0]
        if key == "v3rot":
            # v3rot\tkey\tname\tjson  ->  tsv line is `key\tname\tjson`
            v3rot.append("\t".join(p[1:]))
        elif key in ROTATION_SINGLE:
            col, f = ROTATION_SINGLE[key]
            write_file(f, p[col], written)
        else:
            sys.exit(f"emit_descriptors: rotation key {key!r} has no routing")
    # the registry tsv is the v3rot cohort, one line each, trailing newline.
    write_file(ROTATION_TSV, "\n".join(v3rot) + "\n", written)


def split_bilateral(stdout: str, written):
    # key\tname\tjson  ->  <name>.json
    for line in stdout.splitlines():
        p = line.split("\t")
        if len(p) < 3:
            continue
        write_file(p[1] + ".json", p[2], written)


# ---- FP rewriting -----------------------------------------------------------

def rewrite_fps(written: dict[str, str]) -> int:
    """For every emitted descriptor file, recompute sha256 and rewrite the
    matching `*_FP` constant. Returns count of FP constants updated."""
    # file -> sha256
    file_hash = {
        f: hashlib.sha256(content.encode()).hexdigest()
        for f, content in written.items()
    }
    updated = 0
    for rust in RUST_FP_FILES:
        if not rust.exists():
            continue
        text = rust.read_text()
        c2f = const_to_file(text)
        # invert: file -> set of json-const names
        file2consts: dict[str, list[str]] = {}
        for const, f in c2f.items():
            file2consts.setdefault(f, []).append(const)
        new_text = text
        for f, consts in file2consts.items():
            if f not in file_hash:
                continue
            h = file_hash[f]
            for jsonconst in consts:
                # The FP const shares the json-const prefix: X_JSON -> X_FP, but
                # bespoke pairs (e.g. V3_STAGED_REGISTRY_TSV/_FP) need a lookup by
                # the include_str adjacency. We match the FP const whose body is a
                # sha256 and which is the textually-nearest const after this one
                # that ends in _FP. Simplest robust rule: derive candidates.
                candidates = []
                if jsonconst.endswith("_JSON"):
                    candidates.append(jsonconst[:-5] + "_FP")
                if jsonconst.endswith("_TSV"):
                    candidates.append(jsonconst[:-4] + "_FP")
                # generic: strip a known suffix token then add _FP
                for cand in candidates:
                    pat = re.compile(
                        r'(pub const ' + re.escape(cand) + r':\s*&str\s*=\s*\n?\s*")[0-9a-f]{64}(")'
                    )
                    if pat.search(new_text):
                        new_text, n = pat.subn(r'\g<1>' + h + r'\g<2>', new_text)
                        updated += n
                        break
        if new_text != text:
            rust.write_text(new_text)
    return updated


def main():
    if not (META / "lakefile.lean").exists() and not (META / "lakefile.toml").exists():
        sys.exit(f"emit_descriptors: not a lake project at {META}")
    written: dict[str, str] = {}

    rs_evd = (ROOT / "circuit" / "src" / "effect_vm_descriptors.rs").read_text()
    c2f = const_to_file(rs_evd)
    dn2file = ir2_defname_to_file(rs_evd, c2f)

    print("emit_descriptors: running Lean emitters (source of truth)...")
    for lean in EMITTERS:
        print(f"  -> {lean}")
        out = emit(lean)
        if lean.endswith("EmitAllJson.lean"):
            split_v1(out, written)
        elif lean.endswith("EmitAllJsonV2.lean"):
            split_ir2(out, dn2file, written)
        elif lean.endswith("EmitRotationV3.lean"):
            split_rotation(out, written)
        elif lean.endswith("EmitBilateralLegs.lean"):
            split_bilateral(out, written)
        else:
            sys.exit(f"emit_descriptors: no split routine for {lean}")

    # Coverage check: every checked-in descriptor file must have been (re)emitted.
    on_disk = {p.name for p in DESC.iterdir() if p.is_file()}
    missed = on_disk - set(written)
    if missed:
        sys.exit(
            "emit_descriptors: these checked-in descriptors were NOT reproduced "
            "by any emitter (routing gap):\n  " + "\n  ".join(sorted(missed))
        )

    n_fp = rewrite_fps(written)
    print(f"emit_descriptors: wrote {len(written)} descriptor files; re-pinned {n_fp} FP constants.")


if __name__ == "__main__":
    main()
