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
    "EmitWideTransferProbe.lean",            # ADDITIVE: the faithful 8-felt wide transfer descriptor
    "EmitWideRegistryProbe.lean",            # ADDITIVE: the 57-member faithful 8-felt wide registry (covers live V3)
    "EmitBilateralLegs.lean",                # bilateral-aggregation legs
    "EmitCrossCellConservation.lean",        # turn-wide cross-cell Σδ=0 conservation AIR (foolable gap #6)
    "EmitUMemCohort.lean",                   # ADDITIVE/STAGED: the umem-form per-effect cohort registry
    "EmitUMemCohortMulti.lean",              # ADDITIVE/STAGED: the MULTI-DOMAIN umem-form cohort registry
    "EmitWideUMemWeldRegistryProbe.lean",    # ADDITIVE/STAGED: the WIDE+umem welded registry (covers wide V3)
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
# ADDITIVE: the faithful 8-felt wide transfer descriptor (a single `key\tname\tjson` line,
# `EmitWideTransferProbe.lean`). Beside the live 1-felt registry — the live TSV is untouched.
WIDE_TRANSFER_TSV = "rotation-wide-transfer-staged.tsv"
# ADDITIVE: the 57-member faithful 8-felt wide registry, a member-for-member name-stable cover of the
# live V3 registry (`key\tname\tjson` per line, `EmitWideRegistryProbe.lean`, trailing newline). The
# per-family wide-roundtrip slice consumes it.
# Beside the live 1-felt registry — the live TSV / FP / VK are untouched.
WIDE_REGISTRY_TSV = "rotation-wide-registry-staged.tsv"


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


def split_wide(stdout: str, written):
    """The wide transfer emitter prints ONE `key\tname\tjson` line — the staged wide TSV verbatim
    (no trailing newline, matching the single-line checked-in artifact)."""
    line = stdout.rstrip("\n")
    if not line.startswith("transferVmDescriptor2R24Wide\t"):
        sys.exit(f"emit_descriptors: wide emitter produced unexpected line: {line[:80]!r}")
    write_file(WIDE_TRANSFER_TSV, line, written)


def split_wide_registry(stdout: str, written):
    """The wide-registry emitter prints one `key\tname\tjson` line per wide member, in the LIVE
    `rotation-v3-staged-registry.tsv` order — a member-for-member, name-stable COVER of the live V3
    registry (57 members): the 45 emit-source members (`v3RegistryCapOpenWide`) + the live-only
    `transferCapOpenTB` / `heapWrite` + the 9 WRITE-bearing cap-open tail members
    (`v3RegistryCapOpenWriteWide`, §10, MINUS `grantCapWriteCapOpen` — not a live member) + the
    live-only `supplyMint`, each made 8-felt-wide = 57 lines. The checked-in artifact is those lines
    joined with a trailing newline."""
    lines = [ln for ln in stdout.splitlines() if ln.strip()]
    if len(lines) != 57:
        sys.exit(
            f"emit_descriptors: wide registry emitter produced {len(lines)} lines (expected 57)"
        )
    for ln in lines:
        if ln.count("\t") != 2:
            sys.exit(f"emit_descriptors: wide registry line malformed: {ln[:80]!r}")
    write_file(WIDE_REGISTRY_TSV, "\n".join(lines) + "\n", written)


def split_bilateral(stdout: str, written):
    # key\tname\tjson  ->  <name>.json
    for line in stdout.splitlines():
        p = line.split("\t")
        if len(p) < 3:
            continue
        write_file(p[1] + ".json", p[2], written)


# ADDITIVE: the turn-wide cross-cell Σδ=0 conservation descriptor (foolable gap #6,
# `EmitCrossCellConservation.lean`). The emitter prints the BARE descriptor JSON (no
# `key\tname\tjson` TSV — `IO.println (emitVmJson2 crossCellConservationDescriptor)`), so the
# split routes its stdout verbatim into the single checked-in file.
CROSS_CELL_CONSERVATION_FILE = "dregg-cross-cell-conservation-v1.json"


# ADDITIVE / STAGED: the umem-form per-effect cohort registries (`EmitUMemCohort.lean` /
# `EmitUMemCohortMulti.lean`) + the WIDE+umem welded registry (`EmitWideUMemWeldRegistryProbe.lean`).
# Each emitter prints ONE `key\tname\tjson` line per registry member via `IO.println` (so its stdout
# is the lines + a trailing newline, no blank lines) — the checked-in artifact is exactly those
# bytes. These are STAGED sets beside the deployed per-map / wide registries: nothing rides the live
# wire, the deployed FP/VK are untouched. (The wide-welded TSV is FP-pinned by
# `WIDE_UMEM_WELD_REGISTRY_TSV`/`_FP`; the two cohort TSVs carry no `*_FP` constant.)
UMEM_COHORT_TSV = "umem-cohort-v1-staged-registry.tsv"
UMEM_COHORT_MULTI_TSV = "umem-cohort-multidomain-v1-staged-registry.tsv"
WIDE_UMEM_WELD_REGISTRY_TSV = "rotation-wide-umem-welded-registry-staged.tsv"


def split_member_tsv(stdout: str, written, filename: str):
    """A registry emitter that prints one `key\tname\tjson` line per member (`IO.println`,
    trailing newline). The checked-in artifact is the non-empty lines joined with a trailing
    newline; every line must carry the exact 2-tab `key\tname\tjson` shape."""
    lines = [ln for ln in stdout.splitlines() if ln.strip()]
    if not lines:
        sys.exit(f"emit_descriptors: {filename} emitter produced no lines")
    for ln in lines:
        if ln.count("\t") != 2:
            sys.exit(f"emit_descriptors: {filename} line malformed: {ln[:80]!r}")
    write_file(filename, "\n".join(lines) + "\n", written)


def split_cross_cell_conservation(stdout: str, written):
    """`EmitCrossCellConservation.lean` emits the bare descriptor JSON via `IO.println`
    (no TSV prefix), so its stdout is the descriptor JSON + one trailing newline — exactly
    the checked-in file's bytes. Route the stdout VERBATIM (the trailing `\\n` from
    `IO.println` is part of the checked-in artifact; do NOT strip it)."""
    if not stdout.startswith('{"name":"dregg-cross-cell-conservation-v1"'):
        sys.exit(
            f"emit_descriptors: cross-cell-conservation emitter produced unexpected output: {stdout[:80]!r}"
        )
    write_file(CROSS_CELL_CONSERVATION_FILE, stdout, written)


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
        elif lean.endswith("EmitWideTransferProbe.lean"):
            split_wide(out, written)
        elif lean.endswith("EmitWideRegistryProbe.lean"):
            split_wide_registry(out, written)
        elif lean.endswith("EmitBilateralLegs.lean"):
            split_bilateral(out, written)
        elif lean.endswith("EmitCrossCellConservation.lean"):
            split_cross_cell_conservation(out, written)
        elif lean.endswith("EmitUMemCohortMulti.lean"):
            split_member_tsv(out, written, UMEM_COHORT_MULTI_TSV)
        elif lean.endswith("EmitUMemCohort.lean"):
            split_member_tsv(out, written, UMEM_COHORT_TSV)
        elif lean.endswith("EmitWideUMemWeldRegistryProbe.lean"):
            split_member_tsv(out, written, WIDE_UMEM_WELD_REGISTRY_TSV)
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
