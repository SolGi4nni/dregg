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

Idempotent: on a freshly-emitted tree it is a byte-identical NO-OP (nothing is
written). Run `scripts/check-descriptor-drift.sh` to GATE on drift.

MISUSE-RESISTANT REGEN GATE (docs/VK-REGEN-CONTROLS.md): regenerating a deployed
descriptor set RE-KEYS the federation (the AIR fingerprint feeds the recursive
VK hash — circuit-prove/src/recursive_witness_bundle.rs). A byte-CHANGING install
therefore refuses to proceed unless explicitly authorized:

  DREGG_VK_REGEN_ACK=<git rev-parse HEAD:metatheory/Dregg2>   (the exact source
      tree the operator reviewed; compute it with that command)
  DREGG_VK_REGEN_ALLOW_DIRTY=1   (additionally required when metatheory/Dregg2
      has uncommitted/untracked edits — an unreviewable source tree)

Authorized installs stamp circuit/descriptors/PROVENANCE.json (what source tree
minted these bytes, per-file sha256) and append a row to docs/VK-REGEN-LOG.md
(the audit trail). No-op runs (the common CI / drift-gate case) need no ack and
touch nothing.

Modes:
  (default)              emit from Lean, gate, install, stamp, log
  --stamp-existing       stamp PROVENANCE.json from the CURRENT on-disk bytes
                         (no Lean run; ack-gated + logged, for bootstrap/re-pin)
  --verify-provenance    recompute hashes vs the stamp; --strict additionally
                         requires a clean source (source_dirty=false) and that
                         the stamp's tree hash matches THIS checkout's
                         HEAD:metatheory/Dregg2. No Lean needed.

Exit codes: 0 = ok/no-op · 1 = routing/verify failure · 2 = emitter failed ·
3 = REGEN REFUSED (unauthorized byte-changing install; tree left untouched).
"""
from __future__ import annotations

import datetime
import getpass
import hashlib
import json
import os
import re
import socket
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
META = ROOT / "metatheory"
DESC = ROOT / "circuit" / "descriptors"

# The regen-control surface (docs/VK-REGEN-CONTROLS.md).
PROVENANCE_FILE = "PROVENANCE.json"                # lives inside circuit/descriptors/
AUDIT_LOG_REL = Path("docs") / "VK-REGEN-LOG.md"   # git-tracked append-only regen log
ACK_ENV = "DREGG_VK_REGEN_ACK"
ALLOW_DIRTY_ENV = "DREGG_VK_REGEN_ALLOW_DIRTY"
EXIT_REFUSED = 3

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
    """BUFFER content for circuit/descriptors/<name>, asserting no two emitters
    disagree on a shared file (the attenuate fan-out emits the same bytes N times).
    Nothing touches disk until the install phase — a byte-CHANGING install is
    ack-gated there (see the module docstring)."""
    if name in written and written[name] != content:
        sys.exit(f"emit_descriptors: CONFLICT — two emissions disagree on {name}")
    written[name] = content


# ---- regen gate + provenance stamp + audit trail -----------------------------
# (docs/VK-REGEN-CONTROLS.md — controls 1–3)

def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_out(*args: str) -> str:
    return run(["git", *args], cwd=ROOT).stdout.strip()


def dregg2_tree_hash() -> str:
    """The git tree hash of the committed Lean source of truth."""
    return git_out("rev-parse", "HEAD:metatheory/Dregg2")


def dregg2_source_dirty() -> bool:
    """True when metatheory/Dregg2 has uncommitted or untracked edits — i.e. the
    emitting source is NOT the reviewed committed tree the hash names."""
    return bool(git_out("status", "--porcelain", "--", "metatheory/Dregg2"))


def require_regen_ack(changed: list[str], what: str) -> dict:
    """The CONFIRMATION GATE. A byte-changing descriptor install re-keys the
    federation; require the operator to name the exact Dregg2 source tree they
    reviewed. Returns the authorization record on success; exits EXIT_REFUSED
    (tree untouched) otherwise."""
    tree = dregg2_tree_hash()
    dirty = dregg2_source_dirty()
    ack = os.environ.get(ACK_ENV, "")
    if ack != tree:
        sys.stderr.write(
            f"\nemit_descriptors: REGEN REFUSED — {what} would change "
            f"{len(changed)} artifact(s) and NO valid authorization was given.\n"
            "\n"
            "  Regenerating deployed descriptors RE-KEYS the federation: the AIR\n"
            "  fingerprint feeds the recursive VK hash (circuit-prove/src/\n"
            "  recursive_witness_bundle.rs) and every verifier pins it. This must\n"
            "  never happen as a silent side effect of a script run.\n"
            "\n"
            "  Would change:\n"
            + "".join(f"    {c}\n" for c in changed[:20])
            + (f"    … and {len(changed) - 20} more\n" if len(changed) > 20 else "")
            + "\n"
            "  To authorize (after reviewing the Lean source this mints from):\n"
            f"    {ACK_ENV}=\"$(git rev-parse HEAD:metatheory/Dregg2)\" \\\n"
            "        scripts/emit-descriptors.sh\n"
            f"  (your {ACK_ENV} was "
            + (f"set but does not match HEAD:metatheory/Dregg2 = {tree}"
               if ack else "not set")
            + ")\n"
            "\n  The tree was left UNTOUCHED. See docs/VK-REGEN-CONTROLS.md.\n"
        )
        sys.exit(EXIT_REFUSED)
    if dirty and os.environ.get(ALLOW_DIRTY_ENV) != "1":
        sys.stderr.write(
            "\nemit_descriptors: REGEN REFUSED — metatheory/Dregg2 has uncommitted\n"
            "  or untracked edits, so these artifacts would be minted from an\n"
            f"  UNREVIEWABLE source tree (the acked hash {tree} names the committed\n"
            "  tree, not what is on disk). Commit the Lean first (preferred), or\n"
            f"  set {ALLOW_DIRTY_ENV}=1 to proceed eyes-open (the provenance stamp\n"
            "  will record source_dirty=true, which --verify-provenance --strict\n"
            "  refuses).\n"
            "\n  The tree was left UNTOUCHED. See docs/VK-REGEN-CONTROLS.md.\n"
        )
        sys.exit(EXIT_REFUSED)
    return {"tree": tree, "dirty": dirty, "head": git_out("rev-parse", "HEAD")}


def collect_by_name_hashes() -> dict[str, str]:
    """The by-name goldens (circuit/descriptors/by-name/*.json) are byte-pinned
    by Lean #guards + emit-gate tests, not produced by this script; hash them
    from disk so the stamp covers the WHOLE descriptor surface."""
    by_name = DESC / "by-name"
    if not by_name.is_dir():
        return {}
    return {
        p.name: sha256_hex(p.read_bytes())
        for p in sorted(by_name.iterdir())
        if p.is_file()
    }


def build_provenance(mode: str, auth: dict,
                     desc_hashes: dict[str, str],
                     fp_hashes: dict[str, str]) -> dict:
    toolchain_file = META / "lean-toolchain"
    return {
        "version": 1,
        "mode": mode,  # "emit" (witnessed from the Lean emitters) | "stamp-existing"
        "dregg2_tree_hash": auth["tree"],
        "repo_head": auth["head"],
        "source_dirty": auth["dirty"],
        "lean_toolchain": (
            toolchain_file.read_text().strip() if toolchain_file.exists() else None
        ),
        "emitters": EMITTERS,
        "generated_utc": datetime.datetime.now(datetime.timezone.utc)
            .strftime("%Y-%m-%dT%H:%M:%SZ"),
        "operator": f"{getpass.getuser()}@{socket.gethostname()}",
        "descriptor_sha256": dict(sorted(desc_hashes.items())),
        "by_name_sha256": collect_by_name_hashes(),
        "fp_file_sha256": dict(sorted(fp_hashes.items())),
    }


def write_provenance(prov: dict) -> None:
    (DESC / PROVENANCE_FILE).write_text(json.dumps(prov, indent=2) + "\n")


def append_audit(mode: str, auth: dict, changed: list[str]) -> None:
    """The AUDIT TRAIL: one git-tracked row per applied regen/stamp."""
    log = ROOT / AUDIT_LOG_REL
    if not log.exists():
        log.parent.mkdir(parents=True, exist_ok=True)
        log.write_text(
            "# VK-REGEN LOG — append-only audit trail of descriptor regen events\n"
            "\n"
            "Every authorized descriptor install / provenance stamp appends one row\n"
            "(written by `scripts/emit_descriptors.py`; see docs/VK-REGEN-CONTROLS.md).\n"
            "Rows are never edited or removed; git history is the tamper-evidence.\n"
            "\n"
            "| when (UTC) | operator | mode | HEAD:metatheory/Dregg2 | repo HEAD | source dirty | changed |\n"
            "|---|---|---|---|---|---|---|\n"
        )
    when = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    operator = f"{getpass.getuser()}@{socket.gethostname()}"
    shown = ", ".join(changed[:6]) + (f", … +{len(changed) - 6}" if len(changed) > 6 else "")
    with log.open("a") as fh:
        fh.write(
            f"| {when} | {operator} | {mode} | {auth['tree']} | {auth['head']} "
            f"| {'YES' if auth['dirty'] else 'no'} | {shown or '(stamp only)'} |\n"
        )


def stamp_existing() -> None:
    """--stamp-existing: record provenance for the CURRENT on-disk descriptor set
    without running Lean. Bootstrap / re-pin path; ack-gated + logged so a
    re-stamp is never silent."""
    auth = require_regen_ack([f"{PROVENANCE_FILE} (stamp of the on-disk set)"],
                             "--stamp-existing")
    desc_hashes = {
        p.name: sha256_hex(p.read_bytes())
        for p in sorted(DESC.iterdir())
        if p.is_file() and p.name != PROVENANCE_FILE
    }
    fp_hashes = {
        str(p.relative_to(ROOT)): sha256_hex(p.read_bytes())
        for p in RUST_FP_FILES if p.exists()
    }
    write_provenance(build_provenance("stamp-existing", auth, desc_hashes, fp_hashes))
    append_audit("stamp-existing", auth, [])
    print(
        f"emit_descriptors: stamped {DESC / PROVENANCE_FILE} over "
        f"{len(desc_hashes)} descriptors + {len(fp_hashes)} FP files "
        f"(mode=stamp-existing, tree {auth['tree'][:12]}…, "
        f"source_dirty={'true' if auth['dirty'] else 'false'})."
    )


def verify_provenance(strict: bool) -> None:
    """--verify-provenance [--strict]: the PROVENANCE check a consumer (CI, a
    federation operator pre-epoch-flip) runs before trusting the descriptor set.
    Recomputes every hash against the stamp; --strict additionally requires the
    stamp to name a clean source tree that matches THIS checkout."""
    stamp_path = DESC / PROVENANCE_FILE
    if not stamp_path.exists():
        sys.exit(f"verify-provenance: FAIL — no {stamp_path} (unstamped descriptor set)")
    prov = json.loads(stamp_path.read_text())
    failures: list[str] = []

    def check_set(kind: str, recorded: dict[str, str],
                  on_disk: dict[str, Path]) -> None:
        for name, want in recorded.items():
            p = on_disk.get(name)
            if p is None:
                failures.append(f"{kind}: {name} recorded in the stamp but MISSING on disk")
            elif sha256_hex(p.read_bytes()) != want:
                failures.append(f"{kind}: {name} does NOT match its stamped sha256")
        for name in on_disk:
            if name not in recorded:
                failures.append(f"{kind}: {name} on disk but NOT covered by the stamp")

    check_set("descriptor", prov.get("descriptor_sha256", {}), {
        p.name: p for p in DESC.iterdir()
        if p.is_file() and p.name != PROVENANCE_FILE
    })
    by_name = DESC / "by-name"
    check_set("by-name", prov.get("by_name_sha256", {}), {
        p.name: p for p in by_name.iterdir() if p.is_file()
    } if by_name.is_dir() else {})
    check_set("fp-file", prov.get("fp_file_sha256", {}), {
        str(p.relative_to(ROOT)): p for p in RUST_FP_FILES if p.exists()
    })

    if strict:
        if prov.get("source_dirty"):
            failures.append(
                "strict: the stamp records source_dirty=true — these artifacts were "
                "minted from an unreviewable (uncommitted) Dregg2 tree"
            )
        current = dregg2_tree_hash()
        if prov.get("dregg2_tree_hash") != current:
            failures.append(
                f"strict: stamp tree {prov.get('dregg2_tree_hash')} != this checkout's "
                f"HEAD:metatheory/Dregg2 {current} (the stamp attests a DIFFERENT source)"
            )

    if failures:
        sys.stderr.write("verify-provenance: FAIL\n")
        for f in failures:
            sys.stderr.write(f"  - {f}\n")
        sys.exit(1)
    n = len(prov.get("descriptor_sha256", {})) + len(prov.get("by_name_sha256", {}))
    print(
        f"verify-provenance: PASS — {n} descriptor files + "
        f"{len(prov.get('fp_file_sha256', {}))} FP files match the stamp "
        f"(mode={prov.get('mode')}, tree {str(prov.get('dregg2_tree_hash'))[:12]}…"
        + (", strict" if strict else "") + ")."
    )


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
CROSS_CELL_CONSERVATION_FILE = "dregg-cross-cell-conservation-v2.json"


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
    if not stdout.startswith('{"name":"dregg-cross-cell-conservation-v2"'):
        sys.exit(
            f"emit_descriptors: cross-cell-conservation emitter produced unexpected output: {stdout[:80]!r}"
        )
    write_file(CROSS_CELL_CONSERVATION_FILE, stdout, written)


# ---- FP rewriting -----------------------------------------------------------

def compute_fp_rewrites(written: dict[str, str]) -> tuple[dict[Path, str], int]:
    """For every emitted descriptor file, recompute sha256 and rewrite the
    matching `*_FP` constant IN MEMORY. Returns ({rust_path: new_text} for the
    files whose text actually changes, count of FP constants matched)."""
    # file -> sha256
    file_hash = {
        f: hashlib.sha256(content.encode()).hexdigest()
        for f, content in written.items()
    }
    updated = 0
    changes: dict[Path, str] = {}
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
            changes[rust] = new_text
    return changes, updated


def install_and_stamp(written: dict[str, str]) -> None:
    """The INSTALL phase: diff the buffered emission against disk; a byte-changing
    install is ack-gated, provenance-stamped, and audit-logged. A byte-identical
    emission is a silent no-op (nothing written, no ack needed)."""
    fp_changes, n_fp = compute_fp_rewrites(written)

    changed_desc = sorted(
        name for name, content in written.items()
        if not (DESC / name).exists() or (DESC / name).read_text() != content
    )
    changed = changed_desc + sorted(str(p.relative_to(ROOT)) for p in fp_changes)

    if not changed:
        print(
            f"emit_descriptors: NO-OP — all {len(written)} descriptor files and "
            f"{n_fp} FP constants are byte-identical to the Lean emission."
        )
        return

    auth = require_regen_ack(changed, "this emission")

    for name in changed_desc:
        (DESC / name).write_text(written[name])
    for p, new_text in fp_changes.items():
        p.write_text(new_text)

    desc_hashes = {name: sha256_hex(content.encode()) for name, content in written.items()}
    fp_hashes = {
        str(p.relative_to(ROOT)): sha256_hex(p.read_bytes())
        for p in RUST_FP_FILES if p.exists()
    }
    write_provenance(build_provenance("emit", auth, desc_hashes, fp_hashes))
    append_audit("emit", auth, changed)
    print(
        f"emit_descriptors: AUTHORIZED REGEN — installed {len(changed_desc)} changed "
        f"descriptor files + {len(fp_changes)} FP-bearing Rust files "
        f"(of {len(written)} emitted / {n_fp} FP constants); provenance stamped "
        f"(tree {auth['tree'][:12]}…); audit row appended to {AUDIT_LOG_REL}."
    )


def main():
    argv = sys.argv[1:]
    if "--verify-provenance" in argv:
        verify_provenance(strict="--strict" in argv)
        return
    if "--stamp-existing" in argv:
        stamp_existing()
        return
    if argv:
        sys.exit(f"emit_descriptors: unknown arguments {argv!r} "
                 "(expected none, --stamp-existing, or --verify-provenance [--strict])")

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
    # (PROVENANCE.json is the regen-control stamp, not an emitted artifact.)
    on_disk = {p.name for p in DESC.iterdir() if p.is_file()}
    missed = on_disk - set(written) - {PROVENANCE_FILE}
    if missed:
        sys.exit(
            "emit_descriptors: these checked-in descriptors were NOT reproduced "
            "by any emitter (routing gap):\n  " + "\n  ".join(sorted(missed))
        )

    install_and_stamp(written)


if __name__ == "__main__":
    main()
