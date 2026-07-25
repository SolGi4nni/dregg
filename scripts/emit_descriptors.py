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
  4. Normalize the WHOLE Lean-authored Rust modules (`circuit/src/effect_vm/
     *_generated.rs`) through the pinned rustfmt, so the generator's bytes equal
     the bytes `scripts/git-hooks/pre-commit` and `cargo fmt --all -- --check`
     produce — the two producers cannot disagree (see normalize_generated_rust).

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
  --verify-by-name-routing
                         reconcile `EmitByName.lean`'s routing table against the
                         checked-in by-name/ set and the stamp, BOTH directions.
                         Static parse of the .lean — no Lean run, no cargo, seconds
                         — so it still works while the emit is blocked (which is
                         exactly when a routing gap can sit unnoticed). ALSO runs
                         the second door: every literal `include_str!`/
                         `include_bytes!` target in tracked Rust must EXIST and be
                         TRACKED (an untracked one compiles only for the lane that
                         emitted it — see verify_include_targets).
  --list-emitter-modules print the Lean modules the emitters import (one per line)
                         — the set that must be `lake build`-ed for the emit to run
                         on a cold checkout. Derived from the emitters' own imports;
                         no Lean run. `check-descriptor-drift.sh` builds this.
  --list-guarded-paths   print the repo-relative paths this driver can REWRITE (one
                         per line) — `install_and_stamp`'s whole change-set: the
                         descriptor dir, the `*_FP`-bearing Rust sources, and the
                         Lean-authored `*_generated.rs` modules. No Lean run.
                         `check-descriptor-drift.sh` snapshots exactly this instead
                         of transcribing it.

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

# Artifacts under circuit/descriptors/ that this driver does NOT own — each is regenerated AND
# drift-checked by its OWN pipeline, so requiring an emitter here would be a false routing gap.
# Every entry MUST have a co-located regen/check that keeps it fresh (never a silent exemption):
#   * dregg-cert-qp-portfolio6-s3-ir2.json — regenerated + `--check`ed by regen-cert-qp.sh
#     (`lake env lean --run EmitCertQpDescriptor.lean`, deliberately outside this driver's EMITTERS).
#   * regen-cert-qp.sh — the regen SCRIPT itself (not a descriptor; it has no emitter by construction).
COVERAGE_EXEMPT = frozenset({
    "dregg-cert-qp-portfolio6-s3-ir2.json",
    "regen-cert-qp.sh",
})
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
    "EmitRotationV3SetFieldValue8.lean",     # ADDITIVE/STAGED: the setField VALUE8 epoch (8 written-slot members)
    "EmitLayoutManifest.lean",               # the rotated COLUMN LAYOUT, exported from Lean AS RUST
    "EmitByName.lean",                       # the by-name/ dispatch surface descriptor_by_name() serves
    "EmitCertF.lean",                        # the ring-3 Cert-F IR2 descriptor (cert_f_air.rs include_str!s it)
    "EmitCertFMarket4.lean",                 # the market4 (3-asset/4-order, ε>0) Cert-F IR2 descriptor
]

# The checked-in artifact `circuit-prove/src/cert_f_air.rs:297` include_str!s. It was the ONLY flat
# descriptor no emitter reproduced (tracked in GOAL-STARK-KILL.md) — include_str!'d into a live AIR
# yet outside the re-derivation, so the drift gate could not see it move.
CERT_F_FILE = "dregg-cert-f-ir2.json"

# The market4 registered Cert-F program (the first REAL market shape past the ring-3 toy;
# authored as `certFDescriptorOf market4Prog` in Market/CertFDescriptor.lean §4b).
CERT_F_MARKET4_FILE = "dregg-cert-f-market4-ir2.json"

# The by-name descriptors that are checked in WITH a trailing newline. The directory's convention is
# mixed (21 bare, 5 newline-terminated) and it is purely cosmetic — JSON does not care — but the
# bytes are FP/VK-pinned, so NORMALIZING the convention would re-key those 5 descriptors for a
# whitespace change. We reproduce each file's existing convention exactly instead, which keeps the
# emit a true no-op on a clean tree. Retire this set only as part of a deliberate regen.
BY_NAME_NEWLINE_TERMINATED = frozenset({
    "dark-bazaar-private-n4k4.json",
    "faithful-note-spend-v2.json",
    "field-delta-result-range.json",
    "merkle-membership-4ary-general.json",
    "poseidon2-hash-arity2.json",
    "private-preference-n4k4.json",
    "private-preference-cell-n4k4.json",
    "private-graph-rewrite-4x2.json",
    "private-graph-rewrite-cell-4x2.json",
    "private-quest-graph-4x2.json",
    "private-raid-assignment-n4.json",
    "private-shuffle-n8.json",
    "private-shuffle-fair-n8.json",
    "private-book-bfv-odd-ntt-butterfly-q0-n8.json",
    "private-book-bfv-odd-ntt-butterfly-q0-n4096.json",
    "private-book-bfv-odd-intt-butterfly-q0-n4096.json",
    "private-book-bfv-odd-ntt-butterfly-q0-n8-stage0-exact-public.json",
    "private-book-bfv-odd-ntt-butterfly-q0-n8-stage1-exact-public.json",
    "private-book-bfv-odd-ntt-butterfly-q0-n8-stage2-exact-public.json",
    "turn-chain-binding.json",
    "descent-custody-census-fixed8-v1.json",
    "shielded-whole-note-swap-substrate-v1.json",
})


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, capture_output=True, text=True, **kw)


def emitter_modules() -> list[str]:
    """The Lean library modules that must be BUILT for `emit()` to run at all.

    `lake env lean --run <emitter>` loads its imports from COMPILED oleans; it does not
    build them. So the emit only works where something already warmed those oleans —
    and `lake build` (default targets: Dregg2/Metatheory/Polis/Market) does NOT warm all
    of them. Measured at the time of writing: 17 of `EmitByName.lean`'s 26 imports are
    reachable from NO default target (the `Dregg2.Circuit.Emit.*Emit` authors under
    DfaRouting/Predicates/Presentation/… — nothing in the `Dregg2` root import closure
    pulls them in). On a cold checkout the by-name emit therefore died with 'object file
    does not exist' and `emit_descriptors.py` exited 2 — i.e. the drift gate was green
    only where an EARLIER build step, outside the gate, happened to warm the cache. The
    emitters the gate RAN were not the emitters the gate BUILT.

    This DERIVES the build set from the emitters' own `import` lines rather than pinning
    a hand-written list, so adding an emitter (or an import to one) cannot silently
    reintroduce the hole. Direct imports suffice: `lake build M` builds M's deps too.
    Imports with no in-tree source file are dependencies of the toolchain/mathlib and are
    dropped — `lake build` cannot take them as targets.
    """
    mods: list[str] = []
    dropped: list[str] = []
    for lean_file in EMITTERS:
        path = META / lean_file
        if not path.exists():
            sys.exit(f"emit_descriptors: emitter source missing: {path}")
        for line in path.read_text().splitlines():
            m = re.match(r"^import\s+([A-Za-z0-9_.]+)", line)
            if not m:
                continue
            mod = m.group(1)
            if (META / (mod.replace(".", "/") + ".lean")).exists():
                if mod not in mods:
                    mods.append(mod)
            elif mod not in dropped:
                dropped.append(mod)
    # A dropped import is normally a mathlib/toolchain dep (`lake build` cannot take
    # it as a target, and it is built transitively via the in-tree modules that use
    # it). But dropping is the same "built set != run set" shape the derived list
    # exists to prevent, so REPORT the drops rather than swallowing them silently: a
    # future emitter whose only imports are out-of-tree would otherwise contribute
    # nothing to the build set with no word said. Visible + auditable, behaviour
    # unchanged.
    if dropped:
        print(
            "emit_descriptors: derived build set drops "
            f"{len(dropped)} out-of-tree import(s) (toolchain/mathlib deps, built "
            f"transitively): {', '.join(sorted(dropped))}",
            file=sys.stderr,
        )
    if not mods:
        sys.exit(
            "emit_descriptors: derived build set is EMPTY — every emitter import was "
            "dropped as out-of-tree. Refusing to build nothing and re-depend on a warm "
            "cache (the exact hole this derivation closes)."
        )
    return mods


def emit(lean_file: str) -> str:
    """Run a Lean emitter, return its raw stdout.

    Retries on TRANSIENT failures. On a co-tenant build box (multiple agents running `lake`
    concurrently) a `lake env lean --run` can fail through no fault of the emitter: a concurrent
    `lake` reconfigure holds the exclusive configuration lock ("could not acquire an exclusive
    configuration lock"), or a background rebuild clobbers an olean mid-read (a bare non-zero exit
    with empty stderr). The emitters are deterministic, so a REAL error fails every attempt and still
    exits 2; a transient one clears on retry. Without this, a single unlucky moment aborts the whole
    (~10 min) regen."""
    import time
    attempts = 4
    for i in range(attempts):
        r = subprocess.run(
            ["lake", "env", "lean", "--run", lean_file],
            cwd=META, capture_output=True, text=True,
        )
        if r.returncode == 0:
            return r.stdout
        transient = (
            "configuration lock" in r.stderr
            or "reconfiguring the package" in r.stderr
            or r.stderr.strip() == ""  # a bare kill (concurrent olean clobber / OOM signal)
        )
        if transient and i < attempts - 1:
            sys.stderr.write(
                f"emit_descriptors: transient failure on {lean_file} "
                f"(attempt {i + 1}/{attempts}, rc={r.returncode}); retrying after backoff...\n"
            )
            time.sleep(5 * (i + 1))
            continue
        sys.stderr.write(
            f"\nEMIT FAILED: lake env lean --run {lean_file}\n"
            f"--- stderr ---\n{r.stderr}\n"
        )
        sys.exit(2)
    # unreachable (loop either returns or exits)
    sys.exit(2)


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


# ---- Lean-authored Rust modules ---------------------------------------------
# Unlike the FP constants (which are REWRITTEN in place inside hand-written .rs files), these are
# WHOLE modules whose every byte comes from Lean. The layout module is the single source for the
# rotated column geometry that the producer writes, the descriptors read, and the gates audit.

LAYOUT_RS = ROOT / "circuit" / "src" / "effect_vm" / "layout_generated.rs"
S2_COMPACT_RS = ROOT / "circuit" / "src" / "effect_vm" / "s2_compact_generated.rs"
E1_COMPACT_RS = ROOT / "circuit" / "src" / "effect_vm" / "e1_compact_generated.rs"

# THE DECLARED generated-module set. `GENERATED_RS` below is filled at EMIT time, so nothing
# static can read it — and `scripts/check-descriptor-drift.sh` has to know this driver's whole
# change-set BEFORE the emit, to snapshot it. That set used to be transcribed into the shell as
# a `GUARDED=(…)` array; the header of that script records what a transcription costs here (the
# `*_generated.rs` modules were missing from it, so a generated-Rust-only change took the
# non-ack install path, the gate diffed nothing, and it reported PASS while the tree had just
# been rewritten underneath it). The shell now DERIVES its guarded set from
# `--list-guarded-paths`, which reads this tuple, so there is exactly ONE authority.
#
# `assert_generated_declared()` is the tooth that keeps this tuple honest: a future emitter that
# buffers a FOURTH module into `GENERATED_RS` without listing it here FAILS the emit, instead of
# silently reopening the same hole one module wider.
GENERATED_RS_PATHS: tuple[Path, ...] = (LAYOUT_RS, S2_COMPACT_RS, E1_COMPACT_RS)

GENERATED_RS: dict[Path, str] = {}


def assert_generated_declared() -> None:
    """Every buffered generated module must be DECLARED in `GENERATED_RS_PATHS`.

    Undeclared means `check-descriptor-drift.sh` never snapshots it, so a re-emit that rewrites
    it is invisible to the drift gate — the exact hole that script's header records."""
    undeclared = sorted(str(p) for p in GENERATED_RS if p not in GENERATED_RS_PATHS)
    if undeclared:
        sys.exit(
            "emit_descriptors: these generated modules are buffered for install but NOT "
            "declared in GENERATED_RS_PATHS:\n  " + "\n  ".join(undeclared)
            + "\n  Add them there. Until you do, scripts/check-descriptor-drift.sh does not "
              "snapshot them and cannot see a re-emit rewrite them."
        )


# Directories a source scan must not walk: build output, vendored trees, and the mirror-gate
# canary, which holds DELIBERATE copies of descriptor-bearing sources (a scan that took those for
# real consumers would red on the fixtures whose whole job is to look real).
_SCAN_SKIP_DIRS = frozenset({
    ".git", ".lake", "target", "vendor", "node_modules", "tmp", "old-docs",
    "ts-sdk.archived", "mirror-gates",
})


def fp_bearing_sources() -> list[Path]:
    """Every Rust source that carries the FP CONVENTION: a `pub const X_{JSON,TSV}: &str =
    include_str!("../descriptors/…")` together with the paired `pub const X_FP: &str =
    "<sha256>"` that `compute_fp_rewrites` rewrites.

    A file with that convention and NO row in `RUST_FP_FILES` gets its FP constant left stale by
    the emit, is absent from the stamp's `fp_file_sha256`, and is not snapshotted by
    `check-descriptor-drift.sh` — three gates blind at once, silently."""
    fp_const = re.compile(r'pub const (\w+)_FP:\s*&str\s*=\s*"[0-9a-f]{64}"')
    found: list[Path] = []
    # `os.walk` with in-place pruning, NOT `rglob` — rglob enumerates every skipped tree before
    # the filter sees it, and `target/` alone makes that a minutes-long walk.
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [d for d in dirnames if d not in _SCAN_SKIP_DIRS and not d.startswith(".")]
        for fn in filenames:
            if not fn.endswith(".rs"):
                continue
            path = Path(dirpath) / fn
            try:
                text = path.read_text()
            except (OSError, UnicodeDecodeError):
                continue
            if "descriptors/" not in text:
                continue
            bases = {
                c[:-5] if c.endswith("_JSON") else c[:-4]
                for c in const_to_file(text) if c.endswith(("_JSON", "_TSV"))
            }
            if bases & set(fp_const.findall(text)):
                found.append(path)
    return found


def assert_fp_files_declared() -> None:
    """Every FP-bearing Rust source must be DECLARED in `RUST_FP_FILES`.

    The twin of `assert_generated_declared`, on the other half of the change-set. `RUST_FP_FILES`
    is a hand list over a set that GROWS every time a descriptor gets a new Rust consumer, and a
    hand list over a growing set cannot go red — it just quietly covers less."""
    undeclared = sorted(
        str(p.relative_to(ROOT)) for p in fp_bearing_sources() if p not in RUST_FP_FILES
    )
    if undeclared:
        sys.exit(
            "emit_descriptors: these Rust sources carry the `*_FP` sha256 convention but are NOT "
            "declared in RUST_FP_FILES:\n  " + "\n  ".join(undeclared)
            + "\n  Add them there. Until you do, the emit never rewrites their FP constants, the "
              "PROVENANCE stamp does not cover them, and scripts/check-descriptor-drift.sh does "
              "not snapshot them — their pins can go stale with nothing red."
        )


def guarded_paths() -> list[str]:
    """The repo-relative paths this driver can REWRITE — `install_and_stamp`'s whole change-set:
    the descriptor directory, the Rust sources carrying generated `*_FP` constants, and the
    Lean-authored `*_generated.rs` modules. `check-descriptor-drift.sh` snapshots exactly this."""
    return [str(DESC.relative_to(ROOT))] + [
        str(p.relative_to(ROOT)) for p in (*RUST_FP_FILES, *GENERATED_RS_PATHS)
    ]


# ---- rustfmt normalization of the generated modules --------------------------
# The generated `.rs` files have TWO producers: this script (which writes them) and
# `scripts/git-hooks/pre-commit` (which rustfmt's every STAGED `.rs` on its way into a commit,
# `@generated` header or not — and CI's `cargo fmt --all -- --check` demands the same shape).
# While the two disagreed, the committed bytes were rustfmt's and the emitted bytes were ours,
# so `scripts/check-descriptor-drift.sh` could NEVER go green for such a file — a gate stuck red
# cannot catch the next real break. We converge here, at the generator: every generated module is
# emitted through rustfmt, so generator output == post-hook bytes == what `cargo fmt --check`
# accepts, BY CONSTRUCTION rather than by line-length luck.
#
# rustfmt is version-PINNED repo-wide (`rust-toolchain.toml`, `channel = nightly-2026-06-21`,
# `components = [… "rustfmt"]`), so this is as reproducible across machines as the `cargo fmt
# --check` gate already is. Missing rustfmt is a HARD FAILURE, never a silent skip: emitting
# unformatted bytes would make the drift gate report a fake drift.

def _rust_edition_for(path: Path) -> str:
    """The rustfmt edition for `path` — resolved EXACTLY as `scripts/git-hooks/pre-commit` and
    `cargo fmt` resolve it: nearest ancestor `Cargo.toml` with a `[package]` table, honouring
    `edition.workspace = true` against the root `[workspace.package]`. Hardcoding one edition
    would silently mis-format a module emitted into an edition-2021 crate (rustfmt's macro and
    `use` layout differ per edition), reopening the same two-producers disagreement."""
    import tomllib  # local: keeps --verify-provenance / --list-emitter-modules usable pre-3.11

    ws_edition = "2024"
    try:
        ws = tomllib.loads((ROOT / "Cargo.toml").read_text())
        ws_edition = str(ws.get("workspace", {}).get("package", {}).get("edition", ws_edition))
    except (OSError, tomllib.TOMLDecodeError):
        pass

    for d in path.resolve().parents:
        toml = d / "Cargo.toml"
        if not toml.is_file():
            continue
        try:
            pkg = tomllib.loads(toml.read_text()).get("package")
        except (OSError, tomllib.TOMLDecodeError):
            continue
        if pkg is None:
            continue
        ed = pkg.get("edition")
        if isinstance(ed, str):
            return ed
        if isinstance(ed, dict) and ed.get("workspace") is True:
            return ws_edition
        return "2015"  # a [package] with no edition — cargo's default
    return ws_edition


def normalize_generated_rust() -> None:
    """Run every buffered generated module through the pinned rustfmt, IN PLACE in GENERATED_RS.

    Single choke point on purpose: a future emitter that adds a module to `GENERATED_RS` cannot
    forget to format it. Runs before the install/no-op comparison so the bytes we diff against
    disk are the bytes we would write."""
    if not GENERATED_RS:
        return
    for path in list(GENERATED_RS):
        edition = _rust_edition_for(path)
        try:
            proc = subprocess.run(
                ["rustfmt", "--edition", edition, "--emit", "stdout"],
                input=GENERATED_RS[path],
                capture_output=True,
                text=True,
                cwd=str(path.parent if path.parent.is_dir() else ROOT),
            )
        except FileNotFoundError:
            sys.exit(
                "emit_descriptors: rustfmt NOT FOUND, but the generated Rust modules must be "
                "rustfmt-normalized to match the bytes the pre-commit hook and `cargo fmt --all "
                "-- --check` produce. Emitting unformatted bytes here would make the descriptor "
                "drift gate report a FAKE drift. Install the pinned toolchain "
                "(`rustup toolchain install \"$(grep -m1 '^channel' rust-toolchain.toml | "
                "cut -d'\"' -f2)\" --component rustfmt`) and re-run."
            )
        if proc.returncode != 0:
            sys.exit(
                f"emit_descriptors: rustfmt failed on the generated module "
                f"{path.relative_to(ROOT)} (edition {edition}) — the emitted Rust does not parse, "
                f"so it must not be installed.\n{proc.stderr.strip()}"
            )
        out = proc.stdout
        GENERATED_RS[path] = out if out.endswith("\n") else out + "\n"


def split_layout(stdout: str, _written):
    """The layout emitter prints a COMPLETE Rust module on stdout. Route it verbatim (it is the
    file's exact bytes). Sanity-gate the shape so a broken emit cannot silently install an empty
    or non-Rust layout module — this file is load-bearing for soundness, not decoration."""
    if (
        "@generated" not in stdout
        or "pub const EFFECT_VM_WIDTH" not in stdout
        or "pub const NUM_PRE_LIMBS" not in stdout
        or "pub const ROTATED_GROUP_TABLE" not in stdout
    ):
        sys.exit(
            "emit_descriptors: layout emitter output does not look like the generated Rust layout "
            "module (missing header, scalar spine, or verified group table)"
        )
    GENERATED_RS[LAYOUT_RS] = stdout if stdout.endswith("\n") else stdout + "\n"


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


def by_name_hashes_of(desc_hashes: dict[str, str]) -> dict[str, str]:
    """The by-name leg of the provenance stamp, sourced from the EMITTED content (via
    `desc_hashes`, which `install_and_stamp` computes over `written`) — NOT from disk.

    This used to be `collect_by_name_hashes()`, which read the bytes FROM DISK and stored them as
    `by_name_sha256`; `verify_provenance` then compared disk against a stamp computed from that same
    disk. Pure self-consistency, sold under a PASS that claimed Lean agreement — the exact fallacy
    `check-descriptor-drift.sh`'s own header disowns ("a `sha256(bytes) == committed-FP` rehash
    proves only that a file matches the hash committed beside it ... Re-deriving from Lean is the
    whole point"). Now that `EmitByName.lean` genuinely re-derives the by-name surface, the stamp is
    minted from Lean bytes and the verify leg stops being self-referential."""
    return {
        name.split("/", 1)[1]: h
        for name, h in sorted(desc_hashes.items())
        if name.startswith("by-name/")
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
        # The stamp keeps the two legs separate (flat basenames each), as it always has; the
        # SOURCE of the by-name leg is what changed — emitted Lean bytes, not a disk re-hash.
        "descriptor_sha256": {
            name: h for name, h in sorted(desc_hashes.items())
            if not name.startswith("by-name/")
        },
        "by_name_sha256": by_name_hashes_of(desc_hashes),
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
    # RECURSES (relative-keyed) so the by-name/ subtree is stamped like everything else;
    # `build_provenance` splits the `by-name/` keys back out into the `by_name_sha256` leg.
    # (`stamp-existing` is explicitly a stamp of the ON-DISK set — unlike the emit path it makes
    # no Lean claim, and `--verify-provenance --strict` is what refuses a stamp minted this way
    # from an unreviewable tree.)
    desc_hashes = {
        str(p.relative_to(DESC)): sha256_hex(p.read_bytes())
        for p in sorted(DESC.rglob("*"))
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
        if p.is_file() and p.name != PROVENANCE_FILE and p.name not in COVERAGE_EXEMPT
    })
    by_name = DESC / "by-name"
    check_set("by-name", prov.get("by_name_sha256", {}), {
        p.name: p for p in by_name.iterdir() if p.is_file()
    } if by_name.is_dir() else {})
    check_set("fp-file", prov.get("fp_file_sha256", {}), {
        str(p.relative_to(ROOT)): p for p in RUST_FP_FILES if p.exists()
    })

    # The ROUTING leg (static; no Lean run). The three checks above all start from a file
    # that EXISTS and ask whether the stamp covers it — so a name the Lean routing table
    # authors with no artifact behind it is invisible to every one of them.
    failures.extend(verify_by_name_routing())

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


# ---- the by-name ROUTING round-trip (STATIC — no Lean run) -------------------
#
# `EmitByName.lean`'s `byNameDescriptors` is the routing table for the whole
# `circuit/descriptors/by-name/` surface. Until this check, only ONE of its two
# directions was gated, and only by machinery that needs a full Lean emit:
#
#   * file-on-disk -> table: the coverage check in `main()` fails on a by-name file no
#     emitter reproduces. Needs the emit (hours of `lake build`) to say anything.
#   * table -> file-on-disk: NOTHING. A name added to the table whose artifact was never
#     committed is a GHOST — the emit would mint it, but until the emit runs the routing
#     table advertises a descriptor that does not exist, `descriptor_by_name.rs` cannot
#     serve it, and no byte-pin covers it. The `#guard byNameDescriptors.length == N` in
#     the Lean file counts the ghost as a member, so it passes. `--verify-provenance` and
#     the derived-coverage test in `circuit/src/effect_vm_descriptors.rs` both start from
#     files that EXIST, so a ghost gives them nothing to notice.
#
# This closes it from the OTHER end: parse the table's name literals out of the .lean
# source (they are string literals — no Lean toolchain needed) and reconcile them against
# the tracked/on-disk directory and the PROVENANCE stamp. It therefore keeps working while
# the emit is blocked, which is exactly when a routing gap can sit unnoticed.
#
# The parse is STRUCTURE-CHECKED, never best-effort: it must find the decl, must find the
# terminator, must produce one name per list opener, and must agree with the Lean file's
# own machine-checked `#guard byNameDescriptors.length == N`. Any of those failing is a
# loud FATAL ("the table's shape moved; re-point this parser"), never a quiet pass — same
# rule the COVERAGE_EXEMPT mirror in `circuit/src/effect_vm_descriptors.rs` follows.
BY_NAME_ROUTER = "EmitByName.lean"                     # relative to META
BY_NAME_TABLE_DECL = "def byNameDescriptors : List (String × EffectVmDescriptor2) :="
_BY_NAME_TERM = re.compile(r"^[ \t]*\][ \t]*$", re.M)
_BY_NAME_OPENER = re.compile(r"^[ \t]*[\[,][ \t]*\(", re.M)
_BY_NAME_NAMED = re.compile(r"^[ \t]*[\[,][ \t]*\(\s*\"([^\"\n]*)\"\s*,", re.M)
_BY_NAME_GUARD = re.compile(r"#guard\s+byNameDescriptors\.length\s*==\s*(\d+)")


def parse_by_name_routing() -> list[str]:
    """The filenames `EmitByName.lean`'s routing table claims to author, in table order.

    A STATIC parse of the .lean source. Fails loudly (never silently returns a short or
    empty list) if the table's shape has moved past what this parser understands."""
    path = META / BY_NAME_ROUTER
    fatal = (
        f"emit_descriptors: {path} — the by-name routing table's shape moved past this "
        "parser. Re-point it (do NOT hand-copy the filename list); a routing check that "
        "cannot read the table must not report a pass."
    )
    if not path.exists():
        sys.exit(f"emit_descriptors: by-name router missing: {path}")
    src = path.read_text()
    start = src.find(BY_NAME_TABLE_DECL)
    if start < 0:
        sys.exit(f"{fatal}\n  (declaration `{BY_NAME_TABLE_DECL}` not found)")
    rest = src[start + len(BY_NAME_TABLE_DECL):]
    term = _BY_NAME_TERM.search(rest)
    if not term:
        sys.exit(f"{fatal}\n  (the table literal is unterminated — no closing `]` line)")
    body = rest[: term.start()]

    names = _BY_NAME_NAMED.findall(body)
    openers = len(_BY_NAME_OPENER.findall(body))
    if openers != len(names):
        sys.exit(
            f"{fatal}\n  ({openers} list entries but {len(names)} parsed filename "
            "literals — an entry's first component is not a plain string literal)"
        )
    if not names:
        sys.exit(f"{fatal}\n  (parsed ZERO entries — this check would be vacuous)")

    dupes = sorted({n for n in names if names.count(n) > 1})
    if dupes:
        sys.exit(
            f"emit_descriptors: {path} routes duplicate filename(s) {dupes} — two table "
            "entries claim sole authorship of the same artifact"
        )
    bad = sorted(n for n in names if not n.endswith(".json"))
    if bad:
        sys.exit(f"emit_descriptors: {path} routes non-.json key(s) {bad}")

    # Cross-check against the table's OWN machine-checked length guard. Lean verifies that
    # literal at build time, so it is independent ground truth for "how many entries are
    # there" — agreeing with it is what proves this parse saw all of them and no more.
    guard = _BY_NAME_GUARD.search(src)
    if not guard:
        sys.exit(
            f"{fatal}\n  (no `#guard byNameDescriptors.length == N` — the parse has "
            "nothing independent to check itself against)"
        )
    if int(guard.group(1)) != len(names):
        sys.exit(
            f"emit_descriptors: {path} — parsed {len(names)} routing entries but the "
            f"file's own `#guard byNameDescriptors.length == {guard.group(1)}` says "
            f"{guard.group(1)}. Either the guard is stale (Lean would catch that at build "
            "time) or this parser is missing entries. Refusing to report on a table it "
            "may be reading wrong."
        )
    return names


def by_name_present() -> tuple[set[str], str]:
    """The by-name artifacts that count as CHECKED IN, plus a label for which set it is.

    TRACKED (`git ls-files`) by preference, matching the choice made in
    `circuit/src/effect_vm_descriptors.rs`: ~10 lanes share this tree, so `by-name/`
    routinely holds another lane's untracked scratch emission, and an untracked file is not
    yet a claim about what ships. Falls back to the on-disk listing where there is no git
    index (a vendored export, or the rsync'd remote build lane `scripts/pbuild`, which
    excludes `.git/`) — STRICTER, never weaker — and the label says which, so a red in a
    `.git`-less tree is never mistaken for a red in the repo."""
    try:
        out = subprocess.run(
            ["git", "-C", str(ROOT), "ls-files", "-z", "--", "circuit/descriptors/by-name"],
            capture_output=True, text=True,
        )
        if out.returncode == 0:
            tracked = {p.rsplit("/", 1)[-1] for p in out.stdout.split("\0") if p}
            if tracked:
                return tracked, "tracked by git"
    except OSError:
        pass
    return by_name_on_disk(), "present on disk (NO git index here — untracked files count too)"


def by_name_on_disk() -> set[str]:
    d = DESC / "by-name"
    return {p.name for p in d.iterdir() if p.is_file()} if d.is_dir() else set()


def verify_by_name_routing() -> list[str]:
    """The ROUND TRIP, both directions: every name the Lean routing table authors lands as
    a checked-in file carrying a provenance row, and every checked-in by-name file is
    routed. Returns the finding lines (empty == clean); prints a one-line summary."""
    routed = parse_by_name_routing()
    routed_set = set(routed)
    present, source = by_name_present()
    on_disk = by_name_on_disk()
    stamp_path = DESC / PROVENANCE_FILE
    pinned: set[str] | None = None
    if stamp_path.exists():
        pinned = set(json.loads(stamp_path.read_text()).get("by_name_sha256", {}))

    findings: list[str] = []

    # (1) THE GHOST: routed, but no such file exists anywhere. The class nothing else can
    # see — every other gate starts from a file and asks whether it is covered.
    for n in sorted(routed_set - on_disk):
        findings.append(
            f"GHOST: {BY_NAME_ROUTER} routes `{n}`, which exists NOWHERE under "
            f"circuit/descriptors/by-name/ — the table advertises a descriptor nobody "
            f"committed. Either commit the artifact (re-run the emit ceremony) or drop "
            f"the routing entry; this is the routing entry's AUTHOR's call."
        )

    # (2) routed + on disk + not tracked: a lane mid-flight. Reported, not failed — the
    # file is not yet a claim (same reasoning as by_name_present). Silence here is how a
    # scratch emission graduates to HEAD via a co-tenant `commit -a` with nobody looking.
    inflight = sorted((routed_set & on_disk) - present)

    # (3) the other direction: a checked-in by-name file the table does not author. The
    # emit's coverage check catches this too — but only by RUNNING the emit.
    for n in sorted(present - routed_set):
        findings.append(
            f"UNROUTED: circuit/descriptors/by-name/{n} is checked in ({source}) but no "
            f"{BY_NAME_ROUTER} entry authors it — its bytes are not re-derivable from Lean "
            f"(the ungated hand-transcription hop `predicate-arith.json` drifted through)."
        )

    # (4) the third leg: routed AND checked in, but no provenance row — nothing
    # operator-facing attests those bytes.
    if pinned is not None:
        for n in sorted((routed_set & present) - pinned):
            findings.append(
                f"UNSTAMPED: circuit/descriptors/by-name/{n} is routed and checked in "
                f"({source}) but has no PROVENANCE.json `by_name_sha256` row — it landed "
                f"without re-stamping. Fix at the SOURCE (the emit/stamp ceremony, see "
                f"docs/VK-REGEN-CONTROLS.md); do NOT hand-add rows."
            )

    print(
        f"verify-by-name-routing: {len(routed)} routed / {len(present)} checked in "
        f"({source}) / {len(pinned) if pinned is not None else 0} stamped"
        + (f" · {len(inflight)} routed-but-untracked (in flight): {', '.join(inflight)}"
           if inflight else "")
    )

    # THE SECOND DOOR — see verify_include_targets. The Lean table is one way an artifact gets
    # claimed; a Rust `include_str!` is the other, and the four legs above cannot see it.
    findings.extend(verify_include_targets())
    # ...and the same door one language over: a committed `import` of an uncommitted module.
    findings.extend(verify_lean_imports())

    sys.stdout.flush()  # so the summary precedes the findings this returns (stderr)
    return findings


# ---- THE SECOND DOOR: `include_str!` / `include_bytes!` of an artifact -------------------
#
# `verify_by_name_routing` above reconciles the LEAN routing table against the checked-in
# by-name set. It cannot see the other way an artifact gets claimed: a Rust
# `include_str!("../descriptors/by-name/X.json")`. That macro is resolved by rustc at COMPILE
# time, so an absent or untracked target is not a soft drift — the crate does not build, and
# every crate downstream of it does not build. Both directions of that were live at once:
#
#   * INCLUDE-GHOST — the target exists NOWHERE. An unconditional compile break for everyone.
#   * INCLUDE-UNTRACKED — the target exists on the author's disk but is not tracked by git.
#     Green for the lane that emitted it, RED for every co-tenant and every fresh clone. This
#     is the direction nothing else in the tree can see: the Lean door treats an on-disk
#     untracked artifact as "in flight" and (correctly, for ITS question) stays quiet, the
#     emit's coverage check walks files that exist, and `cargo check` on the author's box
#     passes. It shipped exactly this way — `descriptor_by_name.rs` include_str'd
#     `dfa-routing-table-exact-public-v1.json` while the artifact was uncommitted.
#
# Deliberately NOT scoped to descriptors. An absent `include_str!` target is a compile break
# whatever the file is, and scoping the class to `circuit/descriptors/` would have made the
# check a description of the one instance we happened to find rather than of the shape.
#
# Reads the WORKING TREE of tracked `*.rs` (not `HEAD:`) on purpose: the ~1s preflight in
# `scripts/check-descriptor-drift.sh` is meant to catch this BEFORE the commit lands. In CI the
# two are the same bytes.
_INCLUDE_MACRO = re.compile(r'\binclude_(?:str|bytes)!\s*\(\s*"((?:[^"\\]|\\.)*)"\s*,?\s*\)')
# Non-literal forms (`concat!(env!("OUT_DIR"), ..)`, a macro-built path). Nothing here can
# resolve those, so they are COUNTED and reported rather than silently dropped — a growing
# count is the signal that this check's coverage is shrinking.
_INCLUDE_MACRO_ANY = re.compile(r'\binclude_(?:str|bytes)!\s*\(')

INCLUDE_SCAN_EXCLUDED_DIRS = (
    # `scripts/mirror-gates/canary/` is the mirror gate's OWN falsification corpus: hand-written
    # .rs fixtures that must EXHIBIT the flaw shapes `scripts/mirror-gates/mirror_gates.py`
    # hunts for, so that a gate which stopped detecting them reds. No cargo target compiles
    # them (they are not in any crate), and `A2__circuit-prove__tests__self_golden.rs`
    # include_str's a `canary.json` that deliberately does not exist. Named here, with the
    # reason, rather than skipped by some generic "looks like a fixture" rule — an exclusion
    # from a build gate is a decision that belongs on the record.
    "scripts/mirror-gates/canary/",
)


def _rust_comment_spans(text: str, path: str) -> tuple[list[tuple[int, int]], list[tuple[int, int]]]:
    """Lex `text` as Rust far enough to return (comment spans, string spans).

    Needed because a regex alone cannot tell code from prose: `hints/benches/criterion.rs:11`
    carries a COMMENTED-OUT `include_str!("big_committee.json")` whose target is genuinely
    absent, and a check that reds on it is a check people learn to ignore. Handles line and
    (nested) block comments, plain/byte/raw strings, and the char-literal-vs-lifetime
    ambiguity (`'a'` vs `'static`).

    FATAL on an unterminated comment or string: that is a real syntax error, and a lexer that
    guessed past it would be reporting on a file it read wrong."""
    comments: list[tuple[int, int]] = []
    strings: list[tuple[int, int]] = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            j = text.find("\n", i)
            j = n if j < 0 else j
            comments.append((i, j))
            i = j
        elif c == "/" and i + 1 < n and text[i + 1] == "*":
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/*", j):
                    depth += 1; j += 2
                elif text.startswith("*/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            if depth:
                sys.exit(
                    f"emit_descriptors: {path} — unterminated /* block comment (depth "
                    f"{depth} at EOF). This lexer will not report on a file it cannot read."
                )
            comments.append((i, j))
            i = j
        elif c == "r" or (c == "b" and text.startswith("br", i)):
            # raw string: r"..", r#".."#, br"..", br#".."#  — else an ordinary identifier
            k = i + (2 if c == "b" else 1)
            h = 0
            while k + h < n and text[k + h] == "#":
                h += 1
            if k + h < n and text[k + h] == '"':
                close = '"' + "#" * h
                j = text.find(close, k + h + 1)
                if j < 0:
                    sys.exit(f"emit_descriptors: {path} — unterminated raw string literal.")
                strings.append((i, j + len(close)))
                i = j + len(close)
            else:
                i += 1
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    break
                else:
                    j += 1
            if j >= n:
                sys.exit(f"emit_descriptors: {path} — unterminated string literal.")
            strings.append((i, j + 1))
            i = j + 1
        elif c == "'":
            # char literal (`'a'`, `'\n'`, `'\u{1F600}'`) vs lifetime/label (`'a`, `'static:`).
            if i + 1 < n and text[i + 1] == "\\":
                # An escape's LENGTH is decided by its FORM, never by scanning for the next
                # `'`: in `b'\\'` the char after the backslash IS a backslash, and a scanner
                # that treats it as opening another escape steps OVER the closing quote and
                # swallows the file to the next tick — which is how this lexer read
                # `circuit-prove/tests/law1_enforcement_gate.rs` as an unterminated string and
                # FATALed the whole descriptor gate. `\u{..}` is the one variable-length form.
                if text.startswith("u{", i + 2):
                    j = text.find("}", i + 4)
                    end = j + 2 if j >= 0 else -1
                else:
                    end = i + 4  # `'` `\` <one escape char> `'`
                if end < 0 or end > n or text[end - 1] != "'":
                    sys.exit(
                        f"emit_descriptors: {path} — unterminated char literal at offset {i} "
                        f"({text[i:i + 12]!r}). This lexer will not report on a file it cannot read."
                    )
                strings.append((i, end))
                i = end
            elif i + 2 < n and text[i + 2] == "'":
                strings.append((i, i + 3))
                i += 3
            else:
                i += 1  # a lifetime — consume only the tick
        else:
            i += 1
    return comments, strings


def _tracked_rust_files() -> tuple[list[str], bool]:
    """Tracked `*.rs` paths (repo-relative), and whether a git index answered.

    Without a git index (a vendored export, or the rsync'd remote build lane `scripts/pbuild`,
    which excludes `.git/`) the UNTRACKED leg is not computable — the caller degrades that leg
    and says so, same label discipline as `by_name_present`."""
    try:
        out = subprocess.run(
            ["git", "-C", str(ROOT), "ls-files", "-z", "--", "*.rs"],
            capture_output=True, text=True,
        )
        if out.returncode == 0:
            files = [p for p in out.stdout.split("\0") if p]
            if files:
                return files, True
    except OSError:
        pass
    return sorted(
        p.relative_to(ROOT).as_posix()
        for p in ROOT.rglob("*.rs")
        if p.is_file() and ".git/" not in p.as_posix() and "/target/" not in p.as_posix()
    ), False


def _reference_is_committed(path: str, needle: str) -> bool:
    """Does HEAD's version of `path` already contain `needle`?

    The three-way split both doors below use — and the one `verify_by_name_routing` already
    used for artifacts (its `inflight` list) — turns on this. A reference to an untracked file
    is a BROKEN HEAD if the reference itself is committed, and a lane MID-AUTHORING if it is
    not. Conflating them either lets a real break pass or reds every lane that is writing a new
    module, and a gate that cries wolf during normal authoring is a gate people route around.

    In CI nothing is uncommitted, so working tree == HEAD and every finding is a real break:
    the distinction costs the gate no teeth where it matters."""
    out = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"HEAD:{path}"],
        capture_output=True, text=True,
    )
    if out.returncode != 0:
        return False  # not in HEAD at all -> the reference cannot be committed
    return needle in out.stdout


def verify_include_targets() -> list[str]:
    """Every literal `include_str!`/`include_bytes!` target in tracked Rust must EXIST, and must
    be TRACKED wherever the include itself is already committed. Returns finding lines (empty ==
    clean); prints a one-line summary naming any in-flight (uncommitted-include) pairs."""
    files, have_index = _tracked_rust_files()
    tracked_paths: set[str] = set()
    if have_index:
        out = subprocess.run(
            ["git", "-C", str(ROOT), "ls-files", "-z"], capture_output=True, text=True
        )
        tracked_paths = {p for p in out.stdout.split("\0") if p}

    # Narrow to the files that can possibly matter BEFORE reading any. This is not a weaker
    # filter — it is the SAME predicate ("the source contains the literal token `include_str!`
    # or `include_bytes!`") that the per-file skip below applied, evaluated by git instead of by
    # reading all ~3900 tracked .rs. `-a` keeps a NUL-bearing source in the candidate set so the
    # unreadable-source tooth below still fires on it rather than the file being silently dropped.
    candidates = set(files)
    if have_index:
        g = subprocess.run(
            ["git", "-C", str(ROOT), "grep", "-l", "-a", "-z", "-F",
             "-e", "include_str!", "-e", "include_bytes!", "--", "*.rs"],
            capture_output=True, text=True,
        )
        if g.returncode in (0, 1):  # 1 == no matches, a legitimate (if surprising) answer
            candidates = {p for p in g.stdout.split("\0") if p} & candidates

    findings: list[str] = []
    inflight_includes: list[str] = []
    n_sites = n_nonliteral = 0
    excluded = 0
    for rel in sorted(candidates):
        if rel.startswith(INCLUDE_SCAN_EXCLUDED_DIRS):
            excluded += 1
            continue
        p = ROOT / rel
        try:
            text = p.read_text()
        except (OSError, UnicodeDecodeError) as e:
            sys.exit(
                f"emit_descriptors: cannot read tracked Rust source {rel} ({e}). Refusing to "
                "report a pass over a file this check could not scan."
            )
        if "include_str!" not in text and "include_bytes!" not in text:
            continue
        comments, strings = _rust_comment_spans(text, rel)
        blanked = list(text)
        for a, b in comments:
            for k in range(a, b):
                if blanked[k] != "\n":
                    blanked[k] = " "
        blanked = "".join(blanked)
        # A match must not itself sit inside a string literal (a test that embeds Rust source
        # as a string is not a compile-time include).
        in_string = [(a, b) for a, b in strings]

        def quoted(off: int) -> bool:
            return any(a < off < b for a, b in in_string)

        literal_starts = set()
        for m in _INCLUDE_MACRO.finditer(blanked):
            if quoted(m.start()):
                continue
            literal_starts.add(m.start())
            n_sites += 1
            line = blanked.count("\n", 0, m.start()) + 1
            target = (p.parent / m.group(1)).resolve()
            # Both sides are fully resolved (ROOT is `.resolve()`d at import), so this is a
            # symlink-stable comparison. A target OUTSIDE the repo gets its own class rather than
            # being mislabelled UNTRACKED with a "commit it alongside" instruction that cannot
            # apply — nothing in this repo can make a path outside it tracked.
            inside = True
            try:
                trel = target.relative_to(ROOT).as_posix()
            except ValueError:
                inside = False
                trel = target.as_posix()
            if not inside:
                findings.append(
                    f"INCLUDE-ESCAPES-REPO: {rel}:{line} `include_str!/include_bytes!` of "
                    f"`{m.group(1)}` resolves to {trel}, OUTSIDE this repository. The build then "
                    f"depends on a path no checkout can reproduce. Vendor the file in-tree."
                )
                continue
            if not target.exists():
                findings.append(
                    f"INCLUDE-GHOST: {rel}:{line} `include_str!/include_bytes!` of "
                    f"`{m.group(1)}` -> {trel}, which does not exist. `include_*!` is resolved "
                    f"by rustc at COMPILE time, so this crate and everything downstream of it "
                    f"CANNOT BUILD. Commit the artifact (re-run its emit ceremony) or drop the "
                    f"include and its dispatch arm — do NOT `#[cfg]`-gate the include away."
                )
            elif have_index and trel not in tracked_paths:
                if _reference_is_committed(rel, m.group(1)):
                    findings.append(
                        f"INCLUDE-UNTRACKED: {rel}:{line} `include_str!/include_bytes!` of "
                        f"`{m.group(1)}` -> {trel}, which exists ON DISK but is NOT tracked by "
                        f"git — and the include IS committed. So HEAD is broken RIGHT NOW: it "
                        f"compiles for whoever emitted the artifact and reds for every "
                        f"co-tenant and every fresh clone. `git add` the artifact."
                    )
                else:
                    inflight_includes.append(f"{rel}:{line} -> {trel}")
        for m in _INCLUDE_MACRO_ANY.finditer(blanked):
            if m.start() not in literal_starts and not quoted(m.start()):
                n_nonliteral += 1

    leg = "exists+tracked" if have_index else "exists ONLY (NO git index here — untracked leg unavailable)"
    print(
        f"verify-include-targets: {n_sites} literal include_str!/include_bytes! site(s) over "
        f"{len(files)} tracked .rs · checked {leg}"
        + (f" · {n_nonliteral} non-literal (macro-built path) site(s) NOT checkable" if n_nonliteral else "")
        + (f" · {excluded} candidate file(s) in named exclusions" if excluded else "")
        + (f"\n  IN FLIGHT (untracked target, include NOT yet committed — `git add` the artifact "
           f"IN THE SAME COMMIT or HEAD breaks): {', '.join(inflight_includes)}"
           if inflight_includes else "")
    )
    return findings


# ---- the SAME door, one language over: a committed `import` of an uncommitted module -----
#
# `20b9d9a20f` is titled "repairs a committed tree that imported untracked files": a committed
# .lean imported `Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine`, which was left untracked,
# so a fresh checkout could not build it. Identical shape to INCLUDE-UNTRACKED — green for the
# author, red for everyone else — and worth checking here rather than waiting for the next
# multi-hour `lake build` to discover it, since this driver's whole point is that the emit's Lean
# corpus builds.
#
# Only `Dregg2.*` / `Polis.*` are resolved: Mathlib/Std/Lean/Batteries live in `.lake/packages`,
# which is not this repo's to track. That scope is a decision, not an oversight — a mis-typed
# Mathlib import is Lean's error to give, an untracked FIRST-PARTY module is ours.
LEAN_FIRST_PARTY_ROOTS = ("Dregg2", "Polis")
_LEAN_IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.M)


def verify_lean_imports() -> list[str]:
    """Every first-party `import` in a tracked metatheory/*.lean must name a TRACKED module.

    Returns finding lines (empty == clean); prints a one-line summary. Skipped entirely with a
    stated reason where there is no git index, since "tracked" is the whole question."""
    out = subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "-z", "--", "metatheory/*.lean"],
        capture_output=True, text=True,
    )
    if out.returncode != 0:
        print("verify-lean-imports: SKIPPED — no git index here, and `tracked` is the question.")
        return []
    files = [p for p in out.stdout.split("\0") if p]
    if not files:
        sys.exit(
            "emit_descriptors: `git ls-files metatheory/*.lean` returned NOTHING. A scan that "
            "sees zero modules would report a vacuous pass; re-point it."
        )
    pre = len("metatheory/")
    tracked_mods = {f[pre:-len(".lean")].replace("/", ".") for f in files}
    on_disk_mods = {
        p.relative_to(ROOT / "metatheory").as_posix()[:-len(".lean")].replace("/", ".")
        for p in (ROOT / "metatheory").rglob("*.lean")
        if ".lake" not in p.relative_to(ROOT / "metatheory").parts
    }

    findings: list[str] = []
    inflight: list[str] = []
    n_imports = 0
    for f in files:
        text = (ROOT / f).read_text(errors="replace")
        for m in _LEAN_IMPORT.finditer(text):
            mod = m.group(1)
            if not mod.startswith(LEAN_FIRST_PARTY_ROOTS):
                continue
            n_imports += 1
            if mod in tracked_mods:
                continue
            line = text.count("\n", 0, m.start()) + 1
            if mod not in on_disk_mods:
                # GHOST fails unconditionally: nobody is mid-authoring a file that does not exist,
                # so there is no in-flight reading of this. `lake build` cannot resolve it, and
                # every theorem citing that module is UNBUILT rather than proven.
                findings.append(
                    f"LEAN-IMPORT-GHOST: {f}:{line} imports `{mod}`, whose module file exists "
                    f"NOWHERE — no file, no git history. A fresh checkout cannot `lake build` "
                    f"this, and every theorem downstream of it is unbuilt rather than proven. "
                    f"Commit the module, or drop the import and whatever it was carrying."
                )
            elif _reference_is_committed(f, f"import {mod}"):
                findings.append(
                    f"LEAN-IMPORT-UNTRACKED: {f}:{line} imports `{mod}`, whose module file exists "
                    f"ON DISK but is NOT tracked — and the import IS committed. HEAD is broken "
                    f"RIGHT NOW: it builds for whoever wrote the module and reds for every fresh "
                    f"checkout (this is the wound `20b9d9a20f` repaired). `git add` the module."
                )
            else:
                inflight.append(f"{f}:{line} -> {mod}")
    print(
        f"verify-lean-imports: {n_imports} first-party import(s) over {len(files)} tracked "
        f"metatheory/*.lean ({len(tracked_mods)} modules) · checked exists+tracked"
        + (f"\n  IN FLIGHT (untracked module, import NOT yet committed — `git add` the module IN "
           f"THE SAME COMMIT or HEAD breaks): {', '.join(inflight)}" if inflight else "")
    )
    return findings


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


def _parse_e1_intervals(spec: str) -> list[tuple[int, int]]:
    """Parse an `e1compact` payload (`a-b,c-d,...`, ascending half-open runs; possibly empty)
    into `[(a, b), ...]`. Validates ascending, non-overlapping, well-formed."""
    if spec == "":
        return []
    out: list[tuple[int, int]] = []
    prev_end = 0
    for chunk in spec.split(","):
        a_s, _, b_s = chunk.partition("-")
        a, b = int(a_s), int(b_s)
        if not (a < b and a >= prev_end):
            sys.exit(
                f"emit_descriptors: e1compact interval {chunk!r} not a well-formed ascending "
                f"non-overlapping half-open run (a<b, a>=prev_end={prev_end})"
            )
        out.append((a, b))
        prev_end = b
    return out


def split_wide_registry(stdout: str, written):
    """The wide-registry emitter prints one `key\tname\tjson` line per wide member, in the LIVE
    `rotation-v3-staged-registry.tsv` order — a member-for-member, name-stable COVER of the live V3
    registry (57 members): the 45 emit-source members (`v3RegistryCapOpenWide`) + the live-only
    `transferCapOpenTB` / `heapWrite` + the 9 WRITE-bearing cap-open tail members
    (`v3RegistryCapOpenWriteWide`, §10, MINUS `grantCapWriteCapOpen` — not a live member) + the
    live-only `supplyMint`, each made 8-felt-wide AND S2-COMPACTED (the two rotated 1-felt chains
    deleted, 960 columns removed, gated per member by the Lean `compactOk` falsifier) = 57 lines.

    Each member line is followed by an `s2compact\t<key>\t<bb>\t<lane_base>` companion line — the
    per-member deletion geometry, routed into `circuit/src/effect_vm/s2_compact_generated.rs` so
    the Rust trace producer compacts EXACTLY the columns the Lean emit deleted (single source)."""
    lines = [ln for ln in stdout.splitlines() if ln.strip()]
    members = [
        ln for ln in lines
        if not ln.startswith("s2compact\t") and not ln.startswith("e1compact\t")
    ]
    geo = [ln for ln in lines if ln.startswith("s2compact\t")]
    e1 = [ln for ln in lines if ln.startswith("e1compact\t")]
    if len(members) != 57:
        sys.exit(
            f"emit_descriptors: wide registry emitter produced {len(members)} member lines "
            "(expected 57)"
        )
    if len(geo) != 57:
        sys.exit(
            f"emit_descriptors: wide registry emitter produced {len(geo)} s2compact lines "
            "(expected 57)"
        )
    if len(e1) != 57:
        sys.exit(
            f"emit_descriptors: wide registry emitter produced {len(e1)} e1compact lines "
            "(expected 57)"
        )
    for ln in members:
        if ln.count("\t") != 2:
            sys.exit(f"emit_descriptors: wide registry line malformed: {ln[:80]!r}")
    write_file(WIDE_REGISTRY_TSV, "\n".join(members) + "\n", written)

    rows = []
    for ln in geo:
        _tag, key, bb, lane = ln.split("\t")
        rows.append(f'    ("{key}", {int(bb)}, {int(lane)}),')
    module = (
        "// @generated by metatheory/EmitWideRegistryProbe.lean via scripts/emit_descriptors.py"
        " — DO NOT EDIT BY HAND.\n"
        "//\n"
        "// THE S2 DELETION GEOMETRY (Epoch 1): per wide-registry member, the block base `bb`\n"
        "// (the face width the rotated BEFORE limbs sit at) and the graduated S2 lane base.\n"
        "// The deleted columns of a member are exactly the three bands\n"
        "//   [bb+179, bb+239) ∪ [bb+418, bb+478) ∪ [lane_base, lane_base+840)\n"
        "// — the two rotated 1-felt Merkle–Damgård chain carrier/digest bands plus their 840\n"
        "// graduated chip-lane columns. The Lean emit deleted these from the committed wide\n"
        "// descriptors (`RotWideCompactS2.compactS2`, gated per member by `compactOk`); the Rust\n"
        "// trace producer must drop the SAME columns from its old-geometry rows\n"
        "// (`trace_rotated::compact_s2_columns`). One source: this table.\n"
        "\n"
        "/// In-block offset of the first deleted carrier column (the 1-felt state_commit digest).\n"
        "pub const S2_CARRIER_OFF: usize = 179;\n"
        "/// One deleted carrier band's width (digest + 59 chain carriers).\n"
        "pub const S2_CARRIER_SPAN: usize = 60;\n"
        "/// The deleted graduated lane band's width (120 sites × 7 lanes).\n"
        "pub const S2_LANE_SPAN: usize = 840;\n"
        "/// Total deleted columns per member.\n"
        "pub const S2_DELETED_COLS: usize = 2 * S2_CARRIER_SPAN + S2_LANE_SPAN;\n"
        "\n"
        "/// `(registry key, bb, lane_base)` per wide member, in registry order.\n"
        "pub const S2_COMPACT_TABLE: &[(&str, usize, usize)] = &[\n"
        + "\n".join(rows)
        + "\n];\n"
    )
    GENERATED_RS[S2_COMPACT_RS] = module

    # THE E1 DELETION GEOMETRY (Epoch-1 SECOND flag-day): per wide-registry member, the DERIVED
    # kill-set of dead v1-face columns (POST-S2 coords), as ascending half-open runs. The Rust trace
    # producer drops EXACTLY these columns (`trace_rotated::compact_e1_columns`) so its rows match the
    # E1-compacted committed descriptor. One source: this table (from the Lean `deadColsE1`).
    e1_rows = []
    for ln in e1:
        _tag, key, spec = ln.split("\t", 2)
        intervals = _parse_e1_intervals(spec)
        body = ", ".join(f"({a}, {b})" for a, b in intervals)
        e1_rows.append(f'    ("{key}", &[{body}]),')
    e1_module = (
        "// @generated by metatheory/EmitWideRegistryProbe.lean via scripts/emit_descriptors.py"
        " — DO NOT EDIT BY HAND.\n"
        "//\n"
        "// THE E1 DELETION GEOMETRY (Epoch-1 SECOND flag-day): per wide-registry member, the\n"
        "// DERIVED per-member kill-set of DEAD v1-face columns — every column at index >= 90\n"
        "// referenced by NO surviving constraint / hash site / range (the retired aux band\n"
        "// 90..187 incl. the 60-col balance bit-decomposition, and the note/heap/refusal/cap-open\n"
        "// appendix scratch bands). Coordinates are POST-S2 (the columns as they sit in the\n"
        "// S2-compacted member), as ascending half-open `[start, end)` runs. The scan is capped at\n"
        "// the HOST width (`e1Ceiling`): the gentian floor-refuse aux block + the umem leg ride the\n"
        "// TOP of the member and are NOT producer-emitted (the gentian aux is filled at PROVE time by\n"
        "// `fill_refuse_aux`, AFTER the producer's `compact_e1`), so the kill-set must never reach\n"
        "// into them — else the deployed producer's pre-gentian `compact_e1` panics on a too-short row.\n"
        "// The Lean emit deleted these from the committed wide descriptors\n"
        "// (`RotWideCompactE1.compactE1`, gated per member by `compactE1Ok`);\n"
        "// the Rust trace producer must drop the SAME columns from its S2-compacted rows\n"
        "// (`trace_rotated::compact_e1_columns`, draining descending). One source: this table.\n"
        "\n"
        "/// `(registry key, &[(start, end), ...])` per wide member, in registry order — the\n"
        "/// ascending half-open POST-S2 kill-set runs. An empty slice means no E1-dead columns.\n"
        "pub const E1_COMPACT_TABLE: &[(&str, &[(usize, usize)])] = &[\n"
        + "\n".join(e1_rows)
        + "\n];\n"
    )
    GENERATED_RS[E1_COMPACT_RS] = e1_module


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
# ADDITIVE / STAGED: the setField VALUE8 epoch — the 8 written-slot value8 members
# (`EmitRotationV3SetFieldValue8.lean`, Lean `v3RegistrySetFieldValue8`). Beside the deployed
# `rotation-v3-staged-registry.tsv`; the live TSV / FP / VK are untouched.
SETFIELD_VALUE8_TSV = "rotation-v3-setfield-value8-staged-registry.tsv"


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


def split_by_name(stdout: str, written):
    """`EmitByName.lean` prints one `<filename>\tjson` line per checked-in by-name descriptor —
    the surface `circuit/src/descriptor_by_name.rs::descriptor_by_name()` serves to `bridge/` and
    `wire/` at verify time.

    Routes each to `circuit/descriptors/by-name/<filename>` (the `by-name/` prefix makes the key
    relative to DESC, so install/FP/provenance all treat these exactly like the main set). This is
    what deletes the old UNGATED hand-transcription hop between the Lean `#guard` golden and the
    deployed bytes — the hop `predicate-arith.json` drifted through."""
    lines = [ln for ln in stdout.splitlines() if ln.strip()]
    if not lines:
        sys.exit("emit_descriptors: by-name emitter produced no lines")
    for ln in lines:
        if ln.count("\t") != 1:
            sys.exit(f"emit_descriptors: by-name line malformed (want `file\\tjson`): {ln[:80]!r}")
        filename, blob = ln.split("\t", 1)
        if not filename.endswith(".json"):
            sys.exit(f"emit_descriptors: by-name key is not a .json file: {filename!r}")
        if not blob.startswith('{"name":"'):
            sys.exit(
                f"emit_descriptors: by-name {filename} payload is not a descriptor JSON: {blob[:60]!r}"
            )
        # Reproduce the file's checked-in trailing-newline convention (see the frozenset above).
        if filename in BY_NAME_NEWLINE_TERMINATED:
            blob += "\n"
        write_file(f"by-name/{filename}", blob, written)


def split_cert_f(stdout: str, written):
    """`EmitCertF.lean` prints the bare descriptor JSON via `IO.println`. The checked-in artifact
    carries NO trailing newline, so strip the one `IO.println` adds."""
    blob = stdout.rstrip("\n")
    if not blob.startswith('{"name":"cert-f"'):
        sys.exit(f"emit_descriptors: cert-f emitter produced unexpected output: {blob[:80]!r}")
    write_file(CERT_F_FILE, blob, written)


def split_cert_f_market4(stdout: str, written):
    """`EmitCertFMarket4.lean` — same convention as `EmitCertF.lean` (bare JSON, no trailing
    newline in the checked-in artifact)."""
    blob = stdout.rstrip("\n")
    if not blob.startswith('{"name":"cert-f"'):
        sys.exit(
            f"emit_descriptors: cert-f-market4 emitter produced unexpected output: {blob[:80]!r}"
        )
    write_file(CERT_F_MARKET4_FILE, blob, written)


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
    descriptor install is ack-gated, provenance-stamped, and audit-logged. A generated-Rust-only
    change is byte-safe (it cannot re-key a descriptor) and installs without a VK-regeneration
    acknowledgement. A byte-identical emission is a silent no-op."""
    # Nothing installs a module the drift gate cannot see: every buffered generated module must
    # be declared in GENERATED_RS_PATHS, and every FP-bearing source in RUST_FP_FILES. Together
    # those two tuples ARE `guarded_paths()`, which is what `check-descriptor-drift.sh` snapshots.
    assert_generated_declared()
    assert_fp_files_declared()

    # Converge the generated modules onto rustfmt's shape BEFORE the diff, so what we compare
    # against disk is exactly what we would write — and equals what the pre-commit hook and
    # `cargo fmt --all -- --check` produce (see normalize_generated_rust).
    normalize_generated_rust()

    fp_changes, n_fp = compute_fp_rewrites(written)

    changed_desc = sorted(
        name for name, content in written.items()
        if not (DESC / name).exists() or (DESC / name).read_text() != content
    )
    changed_gen = {
        p: content for p, content in GENERATED_RS.items()
        if not p.exists() or p.read_text() != content
    }
    changed = (
        changed_desc
        + sorted(str(p.relative_to(ROOT)) for p in fp_changes)
        + sorted(str(p.relative_to(ROOT)) for p in changed_gen)
    )

    if not changed:
        print(
            f"emit_descriptors: NO-OP — all {len(written)} descriptor files and "
            f"{n_fp} FP constants are byte-identical to the Lean emission."
        )
        return

    # A Lean-authored Rust projection is not a VK regeneration. Requiring the federation-rekey ACK
    # for a generated-module-only change made the safe half of a layout refactor impossible to run
    # through the canonical emitter. Geometry changes remain protected: because the Lean descriptor
    # emit reads the same RotatedLayout, moving a consumed group column also changes descriptor bytes
    # and therefore enters the ack-gated branch below.
    if not changed_desc and not fp_changes:
        for p, content in changed_gen.items():
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(content)
        print(
            f"emit_descriptors: GENERATED-RUST UPDATE — installed {len(changed_gen)} Lean-authored "
            "module(s); descriptor bytes and FP constants are unchanged (no VK regen)."
        )
        return

    auth = require_regen_ack(changed, "this emission")

    for name in changed_desc:
        (DESC / name).write_text(written[name])
    for p, new_text in fp_changes.items():
        p.write_text(new_text)
    for p, content in changed_gen.items():
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content)

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


# The accepted flags, in ONE place. The usage message below is RENDERED from this rather than
# transcribed beside it — the transcription had already lagged (`--strict` and, the moment it
# landed, `--list-guarded-paths` were missing from the message that claims to enumerate them).
ACCEPTED_FLAGS = (
    "--stamp-existing",
    "--list-emitter-modules",
    "--list-guarded-paths",
    "--verify-by-name-routing",
    "--verify-provenance",
    "--strict",
)


def main():
    argv = sys.argv[1:]
    # An unrecognized flag must REFUSE, not be ignored: every dispatch below is an `in argv`
    # membership test, so a bare-argv fall-through runs the REAL ack-gated emit. A typo'd or
    # imagined `--dry-run` would therefore have regenerated the descriptor set for real.
    unknown = [a for a in argv if a not in ACCEPTED_FLAGS]
    if unknown:
        sys.exit(
            f"emit_descriptors: unknown arguments {unknown!r} (expected none, or one of: "
            + ", ".join(ACCEPTED_FLAGS) + ")"
        )
    if "--verify-provenance" in argv:
        verify_provenance(strict="--strict" in argv)
        return
    if "--verify-by-name-routing" in argv:
        # Static, seconds, no Lean and no cargo — usable while the emit is blocked.
        findings = verify_by_name_routing()
        if findings:
            sys.stderr.write("verify-by-name-routing: FAIL\n")
            for f in findings:
                sys.stderr.write(f"  - {f}\n")
            sys.exit(1)
        print("verify-by-name-routing: PASS — the routing table and the checked-in "
              "by-name set cover each other, every routed artifact is stamped, and every "
              "literal include_str!/include_bytes! target exists and is tracked.")
        return
    if "--stamp-existing" in argv:
        stamp_existing()
        return
    if "--list-guarded-paths" in argv:
        # The change-set `install_and_stamp` can rewrite (see guarded_paths). No Lean run, so
        # `scripts/check-descriptor-drift.sh` can SNAPSHOT exactly what this driver may touch
        # instead of keeping its own transcription of it.
        print("\n".join(guarded_paths()))
        return
    if "--list-emitter-modules" in argv:
        # The build set the emitters need (see emitter_modules). No Lean run; pure source
        # scan, so `scripts/check-descriptor-drift.sh` can build exactly what it runs.
        print("\n".join(emitter_modules()))
        return
    if argv:
        # Recognized, but no mode claimed it — today only a bare `--strict`, which is a MODIFIER
        # of `--verify-provenance`, never a mode. Refuse rather than fall through to the emit.
        sys.exit(f"emit_descriptors: {argv!r} names no mode (expected none, or one of: "
                 + ", ".join(ACCEPTED_FLAGS) + ")")

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
        elif lean.endswith("EmitLayoutManifest.lean"):
            split_layout(out, written)
        elif lean.endswith("EmitCrossCellConservation.lean"):
            split_cross_cell_conservation(out, written)
        elif lean.endswith("EmitUMemCohortMulti.lean"):
            split_member_tsv(out, written, UMEM_COHORT_MULTI_TSV)
        elif lean.endswith("EmitUMemCohort.lean"):
            split_member_tsv(out, written, UMEM_COHORT_TSV)
        elif lean.endswith("EmitWideUMemWeldRegistryProbe.lean"):
            split_member_tsv(out, written, WIDE_UMEM_WELD_REGISTRY_TSV)
        elif lean.endswith("EmitRotationV3SetFieldValue8.lean"):
            split_member_tsv(out, written, SETFIELD_VALUE8_TSV)
        elif lean.endswith("EmitByName.lean"):
            split_by_name(out, written)
        elif lean.endswith("EmitCertFMarket4.lean"):
            split_cert_f_market4(out, written)
        elif lean.endswith("EmitCertF.lean"):
            split_cert_f(out, written)
        else:
            sys.exit(f"emit_descriptors: no split routine for {lean}")

    # Coverage check: every checked-in descriptor file must have been (re)emitted.
    # (PROVENANCE.json is the regen-control stamp, not an emitted artifact.)
    #
    # RECURSES (rglob, relative-keyed). It used to be `DESC.iterdir()` filtered on `p.is_file()` —
    # and `by-name/` is a DIRECTORY, so the entire deployed dispatch surface was silently exempt
    # from this gate: no by-name file was ever in `written`, nothing was ever reported missing, and
    # the drift checker's snapshot->emit->diff therefore left by-name byte-identical on both sides
    # (an unconditional PASS for any content whatsoever). That exemption is how a 5-wide re-authoring
    # of the 24-wide `predicate-arith` descriptor reached production. A by-name file no emitter
    # reproduces is now a routing-gap FAILURE, like every other descriptor.
    on_disk = {
        str(p.relative_to(DESC)) for p in DESC.rglob("*") if p.is_file()
    }
    missed = on_disk - set(written) - {PROVENANCE_FILE} - COVERAGE_EXEMPT
    if missed:
        sys.exit(
            "emit_descriptors: these checked-in descriptors were NOT reproduced "
            "by any emitter (routing gap):\n  " + "\n  ".join(sorted(missed))
        )

    install_and_stamp(written)


if __name__ == "__main__":
    main()
