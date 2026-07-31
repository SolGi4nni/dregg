#!/usr/bin/env bash
# check-lean-seed-closure.sh — does this Lean seed archive actually accelerate a build?
#
# ═══ THE WOUND THIS CLOSES (issue #41) ══════════════════════════════════════════════════
# The seed exists to turn an hours-long cold `lake` bootstrap into minutes. An outside
# reporter measured, on a fresh Linux/x86_64 bootstrap, that it does not: the installed
# base seed held 1,797 members, and the immediate `cargo build -p dregg-lean-ffi
# --features lean-lib` then had to compile and splice **1,251 further objects over 25
# closure passes — 21m47s** — arriving at a 3,085-member working archive. Promoting THAT
# archive as the seed cut a clean fail-loud `dregg-deploy` build to 2m51s and 5 objects.
# Their diagnosis was exact: the seed script and `build.rs` were computing DIFFERENT
# closures. (Fixed at the source in `ec4ed5e17`, 2026-07-29 — both now root at
# `Dregg2.FFI`, and `scripts/lean-ffi-closure.py` computes the one closure.)
#
# ⚑ Nothing in the tree compared a seed's CONTENTS to that closure, so the fix at the
# source cannot be observed from a seed. `scripts/check-lean-seed-freshness.sh` compares
# a TREE HASH recorded in `dregg-lean-ffi/lean-seed.pin`; it says nothing about what is
# in the archive. Measured 2026-07-30, the seed sitting in this checkout carried 188
# `Dregg2_*.o` against a 243-module boundary closure — **55 in-tree modules absent**,
# every one of them a verified decision (the Mina light-client gates, the circuit emit
# modules, DelegAdmit) — and did not carry `Dregg2_FFI.o`, the boundary object itself.
#
# ═══ WHY "IT SELF-LINKS" IS NOT THE BAR ════════════════════════════════════════════════
# That same 55-short archive has ZERO undefined initializers. It self-links perfectly —
# because the boundary object that would REFERENCE the 55 is missing too. An archive can
# be closed and still be missing every gate it exists to arm. So this gate checks the
# boundary FIRST and the link-closure SECOND; either alone is satisfiable by a short seed.
#
# THREE LEGS, each refutable on its own:
#   1. `Dregg2_FFI.o` is a member.  The boundary module IS the manifest (`metatheory/
#      Dregg2/FFI.lean`); its object is that manifest's compiled image. Absent ⇒ nothing
#      in the archive references the runtime closure and leg 3 is vacuous.
#   2. Every IN-TREE module of `Dregg2.FFI`'s import closure has a member. This is the
#      coverage leg: a missing one is an `@[export]` the Rust bridge will compile its
#      ABSENT arm for — green, silent, un-armed.
#   3. No undefined `initialize_*` in the archive AS A WHOLE (referenced-minus-defined,
#      the same U−T computation `dregg-lean-ffi/build.rs::undefined_initializers` runs).
#      This is the SPEED leg and it is the reporter's number: each one is an object the
#      first `cargo build` must resolve, compile and splice before it can link.
#
# Dependency (Mathlib/Batteries/…) modules are deliberately NOT required member-by-member:
# the archive is reachability-GC'd on purpose (a full warm mathlib tree is ~295 MB against
# a ~96 MB closure, docs/LEAN-SEED-SIZE.md). Leg 3 is the correct bar for them — present
# iff something actually needs them.
#
# Usage:  scripts/check-lean-seed-closure.sh [archive]      (default: dregg-lean-ffi/libdregg_lean.a)
# Exit:   0 the seed is closure-complete · 1 it is short (the delta is printed) · 2 cannot measure
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 2

ARCH="${1:-dregg-lean-ffi/libdregg_lean.a}"
META="${DREGG_METATHEORY_DIR:-metatheory}"

[ -f "$ARCH" ] || { echo "check-lean-seed-closure: no archive at $ARCH — nothing to measure. A gate whose input is absent is a FAULT, not a pass." >&2; exit 2; }
[ -f "$META/Dregg2/FFI.lean" ] || { echo "check-lean-seed-closure: no boundary module at $META/Dregg2/FFI.lean — cannot compute the closure." >&2; exit 2; }

AR="ar";  command -v ar  >/dev/null 2>&1 || AR="llvm-ar"
NM="nm";  command -v nm  >/dev/null 2>&1 || NM="llvm-nm"
command -v "$AR" >/dev/null 2>&1 || { echo "check-lean-seed-closure: no ar/llvm-ar on PATH." >&2; exit 2; }
command -v "$NM" >/dev/null 2>&1 || { echo "check-lean-seed-closure: no nm/llvm-nm on PATH." >&2; exit 2; }
command -v python3 >/dev/null 2>&1 || { echo "check-lean-seed-closure: python3 is required (it runs scripts/lean-ffi-closure.py)." >&2; exit 2; }

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

# The closure comes from THE SAME script that cuts the seed
# (dregg-lean-ffi/scripts/seed-dregg2-closure.sh calls it to pick members), so a seed and
# its check can never disagree about what the closure IS — only about whether the archive
# on disk contains it.
python3 scripts/lean-ffi-closure.py "$META" > "$TMP/closure.txt" || {
  echo "check-lean-seed-closure: scripts/lean-ffi-closure.py failed — cannot measure." >&2; exit 2; }
[ -s "$TMP/closure.txt" ] || { echo "check-lean-seed-closure: the closure came back EMPTY — the walk is broken, and passing on an empty expectation is worse than not checking." >&2; exit 2; }

"$AR" t "$ARCH" > "$TMP/members.txt" 2>/dev/null || { echo "check-lean-seed-closure: '$AR t $ARCH' failed — not an archive?" >&2; exit 2; }
"$NM" "$ARCH" > "$TMP/nm.txt" 2>/dev/null || true

python3 - "$TMP/closure.txt" "$TMP/members.txt" "$TMP/nm.txt" "$ARCH" <<'PY'
import sys, collections

closure_f, members_f, nm_f, arch = sys.argv[1:5]
closure = [l.strip() for l in open(closure_f) if l.strip()]
members = set(open(members_f).read().split())

IN_TREE = ("Dregg2", "Metatheory", "Polis")
obj = lambda m: m.replace(".", "_") + ".o"

# ── leg 1: the boundary object ───────────────────────────────────────────────
boundary_present = "Dregg2_FFI.o" in members

# ── leg 2: in-tree coverage ──────────────────────────────────────────────────
in_tree = [m for m in closure if m.split(".")[0] in IN_TREE]
missing_in_tree = [m for m in in_tree if obj(m) not in members]

# ── leg 3: link closure (the same U−T set build.rs::undefined_initializers computes) ──
TOOLCHAIN = ("Init", "Std", "Lean", "Lake")
defined, referenced = set(), set()
for line in open(nm_f, errors="replace"):
    t = line.split()
    if len(t) == 2 and len(t[0]) == 1:
        ty, sym = t[0], t[1]
    elif len(t) == 3 and len(t[1]) == 1:
        ty, sym = t[1], t[2]
    else:
        continue
    name = sym.lstrip("_")
    if not name.startswith("initialize_"):
        continue
    rest = name[len("initialize_"):]
    if any(rest == l or rest.startswith(l + "_") for l in TOOLCHAIN):
        continue
    (referenced if ty == "U" else defined).add(name)
undefined = sorted(referenced - defined)

print(f"archive              {arch}")
print(f"members              {len(members)}")
print(f"closure modules      {len(closure)}  ({len(in_tree)} in-tree)")
print(f"in-tree members      {len(in_tree) - len(missing_in_tree)} / {len(in_tree)}")
print(f"leg 1  Dregg2_FFI.o  {'PRESENT' if boundary_present else 'ABSENT'}")
print(f"leg 2  missing       {len(missing_in_tree)} in-tree closure module(s)")
print(f"leg 3  undefined     {len(undefined)} initializer(s) = objects the first `cargo build` must add")

failed = False
if not boundary_present:
    failed = True
    print()
    print("LEG 1 RED — the archive does not contain `Dregg2_FFI.o`.")
    print("  `metatheory/Dregg2/FFI.lean` is THE Lean<->Rust boundary manifest, and this is its")
    print("  compiled image. Without it nothing in the archive references the runtime closure, so")
    print("  leg 3 reads ZERO no matter how much is missing. This seed predates `ec4ed5e17` and")
    print("  was cut from the old hand-maintained root list.")

if missing_in_tree:
    failed = True
    by_ns = collections.Counter(".".join(m.split(".")[:2]) for m in missing_in_tree)
    print()
    print(f"LEG 2 RED — {len(missing_in_tree)} module(s) of the boundary closure have no object here.")
    print("  Each is an `@[export]` the Rust bridge will compile its ABSENT arm for: the")
    print("  `#[cfg(dregg_*_present)]` gate goes dark, the node runs the un-gated path, and every")
    print("  test behind `if !<x>_available() { SKIP }` reports ok having asserted nothing.")
    for ns, n in by_ns.most_common(12):
        print(f"    {n:4d}  {ns}.*")
    print("  first few:")
    for m in missing_in_tree[:10]:
        print(f"    {m}")

if undefined:
    failed = True
    print()
    print(f"LEG 3 RED — {len(undefined)} undefined initializer(s): this archive does NOT self-link.")
    print("  `build.rs::complete_initializer_closure` will resolve, `leanc -c` and splice one object")
    print("  per symbol before anything can link — the 1,251-object / 21m47s first build issue #41")
    print("  measured. It is also the shape a STALE seed takes after Lean exports are added or")
    print("  removed: the link fails loud rather than silently, and this names it up front.")
    for s in undefined[:10]:
        print(f"    {s}")

print()
if failed:
    print("VERDICT: THIS SEED IS SHORT. It is link-correct-or-not as reported above, but it is not")
    print("  the minutes-fast accelerator it is published as.")
    print("  Re-cut it:  dregg-lean-ffi/scripts/seed-dregg2-closure.sh    (local)")
    print("              gh workflow run lean-seed.yml                   (publish; an outward act)")
    sys.exit(1)

print("VERDICT: closure-complete. The boundary object is present, every in-tree closure module has")
print("  an object, and the archive self-links — the first `cargo build` adds ZERO closure objects.")
PY
