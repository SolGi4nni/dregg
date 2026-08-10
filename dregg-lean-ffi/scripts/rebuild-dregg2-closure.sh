#!/usr/bin/env bash
# rebuild-dregg2-closure.sh — RE-SPLICE the seed archive's in-tree slice from the current Lean.
#
# The seed (`dregg-lean-ffi/libdregg_lean.a`, gitignored — see below) is the base every
# `cargo build -p dregg-lean-ffi` COPIES into its own `OUT_DIR` before splicing and GC-ing that
# copy. A plain cargo build never writes the seed; this script is the one place its in-tree slice
# is rewritten. The expensive dependency members (mathlib/batteries/aesop/Qq, ~2900 objects) are
# carried across untouched — regenerating those is `seed-dregg2-closure.sh`'s job.
#
# ═══ WHAT CHANGED HERE ON 2026-08-07, AND WHY ══════════════════════════════════════════════════
# This script produced a seed that was BOTH stale and short, and neither showed up anywhere:
#
#   * IT SPLICED WHATEVER IR HAPPENED TO BE ON DISK. It never ran `lake build`, so the objects it
#     archived were compiled from whatever `.c` a previous build left behind. Now it runs
#     `lake build Dregg2.FFI` first — 1.8s warm — and that is the ONLY authority on whether the IR
#     matches the source. (Four modules' `.c` currently read OLDER than their `.lean` by
#     filesystem mtime and lake replays all 3315 jobs from cache: those mtimes moved on a
#     `git checkout`, the content did not. An mtime precondition here would refuse a correct tree.)
#   * IT SPLICED `find …/ir/Dregg2 -name '*.c'` — every warm object under the Dregg2 IR root, which
#     is 2241 modules, not the 334 in-tree modules of the `Dregg2.FFI` boundary closure. And it
#     touched ONLY `Dregg2_*`, so the 9 `Metatheory_*` and 1 `Polis_*` members of that same closure
#     were never refreshed at all. The member set is now exactly the closure, from
#     `scripts/lean-ffi-closure.py` — the same one `seed-dregg2-closure.sh` and
#     `check-lean-seed-closure.sh` use, so a seed and its checks cannot disagree about what the
#     closure IS.
#   * IT WROTE THE SEED BEFORE ANYTHING CHECKED IT. The result is now built at `$ARCH.new` and must
#     pass `check-lean-seed-member-freshness.py` (every member at least as new as its Lean) AND
#     `check-lean-seed-closure.sh` (the boundary object, in-tree coverage, self-linking) before it
#     is renamed into place. A re-splice that produced a stale or short seed used to succeed.
#
# The header also said "git-tracked SEED" in three places. It has NEVER been tracked
# (`dregg-lean-ffi/.gitignore:7` is `*.a`, and `git log --all -- dregg-lean-ffi/libdregg_lean.a` is
# empty) — it is a local build artifact that arrives by `scripts/fetch-lean-seed.sh`,
# `scripts/bootstrap.sh`, `seed-dregg2-closure.sh` or a colleague's rsync. That is precisely why
# its members can be a fortnight older than the tree with nothing noticing.
#
# Usage:  dregg-lean-ffi/scripts/rebuild-dregg2-closure.sh [--keep-backup]
# Exit:   0 the seed was replaced and both gates are green · non-zero the seed was NOT touched
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
META="$ROOT/metatheory"
ARCH="$ROOT/dregg-lean-ffi/libdregg_lean.a"
OBJDIR="${DREGG_RESPLICE_OBJDIR:-${TMPDIR:-/tmp}/dregg2_closure_objs}"
NCPU="$(sysctl -n hw.logicalcpu 2>/dev/null || nproc)"
KEEP_BACKUP=0
if [ "${1:-}" = "--keep-backup" ]; then KEEP_BACKUP=1; fi

[ -f "$ARCH" ] || { echo "FATAL: missing $ARCH — there is no seed to re-splice. Get one first: scripts/fetch-lean-seed.sh (or ./scripts/bootstrap.sh, or dregg-lean-ffi/scripts/seed-dregg2-closure.sh)"; exit 1; }
command -v lake >/dev/null 2>&1 || { echo "FATAL: lake not on PATH (install elan; ./scripts/bootstrap.sh teaches the fix)"; exit 1; }

# ── 1 · make the IR authoritative ────────────────────────────────────────────────────────────
# Lake's trace is content-driven, so this is the only check that can tell "the source changed"
# from "a checkout moved the mtime". Warm it is seconds; cold it is the honest cost of a seed.
echo "==> lake build Dregg2.FFI (the boundary closure → :c facets)"
( cd "$META" && lake build Dregg2.FFI ) >/dev/null || { echo "FATAL: lake build Dregg2.FFI failed — refusing to splice objects compiled from an IR that lake will not vouch for."; exit 1; }

INC="$(cd "$META" && lake env printenv LEAN_SYSROOT)/include"
mkdir -p "$OBJDIR"

# ── 2 · the member set IS the boundary closure ───────────────────────────────────────────────
# ⚑ IN-TREE IS DECIDED BY THE FILESYSTEM, NOT BY A NAMESPACE LIST. The first version of this
# filtered on `^(Dregg2|Metatheory|Polis)\.` — the same hardcoded triple
# `check-lean-seed-closure.sh` carries — and that list is already wrong: the closure contains
# `Market.*` (sources at `metatheory/Market/*.lean`), which `Dregg2.Games.PathOfAngels.DarkBazaar`
# references by initializer. Splicing under the list left three `initialize_Dregg2_Market_*` edges
# dangling in an archive that had ZERO before. A module is in-tree iff its `.lean` is in this
# repo's `metatheory/` outside `.lake/`, and a new root directory needs no edit here.
CLOSURE="$(mktemp)"; trap 'rm -f "$CLOSURE"' EXIT
ALLMOD="$(mktemp)"
python3 "$ROOT/scripts/lean-ffi-closure.py" "$META" > "$ALLMOD" \
  || { echo "FATAL: scripts/lean-ffi-closure.py failed — cannot compute the boundary closure."; rm -f "$ALLMOD"; exit 1; }
[ -s "$ALLMOD" ] || { echo "FATAL: the boundary closure came back EMPTY. Splicing an empty set would silently EMPTY the seed's in-tree slice."; rm -f "$ALLMOD"; exit 1; }
# NOTE the `; true`: the filter's exit status is the LAST module's `[ -f ]` test, and the closure
# list ends in Mathlib far more often than not — so a bare `|| FATAL` here fired on a perfectly
# good 347-module list. The emptiness floor below is the real check, and it is on the FILE.
while IFS= read -r m; do
  if [ -f "$META/${m//./\/}.lean" ]; then echo "$m"; fi
done < "$ALLMOD" > "$CLOSURE"; true
rm -f "$ALLMOD"
n_mod="$(wc -l < "$CLOSURE" | tr -d ' ')"
[ "$n_mod" -ge 100 ] || { echo "FATAL: the in-tree closure came back as only $n_mod module(s). Refusing to re-splice against an implausible expectation."; exit 1; }
echo "==> $n_mod in-tree modules in the Dregg2.FFI boundary closure"

# Every one of them must have emitted C. A module in the closure with no `.c` after a successful
# `lake build` means the closure walk and lake disagree, and splicing the difference away is how a
# seed goes 137 modules short without a word.
missing_c=0
while IFS= read -r m; do
  [ -f "$META/.lake/build/ir/${m//./\/}.c" ] || { echo "    NO IR: $m"; missing_c=$((missing_c + 1)); }
done < "$CLOSURE"
[ "$missing_c" -eq 0 ] || { echo "FATAL: $missing_c closure module(s) have no emitted .c after a successful lake build."; exit 1; }

# ── 3 · compile the closure ──────────────────────────────────────────────────────────────────
echo "==> Compiling $n_mod objects into $OBJDIR (parallel ×$NCPU; incremental)"
compile_c() {
  local m="$1"
  local c="$META/.lake/build/ir/${m//./\/}.c"
  local out="$OBJDIR/${m//./_}.o"
  if [ ! -f "$out" ] || [ "$c" -nt "$out" ]; then
    # -fPIC: the archive serves BOTH link modes (static bins and the DREGG_LEAN_LINK=shared cdylib
    # link, e.g. sdk-py). No-op on macOS.
    (cd "$META" && lake env leanc -c -fPIC -I "$INC" "$c" -o "$out") || { echo "FAIL $m" >&2; return 1; }
  fi
  # The member's mtime is the ONLY evidence of its age that survives into the archive, and a cached
  # object is older than the splice. Stamp it now so the archive says when it was packed.
  touch "$out"
}
export -f compile_c
export META INC OBJDIR
job_slots() { jobs -rp | wc -l | tr -d ' '; }
fail_marker="$(mktemp)"
while IFS= read -r m; do
  while [ "$(job_slots)" -ge "$NCPU" ]; do sleep 0.05; done
  { compile_c "$m" || echo "$m" >> "$fail_marker"; } &
done < "$CLOSURE"
wait
if [ -s "$fail_marker" ]; then
  echo "FATAL: $(wc -l < "$fail_marker" | tr -d ' ') module(s) failed to compile:"; cat "$fail_marker"; rm -f "$fail_marker"; exit 1
fi
rm -f "$fail_marker"

obj_count=0
while IFS= read -r m; do
  [ -f "$OBJDIR/${m//./_}.o" ] || { echo "FATAL: no object for $m after a clean compile pass"; exit 1; }
  obj_count=$((obj_count + 1))
done < "$CLOSURE"
echo "==> $obj_count in-tree objects ready"

# ── 4 · repack: fresh in-tree slice + the carried dependency members ─────────────────────────
work="$(mktemp -d)"
cleanup() { rm -rf "$work"; rm -f "$CLOSURE"; }
trap cleanup EXIT
echo "==> Unpacking the current seed"
( cd "$work" && ar x "$ARCH" )
# Drop EVERY in-tree member, decided the same way as step 2 (a `.lean` exists for it under
# metatheory/), so a member whose module left the closure cannot survive as a fossil and the nine
# `Metatheory_*` + one `Polis_*` members cannot stay at 2026-07-25 because a `Dregg2_*` glob
# missed them.
INTREE_OBJ="$(mktemp)"
( cd "$META" && find . -name '*.lean' -not -path './.lake/*' -print ) \
  | sed 's|^\./||; s|\.lean$||; s|/|_|g; s|$|.o|' | sort -u > "$INTREE_OBJ"
before_intree=0
while IFS= read -r o; do
  if [ -f "$work/$o" ]; then rm -f "$work/$o"; before_intree=$((before_intree + 1)); fi
done < "$INTREE_OBJ"
rm -f "$INTREE_OBJ"
non_intree="$(find "$work" -maxdepth 1 -name '*.o' | wc -l | tr -d ' ')"
while IFS= read -r m; do cp -p "$OBJDIR/${m//./_}.o" "$work/"; done < "$CLOSURE"
echo "==> Repacking: $obj_count in-tree (was $before_intree) + $non_intree dependency objects"

rm -f "$ARCH.new"
# find/xargs, NOT a glob: ~3300 full paths blows ARG_MAX on Darwin.
# ⚑ `U` = NON-DETERMINISTIC: keep each member's real mtime. GNU binutils on Debian/Ubuntu is
# built `--enable-deterministic-archives`, so a bare `ar q` there zeroes every member timestamp;
# BSD `ar` on Darwin does not. That difference made the seed publish fail on the Linux runner and
# nowhere else: `check-lean-seed-member-freshness` refused the archive it had just built —
# "every member carries mtime 0 … an archive with no evidence must not read as fresh" — which is
# the RIGHT refusal. The archive's own age is the only evidence that gate has, and determinism
# strips exactly that. `U` is a GNU modifier and BSD `ar` rejects it, so probe rather than assume.
ar_mods=q
if printf '' > /tmp/.ar_probe_$$.o 2>/dev/null && ar qU /tmp/.ar_probe_$$.a /tmp/.ar_probe_$$.o >/dev/null 2>&1; then
  ar_mods=qU
fi
rm -f /tmp/.ar_probe_$$.o /tmp/.ar_probe_$$.a
echo "==> Packing with \`ar $ar_mods\` ($([ "$ar_mods" = qU ] && echo 'real mtimes preserved' || echo 'BSD ar: non-deterministic by default'))"
( cd "$work" && find . -maxdepth 1 -name '*.o' -print0 | sort -z | xargs -0 ar "$ar_mods" "$ARCH.new" >/dev/null 2>&1 )
ranlib "$ARCH.new"

# ── 4b · DEPENDENCY CLOSURE COMPLETION ───────────────────────────────────────────────────────
# Refreshing the in-tree slice ADDS edges: a module that re-enters the closure references
# dependency initializers the previous (short) seed never needed. The first run of the fixed script
# produced an archive with 5 dangling `initialize_*` where the old seed had 0 — three
# `Dregg2_Market_*` (fixed by the filesystem-decided in-tree set above) and two Mathlib objects
# that had never been members. Left there they are not a correctness bug — `build.rs`'s
# `complete_initializer_closure` resolves them on the first `cargo build` — but the seed's whole
# promise is that the first build adds ZERO, and `check-lean-seed-closure.sh` leg 3 is that promise.
# Same U−T computation and same symbol→`.c` resolution as build.rs, so the two cannot disagree.
converged=0
fail_marker="$(mktemp)"
for pass in 1 2 3 4 5 6 7 8; do
  RESOLVE="$(mktemp)"
  python3 - "$ARCH.new" "$META" > "$RESOLVE" <<'PY'
import json, os, subprocess, sys
arch, meta = sys.argv[1], sys.argv[2]

# Every IR root that supplies `.c` (mirrors build.rs::discover_ir_roots and seed-dregg2-closure.sh).
roots = []
p = os.path.join(meta, ".lake/build/ir")
if os.path.isdir(p):
    roots.append(p)
pkgs = os.path.join(meta, ".lake/packages")
if os.path.isdir(pkgs):
    for d in sorted(os.listdir(pkgs)):
        q = os.path.join(pkgs, d, ".lake/build/ir")
        if os.path.isdir(q):
            roots.append(q)
try:
    man = json.load(open(os.path.join(meta, "lake-manifest.json")))
    for pkg in man.get("packages", []):
        if pkg.get("dir"):
            q = os.path.join(meta, pkg["dir"], ".lake/build/ir")
            if os.path.isdir(q):
                roots.append(q)
except Exception:
    pass

index = {}
for r in roots:
    for dirpath, _dirs, files in os.walk(r):
        for fn in files:
            if fn.endswith(".c"):
                c = os.path.join(dirpath, fn)
                flat = os.path.relpath(c, r)[:-2].replace(os.sep, "_")
                index.setdefault(flat, c)

nm = "nm" if subprocess.run(["which", "nm"], capture_output=True).returncode == 0 else "llvm-nm"
text = subprocess.run([nm, arch], capture_output=True, text=True, errors="replace").stdout
TOOLCHAIN = ("Init", "Std", "Lean", "Lake")
defined, referenced = set(), set()
for line in text.splitlines():
    t = line.split()
    if len(t) == 2 and len(t[0]) == 1:
        ty, sym = t
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

# Same library-prefix strip as build.rs::resolve_initializer_cfile, longest prefix first.
LIBS = sorted(
    ["Dregg2", "Metatheory", "mathlib", "aesop", "batteries", "importGraph",
     "LeanSearchClient", "plausible", "proofwidgets", "Qq", "Cli"],
    key=len, reverse=True,
)
for sym in sorted(referenced - defined):
    rest = sym[len("initialize_"):]
    for lib in LIBS:
        if rest.startswith(lib + "_") and rest[len(lib) + 1:] in index:
            flat = rest[len(lib) + 1:]
            print(f"{flat}\t{index[flat]}")
            break
    else:
        print(f"UNRESOLVED\t{sym}")
PY
  if [ ! -s "$RESOLVE" ]; then rm -f "$RESOLVE"; converged=1; echo "==> Closure complete after $((pass - 1)) pass(es): 0 dangling initializers"; break; fi
  if grep -q '^UNRESOLVED' "$RESOLVE"; then
    echo "FATAL: dangling initializer(s) with no resolvable .c — the IR roots do not cover them:"
    grep '^UNRESOLVED' "$RESOLVE" | cut -f2 | sed 's/^/    /'
    rm -f "$RESOLVE"; exit 1
  fi
  n_dep="$(wc -l < "$RESOLVE" | tr -d ' ')"
  echo "==> Closure pass $pass: $n_dep dependency object(s) to add"
  while IFS=$'\t' read -r flat c; do
    while [ "$(job_slots)" -ge "$NCPU" ]; do sleep 0.05; done
    { (cd "$META" && lake env leanc -c -fPIC -I "$INC" "$c" -o "$work/$flat.o") || echo "$flat" >> "$fail_marker"; } &
  done < "$RESOLVE"
  wait
  if [ -s "$fail_marker" ]; then echo "FATAL: dependency compile failed:"; cat "$fail_marker"; exit 1; fi
  ( cd "$work" && cut -f1 "$RESOLVE" | sed 's/$/.o/' | tr '\n' '\0' | xargs -0 ar q "$ARCH.new" >/dev/null 2>&1 )
  ranlib "$ARCH.new"
  rm -f "$RESOLVE"
done
rm -f "$fail_marker"
if [ "$converged" -ne 1 ]; then
  echo "FATAL: the initializer closure did not converge in 8 passes — refusing to install a seed"
  echo "  whose first \`cargo build\` still has to resolve dangling edges. Candidate at $ARCH.new."
  exit 1
fi

# ── 5 · CHECK BEFORE INSTALL ─────────────────────────────────────────────────────────────────
# A re-splice that produces a stale or short seed used to succeed silently. Both gates run against
# the CANDIDATE; the seed on disk is untouched unless they pass.
echo
echo "==> Gate 1/2 · per-member freshness (scripts/check-lean-seed-member-freshness.py)"
if ! python3 "$ROOT/scripts/check-lean-seed-member-freshness.py" "$ARCH.new"; then
  echo "REFUSING TO INSTALL: the archive this script just built is still stale (report above)."
  echo "  The seed on disk is UNCHANGED. The candidate is at $ARCH.new for inspection."
  exit 1
fi
echo
echo "==> Gate 2/2 · boundary closure (scripts/check-lean-seed-closure.sh)"
if ! bash "$ROOT/scripts/check-lean-seed-closure.sh" "$ARCH.new"; then
  echo "REFUSING TO INSTALL: the archive this script just built is short of the boundary closure."
  echo "  The seed on disk is UNCHANGED. The candidate is at $ARCH.new for inspection."
  exit 1
fi

# ── 6 · install ──────────────────────────────────────────────────────────────────────────────
if [ "$KEEP_BACKUP" -eq 1 ]; then
  bak="${ARCH}.bak-$(date +%Y%m%d%H%M%S)"
  cp "$ARCH" "$bak"
fi
# `mv` on the same filesystem is atomic, so a concurrent `cargo build` copying the seed into its
# OUT_DIR sees the old file or the new one, never a torn one.
mv -f "$ARCH.new" "$ARCH"
# ⚠ The evidence sidecar binds a SHA256 to the archive it describes. This file is no longer that
# archive, and this script must NOT write a replacement: `fetch-lean-seed.sh` writes the record
# because it KNOWS the asset was published under a matching content key. Asserting the same thing
# here from the archive we just produced would be asserting the conclusion.
if [ -f "$ARCH.provenance" ]; then
  rm -f "$ARCH.provenance"
  echo "==> Removed the stale evidence sidecar (it described the previous archive). build.rs will"
  echo "    take the stricter 'I ran lake myself' path until a fetch writes a new one."
fi
if [ "$KEEP_BACKUP" -eq 1 ]; then echo "==> Backup kept: $bak"; fi
ls -la "$ARCH"
echo "==> RE-SPLICED. Both gates green against the installed seed."
