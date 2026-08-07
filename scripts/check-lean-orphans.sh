#!/usr/bin/env bash
# check-lean-orphans.sh — no metatheory/Dregg2 module escapes CI unnoticed.
#
# WHAT IT GUARDS
#   The `Dregg2` lean_lib in metatheory/lakefile.toml has NO `globs`, so `lake build`
#   compiles ONLY the modules transitively imported from metatheory/Dregg2.lean. A new
#   metatheory/Dregg2/**.lean that nothing imports builds green under `lake env lean
#   <file>`, passes its own #assert_all_clean / #assert_axioms / #guard checks — and is
#   compiled by NOTHING in the default build. Its checks never run in CI; a downstream
#   regression can silently break it and no gate goes red.
#
#   This hole RECURRED (StepBridge, AciNormal, AciComplete), caught each time only by a
#   human reviewer who then hand-registered the module. This gate makes the coverage
#   MECHANICAL: every Dregg2/**.lean must be reachable from a default lake target, or be
#   listed — with a reason — in scripts/lean-orphans-allow.txt.
#
# WHY AN ALLOWLIST, NOT A GLOB
#   Globbing the Dregg2 lib would pull the WHOLE subtree into the default build. As of
#   writing that is 136 orphan modules — many are intentional WIP (the Circuit.Emit
#   refinement rungs, FRI/STARK soundness drafts, PQ-crypto specs, game AIRs).
#
#   ⚑ CORRECTED 2026-07-24 (measured, not assumed). This header used to claim "and several
#   CARRY `sorry`". That is FALSE and was the stated reason not to glob. A comment-stripped
#   token scan (block `/- -/` and line `--` comments removed, so the many "no `sorry`" PROSE
#   mentions do not count) finds ZERO real `sorry` in the 123 allowlisted orphans AND ZERO in
#   all 1730 metatheory/Dregg2/**.lean files. The 16 files that grep for `sorry` match only
#   inside doc comments asserting they are sorry-FREE. Do not re-assert the sorry claim
#   without re-measuring; `grep sorry` over Lean sources is dominated by prose false hits.
#
#   The REAL reason not to glob is unchanged and is a BUILD-REDNESS reason, not a sorry
#   reason: ci.yml's "Orphan gate" step documents 28 dark Circuit.Emit/*{Refine,Rung2}
#   modules that are RED AT HEAD (a Type mismatch that induces `sorryAx` at ELABORATION —
#   which is NOT a source `sorry` token and is exactly why the textual scan above reads
#   clean). Globbing would turn the default build red on those.
#
#   The allowlist keeps those exclusions EXPLICIT and REASONED while still failing
#   loud the instant a NEW, unlisted orphan appears.
#
# ⚠ WHAT THIS GATE DOES *NOT* GUARANTEE (read before trusting a PASS)
#   Allowlisted == "the exclusion is deliberate", NOT "the module is checked somewhere".
#   Measured 2026-07-24: of 136 orphans, only 58 are actually built by ci.yml's
#   AXIOM_GUARD_TARGETS "Orphan gate"; 79 are compiled by NO CI target at all. See
#   docs/ORPHAN-TRIAGE-2026-07-24.md for the per-module triage. A green run of THIS gate
#   says nothing about those 79.
#
# REACHABILITY (pure source-text scan; no Lean toolchain, no build — like the sibling
# independence-controls gate)
#   Seeds = the default lake targets, READ OUT OF metatheory/lakefile.toml (`defaultTargets`
#   + the matching `lean_lib` stanzas), never a copy of them kept here. A globbed lib seeds
#   every module the glob matches; a root lib seeds its `roots` and the BFS pulls the closure.
#   ⚑ This was a hardcoded 5-target tuple until 2026-08-03 while the lakefile listed EIGHT —
#   see the block at the seeds themselves for why that direction of staleness is the scary one.
#   Reachable = the transitive closure of `import` lines over files that exist in-tree
#   (external imports like Mathlib.* are simply not in-tree and terminate a branch).
#
# NON-VACUITY (this is a gate about COVERAGE — it must never green by scanning nothing)
#   * zero Dregg2/**.lean files found            -> FAIL (the corpus moved / scan path broke)
#   * the reachable set comes back empty          -> FAIL (Dregg2.lean unreadable / parse dead)
#   * metatheory/Dregg2.lean missing              -> FAIL (the lib root is the anchor)
#   A gate that scans an empty set is the exact disease it exists to treat.
#
# ⚑ THE LISTING NAMES EVERY ORPHAN (fixed 2026-08-03 — it did not)
#   This gate USED to print `unlisted[:40]` and then "… and %d more (listing capped)". At 59 unlisted
#   orphans that meant #41–59 were COUNTED AND NEVER NAMED, with no flag, env var or second mode that
#   would name them: Dregg2.Circuit.Emit.TurnAuthLamportEmit and .TurnAuthCapOpenWeld — 1225 lines of
#   in-AIR authorization whose oleans were stale since Jul 30 — sat in that tail. A gate that reports
#   "59 orphans" and prints 40 hides 19 modules WHILE READING THOROUGH, which is this gate's own
#   disease pointed at itself.
#   Now: every unlisted orphan is printed. The LIST_CAP=200 that remains fires only on the
#   root-truncation blowout (~1199), and even then the gate prints how many it did not name and the
#   flag that names them (`--all`, or ORPHAN_LIST_ALL=1). A `⇒ NAMED n of N` line is printed ALWAYS,
#   so the named/counted gap is a number on the same screen as the verdict — never a subtraction the
#   reader has to think to perform.
#
# ROOT TRUNCATION (this gate DETECTS it; it cannot PREVENT it)
#   A truncated metatheory/Dregg2.lean moves this gate from 133 orphans to 1199 (measured), so it
#   goes hard red — but only AFTER the bad commit is history. On a mass orphaning the gate adds a
#   "SUSPECT ROOT TRUNCATION" hint pointing at the root, above the listing.
#   The PREVENTION is scripts/git-hooks/pre-commit's curated-list shrink guard, which refuses to let
#   metatheory/Dregg2.lean (and Market/Bfv/EmitByName) lose an entry without declared intent.
#
# ALLOWLIST STALENESS (the list cannot outlive the exclusion it records)
#   * a listed module that IS now reachable        -> FAIL (registered but not de-listed)
#   * a listed module whose file does not exist     -> FAIL (deleted/renamed; drop the entry)
#
# USAGE
#   bash scripts/check-lean-orphans.sh                  # scan metatheory/ (default)
#   bash scripts/check-lean-orphans.sh --all            # name every orphan, no cap at all
#   METATHEORY_DIR=/path bash scripts/check-lean-orphans.sh   # override the tree (testing)
#   ORPHAN_ALLOWLIST=/path bash scripts/check-lean-orphans.sh # override the allowlist (testing)
#
# EXIT STATUS
#   0  every Dregg2/**.lean is reachable or allowlisted, list is fresh, scan is non-vacuous
#   1  an unlisted orphan, OR a stale allowlist entry, OR a vacuous scan
#   2  the scan could not run at all (missing tree / missing Dregg2.lean root)
set -euo pipefail
export LC_ALL=C

# ── SCOPE ─ this printf is the ONLY copy; it prints on every run, pass or fail. ───────
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
  'is every metatheory/Dregg2/**.lean file ON DISK either reachable by an import-line BFS from the seeds metatheory/lakefile.toml declares as defaultTargets, or named in scripts/lean-orphans-allow.txt — and is every allowlist entry still a real, still-unreachable file under Dregg2/?' \
  'whether an allowlisted orphan is checked ANYWHERE. The list records only that the exclusion is deliberate: measured 2026-07-24, of 136 orphans just 58 were built by any CI target and 79 by none. Nor does reachability mean a module COMPILES, that its own guards ran, or that any CI job built it — this is a pure text scan of import lines, with no Lean toolchain in the loop.'

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mt_dir="${METATHEORY_DIR:-$repo_root/metatheory}"
allowlist="${ORPHAN_ALLOWLIST:-$repo_root/scripts/lean-orphans-allow.txt}"

if [ ! -d "$mt_dir" ]; then
  echo "check-lean-orphans: FATAL — metatheory dir is not a directory: $mt_dir" >&2
  exit 2
fi
if [ ! -f "$mt_dir/Dregg2.lean" ]; then
  echo "check-lean-orphans: FATAL — the lib root is missing: $mt_dir/Dregg2.lean" >&2
  echo "  (moved? then update this gate — the whole reachability anchor is that file.)" >&2
  exit 2
fi

# The graph BFS + diff is done in python3 (present on CI ubuntu-latest; a pure text scan,
# no Lean). It prints human diagnostics to stderr and sets the exit code; this wrapper
# exists so the gate is invoked and wired exactly like scripts/check-independence-controls.sh.
MT_DIR="$mt_dir" ALLOWLIST="$allowlist" python3 - "$@" <<'PYEOF'
import os, re, sys

mt_dir = os.environ["MT_DIR"]
allowlist_path = os.environ["ALLOWLIST"]

# ── LISTING POLICY ────────────────────────────────────────────────────────────────
# Every unlisted orphan is NAMED. The cap below exists only for the ROOT-TRUNCATION
# blowout (a cut Dregg2.lean takes this gate to ~1199 orphans, where a full listing is
# noise around the one line that matters) — and even then the gate prints the count it
# did NOT name and the exact flag that names them. It never stops silently.
LIST_CAP = 200
list_all = ("--all" in sys.argv[1:]) or os.environ.get("ORPHAN_LIST_ALL") == "1"
for _a in sys.argv[1:]:
    if _a not in ("--all",):
        sys.stderr.write("check-lean-orphans: unknown argument %r (only --all)\n" % _a)
        sys.exit(2)

imp_re = re.compile(r'^\s*import\s+([A-Za-z0-9_.]+)')

def mod_to_path(m):
    return os.path.join(mt_dir, m.replace('.', '/') + '.lean')

def path_to_mod(p):
    return os.path.relpath(p, mt_dir)[:-5].replace('/', '.')

def imports_of(path):
    out = []
    try:
        with open(path, encoding='utf-8', errors='replace') as f:
            for line in f:
                m = imp_re.match(line)
                if m:
                    out.append(m.group(1))
    except OSError:
        pass
    return out

def files_under(subdir):
    out = []
    base = os.path.join(mt_dir, subdir)
    if not os.path.isdir(base):
        return out
    for dp, dns, fns in os.walk(base):
        dns[:] = [d for d in dns if d not in ('.lake', '.git', 'build')]
        for fn in fns:
            if fn.endswith('.lean'):
                out.append(path_to_mod(os.path.join(dp, fn)))
    return out

def reach(seeds):
    seen = set()
    stack = list(seeds)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        p = mod_to_path(m)
        if not os.path.isfile(p):   # external (Mathlib.*, Std.*, Init.*) — terminates the branch
            continue
        seen.add(m)
        for im in imports_of(p):
            if im not in seen:
                stack.append(im)
    return seen

# --- default lake targets = reachability seeds -----------------------------
# ⚑ READ FROM THE LAKEFILE, NOT A HARDCODED TUPLE (fixed 2026-08-03).
# This block used to hardcode `("Metatheory", "Polis")` globbed + `("Dregg2", "Market", "Bfv")`
# rooted. metatheory/lakefile.toml's defaultTargets are EIGHT:
#   Dregg2, Metatheory, Polis, Market, Bfv, PicklesSynthesis, MinaBridgeGuards, CommitBindsGuards
# — and the last three exist FOR EXACTLY THIS GATE'S REASON. Each is a lean_lib+defaultTarget added
# by a lane to ROOT a cone of guard-carrying orphans "WITHOUT touching the Dregg2.lean import block
# (swept by sibling lanes)". The gate that measures orphaning could not see any of the three fixes,
# so it went on reporting rooted modules as orphans — and the reverse is the dangerous direction: a
# target DELETED from the lakefile would have left this tuple asserting rootedness that no longer
# existed, a false GREEN. A gate must not carry its own copy of the build's target list.
#
# Lake's lib semantics, mirrored (same as scripts/check-guard-modules.py's lakefile_seeds):
#   globbed lib  "Foo.+" -> Foo and all descendants; "Foo.*" -> descendants only;
#                plain "Foo" -> just Foo.
#   root lib     no globs -> the lib's `roots` (default [name]); BFS pulls the import closure.
#   a defaultTarget with no lean_lib (an exe) -> its own root module is a seed.
try:
    import tomllib
except ModuleNotFoundError:  # python < 3.11
    sys.stderr.write("check-lean-orphans: FATAL — python3.11+ (tomllib) is required to read\n"
                     "  metatheory/lakefile.toml. Refusing to fall back to a hardcoded target\n"
                     "  list: a stale copy of the build's targets is what this gate now exists\n"
                     "  to not have.\n")
    sys.exit(2)

lakefile_path = os.path.join(mt_dir, "lakefile.toml")
try:
    with open(lakefile_path, "rb") as f:
        lakedoc = tomllib.load(f)
except (OSError, ValueError) as e:
    sys.stderr.write("check-lean-orphans: FATAL — cannot read %s (%s).\n"
                     "  The default-target list is the whole reachability anchor.\n"
                     % (lakefile_path, e))
    sys.exit(2)

default_targets = list(lakedoc.get("defaultTargets", []))
lean_libs = {l.get("name"): l for l in lakedoc.get("lean_lib", []) if l.get("name")}
if not default_targets:
    sys.stderr.write("check-lean-orphans: FATAL — lakefile.toml declares NO defaultTargets.\n"
                     "  Every Dregg2 module would read 'orphan'; that is a broken scan, not a finding.\n")
    sys.exit(2)

all_mods = set(files_under(""))   # every in-tree .lean module (os.walk from mt_dir; .lake pruned)
seeds = set()
for t in default_targets:
    lib = lean_libs.get(t)
    if lib is None:              # a defaultTarget with no lean_lib (e.g. a lean_exe)
        seeds.add(t)
        continue
    globs = lib.get("globs")
    if globs:
        for g in globs:
            if g.endswith(".+"):
                pre = g[:-2]
                seeds |= {m for m in all_mods if m == pre or m.startswith(pre + ".")}
            elif g.endswith(".*"):
                pre = g[:-2]
                seeds |= {m for m in all_mods if m.startswith(pre + ".")}
            elif g in all_mods:
                seeds.add(g)
    else:
        roots = lib.get("roots", [t])
        if isinstance(roots, str):
            roots = [roots]
        seeds |= set(roots)

reachable = reach(seeds)
dregg2_files = sorted(files_under("Dregg2"))

# --- NON-VACUITY floors ----------------------------------------------------
if len(dregg2_files) == 0:
    sys.stderr.write(
        "check-lean-orphans: FAIL — ZERO metatheory/Dregg2/**.lean files found.\n"
        "  This is NOT a clean tree; it is a scan that found NOTHING to cover. The corpus\n"
        "  MOVED, the scan path broke, or Dregg2/ was emptied. A coverage gate that scans an\n"
        "  empty set would green forever while guarding nothing — the exact blindness it exists\n"
        "  to prevent. If Dregg2/ was genuinely retired, DELETE this gate in the same change.\n")
    sys.exit(1)

# reachable must contain at least Dregg2.lean's own closure; an empty reachable set means the
# root parse died (unreadable file, import regex broke) — treat as a broken scan, never a pass.
dregg2_reachable = [m for m in dregg2_files if m in reachable]
if len(dregg2_reachable) == 0:
    sys.stderr.write(
        "check-lean-orphans: FAIL — the reachable set is EMPTY: not one Dregg2 module is\n"
        "  reachable from the default lake targets. Dregg2.lean is unreadable, or import\n"
        "  parsing is broken. Every module would be reported 'orphan' — a scan this blind is a\n"
        "  broken gate, not a finding.\n")
    sys.exit(1)

# --- load the allowlist ----------------------------------------------------
allow = {}          # module -> raw line (for messages)
allow_order = []
if os.path.isfile(allowlist_path):
    with open(allowlist_path, encoding='utf-8', errors='replace') as f:
        for raw in f:
            line = raw.rstrip('\n')
            s = line.strip()
            if not s or s.startswith('#'):
                continue
            mod = s.split('#', 1)[0].strip()
            if not mod:
                continue
            if mod not in allow:
                allow[mod] = line
                allow_order.append(mod)
else:
    sys.stderr.write(
        "check-lean-orphans: FAIL — allowlist not found: %s\n"
        "  Every deliberate orphan must be recorded (with a reason) in this file. If there are\n"
        "  genuinely zero deliberate orphans, create it empty — do not let a missing file read\n"
        "  as 'nothing excluded'.\n" % allowlist_path)
    sys.exit(1)

reachable_set = set(reachable)
dregg2_set = set(dregg2_files)

# --- the orphans -----------------------------------------------------------
orphans = [m for m in dregg2_files if m not in reachable_set]
unlisted = [m for m in orphans if m not in allow]
allowed_orphans = [m for m in orphans if m in allow]

# --- STALENESS: a listed module that is reachable, or does not exist --------
stale_registered = [m for m in allow_order if m in reachable_set]
stale_missing = [m for m in allow_order
                 if not os.path.isfile(mod_to_path(m)) and m not in reachable_set]
# entries that name a path outside Dregg2/ are also meaningless here
stale_outside = [m for m in allow_order
                 if os.path.isfile(mod_to_path(m)) and m not in dregg2_set]

sys.stdout.write(
    "check-lean-orphans: %d Dregg2/**.lean files; %d reachable, %d orphan "
    "(%d allowlisted, %d UNLISTED); %d allowlist entries\n"
    % (len(dregg2_files), len(dregg2_reachable), len(orphans),
       len(allowed_orphans), len(unlisted), len(allow_order)))

fail = False

if unlisted:
    fail = True
    sys.stderr.write(
        "\ncheck-lean-orphans: FAIL — %d Dregg2 module(s) are reachable from NOTHING and are\n"
        "  not in the allowlist (they build under `lake env lean` but run in NO CI target):\n"
        % len(unlisted))
    shown = unlisted if list_all else unlisted[:LIST_CAP]
    for m in shown:
        sys.stderr.write("    ORPHAN  %s\n" % m)
    if len(shown) < len(unlisted):
        sys.stderr.write(
            "    … and %d more NOT NAMED ABOVE — rerun with `--all` to name every one:\n"
            "        bash scripts/check-lean-orphans.sh --all\n"
            % (len(unlisted) - len(shown)))
    # ⚑ NAMEABILITY LINE — printed ALWAYS, capped or not. A gate that reports a COUNT it
    # does not print NAMES for hides modules while reading thorough; this line makes the
    # gap a number on the same screen as the verdict rather than something a reader has to
    # notice by subtracting. (2026-08-03: the cap was 40 against 59 unlisted, so
    # TurnAuthLamportEmit / TurnAuthCapOpenWeld sat at #41–59 and were never named — a live
    # blind spot in a gate whose entire job is naming what nothing compiles.)
    sys.stderr.write(
        "    ⇒ NAMED %d of %d unlisted orphan(s)%s\n"
        % (len(shown), len(unlisted),
           "" if len(shown) == len(unlisted) else "  ⚠ %d UNNAMED" % (len(unlisted) - len(shown))))

    # ROOT-TRUNCATION HYPOTHESIS — read this BEFORE registering or allowlisting anything.
    # A mass orphaning is almost never "many new unregistered modules"; it is ONE truncated root.
    # Twice on 2026-07-25 a window-edit cut metatheory/Dregg2.lean down to a ~240-line prefix
    # (6b1e156bdf: 1290 → 231 imports; 8a28420ec9: 1301 → 217), and this gate's own numbers move
    # 133 orphans → 1199 under that cut (measured). Steady state is ~130 TOTAL orphans, so a few
    # hundred UNLISTED means the ROOT lost imports, not that the corpus grew.
    # This is a HINT: it can neither pass nor fail the gate, so the threshold cannot rot into a
    # wrong verdict. PREVENTION lives in scripts/git-hooks/pre-commit (curated-list shrink guard),
    # which refuses the commit that does this in the first place.
    if len(unlisted) > 200:
        root_imports = len(imports_of(os.path.join(mt_dir, "Dregg2.lean")))
        sys.stderr.write(
            "\n  ⚑ SUSPECT ROOT TRUNCATION rather than %d genuinely new orphans.\n"
            "    metatheory/Dregg2.lean currently lists %d imports. Check the ROOT first:\n"
            "      git diff HEAD -- metatheory/Dregg2.lean | head -40\n"
            "      git log --stat -3 -- metatheory/Dregg2.lean     # look for `1 insertion, NNNN deletions`\n"
            "    A CLEAN POSITIONAL SUFFIX CUT — lines 1..N byte-identical, everything past N gone,\n"
            "    one import appended — is a read-window/append/write-back edit, not a real change.\n"
            "    RESTORE the root; do NOT allowlist the fallout.\n"
            % (len(unlisted), root_imports))

    sys.stderr.write(
        "\n  FIX one of:\n"
        "    (a) register it — add `import %s` to metatheory/Dregg2.lean (or an aggregator\n"
        "        already imported from there) so `lake build` compiles it; OR\n"
        "    (b) if it is intentional WIP, add it to scripts/lean-orphans-allow.txt WITH a\n"
        "        one-line reason. An allowlisted module's own checks still do not run in CI —\n"
        "        the allowlist only records that the exclusion is deliberate.\n"
        % unlisted[0])

if stale_registered:
    fail = True
    sys.stderr.write(
        "\ncheck-lean-orphans: FAIL — %d allowlist entr(y/ies) name a module that is NOW\n"
        "  reachable (it got registered but was never de-listed). Remove it from\n"
        "  scripts/lean-orphans-allow.txt — a stale allowlist hides the next real orphan:\n"
        % len(stale_registered))
    for m in stale_registered:
        sys.stderr.write("    STALE (now-reachable)  %s\n" % m)

if stale_missing:
    fail = True
    sys.stderr.write(
        "\ncheck-lean-orphans: FAIL — %d allowlist entr(y/ies) name a file that does not exist\n"
        "  (deleted or renamed). Drop the entry from scripts/lean-orphans-allow.txt:\n"
        % len(stale_missing))
    for m in stale_missing:
        sys.stderr.write("    STALE (no such file)  %s\n" % m)

if stale_outside:
    fail = True
    sys.stderr.write(
        "\ncheck-lean-orphans: FAIL — %d allowlist entr(y/ies) name a module outside\n"
        "  metatheory/Dregg2/ — this gate only governs the Dregg2 subtree:\n"
        % len(stale_outside))
    for m in stale_outside:
        sys.stderr.write("    STALE (outside Dregg2/)  %s\n" % m)

if fail:
    sys.exit(1)

sys.stdout.write(
    "check-lean-orphans: PASS — every Dregg2/**.lean is reachable or deliberately "
    "allowlisted; %d allowlist entr(y/ies) all fresh.\n" % len(allow_order))
sys.exit(0)
PYEOF
