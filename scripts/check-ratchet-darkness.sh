#!/usr/bin/env bash
# check-ratchet-darkness.sh — nothing carrying refuted-floor content is INVISIBLE to the
# accrual gate, and no module lake builds sits outside the gate's environment unrecorded.
#
# ═══ THE HOLE THIS CLOSES (B5) ═══════════════════════════════════════════════════════════
#   `#floor_ratchet` and `#teeth_wired` are Lean commands invoked at the END of
#   `metatheory/Dregg2.lean`. They read `Environment` / `Environment.header.moduleNames` —
#   which is EXACTLY the transitive import closure of that one root, and nothing else.
#
#   `metatheory/lakefile.toml` has FIVE default targets, and only one of them is that root:
#
#       [[lean_lib]] Dregg2       — root module, no globs   ← the ratchet's whole world
#       [[lean_lib]] Metatheory   globs = ["Metatheory.+"]   ← every file is its own target
#       [[lean_lib]] Polis        globs = ["Polis.+"]        ← every file is its own target
#       [[lean_lib]] Market       — root module
#       [[lean_lib]] Bfv          — root module
#
#   A declaration under a GLOBBED lib therefore compiles in the default build, runs its own
#   `#assert_axioms`, is green in CI — and is NOT IN THE RATCHET'S ENVIRONMENT. It can take a
#   hypothesis this tree PROVES FALSE at deployed BabyBear parameters and no gate says so. The
#   same is true of any module reachable from `Market`/`Bfv` but not from `Dregg2`, and of every
#   allowlisted `Dregg2/**` orphan.
#
#   MEASURED at the commit that added this gate (clean `git archive` export of HEAD):
#     2029 in-tree .lean · 1828 in the Dregg2-root closure · 201 DARK · 75 of those still BUILT
#     by lake (65 `Polis.*`, 9 `Metatheory.*`, the `Bfv` root).
#   Nine dark modules MENTIONED a refuted floor in code (comments stripped), 101 mentions:
#     Metatheory.Adversary.Instances 41 · Circuit.FinInjectivityCollapse 13 ·
#     Circuit.FinBindsKernel 11 · Circuit.KernelConfigSoundness 10 ·
#     Circuit.KernelConfigSoundnessAvail 10 · Circuit.Emit.MembershipDepthGeneralRung2 7 ·
#     Metatheory.Adversary.Schema 5 · Metatheory.Adversary.Model 3 · the canary 1.
#
#   This is not hypothetical accounting. The ratchet's own baseline carries a `manual +56`
#   raise that IS this bypass running in reverse: rooting six dark modules surfaced 56
#   already-vacuous theorems that had been hiding from every instrument.
#
# ═══ THE TWO RULES ═══════════════════════════════════════════════════════════════════════
#   RULE 1 — DARK CARRIER (the one that matters).
#     A module that is dark to the Dregg2 root closure and MENTIONS A REFUTED FLOOR in code is
#     a FAILURE. Root it into `metatheory/Dregg2.lean` so the ratchet can see it. Exempting one
#     requires an allowlist line carrying the literal token `FLOOR-EXEMPT:` plus a reason — a
#     deliberately loud, greppable spelling, because "it is scratch" is not a reason to hide
#     floor-carrying content from the gate built to find it.
#
#   RULE 2 — DARK BUILD.
#     A module lake BUILDS that is not in the root closure must be recorded in the allowlist
#     with a reason. Rooting the whole `Polis.+` tree into `Dregg2.lean` would put it on the
#     root's critical path for no proof reason; what is NOT acceptable is that surface growing
#     silently. A NEW built-but-dark module reds this gate and forces a decision.
#
# ═══ THE FLOOR LIST IS NOT WRITTEN HERE ══════════════════════════════════════════════════
#   A hand list in a shell gate is how `scripts/binding_surface_complete.py` went blind to 7 of
#   10 refuted floors. The names are PARSED out of `Dregg2/Verify/FloorCensus.lean`'s
#   `sentinelFloors` — the census's own fail-closed sentinel set, which `#floor_census` and
#   `#floor_ratchet` both refuse to run without rediscovering as refuted. One list, one place.
#
#   ⚠ IT IS AN UNDERCOUNT, ON PURPOSE, AND SAYS SO. The ratchet DERIVES 27 refuted floors from
#   the environment; the sentinels are 17 of them. A text scan cannot derive the other ten
#   (derivation needs elaborated terms), so this gate under-reports and NEVER over-reports the
#   floor set. It is a coverage tripwire, not a census. `#floor_ratchet_floors` is the census.
#
#   Matching is on the floor's LAST NAME COMPONENT (`Poseidon2SpongeCR`), which is how a binder
#   spells it in source. That can over-match an unrelated constant of the same name — and that
#   asymmetry is deliberate: the remedy for a match is "root the module", which is the direction
#   this campaign wants anyway, whereas a missed match is a floor hiding in the dark.
#
#   Comments are STRIPPED before matching (Lean's NESTING `/- -/` and line `--`), because this
#   tree's prose is full of floor names — the whole point of `scripts/check-lean-orphans.sh`'s
#   corrected header is that a naive grep over Lean sources is dominated by prose false hits.
#
# ═══ NON-VACUITY (a coverage gate must never green by scanning nothing) ══════════════════
#   * zero .lean files found                     -> FAIL
#   * the root closure comes back empty/tiny     -> FAIL (root truncated / parse dead)
#   * fewer than 15 sentinel floors parsed, or   -> FAIL (the census moved; a 0-name floor list
#     `Poseidon2SpongeCR` not among them            would pass every module in the tree)
#   * an allowlist entry that is no longer dark  -> FAIL (stale: it got rooted, de-list it)
#   * an allowlist entry with no such file       -> FAIL (stale: deleted/renamed)
#   * a `FLOOR-EXEMPT:` entry that no longer     -> FAIL (the exemption outlived its subject)
#     mentions a floor
#
# USAGE
#   bash scripts/check-ratchet-darkness.sh                        # scan metatheory/ (default)
#   bash scripts/check-ratchet-darkness.sh --list                 # print the dark set, no verdict
#   METATHEORY_DIR=/path  bash scripts/check-ratchet-darkness.sh  # override tree (testing)
#   RATCHET_DARK_ALLOWLIST=/path bash …                           # override allowlist (testing)
#
# EXIT STATUS
#   0  no unrecorded dark module, no dark floor carrier, allowlist fresh, scan non-vacuous
#   1  a violation, a stale allowlist entry, or a vacuous scan
#   2  the scan could not run at all (missing tree / missing root / missing census)
set -euo pipefail
export LC_ALL=C

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mt_dir="${METATHEORY_DIR:-$repo_root/metatheory}"
allowlist="${RATCHET_DARK_ALLOWLIST:-$repo_root/scripts/lean-ratchet-dark-allow.txt}"

if [ ! -d "$mt_dir" ]; then
  echo "check-ratchet-darkness: FATAL — metatheory dir is not a directory: $mt_dir" >&2
  exit 2
fi
if [ ! -f "$mt_dir/Dregg2.lean" ]; then
  echo "check-ratchet-darkness: FATAL — the ratchet's root is missing: $mt_dir/Dregg2.lean" >&2
  exit 2
fi
if [ ! -f "$mt_dir/Dregg2/Verify/FloorCensus.lean" ]; then
  echo "check-ratchet-darkness: FATAL — the floor-name source is missing:" >&2
  echo "  $mt_dir/Dregg2/Verify/FloorCensus.lean (this gate parses its \`sentinelFloors\`)." >&2
  echo "  If the census moved, point this gate at the new location — do NOT hand-write a" >&2
  echo "  floor list here; that is exactly how the Python ruler went blind." >&2
  exit 2
fi

MT_DIR="$mt_dir" ALLOWLIST="$allowlist" python3 - "$@" <<'PYEOF'
import os, re, sys

mt_dir = os.environ["MT_DIR"]
allowlist_path = os.environ["ALLOWLIST"]
list_only = "--list" in sys.argv[1:]

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

def walk_mods(base):
    out = []
    if not os.path.isdir(base):
        return out
    for dp, dns, fns in os.walk(base):
        dns[:] = [d for d in dns if d not in ('.lake', '.git', 'build')]
        for fn in fns:
            if fn.endswith('.lean'):
                out.append(path_to_mod(os.path.join(dp, fn)))
    return out

def reach(seeds):
    seen, stack = set(), list(seeds)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        p = mod_to_path(m)
        if not os.path.isfile(p):     # Mathlib.* / Std.* / Init.* terminate the branch
            continue
        seen.add(m)
        for im in imports_of(p):
            if im not in seen:
                stack.append(im)
    return seen

# ── the floor names, PARSED from the census's own sentinel list ──────────────────────────
census = os.path.join(mt_dir, "Dregg2/Verify/FloorCensus.lean")
src = open(census, encoding='utf-8', errors='replace').read()
m = re.search(r'def\s+sentinelFloors\s*:.*?:=\s*\[(.*?)\n\s*\]', src, re.S)
sentinels = []
if m:
    sentinels = re.findall(r'`([A-Za-z0-9_.]+)\s*,\s*(?:true|false)\s*\)', m.group(1))
shorts = sorted({s.rsplit('.', 1)[-1] for s in sentinels})

if len(shorts) < 15 or "Poseidon2SpongeCR" not in shorts:
    sys.stderr.write(
        "check-ratchet-darkness: FAIL — parsed only %d floor name(s) from FloorCensus's\n"
        "  `sentinelFloors` (need >= 15, and Poseidon2SpongeCR among them). The census's shape\n"
        "  changed and this gate is now scanning for almost nothing — which passes every module\n"
        "  in the tree and looks exactly like coverage. Fix the parse; do not hand-write the list.\n"
        "  parsed: %s\n" % (len(shorts), ", ".join(shorts) or "(none)"))
    sys.exit(1)

# ── the floor BUNDLES too (B3, 2026-07-25) ───────────────────────────────────────────────
# A refuted floor also reaches a module through a STRUCTURE whose FIELD is typed at one: no
# inhabitant of `CommitSurface` exists at deployed BabyBear parameters, so `∀ S : CommitSurface, …`
# is exactly as vacuous as a floor binder while mentioning no floor NAME. Scanning only for floor
# names is the same blindness `#floor_ratchet` itself had until its fixpoint learned to propagate
# through fields — a textual ruler must not be the last place that hole survives.
#
# Parsed from `FloorRatchet.sentinelBundles`, the same way the floors are parsed from the census,
# and fail-closed the same way: a shape change that silently drops the list would narrow this scan
# without narrowing what it claims to cover.
#
# ⚑ THE PRECONDITION IS EXPLICIT, AND IT IS NOT A SOFTENING. `sentinelBundles` is part of the
# ratchet's B3 (bundle) detector, which is a SEPARATE lane's work and is not in `FloorRatchet.lean`
# at the commit that ships this gate. A gate must not hard-fail on a symbol its own tree does not
# contain — that is a red for a scheduling reason, which teaches people to ignore the gate. So the
# rule is keyed on whether the ratchet HAS a bundle sentinel list at all:
#   * token absent  -> the bundle class does not exist in this tree's ratchet yet. Scan floor names
#                      only and SAY SO on stdout, every run, so the narrower coverage is never
#                      silent. This branch deletes itself the moment the B3 lane lands.
#   * token present -> parse it and FAIL-CLOSED exactly as the floor list does (>= 3 names,
#                      `CommitSurface` among them). A shape change that silently emptied the list
#                      would narrow this scan without narrowing what it claims to cover.
ratchet = os.path.join(mt_dir, "Dregg2/Verify/FloorRatchet.lean")
rsrc = open(ratchet, encoding='utf-8', errors='replace').read()
has_bundle_sentinels = 'sentinelBundles' in rsrc
bm = re.search(r'def\s+sentinelBundles\s*:.*?:=\s*\[(.*?)\]', rsrc, re.S)
bundle_names = re.findall(r'`([A-Za-z0-9_.]+)', bm.group(1)) if bm else []
bundle_shorts = sorted({s.rsplit('.', 1)[-1] for s in bundle_names})

if has_bundle_sentinels and (len(bundle_shorts) < 3 or "CommitSurface" not in bundle_shorts):
    sys.stderr.write(
        "check-ratchet-darkness: FAIL — `FloorRatchet.lean` names `sentinelBundles`, but only %d\n"
        "  floor-BUNDLE name(s) parsed out of it (need >= 3, and CommitSurface among them). The\n"
        "  bundle class is how a refuted floor reaches a declaration with no floor NAME anywhere in\n"
        "  its type; a scan blind to it passes the modules most worth catching. Fix the parse.\n"
        "  parsed: %s\n" % (len(bundle_shorts), ", ".join(bundle_shorts) or "(none)"))
    sys.exit(1)
if not has_bundle_sentinels:
    print("check-ratchet-darkness: NOTE — `FloorRatchet.lean` has no `sentinelBundles`, so this run "
          "scans FLOOR NAMES ONLY. A dark module carrying a refuted floor through a STRUCTURE FIELD "
          "(the B3 bundle class — `∀ S : CommitSurface, …` is as vacuous as a floor binder and "
          "mentions no floor name) is NOT covered here. Coverage widens automatically when the "
          "bundle detector lands.")

FLOOR_RE = re.compile(
    r'\b(' + '|'.join(re.escape(s) for s in (shorts + bundle_shorts)) + r')\b')

def strip_comments(text):
    """Lean comments: NESTING `/- … -/` plus line `--`. A non-greedy regex gets nesting
    wrong and leaves prose behind as 'code', which would make this gate fire spuriously."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith('/-', i):
            depth, i = 1, i + 2
        elif depth > 0:
            if text.startswith('/-', i):
                depth, i = depth + 1, i + 2
            elif text.startswith('-/', i):
                depth, i = depth - 1, i + 2
            else:
                i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)

def floor_hits(mod):
    try:
        text = open(mod_to_path(mod), encoding='utf-8', errors='replace').read()
    except OSError:
        return []
    return FLOOR_RE.findall(strip_comments(text))

# ── the three sets ───────────────────────────────────────────────────────────────────────
all_mods = set(walk_mods(mt_dir))
root_env = reach(['Dregg2'])                       # what #floor_ratchet actually sees
built = set(walk_mods(os.path.join(mt_dir, 'Metatheory')))       # globbed lib
built |= set(walk_mods(os.path.join(mt_dir, 'Polis')))           # globbed lib
built |= reach(['Dregg2', 'Market', 'Bfv'])                      # root-module libs
built &= all_mods

if not all_mods:
    sys.stderr.write("check-ratchet-darkness: FAIL — ZERO .lean files under %s. The corpus\n"
                     "  moved or the scan path broke; a gate that scans nothing is the disease.\n"
                     % mt_dir)
    sys.exit(1)
if len(root_env) < 500:
    sys.stderr.write(
        "check-ratchet-darkness: FAIL — the Dregg2 root closure is only %d module(s) (steady\n"
        "  state is ~1800). SUSPECT ROOT TRUNCATION: metatheory/Dregg2.lean has been silently cut\n"
        "  twice before (6b1e156bdf 1290->231 imports, 8a28420ec9 1301->217). Under a cut, almost\n"
        "  the whole tree reads DARK and this gate would print a thousand violations for one bad\n"
        "  edit. Check the ROOT first:  git diff HEAD -- metatheory/Dregg2.lean\n" % len(root_env))
    sys.exit(1)

dark = sorted(all_mods - root_env)
dark_built = sorted(built - root_env)
dark_carriers = {m: floor_hits(m) for m in dark}
dark_carriers = {m: h for m, h in dark_carriers.items() if h}

if list_only:
    print("DARK to the Dregg2 root closure: %d of %d (%d still BUILT by lake)"
          % (len(dark), len(all_mods), len(dark_built)))
    for m in sorted(dark_carriers, key=lambda k: -len(dark_carriers[k])):
        print("  CARRIER %4d  %s" % (len(dark_carriers[m]), m))
    for m in dark_built:
        print("  BUILT-DARK    %s" % m)
    sys.exit(0)

# ── the allowlist ────────────────────────────────────────────────────────────────────────
allow, allow_order, exempt = {}, [], set()
if os.path.isfile(allowlist_path):
    with open(allowlist_path, encoding='utf-8', errors='replace') as f:
        for raw in f:
            s = raw.strip()
            if not s or s.startswith('#'):
                continue
            mod = s.split('#', 1)[0].strip()
            if not mod:
                continue
            if mod not in allow:
                allow[mod] = raw.rstrip('\n')
                allow_order.append(mod)
            if 'FLOOR-EXEMPT:' in raw:
                exempt.add(mod)
else:
    sys.stderr.write(
        "check-ratchet-darkness: FAIL — allowlist not found: %s\n"
        "  Every module that lake builds outside the ratchet's environment must be recorded\n"
        "  there with a reason. If there are genuinely none, create it empty — a missing file\n"
        "  must never read as 'nothing is dark'.\n" % allowlist_path)
    sys.exit(1)

print("check-ratchet-darkness: %d .lean; %d in the Dregg2-root closure; %d DARK "
      "(%d still BUILT by lake); %d dark floor carrier(s); %d allowlist entr(y/ies), "
      "%d floor-exempt; %d sentinel floor names parsed from FloorCensus"
      % (len(all_mods), len(root_env), len(dark), len(dark_built),
         len(dark_carriers), len(allow_order), len(exempt), len(shorts)))

fail = False

# RULE 1 — a dark module that mentions a refuted floor
bad_carriers = [m for m in sorted(dark_carriers) if m not in exempt]
if bad_carriers:
    fail = True
    sys.stderr.write(
        "\ncheck-ratchet-darkness: FAIL — %d module(s) MENTION A REFUTED FLOOR and are DARK to\n"
        "  `#floor_ratchet`. A hypothesis this tree proves FALSE at deployed BabyBear parameters\n"
        "  makes every theorem assuming it VACUOUS; out here, nothing counts them and nothing\n"
        "  stops more from landing:\n" % len(bad_carriers))
    for m in bad_carriers[:40]:
        hits = dark_carriers[m]
        top = sorted({h: hits.count(h) for h in set(hits)}.items(), key=lambda kv: -kv[1])[:4]
        sys.stderr.write("    DARK CARRIER  %-58s %3d mention(s)  [%s]\n"
                         % (m, len(hits), ", ".join("%sx%d" % kv for kv in top)))
    if len(bad_carriers) > 40:
        sys.stderr.write("    … and %d more (listing capped)\n" % (len(bad_carriers) - 40))
    sys.stderr.write(
        "\n  FIX: add `import %s` to metatheory/Dregg2.lean. Expect the ratchet baseline to\n"
        "  RISE — that rise is previously-hidden vacuity becoming COUNTABLE, which is the win.\n"
        "  Exempting instead requires an allowlist line containing `FLOOR-EXEMPT:` and a reason\n"
        "  that survives review; the spelling is loud so the exceptions stay greppable.\n"
        % bad_carriers[0])

# RULE 2 — a module lake builds that the ratchet cannot see
unlisted_built = [m for m in dark_built if m not in allow]
if unlisted_built:
    fail = True
    sys.stderr.write(
        "\ncheck-ratchet-darkness: FAIL — %d module(s) are BUILT by lake but are OUTSIDE the\n"
        "  environment `#floor_ratchet` / `#teeth_wired` read, and are not recorded:\n"
        % len(unlisted_built))
    for m in unlisted_built[:40]:
        sys.stderr.write("    BUILT-BUT-DARK  %s\n" % m)
    if len(unlisted_built) > 40:
        sys.stderr.write("    … and %d more (listing capped)\n" % (len(unlisted_built) - 40))
    sys.stderr.write(
        "\n  FIX one of:\n"
        "    (a) root it — add `import %s` to metatheory/Dregg2.lean, so the accrual gate sees\n"
        "        its declarations; OR\n"
        "    (b) record it in scripts/lean-ratchet-dark-allow.txt WITH a reason. That records the\n"
        "        exclusion; it does NOT make the module's declarations counted by any instrument.\n"
        % unlisted_built[0])

# staleness — an allowlist cannot outlive the exclusion it records
stale_rooted = [m for m in allow_order if m in root_env]
stale_missing = [m for m in allow_order if not os.path.isfile(mod_to_path(m))]
stale_exempt = [m for m in allow_order if m in exempt and m not in dark_carriers
                and os.path.isfile(mod_to_path(m))]
_dark_built_set = set(dark_built)
stale_pointless = [m for m in allow_order
                   if m not in _dark_built_set and m not in exempt and m not in root_env
                   and os.path.isfile(mod_to_path(m))]

if stale_rooted:
    fail = True
    sys.stderr.write(
        "\ncheck-ratchet-darkness: FAIL — %d allowlist entr(y/ies) name a module that is NOW in\n"
        "  the Dregg2 root closure (it got rooted and was never de-listed). Remove it — a stale\n"
        "  allowlist hides the next real dark module:\n" % len(stale_rooted))
    for m in stale_rooted:
        sys.stderr.write("    STALE (now rooted)  %s\n" % m)

if stale_missing:
    fail = True
    sys.stderr.write(
        "\ncheck-ratchet-darkness: FAIL — %d allowlist entr(y/ies) name a file that does not\n"
        "  exist (deleted or renamed). Drop the entry:\n" % len(stale_missing))
    for m in stale_missing:
        sys.stderr.write("    STALE (no such file)  %s\n" % m)

if stale_exempt:
    fail = True
    sys.stderr.write(
        "\ncheck-ratchet-darkness: FAIL — %d `FLOOR-EXEMPT:` entr(y/ies) name a module that no\n"
        "  longer mentions any refuted floor. The exemption has outlived its subject; drop the\n"
        "  token (keep the plain entry if the module is still built-but-dark). An exemption\n"
        "  nobody re-reads is how the next real carrier gets waved through:\n" % len(stale_exempt))
    for m in stale_exempt:
        sys.stderr.write("    STALE (exempt, no floor mention)  %s\n" % m)

if stale_pointless:
    fail = True
    sys.stderr.write(
        "\ncheck-ratchet-darkness: FAIL — %d allowlist entr(y/ies) record NOTHING: the module is\n"
        "  not built by lake and does not mention a refuted floor, so neither rule was ever going\n"
        "  to name it. An entry that excuses a violation that cannot happen is padding, and it is\n"
        "  how a list stops being read. Drop it (`scripts/lean-orphans-allow.txt` is where a mere\n"
        "  Dregg2/** orphan belongs):\n" % len(stale_pointless))
    for m in stale_pointless:
        sys.stderr.write("    STALE (records nothing)  %s\n" % m)

if fail:
    sys.exit(1)

print("check-ratchet-darkness: PASS — no dark module mentions a refuted floor except the "
      "%d recorded exemption(s); every built-but-dark module is recorded; allowlist fresh." % len(exempt))
sys.exit(0)
PYEOF
