#!/usr/bin/env bash
# check-floor-baseline-preflight.sh — a NEW floor carrier must arrive WITH its baseline decision,
# in the same commit, at commit time. The seconds-long preflight for the hours-long gate.
#
# ═══ THE HOLE THIS CLOSES ════════════════════════════════════════════════════════════════
#   `#floor_ratchet` is the real gate and it is sound: it reads the ELABORATED environment at the
#   end of `metatheory/Dregg2.lean`, so it sees prop-body carriers, bundle carriers and every
#   fixpoint mixture a text scan cannot. But it only runs when `Dregg2` is BUILT, and that root is
#   ~10 000 targets. The feedback loop is therefore HOURS, and it does not land on the author:
#
#     915437862f (2026-07-25 17:55) added two modules — `Circuit.Emit.AttestedAutomatonWeld8` and
#     `Circuit.Emit.CommittedRowsSemantics` — rooted BOTH into `metatheory/Dregg2.lean`, and landed
#     FIVE declarations carrying refuted floors (`Compress8CR` x2, `Poseidon2SpongeCR` x3) with NO
#     `FloorRatchetBaseline` entry. The commit was green on its own two files. `lake build Dregg2`
#     then failed the ratchet for EVERY OTHER LANE in the tree, and the lane that hit it had to
#     bisect to discover the carriers were not theirs.
#
#   That is the whole failure mode: a gate whose only home is a build nobody finishes in a commit
#   cycle is a gate that fires on a stranger. This scans the STAGED (or named) `.lean` files in
#   about a second and hard-fails the commit that would do it again.
#
# ═══ WHAT IT CHECKS ══════════════════════════════════════════════════════════════════════
#   For each scanned `.lean` file under the metatheory tree, comments STRIPPED (Lean's nesting
#   `/- -/` and line `--`, because this tree's prose is full of floor names):
#
#     * a `theorem`/`lemma`/`example` whose SIGNATURE (up to the first `:=`) mentions a refuted
#       floor or a floor BUNDLE  -> it is a carrier;
#     * a `def`/`abbrev`/`instance`/`structure`/`inductive` whose WHOLE declaration mentions one
#       -> it is a carrier or a carrier-maker (the prop-body and bundle classes: a `Prop` def whose
#       VALUE carries a floor hands every user a floor with no floor binder anywhere in sight);
#     * ⚑ a declaration with an INLINE `(h.. : Function.Injective f)` BINDER whose `f`'s declared
#       type is a signature this tree REFUTES -> it is a carrier of class `inj-spelled`, even
#       though it names no floor at all (2026-08-02; see the next block).
#
#   A carrier whose NAME is not recorded in `Dregg2/Verify/FloorRatchetBaseline.lean` (or in
#   `FloorRatchetBaselineInline.lean`, the inline-spelled half) FAILS.
#
# ═══ THE SECOND HOLE, AND WHY IT WAS INVISIBLE HERE FOR A WEEK ═══════════════════════════
#   `#floor_ratchet` learned to read INLINE injectivity on 2026-07-25 (`Verify/InjSpelling`):
#   `Poseidon2SpongeCR f` IS `Function.Injective f` at `f : List ℤ → ℤ`, so a binder spelled the
#   second way is the identical hypothesis under no floor NAME. THIS PREFLIGHT NEVER LEARNED IT.
#   It detected carriers with `FLOOR_RE.findall` over floor NAMES only, so on 2026-08-01 commit
#   `1f00267c8` — which landed THREE declarations binding `(hD : Function.Injective D)` at
#   `D : (CellId → AssetId → ℤ) → ℤ`, a digest `Verify/InjSpelledFloors.balDigest_not_injective`
#   refutes by CARDINALITY (uncountable domain, countable codomain: no such injection exists at
#   any parameters) — it printed `OK ... no unbaselined carrier` while the root gate rejected the
#   very same commit. The instrument reported green on the exact wound it exists to catch.
#
#   The fix mirrors the gate rather than guessing: the REFUTED SIGNATURE SET is DERIVED, two ways,
#   the same two `Verify/InjSpelling` uses --
#     * SOURCE B  an in-tree `theorem .. (f : α → β) : ¬ Function.Injective f` (the strong kind:
#                 NO function of that signature is injective), parsed from `InjSpelledFloors.lean`;
#     * SOURCE A  a sentinel floor `F` DEFINED as plain injectivity — literally
#                 `Function.Injective f`, or its eta-spelling `∀ a b, f a = f b → a = b` — whose
#                 parameter type gives the same `(α, β)` pair.
#   Hypothesis position ONLY, exactly like the gate: `¬ Function.Injective f` in a CONCLUSION is a
#   REFUTATION and is never a carrier (which is why the refutations themselves need no exemption).
#   A signature with no in-tree refutation is NOT gated — a widening encoding or a parametric
#   `β → ℤ` may be perfectly injective and gating it would be noise, and a noisy gate gets deleted.
#   (Source A is restricted to sentinels the census marks `true` = REFUTED, so a presence-required
#   floor like `BindingHashCR` contributes no signature. 19 signatures derived on 2026-08-02.)
#
#   ⚑ IT REPRODUCES THE WOUND, WHICH IS THE ONLY EVIDENCE THAT COUNTS:
#       bash scripts/check-floor-baseline-preflight.sh --rev 1f00267c8
#     BEFORE: `OK — 2 file(s) scanned, 23 floor name(s), 1972 baseline entries; no unbaselined
#             carrier.`  exit 0
#     AFTER : exit 1, naming `transferLoweredDesc_is_lowering`, `transferLowered_emits` and
#             `transferLowered_refines_balanceMovement`, each `inj-spelled:balDigest_not_injective`
#             — the same three declarations and the same refutation `#floor_ratchet` named.
#   AND IT IS NOT NOISY: swept over the last 250 `metatheory`-touching commits (each judged against
#   its own parent, as `--rev` does), the new half turns exactly ONE commit from green to red —
#   `1f00267c8` — and no other. 1 of 250, and it is the true positive.
#
#   Matching is on the floor's and the declaration's LAST NAME COMPONENT, the same convention (and
#   the same acknowledged over-match) `scripts/check-ratchet-darkness.sh` uses: a binder spells a
#   floor `Poseidon2SpongeCR`, and reconstructing a fully-qualified Lean name from text through
#   `namespace`/`section`/`variable` is exactly the kind of half-parser that goes quietly wrong.
#
# ═══ IT IS AN UNDERCOUNT, ON PURPOSE, AND SAYS SO ════════════════════════════════════════
#   A PREFLIGHT, NOT THE GATE. `#floor_ratchet` remains the authority and this script never
#   substitutes for it. Known and deliberate gaps, all in the FALSE-NEGATIVE direction (this
#   passes things the real gate catches; it never invents a violation the gate would not):
#     * floors reached through a chain of `Prop` defs / structure fields declared in OTHER,
#       unchanged files — the fixpoint needs the environment;
#     * the 10 refuted floors the ratchet DERIVES beyond the 17 parsed sentinels;
#     * a declaration whose short name collides with an unrelated baseline entry;
#     * an inline `Function.Injective f` whose `f` is typed by a `variable`/`section` binder or by
#       autobound implicits rather than in the signature itself — the type text is not there to
#       match, so no signature is attributed and the site is skipped.
#   ⚠ ONE ASYMMETRY RUNS THE OTHER WAY, and it is not new with the inline half: this scans FILES,
#   `#floor_ratchet` scans the ENVIRONMENT of `metatheory/Dregg2.lean`. A module NOT reachable from
#   that root is invisible to the gate and visible here. Measured 2026-08-02 on the whole tree with
#   the base pinned empty: 41 absolute unbaselined carriers, 36 named and 5 inline, and every one of
#   the 5 sits in the UNROOTED `*Rung2*` cluster. The set-difference-against-HEAD rule below is what
#   keeps that from blocking anybody — those carriers are in HEAD's blob too, so they are reported
#   only if a change INTRODUCES them.
#   The remedy for a hit is always the same and is never "delete the check": either port the
#   declaration off the floor, or record it in the baseline WITH ITS REASON.
#
# ═══ NON-VACUITY (a gate that scans for nothing passes everything) ═══════════════════════
#   * fewer than 15 floor sentinels parsed, or `Poseidon2SpongeCR` missing  -> FAIL
#   * fewer than 8 REFUTED INLINE SIGNATURES derived, or the whole-ledger
#     digest `(CellId → AssetId → ℤ) → ℤ` missing from them                 -> FAIL
#   * fewer than 100 baseline names parsed                                  -> FAIL
#   * a named file that does not exist                                      -> FAIL
#   Zero files to scan is NOT a failure (most commits touch no Lean), but it is announced.
#
# USAGE
#   bash scripts/check-floor-baseline-preflight.sh                # STAGED .lean files (hook mode)
#   bash scripts/check-floor-baseline-preflight.sh --all-changed  # working tree vs HEAD
#   bash scripts/check-floor-baseline-preflight.sh FILE...        # explicit files (testing)
#   bash scripts/check-floor-baseline-preflight.sh --rev REV      # files a commit touched
#
# THE DECLARED-INTENT ESCAPE (mirrors the curated-list shrink guard's, and is never silent):
#   DREGG_ALLOW_NEW_FLOOR_CARRIER=1 git commit ...
#   It prints a loud ALLOWED banner naming every carrier it let through, so an unbaselined carrier
#   still shows up in the terminal and in the agent transcript rather than reaching another lane.
#
# EXIT STATUS
#   0  no unbaselined carrier introduced (or none scanned, or explicitly allowed)
#   1  an unbaselined floor carrier, a vacuous scan, or a missing input
set -uo pipefail

repo_root="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
mt_dir="${METATHEORY_DIR:-$repo_root/metatheory}"

mode="staged"
files=()
case "${1:-}" in
  --all-changed) mode="changed" ;;
  --rev)         mode="rev"; rev="${2:-HEAD}" ;;
  "")            mode="staged" ;;
  -*)            echo "check-floor-baseline-preflight: unknown flag $1" >&2; exit 1 ;;
  *)             mode="explicit"; files=("$@") ;;
esac

# CUR_REV empty = read the working tree. BASE_REV is what the introduction is measured against.
cur_rev=""
base_rev="HEAD"
case "$mode" in
  staged)   mapfile -t files < <(git diff --cached --name-only --diff-filter=ACMR -- '*.lean' 2>/dev/null) ;;
  changed)  mapfile -t files < <(git diff --name-only --diff-filter=ACMR HEAD -- '*.lean' 2>/dev/null) ;;
  rev)      mapfile -t files < <(git show --name-only --diff-filter=ACMR --format= "$rev" -- '*.lean' 2>/dev/null)
            # A historical commit is judged against ITS OWN PARENT, not against today's HEAD —
            # otherwise re-running the demonstration silently passes the moment the carrier is
            # anywhere in HEAD, which is exactly the "gate that cannot go red" failure.
            cur_rev="$rev"; base_rev="$rev^" ;;
esac

# Keep only files that exist and live under the metatheory tree.
kept=()
for f in "${files[@]}"; do
  [ -n "$f" ] || continue
  p="$f"; [ -f "$p" ] || p="$repo_root/$f"
  if [ ! -f "$p" ] && [ -z "$cur_rev" ]; then
    if [ "$mode" = "explicit" ]; then
      echo "check-floor-baseline-preflight: FAIL — no such file: $f" >&2
      exit 1
    fi
    continue    # deleted / moved away in a diff listing: nothing to scan
  fi
  case "$(cd "$(dirname "$p")" && pwd)/" in
    "$mt_dir"/*) kept+=("$p") ;;
  esac
done

if [ ${#kept[@]} -eq 0 ]; then
  echo "check-floor-baseline-preflight: no metatheory .lean files to scan (mode=$mode)."
  exit 0
fi

python3 - "$mt_dir" "$repo_root" "$cur_rev" "$base_rev" "${kept[@]}" <<'PY'
import os, re, subprocess, sys

mt_dir, repo_root, cur_rev, base_rev, paths = (
    sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5:])

# ── the floor names, PARSED from the census's own sentinel list (never hand-written here: a hand
#    list is how binding_surface_complete.py went blind to 7 of 10 floors) ────────────────────
census = os.path.join(mt_dir, "Dregg2/Verify/FloorCensus.lean")
try:
    src = open(census, encoding='utf-8', errors='replace').read()
except OSError:
    sys.stderr.write("check-floor-baseline-preflight: FAIL — cannot read %s\n" % census)
    sys.exit(1)
m = re.search(r'def\s+sentinelFloors\s*:.*?:=\s*\[(.*?)\n\s*\]', src, re.S)
sentinels = re.findall(r'`([A-Za-z0-9_.]+)\s*,\s*(true|false)\s*\)', m.group(1)) if m else []
shorts = sorted({s.rsplit('.', 1)[-1] for s, _ in sentinels})
# ⚑ The census's own `Bool` is `true` IFF THE TREE HOLDS A REFUTATION (`FloorCensus.lean:186` —
# "BindingHashCR is refuted only at a chosen bad instance — presence-required only"). The named
# classes below scan for ALL sentinels, refuted or not, because a presence-required floor is still
# floor content. The INLINE class must NOT: `#floor_ratchet` derives its inline signature set from
# the REFUTED floors alone, and gating `Function.Injective f` at a signature nothing refutes is
# exactly the noise `Verify/InjSpelling` refuses to make.
refuted_shorts = sorted({s.rsplit('.', 1)[-1] for s, b in sentinels if b == 'true'})

if len(shorts) < 15 or "Poseidon2SpongeCR" not in shorts:
    sys.stderr.write(
        "check-floor-baseline-preflight: FAIL — parsed only %d floor name(s) from FloorCensus's\n"
        "  `sentinelFloors` (need >= 15, and Poseidon2SpongeCR among them). The census's shape\n"
        "  changed and this preflight is now scanning for almost nothing, which passes every file\n"
        "  and looks exactly like coverage. Fix the parse; do not hand-write the list.\n"
        "  parsed: %s\n" % (len(shorts), ", ".join(shorts) or "(none)"))
    sys.exit(1)

# ── the floor BUNDLES (B3): a structure with a floor-typed FIELD reaches a declaration that
#    mentions no floor NAME at all. Optional in the tree, fail-closed when present. ────────────
ratchet = os.path.join(mt_dir, "Dregg2/Verify/FloorRatchet.lean")
rsrc = open(ratchet, encoding='utf-8', errors='replace').read() if os.path.isfile(ratchet) else ""
bm = re.search(r'def\s+sentinelBundles\s*:.*?:=\s*\[(.*?)\]', rsrc, re.S)
bundle_shorts = sorted({s.rsplit('.', 1)[-1] for s in re.findall(r'`([A-Za-z0-9_.]+)', bm.group(1))}) if bm else []
# The named witness is a PARSE CANARY, not a policy: it proves the regex above actually matched
# something real, because a silent empty parse would leave FLOOR_RE (below) blind and this whole
# scan would pass by seeing nothing. It must therefore name a bundle that genuinely EXISTS.
# ⚑ It named `CommitSurface` until 2026-08-01, when that structure's four injectivity fields were
# deleted (they asserted a compressing map into one BabyBear felt is injective — false by
# pigeonhole) and it stopped being a floor-carrying bundle at all. Re-pointed at
# `Poseidon2RealizedSponge`, which still carries a floor-typed field. The strength is unchanged:
# same >= 3 floor, same "a known bundle must be present" requirement, live witness.
if 'sentinelBundles' in rsrc and (len(bundle_shorts) < 3 or "Poseidon2RealizedSponge" not in bundle_shorts):
    sys.stderr.write(
        "check-floor-baseline-preflight: FAIL — `FloorRatchet.lean` names `sentinelBundles`, but\n"
        "  only %d bundle name(s) parsed (need >= 3, Poseidon2RealizedSponge among them). Fix the parse.\n"
        "  parsed: %s\n" % (len(bundle_shorts), ", ".join(bundle_shorts) or "(none)"))
    sys.exit(1)
if 'sentinelBundles' not in rsrc:
    print("check-floor-baseline-preflight: NOTE — no `sentinelBundles` in FloorRatchet.lean, so "
          "this run scans FLOOR NAMES ONLY; the B3 bundle class is not covered here.")

FLOOR_RE = re.compile(r'\b(' + '|'.join(re.escape(s) for s in (shorts + bundle_shorts)) + r')\b')

# ── the baseline: every grandfathered name, by LAST COMPONENT ────────────────────────────────
# The grandfather list lives in TWO generated files: the main one, and the INLINE-SPELLED half
# (`FloorRatchetBaselineInline.lean`), which is separate because every name in it became visible on
# one day from one cause — the gate learned to read a floor spelled `Function.Injective f` instead
# of by name — and because the main baseline is edited concurrently by other lanes in this same
# working tree. `#floor_ratchet` compares against their UNION; so does this preflight, or it would
# report a recorded carrier as unrecorded.
baseline_paths = [os.path.join(mt_dir, "Dregg2/Verify/FloorRatchetBaseline.lean"),
                  os.path.join(mt_dir, "Dregg2/Verify/FloorRatchetBaselineInline.lean")]
baseline_path = baseline_paths[0]
bsrc = ""
for bp in baseline_paths:
    try:
        bsrc += open(bp, encoding='utf-8', errors='replace').read()
    except OSError:
        if bp is baseline_paths[0]:
            sys.stderr.write("check-floor-baseline-preflight: FAIL — cannot read %s\n" % bp)
            sys.exit(1)
# ⚑ A ROW IS A PAIR — `name ⊣ floor+floor+…` — since the 2026-08-01 re-key. The old parser was
# `re.findall(r'"([A-Za-z0-9_.À-￿]+)"')`, whose character class admits neither the SPACE nor the `+`
# in a keyed row, so it matched a keyed row NOWHERE and parsed the whole baseline as empty. It
# survived only because every row was still LEGACY (name-only) on the day the key landed; the first
# `#floor_ratchet_emit` that keyed them would have tripped the `< 100` floor below on every commit.
# Rows are read LINE-WISE (an array element, not any quoted string in the prose) and the floor set
# is stripped: this gate asks only "is this declaration recorded", which is the NAME half.
_ROW_RE = re.compile(r'^\s*"([^"\n]+)"[,\]]?\s*$', re.M)
baseline = {r.split(' ⊣ ', 1)[0].rsplit('.', 1)[-1] for r in _ROW_RE.findall(bsrc)}
if len(baseline) < 100:
    sys.stderr.write(
        "check-floor-baseline-preflight: FAIL — parsed only %d name(s) from FloorRatchetBaseline\n"
        "  (expected the ~1600-entry grandfather list). A baseline that parses as almost empty\n"
        "  turns every existing carrier into a fresh violation and every new one into noise.\n"
        % len(baseline))
    sys.exit(1)

# ── comment stripping: Lean's NESTING block comments, then line comments ─────────────────────
def strip_comments(s: str) -> str:
    out, i, depth, n = [], 0, 0, len(s)
    while i < n:
        if s.startswith('/-', i):
            depth += 1; i += 2; continue
        if s.startswith('-/', i) and depth:
            depth -= 1; i += 2; out.append(' '); continue
        if depth:
            i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i)
            i = n if j < 0 else j
            continue
        out.append(s[i]); i += 1
    return ''.join(out)

# ── ⚑ THE REFUTED INLINE SIGNATURES, DERIVED (never hand-written) ────────────────────────────
# Mirrors `Verify/InjSpelling`: a `Function.Injective f` HYPOTHESIS is a carrier exactly when this
# tree refutes injectivity AT `f`'s SIGNATURE. Two derivations, the gate's own two.

def norm_type(t: str) -> str:
    """Compare types as TEXT, canonically: `->` as the arrow, every dotted name reduced to its LAST
    component (the same convention the rest of this script uses for declaration and floor names),
    all whitespace gone. So `Dregg2.Exec.CellId -> AssetId -> Int` and `CellId → AssetId → ℤ`
    compare unequal only where they genuinely differ."""
    t = t.replace('->', '→')
    t = re.sub(r'[A-Za-z_À-￿][A-Za-z0-9_.\'À-￿]*',
               lambda m: m.group(0).rsplit('.', 1)[-1], t)
    return re.sub(r'\s+', '', t)

# SOURCE B — an unconditional non-injectivity theorem: `theorem T (f : α → β) : ¬ Function.Injective f`
# says NO function of that signature is injective. Strength: total, no deployed parameter.
inj_sigs = {}          # normalized type text -> the refutation/floor that gates it
injfile = os.path.join(mt_dir, "Dregg2/Verify/InjSpelledFloors.lean")
try:
    isrc = strip_comments(open(injfile, encoding='utf-8', errors='replace').read())
except OSError:
    isrc = ""
for nm, var, ty in re.findall(
        r'theorem\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*\(\s*([A-Za-z_][A-Za-z0-9_\']*)\s*:\s*'
        r'(.+?)\)\s*:\s*(?:¬|Not\b)\s*Function\.Injective\s+\2\b', isrc, re.S):
    inj_sigs.setdefault(norm_type(ty), nm)

# SOURCE A — a SENTINEL FLOOR that IS plain injectivity. `Poseidon2SpongeCR f` is spelled
# `∀ xs ys, sponge xs = sponge ys → xs = ys`, which is `Function.Injective sponge`; writing the
# inline form is writing the floor, so the two must not have different prices. Floors that are NOT
# plain injectivity (`compressInjective`'s 2-to-1 form, `cellLeafInjective`'s per-index form) simply
# do not match and contribute no signature — exactly as in the gate.
try:
    hits = subprocess.run(
        ["grep", "-rlE", r'^\s*def\s+(' + '|'.join(re.escape(s) for s in refuted_shorts) + r')\b',
         "--include=*.lean", mt_dir],
        capture_output=True, text=True, timeout=60).stdout.split()
except Exception:
    hits = []
for hp in hits:
    try:
        hsrc = open(hp, encoding='utf-8', errors='replace').read()
    except OSError:
        continue
    for fl, var, ty, body in re.findall(
            r'^\s*def\s+(' + '|'.join(re.escape(s) for s in refuted_shorts) + r')\s*'
            r'\(\s*([A-Za-z_][A-Za-z0-9_\']*)\s*:\s*(.+?)\)\s*:\s*Prop\s*:=\s*(.+?)(?=\n\s*\n|\n\S)',
            hsrc, re.S | re.M):
        b = ' '.join(body.split())
        v = re.escape(var)
        if (re.fullmatch(r'Function\.Injective\s+' + v, b)
                or re.fullmatch(r'∀[^,]*,\s*' + v + r'\s+(\w+)\s*=\s*' + v
                                + r'\s+(\w+)\s*→\s*\1\s*=\s*\2', b)):
            inj_sigs.setdefault(norm_type(ty), fl)

BAL_SIG = norm_type("(CellId → AssetId → ℤ) → ℤ")
if len(inj_sigs) < 8 or BAL_SIG not in inj_sigs:
    sys.stderr.write(
        "check-floor-baseline-preflight: FAIL — derived only %d refuted inline-injectivity\n"
        "  signature(s) (need >= 8, and the whole-ledger digest `(CellId → AssetId → ℤ) → ℤ`\n"
        "  among them). Either `Dregg2/Verify/InjSpelledFloors.lean` moved/changed shape, or the\n"
        "  parse broke. Until this is fixed EVERY floor spelled `Function.Injective f` is ungated\n"
        "  here again — which is exactly how commit 1f00267c8's three vacuous keystones printed\n"
        "  OK on this script while `#floor_ratchet` rejected them. Fix the parse; do not\n"
        "  hand-write the list.\n"
        "  derived: %s\n" % (len(inj_sigs), ", ".join(sorted(inj_sigs)) or "(none)"))
    sys.exit(1)

_OPENS, _CLOSES = '([{⦃⟨', ')]}⦄⟩'

def binder_groups(s: str):
    """The DEPTH-1 bracketed binder groups of a signature, as inner text. Balanced, so a nested
    function type `(D : (CellId → AssetId → ℤ) → ℤ)` yields ONE group, not two."""
    out, depth, start = [], 0, None
    for i, c in enumerate(s):
        if c in _OPENS:
            if depth == 0:
                start = i + 1
            depth += 1
        elif c in _CLOSES:
            depth -= 1
            if depth <= 0:
                if start is not None:
                    out.append(s[start:i])
                start, depth = None, 0
    return out

def split_binder(inner: str):
    """`names : type` at the first DEPTH-0 colon of a binder group; (None, None) if untyped."""
    depth = 0
    for i, c in enumerate(inner):
        if c in _OPENS:
            depth += 1
        elif c in _CLOSES:
            depth -= 1
        elif c == ':' and depth == 0 and inner[i + 1:i + 2] not in ('=', ':'):
            return inner[:i].strip(), inner[i + 1:].strip()
    return None, None

INJ_BINDER_RE = re.compile(r'^Function\.Injective\s+([A-Za-z_][A-Za-z0-9_\']*)$')

def inline_inj_floors(sig: str):
    """The refuted signatures a declaration ASSUMES inline. Hypothesis position only: we read the
    BINDERS, never the conclusion, so `¬ Function.Injective f` as a CONCLUSION (a refutation — the
    content this campaign wants more of) is not a carrier and needs no exemption."""
    binders, _concl = split_sig(sig)
    typed, injected = {}, []
    for inner in binder_groups(binders):
        names, ty = split_binder(inner)
        if names is None:
            continue
        ty = ' '.join(ty.split())
        m = INJ_BINDER_RE.match(ty)
        if m:
            injected.append(m.group(1))
        else:
            for nm in names.replace('{', ' ').replace('}', ' ').split():
                typed[nm] = ty
    found = []
    for f in injected:
        ty = typed.get(f)
        if ty is None:
            continue                     # typed elsewhere (`variable`, autobound): undercount, stated
        fl = inj_sigs.get(norm_type(ty))
        if fl and fl not in found:
            found.append(fl)
    return sorted(found)


DECL_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+)*'
    r'(theorem|lemma|example|def|abbrev|instance|structure|inductive|class)\s+'
    r'([A-Za-z_À-￿][A-Za-z0-9_.\'À-￿!?]*)',
    re.M)
# theorem-like: only the SIGNATURE carries a floor meaningfully; a proof BODY mentioning one is not
# a carrier. `def`/`abbrev`: the prop-body class lives in the VALUE, but ONLY for `Prop`-valued defs
# — `def sentinelFloors : List (Name x Bool) := [`Poseidon2SpongeCR, ..]` is a LIST OF NAMES, not a
# carrier, and neither is any other data def that happens to spell one. Bundles are whole-decl.
SIG_ONLY = {'theorem', 'lemma', 'example', 'instance'}
BUNDLE_LIKE = {'structure', 'class', 'inductive'}

# ── THE INSTRUMENT'S OWN FILES ARE NOT TREE CONTENT ──────────────────────────────────────────
# The census's floor list, the ratchet's bundle list, the baseline's grandfather arrays and the
# specimens are all FIXTURES: they spell floor names as DATA. Scanning them would make this gate
# fire on the very edit it tells you to make — recording a carrier in `manual` would be blocked by
# the check that asked for it — and `FloorRatchetSpecimens` is excluded from the real gate's
# carrier surface for exactly the same reason.
INSTRUMENT = {
    "Dregg2/Verify/FloorRatchet.lean",
    "Dregg2/Verify/FloorRatchetBaseline.lean",
    "Dregg2/Verify/FloorRatchetBaselineInline.lean",
    "Dregg2/Verify/FloorRatchetSpecimens.lean",
    "Dregg2/Verify/FloorCensus.lean",
    "Dregg2/Verify/InjSpelling.lean",
    # The inline half's DERIVATION SOURCE, for the same reason `FloorCensus` is here: this is where
    # you go to ADD a refutation, and the check must never fire on the edit it asks for.
    "Dregg2/Verify/InjSpelledFloors.lean",
}

# ── ANTI-FLOOR is EXEMPT, mirroring `FloorRatchet.antiFloor` ─────────────────────────────────
# A declaration that REFUTES floor content and ASSUMES none is exactly what this campaign wants
# MORE of — `compress8CR_false_babyBear : ... -> not Compress8CR f` is the tooth, not the debt.
# Reading the type as `forall x1:A1 .. xn:An, C`, the two spellings of writing a refutation are:
#   * C = `not F ..` with F floor content and NO Ai floor content; and
#   * C = `False` with the INNERMOST Ai floor content and no other  (`G -> F -> False` IS `G -> not F`).
# ASSUMING a refuted floor on the way to a negation is NOT exempt and never becomes exempt: that is
# the B1 laundering probe the real gate's `specB1NegationLaundry` specimen pins to `false`.
def split_sig(sig: str):
    """(binders, conclusion) at the FIRST depth-0 `:` — binder groups are all bracketed, so the
    first unbracketed colon is the type ascription. Returns (sig, '') if there is none."""
    depth = 0
    opens, closes = '([{⦃⟨', ')]}⦄⟩'
    i, n = 0, len(sig)
    while i < n:
        c = sig[i]
        if c in opens:
            depth += 1
        elif c in closes:
            depth -= 1
        elif c == ':' and depth <= 0:
            if sig[i + 1:i + 2] not in ('=', ':') and sig[i - 1:i] != ':':
                return sig[:i], sig[i + 1:]
        i += 1
    return sig, ''

BINDER_RE = re.compile(r'[(\[{⦃][^()\[\]{}⦃⦄]*[)\]}⦄]')

def is_anti_floor(sig: str) -> bool:
    binders, concl = split_sig(sig)
    if not concl:
        return False
    concl_s = concl.strip()
    binder_floors = FLOOR_RE.findall(binders)
    # spelling 1: concludes a floor's NEGATION, assuming no floor.
    if not binder_floors and re.match(r'^(¬|\\not\b|Not\b)', concl_s) and FLOOR_RE.search(concl_s):
        return True
    # spelling 2: the same, uncurried — concludes False with the innermost binder the only floor.
    if re.match(r'^False\b', concl_s) and len(binder_floors) >= 1:
        groups = BINDER_RE.findall(binders)
        floor_groups = [g for g in groups if FLOOR_RE.search(g)]
        if len(floor_groups) == 1 and groups and groups[-1] is floor_groups[0]:
            return True
    return False

def carriers(text: str):
    """{short name: (kind, name, [floors])} for every unbaselined carrier in this source text."""
    text = strip_comments(text)
    out = {}
    decls = list(DECL_RE.finditer(text))
    for idx, mt in enumerate(decls):
        kind, name = mt.group(1), mt.group(2)
        end = decls[idx + 1].start() if idx + 1 < len(decls) else len(text)
        chunk = text[mt.end():end]
        cut = chunk.find(':=')
        sig = chunk if cut < 0 else chunk[:cut]
        # ⚑ THE INLINE SPELLING, on EVERY declaration kind. A `def` is gated too: the gate's own
        # inline surface holds `Inst.Transfer.balanceE`, a `def` whose only floor is the
        # `(hD : Function.Injective D)` parameter, and a preflight that skipped non-`Prop` defs
        # here would let the next one in for free. Hypothesis position only, so a refutation
        # (`¬ Function.Injective f` as the CONCLUSION) is never a hit and needs no exemption.
        found = ["inj-spelled:" + f for f in inline_inj_floors(sig)]
        # …and the NAMED classes, exactly as before.
        if kind in SIG_ONLY:
            chunk = sig
            if not is_anti_floor(chunk):
                found += FLOOR_RE.findall(chunk)
        elif kind in BUNDLE_LIKE:
            found += FLOOR_RE.findall(chunk)
        elif re.search(r':\s*Prop\s*$', sig.strip()):
            # def / abbrev: the prop-body class only. A data def spelling a floor name is data.
            found += FLOOR_RE.findall(chunk)
        found = sorted(set(found))
        if not found:
            continue
        short = name.rsplit('.', 1)[-1]
        if short in baseline:
            continue
        out[short] = (kind, name, found)
    return out

def at_rev(rev: str, rel_repo: str) -> str:
    """The file as `rev` has it; '' when that rev does not carry it (a genuinely new module)."""
    try:
        return subprocess.run(["git", "show", "%s:%s" % (rev, rel_repo)], cwd=repo_root,
                              capture_output=True, text=True, timeout=30).stdout
    except Exception:
        return ""

# ⚑ SET DIFFERENCE AGAINST HEAD, deliberately not an absolute count — the same invariant shape the
# curated-list shrink guard uses. Only carriers this change INTRODUCES are violations; a carrier
# already in HEAD's blob is somebody else's open decision and must not block an unrelated edit to
# the same file. (In a healthy tree HEAD has none: the ratchet guarantees it. This matters exactly
# during the window when one is outstanding — which is when people are touching those files.)
violations = []
scanned = 0
for p in paths:
    rel = os.path.relpath(p, mt_dir)
    if rel in INSTRUMENT:
        continue
    scanned += 1
    rel_repo = os.path.relpath(p, repo_root)
    cur_src = (at_rev(cur_rev, rel_repo) if cur_rev
               else open(p, encoding='utf-8', errors='replace').read())
    now = carriers(cur_src)
    if not now:
        continue
    before = carriers(at_rev(base_rev, rel_repo))
    for short, (kind, name, found) in sorted(now.items()):
        if short in before:
            continue
        violations.append((rel, kind, name, found))

if violations:
    sys.stderr.write(
        "\n"
        "  ══ check-floor-baseline-preflight: NEW FLOOR CARRIER WITH NO BASELINE DECISION ══\n\n"
        "  These declarations take a REFUTED floor — a hypothesis this tree PROVES FALSE at\n"
        "  deployed BabyBear parameters — and are not recorded in FloorRatchetBaseline. A theorem\n"
        "  under a refuted floor is VACUOUSLY TRUE at deployment: it says nothing about the\n"
        "  shipping system. `lake build Dregg2` WILL fail on these, for every other lane, hours\n"
        "  from now.\n\n"
        "  An `inj-spelled:` tag means the binder reads `Function.Injective f` and names no floor:\n"
        "  it is the SAME hypothesis, and the refutation named after the colon is the theorem that\n"
        "  proves it false at your `f`'s signature. `(CellId → AssetId → ℤ) → ℤ` is refuted by\n"
        "  CARDINALITY, not by parameters — an uncountable domain cannot inject into ℤ, ever.\n\n")
    for rel, kind, name, found in violations:
        sys.stderr.write("    %s\n      %s %s   carries: %s\n" % (rel, kind, name, ", ".join(found)))
    sys.stderr.write(
        "\n  THE TWO HONEST WAYS FORWARD (adding a carrier is a DECISION, not a chore):\n"
        "    (a) PORT IT — restate in the `_or_collides` + total-extractor idiom, so the binding\n"
        "        half is UNCONDITIONAL and the residual is a NAMED, REFUTABLE collision at a pair\n"
        "        an extractor hands back. See `MapMerkleRoot` 5b and `Emit/CommittedRowsSemantics`.\n"
        "        A residual stated existentially (`exists a b, a != b and h a = h b`) is a FREE\n"
        "        PASS: at deployed parameters it is simply TRUE.\n"
        "    (b) RECORD IT — add the FULL name to `manual` in FloorRatchetBaseline.lean WITH the\n"
        "        reason it must carry the floor. That is the deliberate, reviewable direction.\n"
        "  Escape (loud, never silent):  DREGG_ALLOW_NEW_FLOOR_CARRIER=1 git commit ...\n\n")
    sys.exit(1)

print("check-floor-baseline-preflight: OK — %d file(s) scanned, %d floor name(s), "
      "%d refuted inline signature(s), %d baseline entries; no unbaselined carrier."
      % (scanned, len(shorts) + len(bundle_shorts), len(inj_sigs), len(baseline)))
PY
rc=$?

if [ $rc -ne 0 ] && [ -n "${DREGG_ALLOW_NEW_FLOOR_CARRIER:-}" ]; then
  echo ""
  echo "  ══ ALLOWED: DREGG_ALLOW_NEW_FLOOR_CARRIER is set ═════════════════════════════════"
  echo "  The unbaselined floor carrier(s) listed above are being let through DELIBERATELY."
  echo "  \`lake build Dregg2\` will still fail until FloorRatchetBaseline records them."
  echo ""
  exit 0
fi
exit $rc
