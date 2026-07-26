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
#       VALUE carries a floor hands every user a floor with no floor binder anywhere in sight).
#
#   A carrier whose NAME is not recorded in `Dregg2/Verify/FloorRatchetBaseline.lean` FAILS.
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
#     * a declaration whose short name collides with an unrelated baseline entry.
#   The remedy for a hit is always the same and is never "delete the check": either port the
#   declaration off the floor, or record it in the baseline WITH ITS REASON.
#
# ═══ NON-VACUITY (a gate that scans for nothing passes everything) ═══════════════════════
#   * fewer than 15 floor sentinels parsed, or `Poseidon2SpongeCR` missing  -> FAIL
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
sentinels = re.findall(r'`([A-Za-z0-9_.]+)\s*,\s*(?:true|false)\s*\)', m.group(1)) if m else []
shorts = sorted({s.rsplit('.', 1)[-1] for s in sentinels})

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
if 'sentinelBundles' in rsrc and (len(bundle_shorts) < 3 or "CommitSurface" not in bundle_shorts):
    sys.stderr.write(
        "check-floor-baseline-preflight: FAIL — `FloorRatchet.lean` names `sentinelBundles`, but\n"
        "  only %d bundle name(s) parsed (need >= 3, CommitSurface among them). Fix the parse.\n"
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
baseline = {q.rsplit('.', 1)[-1] for q in re.findall(r'"([A-Za-z0-9_.À-￿]+)"', bsrc)}
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
    hits = list(DECL_RE.finditer(text))
    for idx, mt in enumerate(hits):
        kind, name = mt.group(1), mt.group(2)
        end = hits[idx + 1].start() if idx + 1 < len(hits) else len(text)
        chunk = text[mt.end():end]
        if kind in SIG_ONLY:
            cut = chunk.find(':=')
            chunk = chunk if cut < 0 else chunk[:cut]
        elif kind not in BUNDLE_LIKE:
            # def / abbrev: the prop-body class only. A data def spelling a floor name is data.
            sig, _sep, _body = chunk.partition(':=')
            if not re.search(r':\s*Prop\s*$', sig.strip()):
                continue
        found = sorted(set(FLOOR_RE.findall(chunk)))
        if not found:
            continue
        if kind in SIG_ONLY and is_anti_floor(chunk):
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
        "  from now.\n\n")
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
      "%d baseline entries; no unbaselined carrier."
      % (scanned, len(shorts) + len(bundle_shorts), len(baseline)))
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
