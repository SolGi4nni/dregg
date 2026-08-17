#!/usr/bin/env python3
"""check-anti-vacuity-witness.py — THE ANTI-VACUITY TOOTH MAY NOT ITSELF BE VACUOUS.

═══ THE DEFECT THIS EXISTS FOR ═══════════════════════════════════════════════════
A theorem whose entire job is to REFUTE vacuity — "`X` is INHABITED", "the carrier
FIRES", "non-vacuity, positive" — discharged at an instance where the discrimination
it claims to exhibit **cannot be expressed**. It is strictly worse than an ordinary
vacuous theorem, because it is the instrument pointed AT vacuity, and it reads green.

Measured 2026-08-16, `Dregg2/Circuit/RecursiveAggregation.lean` §5:

    abbrev RealProof := Unit
    def acceptAll : RealProof → Bool := fun _ => true
    theorem real_engine_sound : EngineSound RealProof acceptAll … := …
    -- docstring: "So `EngineSound` is INHABITED — the headline is not vacuous."

One proof inhabitant; a verifier with no `false` in its range. `recursive_sound` was
discharged by a bare `rfl`. No forged proof EXISTS at that instance, so `EngineSound`
could not be refuted from the verify side at any aggregate whatsoever — and the file
said the opposite. The sibling instance, `Dregg2/Circuit/RecursiveSoundFromNodes.lean`
§7 (`accept : Unit → Bool := fun _ => true`, `honestTree : PTree Unit`), claimed "the
carrier is INHABITED" and "the fold FIRES" over a carrier that admits EVERY tree.

Both survived `#assert_axioms`, `#keystone_audit`, the guard-discipline ratchet and an
adversarial read, because every one of those instruments asks "is this proved?" and the
answer was yes. **A witness at `Unit` with an accept-everything predicate passes every
other check in this repo.** That is the gap this gate fills.

═══ THE RULE ═════════════════════════════════════════════════════════════════════
An ANNOUNCED anti-vacuity declaration (§A) whose statement rides a DEGENERATE
substrate (§B) must have a REFUSAL COMPANION in the same file (§C). Satisfiability
alone never refutes vacuity: a predicate satisfiable at every input is `True` wearing a
costume, and only a refutation tells the two apart. The pair to aim for is the one
`RecursiveAggregation.engineSound_is_a_real_boundary` now states —

    SATISFIABLE ∧ REFUTABLE, at ONE AND THE SAME instance.

§A ANNOUNCED — the declaration says it is doing anti-vacuity work, by NAME
   (`_inhabited`, `_nonempty`, `_non_vacuous`, `_satisfiable`, `_realizable`,
   `_fires`, `_witnessed`, `honest_*`, `real_*`, …) or by DOCSTRING phrase
   ("NON-VACUITY", "is INHABITED", "the fold FIRES", "not vacuous", "REALIZABLE", …).

§B DEGENERATE substrate — the statement names either
   (b1) a predicate defined IN THE SAME FILE as a constant: `fun _ => true`,
        `fun _ _ => true`, `fun _ => True`, `fun _ _ _ => 0`, or a `match` whose every
        arm is `true`/`True`; or
   (b2) a witness definition IN THE SAME FILE whose carrier type is `Unit` / `PUnit`
        (`abbrev X := Unit`, `def t : PTree Unit`, `Aggregate Unit`, …).

§C REFUSAL COMPANION — some declaration in the same file whose STATEMENT contains a
   negation (`¬`, `= false`, `≠`, `False`) and mentions the same degenerate symbol.
   That is the theorem proving the predicate can REFUSE, or the structure is REFUTABLE.

═══ WHY IT GATES ON THE FINDING, NOT ON A SELF-TEST ══════════════════════════════
`--self-test` proves the detector CAN go red; it does not prove the tree is clean, and
a gate whose only red path is its own self-test is the fail-open class this repo has
been bitten by. So the census is compared against an ALLOWLIST ledger with three red
arms, the middle one being the arm that makes it a ratchet rather than a floor:

  (a) UNLISTED finding — a new self-vacuous anti-vacuity tooth. RED.
  (b) STALE row — a listed site that no longer triggers. RED, and the fix is to RETIRE
      the row. Without this arm the ledger silently accumulates rows that describe
      nothing, and the next reader trusts them.
  (c) MALFORMED row / missing file. RED.

⚠ WHAT A GREEN HERE DOES NOT MEAN — read before trusting one:
  * It does not read PROOFS. A witness at a rich type whose proof still discharges
    everything by `rfl` is invisible here.
  * It does not count INHABITANTS. A two-constructor type both of whose constructors
    the verifier accepts passes §B and is just as degenerate.
  * §C accepts any negation mentioning the symbol. A refusal companion pointing at a
    DIFFERENT axis than the announced claim (see `scripts/free_conclusion_canary.lean`
    on exactly this evasion) counts as present. Read the companion.
  * `private` declarations are matched textually like any other, but the repo's carrier
    census cannot see private producers; do not cross-check against that census here.

Usage:
    python3 scripts/check-anti-vacuity-witness.py
    python3 scripts/check-anti-vacuity-witness.py --self-test
    python3 scripts/check-anti-vacuity-witness.py --update-allowlist   # prints, never writes
"""

from __future__ import annotations

import argparse
import bisect
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEAN_ROOT = REPO / "metatheory"
ALLOWLIST = REPO / "scripts" / "anti-vacuity-witness-allowlist.txt"

# ── §A: how a declaration ANNOUNCES that it is doing anti-vacuity work ──────────────
NAME_PATTERNS = re.compile(
    r"(?:^|_)(?:inhabited|inhabitable|instantiable|nonempty|non_?vacuous|not_?vacuous"
    r"|satisfiable|realizable|realized|witnessed|exhibited|fires|is_real)(?:_|$)",
    re.IGNORECASE,
)
NAME_PREFIXES = re.compile(r"^(?:honest|real|genuine)_", re.IGNORECASE)

DOC_PHRASES = [
    "non-vacuity", "non-vacuous", "nonvacuous", "not vacuous", "non vacuous",
    "is inhabited", "the carrier is inhabited", "would be hollow", "is not hollow",
    "the fold fires", "fires on", "is witnessed", "realizable", "satisfiable",
    "not an empty implication", "not a formal husk",
]

# ── §B: what a DEGENERATE substrate looks like, defined in the same file ───────────
#   ⚑ SHAPE DISCIPLINE, PAID FOR TWICE. These detectors are LINE-BASED string tests, not
#   regexes with several `[^\n]*` runs. Two earlier drafts used multi-star line patterns
#   (`…[^\n]*:[ \t][^\n]*(?:Unit|PUnit)[^\n]*$`) and backtracked super-linearly in the
#   line length; Lean files here have very long lines, and the census did not finish in
#   ten minutes over ~3k files either time. A per-line prefix match plus `in` tests is
#   linear and runs the whole tree in seconds. Do not "tidy" these back into one regex.
DECL_HEAD = re.compile(r"^[ \t]*(?:private[ \t]+)?(def|abbrev)[ \t]+([A-Za-z_][A-Za-z0-9_'!?]*)")
CONST_RHS = re.compile(r":=[ \t]*fun[ \t][^=]*=>[ \t]*(?:true|True|0)[ \t]*$")
MATCH_ARM = re.compile(r"^\s*\|[^=]*=>\s*(\S+)\s*$")
UNIT_TOK = re.compile(r"(?<![A-Za-z0-9_'])(?:Unit|PUnit)(?![A-Za-z0-9_'])")


def _degenerate_symbols(lines: list[str]) -> set[str]:
    """(b1) constant predicates and (b2) `Unit`/`PUnit`-carried witnesses, per line."""
    names: set[str] = set()
    for i, line in enumerate(lines):
        m = DECL_HEAD.match(line)
        if not m:
            continue
        name = m.group(2)
        rest = line[m.end():]
        # (b1) `… := fun _ … => true`
        if CONST_RHS.search(rest):
            names.add(name)
            continue
        # (b1') `def f : … Bool` followed by match arms that are ALL `true`/`True`
        if ":" in rest and (rest.rstrip().endswith("Bool") or rest.rstrip().endswith("Prop")):
            arms = []
            for nxt in lines[i + 1:]:
                am = MATCH_ARM.match(nxt)
                if not am:
                    break
                arms.append(am.group(1))
            if arms and all(a in ("true", "True") for a in arms):
                names.add(name)
                continue
        # (b2) the declared TYPE mentions `Unit`/`PUnit` — `abbrev X := Unit`,
        #      `def t : PTree Unit`, `def a : Aggregate Unit`, …
        colon = rest.find(":")
        walrus = rest.find(":=")
        if walrus != -1 and rest[walrus + 2:].strip() in ("Unit", "PUnit"):
            names.add(name)
            continue
        if colon != -1 and (walrus == -1 or colon < walrus):
            ty = rest[colon + 1: walrus if walrus != -1 else len(rest)]
            if UNIT_TOK.search(ty):
                names.add(name)
    return names


# ── §C: what a REFUSAL COMPANION looks like ────────────────────────────────────────
NEGATION = re.compile(r"¬|=\s*false|≠|\bFalse\b|Not\s")

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|example|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)",
    re.MULTILINE,
)


def strip_comments(text: str) -> str:
    """Blank out `--` line comments, keeping offsets so line numbers stay true.

    Block comments `/- … -/` are KEPT: docstrings `/-- … -/` are §A evidence, and the
    section headers `/-! … -/` carry the announcements too.
    """
    out = []
    for line in text.split("\n"):
        idx = line.find("--")
        # keep `/--` docstring openers and `-- ` inside strings is not worth modelling
        if idx >= 0 and not line[:idx].rstrip().endswith("/"):
            line = line[:idx]
        out.append(line)
    return "\n".join(out)


def declarations(text: str):
    """Return [(kind, name, start_offset, statement_text, docstring_text)].

    Materialized (not a generator) because `scan_file` needs two passes over it — the
    §C refusal sweep and the §A finding sweep — and re-running `DECL.finditer` plus the
    per-declaration slicing was the second half of the census's quadratic blow-up.
    """
    out = []
    marks = [(m.start(), m.group(1), m.group(2)) for m in DECL.finditer(text)]
    for i, (start, kind, name) in enumerate(marks):
        end = marks[i + 1][0] if i + 1 < len(marks) else len(text)
        body = text[start:end]
        # the STATEMENT is everything up to the first `:=` or ` by ` at depth 0-ish
        cut = len(body)
        for token in (":=", "\n  by", " by\n"):
            j = body.find(token)
            if j != -1:
                cut = min(cut, j)
        statement = body[:cut]
        # the docstring is the `/-- … -/` immediately preceding `start`
        doc = ""
        prev_end = marks[i - 1][0] if i else 0
        window = text[prev_end:start]
        k = window.rfind("/--")
        if k != -1:
            doc = window[k:]
        # a `/-! … -/` section header also announces
        s = window.rfind("/-!")
        if s != -1:
            doc += window[s:]
        out.append((kind, name, start, statement, doc))
    return out


def announced(name: str, doc: str) -> bool:
    if NAME_PATTERNS.search(name) or NAME_PREFIXES.search(name):
        return True
    low = doc.lower()
    return any(p in low for p in DOC_PHRASES)


def scan_file(path: Path):
    raw = path.read_text(encoding="utf-8", errors="replace")
    text = strip_comments(raw)
    lines = text.split("\n")
    degen = _degenerate_symbols(lines)
    if not degen:
        return []
    word = {s: re.compile(r"(?<![A-Za-z0-9_'])" + re.escape(s) + r"(?![A-Za-z0-9_'])")
            for s in degen}
    decls = declarations(text)
    # line lookup without slicing the prefix per declaration (that WAS a quadratic).
    nl = [i for i, ch in enumerate(text) if ch == "\n"]

    # §C — which degenerate symbols already have a refusal companion in this file?
    refuted: set[str] = set()
    for kind, name, _start, statement, _doc in decls:
        if kind not in ("theorem", "lemma", "example"):
            continue
        if not NEGATION.search(statement):
            continue
        for s in degen:
            if word[s].search(statement):
                refuted.add(s)

    findings = []
    for kind, name, start, statement, doc in decls:
        if kind not in ("theorem", "lemma", "example"):
            continue
        if not announced(name, doc):
            continue
        if NEGATION.search(statement):
            continue  # this IS a refusal; not a candidate
        hits = sorted(s for s in degen if word[s].search(statement) and s not in refuted)
        if hits:
            line = bisect.bisect_left(nl, start) + 1
            try:
                shown = str(path.relative_to(REPO))
            except ValueError:  # --self-test runs over a tempfile outside the repo
                shown = str(path)
            findings.append((shown, line, name, ",".join(hits)))
    return findings


def census():
    out = []
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        out.extend(scan_file(path))
    return out


def load_allowlist():
    if not ALLOWLIST.exists():
        return {}
    rows = {}
    for n, line in enumerate(ALLOWLIST.read_text().split("\n"), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("|")
        if len(parts) < 3:
            print(f"MALFORMED allowlist row {ALLOWLIST}:{n}: {line}", file=sys.stderr)
            sys.exit(2)
        rows[(parts[0].strip(), parts[1].strip())] = line
    return rows


SELF_TEST_SRC = '''
namespace SelfTest
def acceptEverything : Nat → Bool := fun _ => true
/-- **`toy_is_inhabited` (NON-VACUITY).** So the predicate is INHABITED. -/
theorem toy_is_inhabited : acceptEverything 0 = true := rfl
end SelfTest
'''


def self_test() -> int:
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / "SelfTest.lean"
        p.write_text(SELF_TEST_SRC)
        found = scan_file(p)
    if not found:
        print("SELF-TEST FAILED: the detector did not flag a planted "
              "`fun _ => true` + '(NON-VACUITY) … is INHABITED' pair. "
              "The gate cannot go red; it is worthless.", file=sys.stderr)
        return 1
    print(f"self-test OK — detector flagged the planted instance: {found[0][2]}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--update-allowlist", action="store_true",
                    help="print the ledger rows for the current census; never writes")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    found = census()

    if args.update_allowlist:
        for f, line, name, sym in found:
            print(f"{f} | {name} | line~{line} degenerate={sym} | REASON: <fill in>")
        return 0

    allow = load_allowlist()
    listed = set(allow)
    seen = {(f, name) for f, _l, name, _s in found}

    unlisted = [x for x in found if (x[0], x[2]) not in listed]
    stale = sorted(listed - seen)

    rc = 0
    if unlisted:
        rc = 1
        print("⚑ ANTI-VACUITY TOOTH IS ITSELF VACUOUS — unlisted findings:\n", file=sys.stderr)
        for f, line, name, sym in unlisted:
            print(f"  {f}:{line}  {name}", file=sys.stderr)
            print(f"      announced as anti-vacuity; statement rides degenerate `{sym}`;"
                  f" NO refusal companion in the file.", file=sys.stderr)
        print("\nFix, do not list: give the instance a witness type with more than one\n"
              "inhabitant and a predicate that can REFUSE, then add the refusal theorem\n"
              "(satisfiable ∧ refutable at ONE instance — see\n"
              "`Dregg2/Circuit/RecursiveAggregation.engineSound_is_a_real_boundary`).\n"
              "Listing is for sites whose degeneracy is a THEOREM OF THE MODEL, and the\n"
              "row must say which.", file=sys.stderr)
    if stale:
        rc = 1
        print("\n⚑ STALE allowlist rows — these no longer trigger. RETIRE them:", file=sys.stderr)
        for f, name in stale:
            print(f"  {f} | {name}", file=sys.stderr)

    if rc == 0:
        print(f"anti-vacuity-witness OK — {len(found)} announced/degenerate site(s), "
              f"all {len(allow)} accounted for in the ledger.")
    return rc


if __name__ == "__main__":
    sys.exit(main())
