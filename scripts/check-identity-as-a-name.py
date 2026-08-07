#!/usr/bin/env python3
"""check-identity-as-a-name.py — a ROUTING IDENTITY rendered where a player expects a PERSON.

═══ THE HOLE THIS CLOSES ══════════════════════════════════════════════════════════
`dreggnet_offerings::refusal::audit_player_text` already bans a raw hex run in player
copy, and it works — on REFUSALS. It is pointed at notices: the stale-page body, the
shared vocabulary, a rendered `Outcome::Refused`. So the shared party lobby could print

    Role     Holder              Status
    Tank     71b278f3dc43444…    not ready

and score zero violations, because a ROSTER is not a notice. The gate was not wrong;
its SCOPE was one *kind of string* wide — the same shape as `guide.rs`'s vocabulary
list certifying the one page that needed it least, which is why
`scripts/check-player-vocabulary.py` exists.

And it is not one site. Read back off the tree on 2026-07-27, before this gate:

    dreggnet-surfaces/src/party.rs         the party lobby's Holder column
    dreggnet-surfaces/src/private_raid.rs  the raid roster (twice), and two status lines
    dreggnet-market/src/dark_amm_collective.rs  the staging-slot owner line

Six sites, three crates, all rendering a truncated `blake3(label)` where a player is
looking for the friend they invited — and each crate had minted its OWN
`fn short_identity` to do it, so the wound propagated by copy-paste rather than by
call. The fix is `dreggnet_offerings::player_name::display_name_of`, which returns the
frontend-attributed name and, when there is none, `player 71b278` — short, sayable, and
visibly a stand-in rather than a key.

⚠ IT ALSO WOULD NOT HAVE BEEN CAUGHT BY THE HEX RULE. `short_identity` truncates to
15–18 characters, and `audit_player_text`'s `RawHexRun` starts at 32 — the shortest run
in this product that IS a key. So even pointed at a roster, that rule reads the column
as clean. A person-shaped column needs a rule about WHAT REACHES IT, not about how long
the result is. That is this file.

═══ THE TWO RULES ═════════════════════════════════════════════════════════════════
R1  An IDENTITY ACCESSOR inside a PLAYER-FACING TEXT POSITION, not passed through a
    naming call. The positions are the deos view-node text constructors and an
    affordance LABEL (`Action::new`'s first argument is a button a person reads); the
    accessors are the ones that yield a frontend-attributed identity string in this
    tree. Balanced-paren spans, so a multi-line call — which is how the party bug was
    written — is one unit rather than four unrelated lines.

R2  A LOCALLY RE-MINTED IDENTITY TRUNCATOR (`fn short_identity`, `fn short_actor`, …).
    Three crates had one; deleting them is what makes R1 enforceable, because a local
    helper hides the accessor one call frame down where a grep-shaped gate cannot see
    it. `short_root` / `short_digest` / `short_id` are NOT banned: a root IS a machine
    value and shortening it is the right thing.

═══ THE BLIND SPOT, NAMED ═════════════════════════════════════════════════════════
An identity bound to a local first — `let who = &roster[seat]; text(who.to_string())` —
is invisible here. Closing that needs dataflow, which a source sweep does not have. R2
is the mitigation that matters in practice: every instance found on the tree reached the
column through a *named truncator*, because a bare 64-character hex string in a table
cell is obvious enough that someone always shortens it first. A gate that catches the
shortening catches the shape.

═══ THE EXEMPTION LIST IS A RATCHET, NOT A MUTE ═══════════════════════════════════
`scripts/identity-as-a-name-allow.tsv`, one row per site:

    path <TAB> rule <TAB> the exact text, escaped <TAB> why it stays

Keyed by TEXT, not line number — lanes move lines all day. **A row whose text no longer
appears at that path FAILS**, so fixing a site retires its exemption instead of leaving
a permission slip behind.

═══ CAN IT GO RED ═════════════════════════════════════════════════════════════════
`--self-test` drives the classifier over inputs it MUST catch and inputs it MUST NOT,
and narrows the scope to prove the FLOOR bites. The headline is a NEGATIVE assertion
(`no routing identity reaches a person-shaped column`), which is exactly the shape that
passes when the reader is broken or the file set is empty — so the sweep also asserts
MIN_FILES and MIN_POSITIONS, or it reports itself BROKEN rather than clean.

⚠ IT SWEEPS THE INDEX, NOT THE WORKING TREE. `git ls-files` is the file set, so a NEW
file you have not `git add`ed is INVISIBLE to a local run.

Usage:  python3 scripts/check-identity-as-a-name.py [--list PATH] [--self-test]
Exit:   0 clean · 1 a violation, a stale exemption row, or a sweep that fell through
        its own floor · 2 usage error

Runs in ~1s (no cargo), so it belongs in the CHEAP set of `scripts/local-gates.sh`.
That runner takes the command's SECOND token as a path to stat, and for
`python3 scripts/check-…py` that token is this file, so it needs no wrapper.
"""

from __future__ import annotations

import argparse
import importlib.util
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_LIST = REPO / "scripts" / "identity-as-a-name-allow.tsv"

# ── the reader ─────────────────────────────────────────────────────────────────────
# `check-production-callers.py::strip_noise` blanks comments and string literals while
# PRESERVING offsets, which is exactly what this needs: this repo names its own helpers
# in doc comments constantly (this file's own rule text does it), and a sweep that
# counts prose reports a violation that is a sentence. Reimplementing it would be a
# second reader of the same tree with its own bugs.
_spec = importlib.util.spec_from_file_location(
    "production_callers", REPO / "scripts" / "check-production-callers.py"
)
if _spec is None or _spec.loader is None:  # pragma: no cover - a missing sibling is fatal
    print("scripts/check-production-callers.py is missing; this gate reads it", file=sys.stderr)
    sys.exit(2)
pc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pc)

# ── SCOPE ──────────────────────────────────────────────────────────────────────────
# The crates that build player-facing view trees. The unit is a CRATE rather than a
# route, because the rule is structural (what reaches a text position) and not about
# which URL serves it — a surface crate's roster is the same wound whichever frontend
# paints it.
SURFACE_CRATES: dict[str, str] = {
    "dreggnet-surfaces": "the shared multi-player tables (party lobby, private raid, …)",
    "dreggnet-web": "every browser page and the Telegram / Discord embedded twins",
    "dreggnet-market": "the market and dark-AMM operation surfaces",
    "dreggnet-council": "the governance table",
    "dreggnet-offerings": "the dungeon / Descent / campaign surfaces and the shared refusal copy",
    "dreggnet-party": "the party substrate's own rendered lobby record",
    "dreggnet-catalog": "the shelf and the per-player worlds registry",
    "deos-view": "the view-node backends every surface is painted through",
}

# A player-facing TEXT POSITION: the opener, and which argument index is copy.
# `Action::new(label, turn, arg, enabled)` — argument 0 is the button a person reads.
POSITIONS: tuple[str, ...] = (
    "text(",
    "pill(",
    "ViewNode::Text(",
    "Action::new(",
)

# The accessors that yield a frontend-attributed IDENTITY string in this tree.
IDENTITY_TELLS: tuple[str, ...] = (
    ".identity()",
    ".identity_in(",
    ".leader()",
    "short_identity(",
)

# Calls that turn an identity INTO a name. A position containing one is clean.
NAMING_CALLS: tuple[str, ...] = (
    "display_name",
    "player_name",
    "readable_handle",
)

# R2: helper names that re-mint a local identity truncator. Deliberately NOT `short_*`:
# `short_root` / `short_digest` / `short_id` shorten machine values, which is correct.
BANNED_HELPERS: tuple[str, ...] = (
    "fn short_identity",
    "fn short_actor",
    "fn short_player",
    "fn short_holder",
    "fn short_name",
)

# ── THE FLOOR. A negative assertion passes just as happily on an empty premise. ─────
MIN_FILES = 60
MIN_POSITIONS = 400


def tracked_sources() -> list[Path]:
    """Every tracked Rust source under a surface crate, EXCLUDING test targets.

    A `tests/` binary is test code: it pins copy rather than being copy, and a fixture
    that constructs `text(id.identity())` to prove the gate bites must not red the gate.
    """
    out = subprocess.run(
        ["git", "ls-files", "--", *[f"{c}/**/*.rs" for c in SURFACE_CRATES]],
        cwd=REPO,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.split()
    keep = []
    for rel in out:
        parts = Path(rel).parts
        if "tests" in parts or "benches" in parts or "examples" in parts:
            continue
        keep.append(Path(rel))
    return sorted(keep)


def spans(source: str) -> list[tuple[int, str]]:
    """Every player-facing text position in `source`, as `(offset, argument text)`.

    Balanced parens, so a multi-line call is ONE unit — which is how the party bug was
    written (`text(\\n  seat.map(|seat| short_identity(seat.identity()))\\n)`), and a
    line-shaped reader sees four unrelated lines there.
    """
    found: list[tuple[int, str]] = []
    for opener in POSITIONS:
        at = 0
        while True:
            at = source.find(opener, at)
            if at < 0:
                break
            # An opener must start a call, not end an identifier (`context(` vs `text(`).
            before = source[at - 1] if at else " "
            if before.isalnum() or before in "_:" and not opener.startswith("ViewNode"):
                at += len(opener)
                continue
            start = at + len(opener)
            depth = 1
            i = start
            while i < len(source) and depth:
                if source[i] == "(":
                    depth += 1
                elif source[i] == ")":
                    depth -= 1
                i += 1
            found.append((at, source[start : i - 1]))
            at = start
    return found


def escape(text: str) -> str:
    """One line, for a TSV key."""
    return " ".join(text.split())


def findings(files: list[Path]) -> tuple[list[dict], int, int]:
    """Every violation, plus the counts the floor is checked against."""
    hits: list[dict] = []
    positions = 0
    scanned = 0
    for rel in files:
        try:
            raw = (REPO / rel).read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        scanned += 1
        blanked = pc.strip_noise(raw)
        # R1 — an identity accessor in a text position with no naming call.
        for at, arg in spans(blanked):
            positions += 1
            if not any(tell in arg for tell in IDENTITY_TELLS):
                continue
            if any(name in arg for name in NAMING_CALLS):
                continue
            line = blanked.count("\n", 0, at) + 1
            hits.append(
                {
                    "path": str(rel),
                    "line": line,
                    "rule": "R1",
                    "text": escape(raw[at : at + 200]),
                }
            )
        # R2 — a locally re-minted identity truncator.
        for helper in BANNED_HELPERS:
            at = 0
            while True:
                at = blanked.find(helper, at)
                if at < 0:
                    break
                line = blanked.count("\n", 0, at) + 1
                hits.append(
                    {
                        "path": str(rel),
                        "line": line,
                        "rule": "R2",
                        "text": escape(raw[at : at + 120]),
                    }
                )
                at += len(helper)
    return hits, scanned, positions


def read_allowlist(path: Path) -> list[tuple[str, str, str, str, int]]:
    rows: list[tuple[str, str, str, str, int]] = []
    if not path.exists():
        return rows
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        parts = raw.split("\t")
        if len(parts) != 4:
            print(f"{path}:{lineno}: need 4 tab-separated fields, saw {len(parts)}", file=sys.stderr)
            sys.exit(2)
        rows.append((parts[0], parts[1], parts[2], parts[3], lineno))
    return rows


def shown(path: Path) -> str:
    try:
        return str(path.relative_to(REPO))
    except ValueError:
        return str(path)


def self_test() -> int:
    ok = True

    def check(cond: bool, what: str) -> None:
        nonlocal ok
        ok = ok and bool(cond)
        print(f"  {'ok  ' if cond else 'FAIL'}  {what}")

    print("self-test — MUST CATCH")
    must_catch = [
        ('text(short_identity(seat.identity()))', "the party lobby's Holder column, verbatim"),
        ('pill(short_identity(identity), "genuine")', "the raid roster's seat pill"),
        ("text(\n  seat.map(|seat| short_identity(seat.identity()))\n    .unwrap_or_default(),\n)",
         "the MULTI-LINE form the party bug was actually written in"),
        ('Action::new(format!("{} accepts", short_identity(actor)), T, 0, true)',
         "an affordance LABEL is a button a person reads"),
        ("fn short_identity(identity: &str) -> String {", "R2 — a re-minted local truncator"),
        ('ViewNode::Text(format!("owner {}", actor.identity()))', "a raw accessor, no truncator"),
    ]
    for src, what in must_catch:
        blanked = pc.strip_noise(src)
        caught = any(
            any(t in arg for t in IDENTITY_TELLS) and not any(n in arg for n in NAMING_CALLS)
            for _, arg in spans(blanked)
        ) or any(h in blanked for h in BANNED_HELPERS)
        check(caught, what)

    print("\nself-test — MUST NOT CATCH")
    must_not = [
        ("text(display_name_of(seat.identity()))", "the FIX itself must be clean"),
        ('pill(display_name_of(identity), "genuine")', "…in a pill too"),
        ("fn short_root(root: &[u8; 32]) -> String {", "a ROOT is a machine value; shortening is right"),
        ("fn short_digest(d: &[u8; 32]) -> String {", "…and so is a digest"),
        ("// text(short_identity(seat.identity())) — the shape this gate bans",
         "a COMMENT naming the shape is prose, not code"),
        ('let doc = "text(short_identity(x))";', "…and so is a string literal"),
        ('text(role.name())', "an ordinary label"),
        ('context(short_identity(x))', "an opener that only ENDS in `text(` is not `text(`"),
    ]
    for src, what in must_not:
        blanked = pc.strip_noise(src)
        caught = any(
            any(t in arg for t in IDENTITY_TELLS) and not any(n in arg for n in NAMING_CALLS)
            for _, arg in spans(blanked)
        ) or any(h in blanked for h in BANNED_HELPERS)
        check(not caught, what)

    print("\nself-test — the FLOOR bites")
    # Narrow the scope to one crate and the sweep must report itself BROKEN, not clean —
    # `no identity reaches a person-shaped column` is true of a sweep that read nothing.
    real = dict(SURFACE_CRATES)
    try:
        SURFACE_CRATES.clear()
        SURFACE_CRATES["dreggnet-party"] = "one crate, on purpose"
        _, narrow_files, narrow_positions = findings(tracked_sources())
    finally:
        SURFACE_CRATES.clear()
        SURFACE_CRATES.update(real)
    check(
        narrow_files < MIN_FILES or narrow_positions < MIN_POSITIONS,
        f"a scope narrowed to one crate falls through the floor "
        f"({narrow_files} files, {narrow_positions} positions)",
    )
    _, files, positions = findings(tracked_sources())
    check(
        files >= MIN_FILES and positions >= MIN_POSITIONS,
        f"…while the real sweep clears it with room: {files} files, {positions} positions",
    )

    print("\nself-test — the ratchet")
    check(read_allowlist(DEFAULT_LIST) is not None, "the exemption list parses")

    print("\nself-test " + ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--list", type=Path, default=DEFAULT_LIST)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    hits, files, positions = findings(tracked_sources())
    allow = read_allowlist(args.list)

    remaining: list[dict] = []
    used: set[int] = set()
    for h in hits:
        idx = next(
            (
                i
                for i, (p, rule, txt, _, _) in enumerate(allow)
                if p == h["path"] and rule == h["rule"] and txt == h["text"]
            ),
            None,
        )
        if idx is None:
            remaining.append(h)
        else:
            used.add(idx)
    stale = [(i, r) for i, r in enumerate(allow) if i not in used]

    rc = 0
    # ⚑ THE FLOOR, CHECKED BEFORE THE VERDICT.
    if files < MIN_FILES or positions < MIN_POSITIONS:
        rc = 1
        print(
            f"\n⛔ THE SWEEP FELL THROUGH ITS OWN FLOOR: {files} file(s) (need {MIN_FILES}) and "
            f"{positions} text position(s) (need {MIN_POSITIONS}).\n"
            "   This is a BROKEN READER reported as a broken reader, not a clean tree. Check\n"
            "   `git ls-files` (an unstaged new file is invisible), SURFACE_CRATES, and that\n"
            "   check-production-callers.py still imports.\n"
        )
    if remaining:
        rc = 1
        print(
            f"\n⛔ {len(remaining)} site(s) put a ROUTING IDENTITY where a player expects a PERSON.\n"
            "   A `DreggIdentity` is the right thing to route and attribute a turn with and the\n"
            "   wrong thing to print in a column headed Holder: a player reads\n"
            "   `71b278f3dc43444…` where the friend they invited belongs. Render it through\n"
            "   `dreggnet_offerings::player_name::display_name_of`, which returns the\n"
            "   frontend-attributed name and otherwise the readable stand-in `player 71b278`.\n"
            f"   If a site genuinely shows an identifier ON PURPOSE, add it to {shown(args.list)}\n"
            "   with the reason.\n"
        )
        for h in sorted(remaining, key=lambda x: (x["path"], x["line"])):
            excerpt = h["text"][:140] + ("..." if len(h["text"]) > 140 else "")
            print(f"  {h['path']}:{h['line']}  [{h['rule']}]")
            print(f"      {excerpt}")
    if stale:
        rc = 1
        print(
            f"\n⛔ {len(stale)} STALE exemption row(s) — the text is no longer there.\n"
            "   Fixing a site retires its exemption; delete the row.\n"
        )
        for _, (p, rule, text, reason, lineno) in stale:
            print(f"  {shown(args.list)}:{lineno}  claims {p} still has [{rule}]")
            print(f"      {text[:120]}")
            print(f"      was allowed because: {reason}")

    if rc == 0:
        print(
            f"swept {files} surface sources · {positions} player-facing text positions · "
            f"{len(allow)} exempt"
        )
        print("no routing identity reaches a person-shaped column")
    return rc


if __name__ == "__main__":
    sys.exit(main())
