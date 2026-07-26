#!/usr/bin/env python3
"""check-player-vocabulary.py — a word from the project's private vocabulary in copy a PLAYER reads.

═══ THE HOLE THIS CLOSES ══════════════════════════════════════════════════════════
`dreggnet-web/src/guide.rs` already had this gate, and it worked: a banned-jargon list
as data, a can-it-go-red test beside it, a build failure if `executor` or `receipt`
reached the copy. **It ran on `guide_body()` and nothing else.** So `/guide` scored 0
violations while an audit found the same list violated on 6 of 13 live surfaces. Read
back off the tree on 2026-07-26, with the rules below applied, that was:

    /session/{id}, /offerings/…   receipt (5) · commitment (1)
    /you                          receipt (8) · executor (3)
    /descent, /descent/run/*      no-cheat (4) · receipt (4) · journal-root (2)
    /identity                     receipt (1)
    /descent/play?engine=browser  receipt (2) · executor (1)
    /tg/**, /da/**                receipt (6) · no-cheat (1)

⚑ One term in the audit's list does NOT live in `dreggnet-web` at all: `merkle` reaches
the session page from `dreggnet-offerings`' `*_DISCLOSURE` consts, which
`BinaryOperationDescriptor.disclosure` documents as *the security disclosure every
renderer must show verbatim* and `lib.rs` prints into `<p class=operation-disclosure>`.
That is a real hole and it is named as such in `NOT_PLAYER_SURFACES` below, with its
two exact sites — not fixed here, because those are security disclosures whose
precision is the point and rewriting them is its own pass.

The gate was not wrong. Its SCOPE was one function wide, so it certified the one page
that needed it least. That is the same shape as the em-dash convention decaying within
hours of being swept ([[feedback-a-documented-wound-is-not-a-detected-one]]): a rule
enforced in one place and honoured nowhere else. This file is the widening.

═══ ONE LIST, TWO READERS ═════════════════════════════════════════════════════════
`scripts/player-vocabulary.tsv` is THE list — `term <TAB> why <TAB> what to say instead`.
This script parses it; so does `guide.rs`, via `include_str!`. A second reader must
never mean a second list, because two lists drift and the weaker one wins the day they
do. The two readers are deliberately different instruments over the same rule:

  * THIS ONE reads SOURCE, so it sees every branch of the copy including the ones a
    fixture would never reach. A render-driven test passes on an empty store.
  * `guide.rs`'s reads the RENDERED body, so it catches jargon composed in from another
    module, which a source sweep of one file cannot.

═══ WHERE THE PLAYER/DEVELOPER LINE IS DRAWN, AND WHY ═════════════════════════════
Getting scope wrong makes the gate worthless in BOTH directions. Too wide and it fires
on an SDK author's own vocabulary, and the next lane silences it; too narrow and it
passes while `/you` says `executor` under a button.

**A string is in scope if it is rendered into a PAGE A PLAYER OPENS.** The unit is a
live ROUTE, which is the unit the audit used, so `PLAYER_SURFACES` below names every
`dreggnet-web` module with the routes it serves. Everything else is out, and the
excluded halves are named in `NOT_PLAYER_SURFACES` so an omission is a decision on the
record rather than a gap.

Out, and each for a stated reason:

  * **The ingest and act APIs' JSON bodies.** `POST /descent/submit` answers a
    `serde_json::json!` document read by a SUBMITTING CLIENT — the Discord bot, a
    native runner, `curl`. `executor` in a `"detail"` field is addressed to whoever
    wrote that client. Rule R5.
  * **Operator sinks and assertions.** `tracing::*!`, `eprintln!`, `assert!`,
    `.expect()`. Rule R3, inherited from the punctuation gate.
  * **Comments and test bodies.** A doc comment is prose FOR A DEVELOPER, and a golden
    PINS copy rather than being copy. Rules R1 and R2, inherited.
  * **`{placeholder}` spans.** `"{notice}{fragment}{receipt}"` is three variable names,
    not a sentence, and `.receipt` is a CSS class on nearly every page in this product.
    (This is the exact trap `guide.rs` names: `page.contains("receipt")` is true of
    every page regardless of its copy, which is why the whole document was never
    checkable.) Rule R6, plus the HTML reader, which keeps text nodes and the handful
    of attributes a person actually reads.
  * **Developer instruments that happen to be HTTP.** `/explorer` browses a node's
    read API and `/metrics` is Prometheus. A developer reading them OWNS the word
    `receipt`: it is the name of the thing they asked for. Named below.

═══ THE EXEMPTION LIST IS A RATCHET, NOT A MUTE ═══════════════════════════════════
`scripts/player-vocabulary-allow.tsv`, one row per site:

    path <TAB> term <TAB> the exact text, escaped <TAB> why the word stays

Keyed by the TEXT, not the line number — lanes move lines all day and a line-number key
rots into a blanket ignore inside a day. Keying on the text is also what gives the
ratchet its second edge: **a row whose text no longer appears at that path FAILS.**
Fixing a string retires its exemption instead of leaving a permission slip behind.

═══ CAN IT GO RED ═════════════════════════════════════════════════════════════════
`--self-test` drives the classifier over inputs it MUST catch and inputs it MUST NOT.
The gate's headline is a NEGATIVE assertion (`no banned word reached player copy`),
which is exactly the shape that passes when the reader is broken or the file set is
empty — so the sweep also asserts a FLOOR: `MIN_SURFACES` files and `MIN_UNITS` text
units, or it fails as broken rather than passing as clean.

⚠ IT SWEEPS THE INDEX, NOT THE WORKING TREE. `git ls-files` is the file set, so a NEW
file you have not `git add`ed is INVISIBLE to a local run. In CI that is correct and
total; locally, `git add` first, then sweep.

Usage:  python3 scripts/check-player-vocabulary.py [--list PATH] [--self-test]
                                                   [--show-skipped]
Exit:   0 clean · 1 a banned word in player copy, a stale exemption row, or a sweep
        that fell through its own floor · 2 usage error

Runs in ~1s (no cargo), so it belongs in the CHEAP set of `scripts/local-gates.sh`.
That runner takes the command's SECOND token as a path to stat, and for
`python3 scripts/check-…py` that token is this file, so it needs no wrapper.
"""

from __future__ import annotations

import argparse
import importlib.util
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
VOCABULARY = REPO / "scripts" / "player-vocabulary.tsv"
DEFAULT_LIST = REPO / "scripts" / "player-vocabulary-allow.tsv"

# ── the readers ────────────────────────────────────────────────────────────────────
# `check-player-copy-punctuation.py` already solved the hard half of this problem: a
# Rust scanner that never yields a comment, `#[cfg(test)]` ranges, an operator-sink
# rule, and — the one that matters most here — an HTML reader that goes ONE LEVEL DOWN
# into a Rust literal holding a page, so `class="receipt"` is a tag attribute and not
# prose. Reimplementing any of that would be a second reader of the same tree with its
# own bugs; this imports it. (The filename has dashes, hence the loader dance.)
_spec = importlib.util.spec_from_file_location(
    "player_copy_punctuation", REPO / "scripts" / "check-player-copy-punctuation.py"
)
if _spec is None or _spec.loader is None:  # pragma: no cover - a missing sibling is fatal
    print("scripts/check-player-copy-punctuation.py is missing; this gate reads it", file=sys.stderr)
    sys.exit(2)
pcp = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pcp)

# ── SCOPE ──────────────────────────────────────────────────────────────────────────
# Every entry is a `dreggnet-web` module, keyed by the ROUTES it renders. The route is
# the load-bearing half: it is what a future reader checks a NEW module against.
PLAYER_SURFACES: dict[str, str] = {
    "lib.rs": "`/`, `/offerings`, `/session/{id}`, `/offerings/{key}/session/{id}` — the landing, the catalog and every offering session page",
    "you.rs": "`/you`, `/me` — a player's own tables, matches, runs and landed moves",
    "descent.rs": "`/descent`, `/descent/leaderboard`, `/descent/run/{id}`, `/descent/native/run/{id}` — the board and the shared run cards",
    "descent_card.rs": "the run picture painted onto `/descent/native/run/{id}`",
    "descent_play.rs": "`/descent/play` and `?engine=browser` — the flagship played in a tab",
    "descent_door.rs": "`/descent/play/run` — the per-browser door that opens or resumes a player's own run",
    "descent_attest.rs": "the signature block a run card shows",
    "game_session.rs": "the session rail and the privacy sentence on every offering session page",
    "guide.rs": "`/guide`, `/how-to-play` — the page this rule started on",
    "seed_identity.rs": "`/identity` and the claim/restore ceremony",
    "identity_link.rs": "`/identity/link` — the cross-platform link ceremony",
    "identity_unlink.rs": "`/identity/unlink` — the un-link door",
    "device_key.rs": "`/identity/device` — the browser-signing enrolment page",
    "act_signed.rs": "the banner a signed turn lands with",
    "table_door.rs": "the front door every seat-locked two-player table is minted from",
    "table_seats.rs": "the seat lock's refusals and its lobby copy",
    "automatafl_web.rs": "`/automatafl` — the table, the rules panel and the spectator view",
    "tug_web.rs": "`/tug` — the table, the rules panel and the spectator view",
    "telegram_miniapp.rs": "`/tg/**` — the same games inside Telegram",
    "discord_activity.rs": "`/da/**` — the same games inside a Discord Activity",
    "tg_link_page.rs": "`/tg/link` — the page a human signs the link claim on",
    "attribution.rs": "the chip and legend the board, `/you` and the identity pages all render",
    "crown_ingest.rs": "`/crown` — the re-verified crown board",
    "sprite.rs": "`/gallery` — the generated art shelf",
    "overlay.rs": "`/overlay` — the spectator vote overlay",
    "crowd_round.rs": "the crowd-stream round copy the overlay and the stream chat read",
    "chutes_consent.rs": "the consent and provenance fragments a player is shown before a narrated turn",
    "fhegg_operation.rs": None,  # see NOT_PLAYER_SURFACES
    "explorer.rs": None,
    "verified_settlement.rs": None,
    "metrics.rs": None,
    "audit.rs": None,
    "descent_store.rs": None,
    "web_identity_http.rs": None,
    "seated.rs": None,
}

# Named omissions. A gap nobody wrote down is indistinguishable from an oversight.
NOT_PLAYER_SURFACES: dict[str, str] = {
    "dreggnet-web/src/explorer.rs": (
        "`/explorer` browses a NODE's public read API. Its audience asked for `/api/receipts` by "
        "name and owns the word; the strings this gate would flag there are route path segments "
        "in a `match` (`[\"api\", \"receipts\"]`), not prose."
    ),
    "dreggnet-web/src/verified_settlement.rs": (
        "no route. A STARTUP install probe whose strings are refusals an operator reads in a boot "
        "log — its own `install_failure_advice` doc says `operator-facing` — and whose subject "
        "genuinely IS the executor."
    ),
    "dreggnet-web/src/fhegg_operation.rs": (
        "the JSON transport and discovery layer for hosted binary operations — it emits not one "
        "byte of markup (grep it for a tag). `/operations/{name}` is a machine-readable descriptor "
        "an SDK author reads, and its errors are `Json(OperationErrorWire)` bodies. The PAGE half "
        "of the same feature — the uploader form, the verbatim disclosure paragraph, the status "
        "line — is in `lib.rs`, which IS in scope."
    ),
    "dreggnet-web/src/metrics.rs": "`/metrics` is Prometheus exposition, read by a scraper.",
    "dreggnet-web/src/audit.rs": "one AuditEvent JSON line per interaction, for an operator.",
    "dreggnet-web/src/descent_store.rs": "durable persistence; carries no rendered prose.",
    "dreggnet-web/src/web_identity_http.rs": "cookie plumbing; carries no rendered prose.",
    "dreggnet-web/src/seated.rs": "a six-line `pub use`.",
    "dreggnet-web/src/bin, */tests, */benches, */examples": (
        "a binary is an operator entry point, and a golden PINS player copy rather than being it."
    ),
    "NOT YET SWEPT — a named residual, not a judgement": (
        "these render to a player and are NOT gated, measured 2026-07-26 with the rules above "
        "applied. `dreggnet-offerings`' `*_DISCLOSURE` consts are the sharpest one: "
        "`BinaryOperationDescriptor.disclosure` is documented as *the security disclosure every "
        "renderer must show verbatim* and `lib.rs` prints it into `<p class=operation-disclosure>` "
        "on the session page, which is where the audit's `merkle` on the session page comes from "
        "(dungeon.rs:155 and native_descent.rs:162, both behind a `private-*-operation` feature). "
        "They are SECURITY disclosures whose precision is the point, so rewriting them is its own "
        "pass with its own reviewer, not a line in this one. Also unswept: discord-bot 118 sites · "
        "dreggnet-catalog 76 · dreggnet-offerings 79 · site/**.html 232 · dreggnet-surfaces 48 · "
        "dreggnet-telegram 29 · deos-view 20 · dregg-mirror 8 · dregg-multiway-tug 15 · "
        "dregg-automatafl 6. Adding a root is one line above and then THE SWEEP IS THE WORK — do "
        "not add one without doing it, because a scope that is red on arrival teaches every lane "
        "to ignore this gate."
    ),
}

# ── THE FLOOR ──────────────────────────────────────────────────────────────────────
# ⚑ A BROKEN EXTRACTOR MUST NOT PASS BY FINDING NOTHING. The headline assertion here is
# negative, and every negative assertion in this repo has eventually been found passing
# on an empty premise ([[feedback-every-instrument-is-blind-to-the-next-wound]]). A
# sibling gate uses `MIN_COMPARED = 12` for exactly this. These are floors, not targets:
# both sit well under what a working sweep sees, so ordinary churn never trips them and
# a reader that silently stops reading always does.
MIN_SURFACES = 24
MIN_UNITS = 2_000

# ── R5: the machine-readable sinks ─────────────────────────────────────────────────
# A literal inside one of these is a field of a document a PROGRAM parses. The ingest
# API's `"detail"` string is addressed to whoever wrote the submitting client.
WIRE_SINKS: frozenset[str] = frozenset({"json!", "Json", "to_value", "from_value"})

# ── R6: a `{…}` span is a variable name, not a word ─────────────────────────────────
# `"{notice}{fragment}{receipt}"` names three locals. `{{` is an escaped brace and is
# left alone; a format spec (`{x:>4}`) goes with its name.
PLACEHOLDER = re.compile(r"(?<!\{)\{[^{}]*\}")


def shown(path: Path) -> str:
    """A path as a reader should see it: repo-relative when it is in the repo, else as given.

    `Path.relative_to` RAISES on a path outside the repo, and `--list /tmp/x.tsv` is exactly how
    this gate gets driven while somebody is proving it can go red — a crash there teaches the
    reader that the gate is broken rather than that their tree is.
    """
    try:
        return str(path.resolve().relative_to(REPO))
    except ValueError:
        return str(path)


def vocabulary() -> list[tuple[str, str, str]]:
    """`(term, why, what to say instead)` for every row of the shared list."""
    rows: list[tuple[str, str, str]] = []
    for lineno, raw in enumerate(VOCABULARY.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        parts = raw.rstrip("\n").split("\t")
        if len(parts) != 3 or not all(p.strip() for p in parts):
            print(
                f"{shown(VOCABULARY)}:{lineno}: a row needs "
                f"`term<TAB>why<TAB>what to say instead`; got {len(parts)} field(s)",
                file=sys.stderr,
            )
            sys.exit(2)
        rows.append((parts[0].strip().lower(), parts[1].strip(), parts[2].strip()))
    return rows


def terms_in(text: str, terms: list[str]) -> list[str]:
    """Every banned term this unit uses, with R6 applied."""
    lower = PLACEHOLDER.sub(" ", text).lower()
    return [t for t in terms if t in lower]


def is_wire_sink(callees: list[str]) -> str | None:
    """R5: the machine-readable document this literal is a field of, or None."""
    for callee in callees:
        if callee.split("::")[-1] in WIRE_SINKS:
            return callee
    return None


def classifiable(rel: Path) -> bool:
    """Is this a `dreggnet-web` module the scope table is REQUIRED to have an opinion about?"""
    parts = rel.as_posix()
    if not parts.startswith("dreggnet-web/src/") or rel.suffix != ".rs":
        return False
    return not (
        "/bin/" in parts or "/tests/" in parts or "/benches/" in parts or "/examples/" in parts
    )


def in_scope(rel: Path) -> str | None:
    """The route(s) this file renders, or None if it is not a player surface."""
    if not classifiable(rel):
        return None
    return PLAYER_SURFACES.get(rel.name)


def unclassified_modules() -> tuple[list[str], list[str]]:
    """⚑ A NEW MODULE MUST NOT BE SILENTLY OUT OF SCOPE.

    `PLAYER_SURFACES` is a NAMED table, which makes an unlisted module default to
    *ungated* — a subtraction that emits no line, which is the shape this repo keeps
    getting bitten by ([[minted-gating-defaults-to-silence]]). `dreggnet-web` grows a
    route module every few days (one landed in this tree WHILE this gate was being
    written), so the scope table is itself put under a ratchet: an unlisted module is a
    FAILURE, and so is a table row naming a file that no longer exists. Both force a
    decision — in scope with its route, or out with a reason — rather than silence.
    """
    on_disk = {rel.name for rel in pcp.tracked_files() if classifiable(rel)}
    missing = sorted(on_disk - set(PLAYER_SURFACES))
    stale = sorted(set(PLAYER_SURFACES) - on_disk)
    return missing, stale


def findings(terms: list[str]) -> tuple[list[dict], dict[str, int], int, int]:
    """Every banned word in player copy that no rule subtracts, plus the tallies."""
    hits: list[dict] = []
    skipped = {
        "R1/R2 comment-or-test": 0,
        "R3 operator sink": 0,
        "R5 machine-readable body": 0,
    }
    surfaces = 0
    units = 0

    for rel in pcp.tracked_files():
        if in_scope(rel) is None:
            continue
        surfaces += 1
        try:
            src = (REPO / rel).read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue

        test_ranges = pcp.rust_test_ranges(src)
        for lit in pcp.rust_string_literals(src):
            if any(a <= lit["pos"] < b for a, b in test_ranges):
                skipped["R1/R2 comment-or-test"] += 1
                continue
            if pcp.is_operator_sink(lit["callees"]) is not None:
                skipped["R3 operator sink"] += 1
                continue
            if is_wire_sink(lit["callees"]) is not None:
                skipped["R5 machine-readable body"] += 1
                continue
            decoded, back = pcp.rust_unescape(lit["text"])
            # R1 one level down: a literal may CONTAIN a page, a stylesheet or a script,
            # whose comments, tags and class names are no more player copy than a `//` is.
            for unit in pcp.nested_units(decoded):
                units += 1
                if unit.get("op"):
                    skipped["R3 operator sink"] += 1
                    continue
                found = terms_in(unit["text"], terms)
                if not found:
                    continue
                raw = lit["pos"] + 1 + back[min(unit["pos"], len(back) - 1)]
                hits.append(
                    {
                        "path": rel.as_posix(),
                        "line": src.count("\n", 0, raw) + 1,
                        "terms": found,
                        "text": unit["text"].strip(),
                    }
                )
    return hits, skipped, surfaces, units


# ══ the exemption ratchet ══════════════════════════════════════════════════════════
def read_allowlist(path: Path) -> list[tuple[str, str, str, str, int]]:
    """Rows as `(path, term, escaped text, reason, FILE line)` — the line so a stale row is citable."""
    rows: list[tuple[str, str, str, str, int]] = []
    if not path.exists():
        return rows
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.rstrip("\n")
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 4:
            print(
                f"{path}:{lineno}: a row needs 4 tab-separated fields "
                f"(path, term, escaped text, reason); got {len(parts)}",
                file=sys.stderr,
            )
            sys.exit(2)
        # ⚑ The text field is STRIPPED on both sides. A reported hit is already stripped, and a
        # row whose only difference from the live string is a trailing space would read as stale
        # forever — which every editor that trims trailing whitespace would cause on save.
        p, term, text, reason = (
            parts[0].strip(),
            parts[1].strip(),
            parts[2].strip(),
            "\t".join(parts[3:]).strip(),
        )
        if not reason:
            print(f"{path}:{lineno}: an exemption row with no reason is a mute", file=sys.stderr)
            sys.exit(2)
        rows.append((p, term.lower(), text, reason, lineno))
    return rows


# ══ can it go red ══════════════════════════════════════════════════════════════════
SELF_TEST_RUST = r'''
//! A doc comment about the executor — invisible to this gate.
/* a block comment naming a receipt — also invisible */
fn page() -> String {
    tracing::warn!("the executor refused the leg");
    eprintln!("no-cheat gate not installed");
    assert!(ok, "the executor must decide");
    let _wire = Json(serde_json::json!({
        "detail": "the stable move tape could not address this executor",
    }));
    let _css = "<style>.receipt{color:red}/* THE RECEIPT STRIP — a design note */</style>";
    let _slots = format!("{notice}{fragment}{receipt}");
    let _markup = "<p class=\"receipt ok\"><span class=\"label\">verified by re-execution</span></p>";
    format!("<p class=\"prose\">Your receipts are listed below.</p>")
}
#[cfg(test)]
mod tests {
    #[test]
    fn pins() { assert_eq!(render(), "<h2>Your receipts</h2>"); }
}
'''


def self_test() -> int:
    """Drive the classifier at things it MUST catch and things it MUST NOT."""
    ok = True

    def check(cond: bool, msg: str) -> None:
        nonlocal ok
        print(("  ok    " if cond else "  RED   ") + msg)
        ok = ok and cond

    print("self-test — the shared list")
    rows = vocabulary()
    terms = [t for t, _, _ in rows]
    check(len(rows) >= 15, f"scripts/player-vocabulary.tsv parses to {len(rows)} rows (>= 15)")
    check(
        all(t in terms for t in ("executor", "receipt", "merkle", "no-cheat", "◈")),
        "the sweep's headline terms are all present",
    )
    check(
        all(why and instead for _, why, instead in rows),
        "every row carries a reason AND a replacement strategy",
    )

    print("self-test — the reader")
    lits = pcp.rust_string_literals(SELF_TEST_RUST)
    trs = pcp.rust_test_ranges(SELF_TEST_RUST)
    kept: list[str] = []
    dropped: list[str] = []
    for lit in lits:
        target = kept
        if (
            any(a <= lit["pos"] < b for a, b in trs)
            or pcp.is_operator_sink(lit["callees"])
            or is_wire_sink(lit["callees"])
        ):
            target = dropped
        decoded, _ = pcp.rust_unescape(lit["text"])
        for unit in pcp.nested_units(decoded):
            if unit.get("op"):
                dropped.append(unit["text"])
                continue
            (dropped if target is dropped else kept).append(unit["text"])

    def caught(needle: str) -> bool:
        return any(needle in t and terms_in(t, terms) for t in kept)

    def subtracted(needle: str) -> bool:
        return not any(needle in t and terms_in(t, terms) for t in kept)

    check(caught("Your receipts are listed below"), "CATCHES a banned word in page prose")
    check(subtracted("doc comment about the executor"), "R1 never even produces a comment")
    check(subtracted("block comment naming a receipt"), "R1 covers block comments too")
    check(subtracted("<h2>Your receipts</h2>"), "R2 drops a `#[cfg(test)]` golden")
    check(subtracted("the executor refused the leg"), "R3 drops a `tracing::warn!` literal")
    check(subtracted("no-cheat gate not installed"), "R3 drops an `eprintln!` literal")
    check(subtracted("the executor must decide"), "R3 drops an `assert!` message")
    check(
        subtracted("could not address this executor"),
        "R5 drops a `serde_json::json!` field an ingest CLIENT reads",
    )
    check(
        terms_in("{notice}{fragment}{receipt}", terms) == [],
        "R6 reads `{receipt}` as a variable name, not the word",
    )
    check(
        terms_in("Your {kind} receipt{s} landed", terms) == ["receipt"],
        "…and still sees a real word standing beside placeholders",
    )
    check(
        subtracted("THE RECEIPT STRIP"),
        "a CSS design comment inside a Rust literal is not player copy",
    )
    check(
        subtracted(".receipt{color:red}"),
        "…and neither is the CSS class it styles",
    )
    check(
        subtracted('class="receipt ok"'),
        "an HTML CLASS ATTRIBUTE is not prose — the exact reason the whole document was never checkable",
    )
    check(
        any("verified by re-execution" in t for t in kept),
        "…while the TEXT NODE inside that same markup is still read",
    )

    print("self-test — scope")
    check(
        in_scope(Path("dreggnet-web/src/you.rs")) is not None,
        "`/you` is in scope",
    )
    check(
        in_scope(Path("dreggnet-web/src/explorer.rs")) is None,
        "the chain explorer is a DEVELOPER instrument and is out",
    )
    check(
        in_scope(Path("dreggnet-web/src/bin/serve.rs")) is None,
        "an operator binary is out",
    )
    check(
        in_scope(Path("dreggnet-web/tests/server.rs")) is None,
        "a test is out (R2 at the path level)",
    )
    check(
        len([v for v in PLAYER_SURFACES.values() if v]) >= MIN_SURFACES,
        f"the named route table covers >= {MIN_SURFACES} modules",
    )
    check(
        all(
            f"dreggnet-web/src/{name}" in NOT_PLAYER_SURFACES
            for name, route in PLAYER_SURFACES.items()
            if route is None
        ),
        "every module marked out-of-scope has a written reason",
    )
    # ⚑ The scope table's OWN ratchet, shown to bite: hide a module the tree really has and the
    # sweep must report it, or a new route page is ungated the day it lands.
    real_surfaces = dict(PLAYER_SURFACES)
    try:
        PLAYER_SURFACES.pop("you.rs", None)
        missing, _ = unclassified_modules()
    finally:
        PLAYER_SURFACES.clear()
        PLAYER_SURFACES.update(real_surfaces)
    check("you.rs" in missing, f"an UNLISTED module is reported, not silently skipped — {missing}")
    live_missing, live_stale = unclassified_modules()
    check(
        not live_missing and not live_stale,
        f"…and the table currently matches the tree (missing {live_missing}, stale {live_stale})",
    )

    print("self-test — the floor")
    # ⚑ A FLOOR NOBODY HAS SEEN BITE IS A COMMENT. Narrow the scope to one module and confirm the
    # sweep reports itself BROKEN rather than clean — the exact failure mode this gate is shaped
    # against, since `no banned word reached player copy` is true of a sweep that read nothing.
    real_surfaces = dict(PLAYER_SURFACES)
    try:
        PLAYER_SURFACES.clear()
        PLAYER_SURFACES["guide.rs"] = "only one module, on purpose"
        _, _, narrowed_surfaces, narrowed_units = findings([t for t, _, _ in rows])
    finally:
        PLAYER_SURFACES.clear()
        PLAYER_SURFACES.update(real_surfaces)
    check(
        narrowed_surfaces < MIN_SURFACES,
        f"a scope narrowed to one module falls under the {MIN_SURFACES}-surface floor "
        f"(saw {narrowed_surfaces})",
    )
    check(
        narrowed_units < MIN_UNITS,
        f"…and under the {MIN_UNITS}-unit floor (saw {narrowed_units})",
    )
    _, _, full_surfaces, full_units = findings([t for t, _, _ in rows])
    check(
        full_surfaces >= MIN_SURFACES and full_units >= MIN_UNITS,
        f"…while the real sweep clears both with room: {full_surfaces} surfaces, {full_units} units",
    )

    print("self-test — the ratchet")
    check(read_allowlist(DEFAULT_LIST) is not None, "the exemption list parses")

    print("\nself-test " + ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--list", type=Path, default=DEFAULT_LIST)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--show-skipped", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    rows = vocabulary()
    advice = {term: instead for term, _, instead in rows}
    hits, skipped, surfaces, units = findings([t for t, _, _ in rows])
    allow = read_allowlist(args.list)

    # A row matches a hit at the same path, on the same term, with the same text.
    remaining: list[dict] = []
    used: set[int] = set()
    for h in hits:
        text = pcp.escape(h["text"])
        for term in h["terms"]:
            idx = next(
                (
                    i
                    for i, (p, t, txt, _, _) in enumerate(allow)
                    if p == h["path"] and t == term and txt == text
                ),
                None,
            )
            if idx is None:
                remaining.append({**h, "term": term})
            else:
                used.add(idx)
    stale = [(i, r) for i, r in enumerate(allow) if i not in used]

    rc = 0
    missing, stale_rows = unclassified_modules()
    if missing or stale_rows:
        rc = 1
        if missing:
            print(
                f"\n⛔ {len(missing)} `dreggnet-web` module(s) the scope table has no opinion "
                "about.\n"
                "   An unlisted module is UNGATED, and an ungated module emits no line — which is\n"
                "   exactly how a new route page picks up `receipt` and nothing notices. Add each\n"
                "   to PLAYER_SURFACES with the ROUTE it renders, or set it to None and write the\n"
                "   reason in NOT_PLAYER_SURFACES.\n"
            )
            for name in missing:
                print(f"  dreggnet-web/src/{name}")
        if stale_rows:
            print(
                f"\n⛔ {len(stale_rows)} scope-table row(s) name a module that is no longer "
                "there.\n   Delete the row; a rule about a deleted file is noise.\n"
            )
            for name in stale_rows:
                print(f"  PLAYER_SURFACES[\"{name}\"]")
    # ⚑ THE FLOOR, CHECKED BEFORE THE VERDICT. `no banned word reached player copy` is true
    # of a sweep that read nothing at all.
    if surfaces < MIN_SURFACES or units < MIN_UNITS:
        rc = 1
        print(
            f"\n⛔ THE SWEEP FELL THROUGH ITS OWN FLOOR: {surfaces} surface(s) "
            f"(need {MIN_SURFACES}) and {units} text unit(s) (need {MIN_UNITS}).\n"
            "   This is a BROKEN READER reported as a broken reader, not a clean tree. A\n"
            "   negative assertion passes just as happily on an empty premise; that is why\n"
            "   this floor exists. Check `git ls-files` (an unstaged new file is invisible),\n"
            "   `PLAYER_SURFACES`, and that the punctuation gate's readers still import.\n"
        )
    if remaining:
        rc = 1
        print(
            f"\n⛔ {len(remaining)} use(s) of the project's PRIVATE VOCABULARY reached copy a\n"
            "   player reads. A newcomer would have to learn the word here, and that is the\n"
            "   finding this rule came from. The replacement has to be TRUE, not vaguer:\n"
            "   swapping a precise word for a fuzzy one is the same error, only quieter.\n"
            "   If the word is genuinely load-bearing, add it to\n"
            f"   {shown(args.list)} with the reason it stays.\n"
        )
        for h in sorted(remaining, key=lambda x: (x["path"], x["line"], x["term"])):
            excerpt = pcp.escape(h["text"])
            if len(excerpt) > 140:
                excerpt = excerpt[:137] + "..."
            print(f"  {h['path']}:{h['line']}  `{h['term']}`")
            print(f"      {excerpt}")
            print(f"      instead: {advice[h['term']]}")
    if stale:
        rc = 1
        print(
            f"\n⛔ {len(stale)} STALE exemption row(s) — the text is no longer there.\n"
            "   Fixing a string retires its exemption; delete the row.\n"
        )
        for _, (p, term, text, reason, lineno) in stale:
            print(f"  {shown(args.list)}:{lineno}  claims {p} still says `{term}` in")
            print(f"      {text[:120]}")
            print(f"      was allowed because: {reason}")

    if args.show_skipped or rc == 0:
        print(
            f"\nswept {surfaces} player-facing surfaces · {units} text units · "
            + " · ".join(f"{v} {k}" for k, v in skipped.items())
            + f" · {len(allow)} exempt"
        )
    if rc == 0:
        print("no private-vocabulary word reaches player copy")
    return rc


if __name__ == "__main__":
    sys.exit(main())
