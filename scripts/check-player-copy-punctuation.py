#!/usr/bin/env python3
"""check-player-copy-punctuation.py — an em-dash in a string a PLAYER reads.

═══ THE HOLE THIS CLOSES ══════════════════════════════════════════════════════════
On 2026-07-26 a pass took 1,370 em-dashes out of player-facing copy across 155 files
(`456070596`), classifying every site by the grammatical job the dash was doing:
` · ` for joiners, commas/parens for parentheticals, colons/semicolons/sentence-splits
for breaks. **Within hours the count had drifted back up** — 91 literals at hand-off,
96 on a re-check twenty minutes later, all of it new copy written by concurrent lanes
that had no way to know the convention existed.

That is the whole finding, and it is not about punctuation. A convention with no gate
is a snapshot, not a state ([[feedback-a-documented-wound-is-not-a-detected-one]]: a
wound that is documented and not DETECTED is not closed). This file is the detector.

═══ WHAT IS IN SCOPE, AND WHY THAT IS THE HARD PART ═══════════════════════════════
Getting scope wrong makes the gate worthless in BOTH directions. Too wide and it
fires on `tracing::warn!` lines no player will ever see, and the next lane silences
it. Too narrow and it passes while the Automatafl board says `—` in front of every
seat.

So scope is a NAMED LIST of surfaces, each with the reason it renders to a person
(`PLAYER_SURFACES` below), and everything else is out — including several crates that
are full of em-dashes and *should* be, named in `NOT_PLAYER_SURFACES` so the omission
is a decision on the record rather than a gap.

Within a surface, four rules SUBTRACT, each named in the failure output so a reader
can argue with the rule instead of with the gate:

  R1  comments        `//`, `///`, `/* */` — a doc comment is prose for a developer.
                      ⚑ AND ONE LEVEL DOWN. A Rust literal often CONTAINS a page, a
                      stylesheet or a script, and that content has comments of its own.
                      Reading such a literal as one flat unit reported 162 CSS and JS
                      design comments in `dreggnet-web` as player copy — and hid the
                      seven real sites among them. See `nested_units`.
  R2  test bodies     `#[cfg(test)]` / `#[test]` / `#[tokio::test]` / `#[ignore]`
                      items, and every `tests/`, `benches/`, `examples/` path. A
                      golden PINS the copy; it is not itself copy.
  R3  operator sinks  a literal with `tracing::*!` / `info!` / `warn!` / `error!` /
                      `eprintln!` / `println!` / `panic!` / `assert*!` / `.expect()`
                      anywhere in its enclosing-call chain. ~54 Rust strings were
                      deliberately skipped by the 07-26 pass for exactly this reason:
                      an operator log is not player copy and reads BETTER with a dash.
  R4  the glyph       a literal (or an HTML text node) whose entire content is `—`.
                      `unwrap_or_else(|| "—")` is a NO-VALUE TABLE CELL. That is a
                      glyph, not punctuation, and 35 of them are deliberate.

What is left is copy a person reads, and it must carry no em-dash. Anything that
genuinely must keep one goes in the allowlist, by name, with a reason.

═══ THE ALLOWLIST IS A RATCHET, NOT A MUTE ════════════════════════════════════════
`scripts/player-copy-punctuation-allow.tsv`, one row per exempt site:

    path <TAB> the exact text, escaped <TAB> why it keeps its dash

Keyed by the TEXT, not the line number — lanes move lines constantly, and a line
number key would rot into a blanket ignore within a day. Keying by text also gives
the ratchet its teeth in the other direction: a row whose text no longer appears at
that path FAILS. Fixing a string retires its exemption; it does not leave a permission
slip behind for the next dash to slip through.

═══ CAN IT GO RED ═════════════════════════════════════════════════════════════════
`--self-test` drives the classifier over inputs it MUST catch and inputs it MUST NOT,
so the checker is shown to bite without touching the tree
([[feedback-a-documented-wound-is-not-a-detected-one]] again: the negative assertion
`found.is_empty()` passes just as happily when the reader is broken).

⚠ IT SWEEPS THE INDEX, NOT THE WORKING TREE. `git ls-files` is the file set, so a NEW
file you have not `git add`ed is INVISIBLE to a local run. In CI that is correct and
total (a checkout of HEAD has nothing untracked); locally, `git add` first, then sweep.
Both canaries used to prove this gate bites were written into TRACKED files for exactly
that reason.

Usage:  python3 scripts/check-player-copy-punctuation.py [--list PATH] [--self-test]
                                                        [--show-skipped]
Exit:   0 clean · 1 a dash in player copy, or a stale allowlist row · 2 usage error

Runs in ~1s (no cargo), so it goes in the CHEAP set of `scripts/local-gates.sh`. It
needs no wrapper script there: that runner takes the command's SECOND token as a path
to stat, and for `python3 scripts/check-…py` that token is this file. Only a `cargo
test` row needs the `scripts/check-effect-payload-shape.sh` treatment.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_LIST = REPO / "scripts" / "player-copy-punctuation-allow.tsv"

EM = "—"  # EM DASH
# Every other way this repo spells U+2014. A reader sees the same character from all of
# them, so the gate has to. The `—` forms are not theoretical: `deos-view/src/web.rs`
# emits JavaScript from a Rust string, and a `\\u2014` in that Rust source reaches the
# browser as a real em-dash while looking like nothing at all in a grep.
MDASH_ENTITIES = ("&mdash;", "&#8212;", "&#x2014;", "\\u2014", "\\u{2014}", "\\x{2014}")

# ── SCOPE ──────────────────────────────────────────────────────────────────────────
# Every root here renders strings to a person. The reason is the load-bearing half:
# it is what a future reader checks a NEW crate against before adding it.
PLAYER_SURFACES: dict[str, str] = {
    "deos-view/src": "the shared ViewNode walk — every Telegram and WeChat player reads its prose",
    "discord-bot/src": "Discord messages, embeds, button labels and command descriptions",
    "dregg-automatafl/src": "the Automatafl board and seat lines a player reads",
    "dregg-mirror/src": "the mirror's trust banner and object pages",
    "dregg-multiway-tug/src": "the Tug board a player reads",
    "dreggnet-catalog/src": "offering titles and descriptors, on every shelf on every channel",
    "dreggnet-game-board/src": "the ranked proof board's universe titles and fold refusals",
    "dreggnet-offerings/src": "offering copy, session prose and refusal text",
    "dreggnet-surfaces/src": "the surface renders (inventory, guild, quest, tavern, trade…)",
    "dreggnet-telegram/src": "Telegram messages and command help",
    "dreggnet-web/src": "the web pages",
    "starbridge-apps/first-room/src": "the first-room scenario's player copy",
    "site": "the static pages, served as-is",
}

# Named omissions. A gap nobody wrote down is indistinguishable from an oversight.
NOT_PLAYER_SURFACES: dict[str, str] = {
    "dregg-drive/src": (
        "a developer DRIVER. It prints a surface exactly as that surface would send it, "
        "and annotates the transcript with `Frame::note` lines addressed to whoever is "
        "driving. The surface half is already gated at its own crate; the notes are QA "
        "output, not player copy."
    ),
    "node, cell, turn, circuit, metatheory": (
        "protocol and proof layers. What little string they carry is an operator log or "
        "an error a developer reads."
    ),
    "*/tests, */benches, */examples": (
        "a golden PINS player copy — it is not itself player copy. Gating it too would "
        "make every wording fix a two-sided edit for no added signal."
    ),
    "NOT YET SWEPT — a named residual, not a judgement": (
        "these carry player copy and are NOT gated, measured 2026-07-26 with the rules "
        "above applied: dreggnet-market 50 · attested-dm 46 · sdk 34 · dungeon-on-dregg 33 "
        "· wasm 33 · dreggnet-council 16 · dreggnet-doc 9 · webauth-core 5 · "
        "dreggnet-hermes 4 · starbridge-web-surface 3 · dreggnet-gear 2 · dreggnet-grain 2 "
        "· dreggnet-names 2 · interactive-fiction-demo 1. 244 sites. Adding a root here is "
        "one line above, and then the sweep is the work — do NOT add a root without doing "
        "it, because a scope that is red on arrival teaches every lane to ignore this gate."
    ),
}

# `site/dist` is a build output (gitignored); `site/**/*.md` is documentation.
SITE_EXTS = (".html",)

# ── R3: the operator sinks ─────────────────────────────────────────────────────────
OPERATOR_SINKS: frozenset[str] = frozenset(
    {
        # tracing / log — matched on the LAST path segment, so `tracing::warn!`,
        # `log::warn!` and a bare `warn!` are one rule.
        "trace!", "debug!", "info!", "warn!", "error!",
        # stdio
        "println!", "print!", "eprintln!", "eprint!",
        # aborts and assertions — a panic message is for whoever reads the crash
        "panic!", "unreachable!", "todo!", "unimplemented!",
        "assert!", "assert_eq!", "assert_ne!",
        "debug_assert!", "debug_assert_eq!", "debug_assert_ne!",
        "expect", "expect_err", "unwrap_err",
    }
)

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


# ══ the Rust reader ════════════════════════════════════════════════════════════════
def rust_string_literals(src: str) -> list[dict]:
    """Every string literal, with the chain of calls enclosing it.

    Comments (R1) never produce a literal — the scanner skips them outright. The
    `callees` list is what R3 reads: the identifier immediately before each still-open
    `(`/`[`/`{`, innermost last, so `tracing::warn!(x = 1, "…")` reports
    `["tracing::warn!"]` and a `format!` nested inside one reports both.
    """
    out: list[dict] = []
    i, n = 0, len(src)
    stack: list[tuple[str, str | None]] = []
    last_ident: str | None = None
    attr_depth = 0

    while i < n:
        c = src[i]
        if c == "/" and i + 1 < n and src[i + 1] == "/":  # R1 line comment
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "*":  # R1 block comment (nests)
            depth, j = 1, i + 2
            while j < n and depth:
                if src[j] == "/" and j + 1 < n and src[j + 1] == "*":
                    depth += 1
                    j += 2
                elif src[j] == "*" and j + 1 < n and src[j + 1] == "/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            i = j
            continue
        if c == "'":  # char literal or lifetime
            m = re.match(r"'(\\.|[^\\'])'", src[i:])
            i += m.end() if m else 1
            continue
        if c in "rb" and i + 1 < n:  # raw / byte string
            m = re.match(r'(b?r)(#*)"', src[i:])
            if m:
                term = '"' + m.group(2)
                bs = i + m.end()
                j = src.find(term, bs)
                if j < 0:
                    j = n
                out.append(
                    {
                        "pos": i,
                        "text": src[bs:j],
                        "callees": [a for (_, a) in stack if a],
                        "attr": attr_depth > 0,
                    }
                )
                i = j + len(term)
                last_ident = None
                continue
        if c == '"':
            j = i + 1
            bs = j
            while j < n:
                if src[j] == "\\":
                    j += 2
                    continue
                if src[j] == '"':
                    break
                j += 1
            out.append(
                {
                    "pos": i,
                    "text": src[bs:j],
                    "callees": [a for (_, a) in stack if a],
                    "attr": attr_depth > 0,
                }
            )
            i = j + 1
            last_ident = None
            continue
        if c == "#":  # attribute  #[ … ]  /  #![ … ]
            j = i + 1
            if j < n and src[j] == "!":
                j += 1
            if j < n and src[j] == "[":
                stack.append(("]", None))
                attr_depth += 1
                i = j + 1
                last_ident = None
                continue
            i += 1
            continue
        if c in "([{":
            stack.append(({"(": ")", "[": "]", "{": "}"}[c], last_ident))
            last_ident = None
            i += 1
            continue
        if c in ")]}":
            if stack:
                close, callee = stack.pop()
                if close == "]" and callee is None and attr_depth > 0:
                    attr_depth -= 1
            last_ident = None
            i += 1
            continue
        m = IDENT.match(src, i)
        if m:
            name, j = m.group(0), m.end()
            while j + 1 < n and src[j] == ":" and src[j + 1] == ":":
                m2 = IDENT.match(src, j + 2)
                if not m2:
                    break
                name += "::" + m2.group(0)
                j = m2.end()
            if j < n and src[j] == "!" and (j + 1 >= n or src[j + 1] != "="):
                name += "!"
                j += 1
            last_ident = name
            i = j
            continue
        if c not in " \t\n\r":
            last_ident = None
        i += 1
    return out


TEST_ATTR = re.compile(r"#\[(cfg\(test\)|test\]|tokio::test|ignore)")


def rust_test_ranges(src: str) -> list[tuple[int, int]]:
    """R2: byte ranges of `#[cfg(test)]`/`#[test]`/`#[tokio::test]`/`#[ignore]` items."""
    out = []
    for m in TEST_ATTR.finditer(src):
        j = src.find("{", m.end())
        if j < 0:
            continue
        depth, k = 0, j
        while k < len(src):
            ch = src[k]
            if ch == '"':
                k += 1
                while k < len(src):
                    if src[k] == "\\":
                        k += 2
                        continue
                    if src[k] == '"':
                        break
                    k += 1
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    break
            k += 1
        out.append((m.start(), k + 1))
    return out


def is_operator_sink(callees: list[str]) -> str | None:
    """R3: the sink that owns this literal, or None."""
    for callee in callees:
        leaf = callee.split("::")[-1]
        if leaf in OPERATOR_SINKS:
            return callee
    return None


RUST_ESCAPES = {"n": "\n", "t": "\t", "r": "\r", "0": "\0", "\\": "\\", '"': '"', "'": "'"}


def rust_unescape(text: str) -> tuple[str, list[int]]:
    """Decode a Rust literal body, carrying an index map back into the raw text.

    The map is what keeps a nested finding CITABLE: after `\\"` becomes `"` and a
    line-continuation collapses, an offset in the decoded page no longer means anything
    in the file, and a gate that points at the wrong line is a gate people learn to
    scroll past.
    """
    out: list[str] = []
    idx: list[int] = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c != "\\":
            out.append(c)
            idx.append(i)
            i += 1
            continue
        if i + 1 >= n:
            break
        nxt = text[i + 1]
        if nxt == "\n":  # line continuation: the newline AND the next line's indent go
            j = i + 2
            while j < n and text[j] in " \t":
                j += 1
            i = j
            continue
        if nxt == "u" and i + 2 < n and text[i + 2] == "{":
            j = text.find("}", i + 3)
            if j > 0:
                try:
                    out.append(chr(int(text[i + 3 : j], 16)))
                    idx.append(i)
                except ValueError:
                    pass
                i = j + 1
                continue
        if nxt == "x" and i + 3 < n:
            try:
                out.append(chr(int(text[i + 2 : i + 4], 16)))
                idx.append(i)
            except ValueError:
                pass
            i += 4
            continue
        out.append(RUST_ESCAPES.get(nxt, nxt))
        idx.append(i)
        i += 2
    idx.append(n)
    return "".join(out), idx


CSS_JS_COMMENT = re.compile(r"/\*.*?\*/", re.S)
# ⚠ A CLOSING TAG, not just a `<`. `i < arr.length` and `a < b` are everywhere in the
# script blobs these literals carry, and a looser test routed a 700-line JavaScript file
# into the HTML reader, which then reported every `//` comment in it as page prose.
IS_MARKUP = re.compile(r"</\s*[A-Za-z]|<!\s*(?:--|[A-Za-z])")
# Strong evidence the literal is a STYLESHEET or a SCRIPT rather than a sentence: a
# block comment, or a line comment next to real code. Deliberately conservative — a plain
# prose literal must never be routed here, because the nested readers only surface
# STRING literals and a sentence routed into them would vanish instead of being reported.
IS_STYLESHEET_OR_SCRIPT = re.compile(
    r"/\*.*?\*/|//[^\n]*\n(?=.*?(?:\bfunction\b|\bconst \b|\blet \b|\bvar \b|=>|;))", re.S
)


def nested_units(decoded: str) -> list[dict]:
    """R1 ONE LEVEL DOWN: a Rust literal that CONTAINS a page, a stylesheet or a script.

    ⚑ THE DEFECT THIS CLOSES, found by a lane using this gate as its worklist. A Rust
    string holding 20KB of `PAGE_CSS` is ONE literal, so a single em-dash in a single CSS
    comment reported the whole blob as player copy — 162 of 169 remaining dashes in
    `dreggnet-web` were hand-written CSS and JS DESIGN COMMENTS, which is precisely what
    R1 exists to exempt. A gate that hands a lane 120 developer comments to rewrite is a
    gate that lane learns to ignore, and it was ALSO hiding the seven real sites among
    them.

    So the readers this file already has get pointed one level down: markup goes through
    `html_units` (which knows about comments, `<style>`, `<script>` and attributes), and
    a bare stylesheet or script has its comments blanked and its lines read.
    """
    markup = IS_MARKUP.search(decoded)
    code = IS_STYLESHEET_OR_SCRIPT.search(decoded)
    if not markup and not code:
        return [{"pos": 0, "text": decoded}]

    # ⚑ MARKUP INSIDE A JS STRING DOES NOT MAKE THE LITERAL A PAGE. `LINK_APP_JS` is a
    # whole ES module that BUILDS markup in template literals, so a plain `</…>` test
    # called it HTML and read its code as page text. The question that actually decides it
    # is whether a tag appears OUTSIDE the string literals — in a page, `<div class=…>`
    # survives blanking the quoted attribute values; in a script, nothing is left.
    if markup and code:
        bare = list(decoded)
        for lit in js_string_literals(decoded, 0):
            for k in range(lit["pos"], min(lit.get("end", lit["pos"]), len(bare))):
                if bare[k] != "\n":
                    bare[k] = " "
        markup = IS_MARKUP.search("".join(bare))

    # Comments go FIRST, before either reader. A page here is usually a FRAGMENT — the
    # `<script>` opens in one `push_str` literal and its body is the next one — so
    # `html_units`' `<script>` handling never sees the pair, and the script's `//` lines
    # come back as page text. `/* */` and a guarded `//` mean the same thing in all three
    # languages, so blanking them up front is correct for whichever reader runs.
    body = _blank_out(decoded, CSS_JS_COMMENT)
    body = _blank_out(body, JS_LINE_COMMENT)

    if markup:
        return html_units(body)
    # A bare stylesheet or script — no `<script>` wrapper for `html_units` to find, so its
    # own reader is the right one: everything OUTSIDE a string in CSS or JS is code, and
    # `js_string_literals` flags `console.warn` for R3 on the way past.
    return js_string_literals(body, 0)


# ══ the HTML reader ════════════════════════════════════════════════════════════════
# A static page is player copy end to end, with two subtractions of its own: HTML
# comments and JS/CSS comments are R1, and a `<style>` block has no prose. A `<script>`
# block DOES — `site/grain/play.html` keeps a poem in a JS string — so scripts are read
# for their string literals rather than skipped.
HTML_COMMENT = re.compile(r"<!--.*?-->", re.S)
# `(?<![:/])` so `https://…` is a URL and not the start of a comment.
JS_LINE_COMMENT = re.compile(r"(?<![:/])//[^\n]*")
SCRIPT_BLOCK = re.compile(r"<script\b[^>]*>(.*?)</script\s*>", re.S | re.I)
STYLE_BLOCK = re.compile(r"<style\b[^>]*>.*?</style\s*>", re.S | re.I)
TAG = re.compile(r"<[^>]*>", re.S)
# Attributes a person READS. `title`/`alt`/`placeholder`/`aria-label` are rendered;
# `<meta name=description content=…>` is the search-result copy.
VISIBLE_ATTR = re.compile(
    r"""\b(title|alt|placeholder|aria-label|content|value|label)\s*=\s*("([^"]*)"|'([^']*)')""",
    re.I,
)


def _blank_out(src: str, pat: re.Pattern, group: int = 0) -> str:
    """Replace a match with same-length whitespace so byte offsets (and lines) hold."""
    out = list(src)
    for m in pat.finditer(src):
        a, b = m.span(group)
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "
    return "".join(out)


# A `/` opens a REGEX only where a value is expected. This is the standard heuristic
# and it matters here: `/https?:\/\/[^\s"'<>]+/` carries a `"`, a `'` and a backtick,
# every one of which would otherwise open a string.
REGEX_PRECEDERS = frozenset("(,=:[!&|?{};+-*%<>~^")
REGEX_KEYWORDS = frozenset({"return", "typeof", "instanceof", "in", "of", "new",
                            "delete", "void", "case", "do", "else", "yield", "await"})
# R3, in JavaScript. A `console.warn` on a page is the same thing a `tracing::warn!` is
# in Rust: a line for whoever opened the devtools, never for the reader.
JS_OPERATOR_SINK = re.compile(r"console\s*\.\s*(log|warn|error|info|debug|trace)\s*\($")


def js_string_literals(js: str, base: int) -> list[dict]:
    """Every JS string literal, lexed left to right.

    ⚠ THREE TRAPS, each one measured on this repo's own pages, and each the reason this
    is a scanner and not a regex:

      APOSTROPHES  a page's prose is full of `Couldn't` and `don't`. A regex over `'…'`
                   opens at that apostrophe and closes at the NEXT quote lines away, and
                   from there every quote in the file is off by one. A single- or
                   double-quoted JS string cannot hold a raw newline, so hitting one
                   proves the quote was never an opener: back off one character.
      REGEXES      `/https?:\\/\\/[^\\s"'<>]+/` and ``/`([^`]+)`/`` hold every quote
                   character there is. A `/` in value position is skipped as a regex.
      TEMPLATES    a `${…}` interpolation is an EXPRESSION, not copy. Its chunks are
                   emitted separately and the expression is lexed in turn, so the `'—'`
                   in ``${esc(x || '—')}`` is seen as the no-value glyph R4 knows about
                   rather than buried inside a 400-character blob of JavaScript.
    """
    out: list[dict] = []
    i, n = 0, len(js)
    prev_significant = ""

    def _is_regex_position() -> bool:
        if not prev_significant:
            return True
        if prev_significant[-1] in REGEX_PRECEDERS:
            return True
        m = re.search(r"[A-Za-z_$][A-Za-z0-9_$]*$", prev_significant)
        return bool(m) and m.group(0) in REGEX_KEYWORDS

    while i < n:
        c = js[i]
        if c == "/" and i + 1 < n and js[i + 1] == "/":  # R1
            j = js.find("\n", i)
            i = n if j < 0 else j
            continue
        if c == "/" and i + 1 < n and js[i + 1] == "*":  # R1
            j = js.find("*/", i + 2)
            i = n if j < 0 else j + 2
            continue
        if c == "/" and _is_regex_position():
            j, cls = i + 1, False
            while j < n:
                if js[j] == "\\":
                    j += 2
                    continue
                if js[j] == "\n":
                    break  # not a regex after all
                if js[j] == "[":
                    cls = True
                elif js[j] == "]":
                    cls = False
                elif js[j] == "/" and not cls:
                    j += 1
                    break
                j += 1
            i = j
            prev_significant = "/"
            continue
        if c in "'\"":
            j, bad = i + 1, False
            while j < n:
                if js[j] == "\\":
                    j += 2
                    continue
                if js[j] == "\n":
                    bad = True  # an apostrophe in prose, not a string opener
                    break
                if js[j] == c:
                    break
                j += 1
            if bad or j >= n:
                i += 1
                continue
            out.append(
                {
                    "pos": base + i + 1,
                    "end": base + j,
                    "text": js[i + 1 : j],
                    "op": bool(JS_OPERATOR_SINK.search(prev_significant)),
                }
            )
            i = j + 1
            prev_significant = "'"
            continue
        if c == "`":
            j = i + 1
            chunk_start = j
            while j < n:
                if js[j] == "\\":
                    j += 2
                    continue
                if js[j] == "`":
                    break
                if js[j] == "$" and j + 1 < n and js[j + 1] == "{":
                    out.append({"pos": base + chunk_start, "end": base + j,
                                "text": js[chunk_start:j]})
                    depth, k = 1, j + 2
                    expr_start = k
                    while k < n and depth:
                        ch = js[k]
                        if ch in "'\"`":  # skip a nested string wholesale
                            q, k2 = ch, k + 1
                            while k2 < n:
                                if js[k2] == "\\":
                                    k2 += 2
                                    continue
                                if js[k2] == q or (q != "`" and js[k2] == "\n"):
                                    break
                                k2 += 1
                            k = k2 + 1
                            continue
                        if ch == "{":
                            depth += 1
                        elif ch == "}":
                            depth -= 1
                        k += 1
                    out += js_string_literals(js[expr_start : k - 1], base + expr_start)
                    j = k
                    chunk_start = k
                    continue
                j += 1
            out.append({"pos": base + chunk_start, "end": base + j,
                        "text": js[chunk_start:j]})
            i = j + 1
            prev_significant = "`"
            continue
        if c not in " \t\n\r":
            prev_significant = (prev_significant + c)[-32:]
        i += 1
    return out


def html_units(src: str) -> list[dict]:
    """Player-visible units of a page.

    A unit is a TEXT NODE, not a line: `<b>committed on-chain</b><span>—</span>` puts
    a sentence and a no-value glyph cell on one line, and reading it as a line makes R4
    unable to see the glyph for what it is.
    """
    units: list[dict] = []

    for m in SCRIPT_BLOCK.finditer(src):
        units += js_string_literals(m.group(1), m.start(1))

    body = _blank_out(src, HTML_COMMENT)
    body = _blank_out(body, STYLE_BLOCK)
    body = _blank_out(body, SCRIPT_BLOCK)

    for m in TAG.finditer(body):  # attributes a person reads
        for a in VISIBLE_ATTR.finditer(m.group(0)):
            val = a.group(3) if a.group(3) is not None else a.group(4)
            units.append({"pos": m.start() + a.start(2), "text": val or ""})

    prev = 0  # text nodes: the gaps between tags
    spans: list[tuple[int, int]] = []
    for m in TAG.finditer(body):
        if m.start() > prev:
            spans.append((prev, m.start()))
        prev = m.end()
    if prev < len(body):
        spans.append((prev, len(body)))
    for a, b in spans:
        for node in re.finditer(r"\S[^\n]*", body[a:b]):
            units.append({"pos": a + node.start(), "text": node.group(0).rstrip()})
    return units


# ══ the sweep ══════════════════════════════════════════════════════════════════════
def carries_em_dash(text: str) -> bool:
    return EM in text or any(e in text for e in MDASH_ENTITIES)


def is_bare_glyph(text: str) -> bool:
    """R4: the whole unit is the glyph — a no-value cell, not punctuation."""
    stripped = text.strip()
    for e in MDASH_ENTITIES:
        stripped = stripped.replace(e, EM)
    return stripped == EM


def escape(text: str) -> str:
    return (
        text.replace("\\", "\\\\")
        .replace("\t", "\\t")
        .replace("\r", "\\r")
        .replace("\n", "\\n")
    )


def tracked_files() -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=REPO,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    return [Path(p) for p in out.split("\0") if p and (REPO / p).is_file()]


def in_scope(rel: Path) -> str | None:
    """The PLAYER_SURFACES root owning this file, or None."""
    parts = rel.as_posix()
    if "/tests/" in parts or "/benches/" in parts or "/examples/" in parts:
        return None  # R2
    if parts.startswith("site/"):
        if parts.startswith("site/dist/") or rel.suffix not in SITE_EXTS:
            return None
        return "site"
    if rel.suffix != ".rs":
        return None
    for root in PLAYER_SURFACES:
        if root != "site" and parts.startswith(root + "/"):
            return root
    return None


def findings() -> tuple[list[dict], dict[str, int]]:
    """Every em-dash in player copy that no rule subtracts, plus the rule tally."""
    hits: list[dict] = []
    skipped = {"R1/R2 comment-or-test": 0, "R3 operator sink": 0, "R4 bare glyph": 0}

    for rel in tracked_files():
        root = in_scope(rel)
        if root is None:
            continue
        try:
            src = (REPO / rel).read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        if not carries_em_dash(src):
            continue

        if root == "site":
            units = html_units(src)
            for u in units:
                if not carries_em_dash(u["text"]):
                    continue
                if is_bare_glyph(u["text"]):
                    skipped["R4 bare glyph"] += 1
                    continue
                hits.append(
                    {
                        "path": rel.as_posix(),
                        "line": src.count("\n", 0, u["pos"]) + 1,
                        "text": u["text"].strip(),
                    }
                )
            continue

        test_ranges = rust_test_ranges(src)
        for lit in rust_string_literals(src):
            if not carries_em_dash(lit["text"]):
                continue
            if any(a <= lit["pos"] < b for a, b in test_ranges):
                skipped["R1/R2 comment-or-test"] += 1
                continue
            sink = is_operator_sink(lit["callees"])
            if sink is not None:
                skipped["R3 operator sink"] += 1
                continue
            # R1 one level down: a literal may CONTAIN a page, a stylesheet or a script,
            # whose own comments are no more player copy than a `//` in this file is.
            decoded, back = rust_unescape(lit["text"])
            for unit in nested_units(decoded):
                if not carries_em_dash(unit["text"]):
                    continue
                if unit.get("op"):
                    skipped["R3 operator sink"] += 1
                    continue
                if is_bare_glyph(unit["text"]):
                    skipped["R4 bare glyph"] += 1
                    continue
                raw = lit["pos"] + 1 + back[min(unit["pos"], len(back) - 1)]
                hits.append(
                    {
                        "path": rel.as_posix(),
                        "line": src.count("\n", 0, raw) + 1,
                        "text": unit["text"],
                    }
                )
    return hits, skipped


# ══ the allowlist ══════════════════════════════════════════════════════════════════
def shown(path: Path) -> str:
    """A path as a reader should see it: repo-relative when it is in the repo, else as given.

    `Path.relative_to` RAISES on a path outside the repo, and `--list /tmp/x.tsv` is exactly
    how this gate gets driven while somebody is proving it can go red. A crash in the FAILURE
    PRINTER teaches the reader that the gate is broken rather than that their tree is — and it
    fires only on the failure path, so it survives every green run unnoticed.

    Ported from `check-player-vocabulary.py`, whose docstring already named this scenario. Two
    sibling gates, one of them carrying the fix and the other carrying the bug, is the
    twin-that-drifts shape this repo keeps finding; the helper is duplicated deliberately
    rather than shared, because a shared import between two standalone one-second scripts is
    its own coupling.
    """
    try:
        return str(path.resolve().relative_to(REPO))
    except ValueError:
        return str(path)


def read_allowlist(path: Path) -> list[tuple[str, str, str, int]]:
    """Rows as (path, escaped text, reason, FILE line) — the line so a stale row is citable."""
    rows = []
    if not path.exists():
        # ⚑ A MISSING ALLOWLIST IS A FAULT, NOT AN EMPTY ONE.
        #
        # This returned `[]` silently, and it cost 25.5 hours of a gate that was RED in every
        # clean checkout while its own red-proof reported green. The gate landed (b7f7f249e)
        # before the allowlist was tracked, so `git archive HEAD` had no file, `read_allowlist`
        # answered `[]`, and the sweep reported 19 violations and exited 1 — for anyone but the
        # author, whose working tree had it.
        #
        # The exemptions are not decoration: with an empty list this gate finds exactly the 19
        # sites the committed rows cover, one-for-one. So "no allowlist" and "nothing is exempt"
        # are the same state to the reader and completely different states in fact. Refuse.
        #
        # This is the repo's signature disease at its most embarrassing site — a gate written to
        # catch silent subtraction, silently subtracting its own configuration. Compare the
        # mirror-gates G2 canary fixture whose `pkg/.gitignore` contained `*` and ignored ITSELF,
        # so four files lived only on the author's disk and no clone ever had them.
        print(
            f"{path}: MISSING. The allowlist is not on disk. A clean checkout would run this "
            f"gate with zero exemptions and report every deliberate keep as a violation.\n"
            f"  This is a FAULT, not an empty allowlist: `git ls-files --error-unmatch {path}` "
            f"is the check, and a gate whose config is untracked is a gate nobody else can run.",
            file=sys.stderr,
        )
        raise SystemExit(2)
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.rstrip("\n")
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 3:
            print(
                f"{path}:{lineno}: a row needs 3 tab-separated fields "
                f"(path, escaped text, reason); got {len(parts)}",
                file=sys.stderr,
            )
            sys.exit(2)
        p, text, reason = parts[0].strip(), parts[1], "\t".join(parts[2:]).strip()
        if not reason:
            print(f"{path}:{lineno}: an allowlist row with no reason is a mute", file=sys.stderr)
            sys.exit(2)
        rows.append((p, text, reason, lineno))
    return rows


# ══ can it go red ══════════════════════════════════════════════════════════════════
SELF_TEST_RUST = '''
//! A doc comment — this dash must be invisible to the gate.
/* a block comment — also invisible */
fn player() -> String {
    tracing::warn!("the store did not answer — nothing was banked");
    eprintln!("boot — operator only");
    assert!(x, "invariant broke — operator only");
    let cell = value.unwrap_or_else(|| "—".to_string());
    format!("Seat A — OPEN")
}
#[cfg(test)]
mod tests {
    #[test]
    fn pins() { assert_eq!(render(), "Automatafl — turn 3"); }
}
'''

SELF_TEST_HTML = """
<!-- a comment — invisible -->
<style>.x{content:"—"}</style>
<script>
  // a JS comment — invisible
  const poem = 'Grains in a sealed box —';
  el.textContent = '—';
  const u = t.match(/https?:\\/\\/[^\\s"'<>]+/);
  const b = task.match(/`([^`]+)`/);
  el.innerHTML = `<b>caps ${esc(list.join(', ') || '—')}</b> — and a tail`;
  if (!ok) { el.innerHTML = `<p>Couldn't reach the sandbox — try again.</p>`; }
</script>
<p>The pool never held value — say so plainly.</p>
<b>committed on-chain</b><span id="c">—</span>
<img alt="a receipt — folded" src="x.png">
<span class="readout">—</span>
"""


def self_test() -> int:
    """Drive the classifier at things it MUST catch and things it MUST NOT."""
    ok = True

    def check(cond: bool, msg: str) -> None:
        nonlocal ok
        print(("  ok    " if cond else "  RED   ") + msg)
        ok = ok and cond

    print("self-test — the Rust reader")
    lits = rust_string_literals(SELF_TEST_RUST)
    trs = rust_test_ranges(SELF_TEST_RUST)
    kept, dropped = [], []
    for lit in lits:
        if not carries_em_dash(lit["text"]):
            continue
        if any(a <= lit["pos"] < b for a, b in trs) or is_operator_sink(lit["callees"]) or is_bare_glyph(lit["text"]):
            dropped.append(lit["text"])
        else:
            kept.append(lit["text"])
    check(any("Seat A" in t for t in kept), "CATCHES a player-facing `format!` literal")
    check(len(kept) == 1, f"catches ONLY that one — kept {kept}")
    check(any("did not answer" in t for t in dropped), "R3 drops a `tracing::warn!` literal")
    check(any("boot" in t for t in dropped), "R3 drops an `eprintln!` literal")
    check(any("invariant broke" in t for t in dropped), "R3 drops an `assert!` message")
    check(any(t == EM for t in dropped), "R4 drops the bare `—` no-value cell")
    check(any("turn 3" in t for t in dropped), "R2 drops a `#[cfg(test)]` golden")
    check(
        not any("doc comment" in t or "block comment" in t for t in kept + dropped),
        "R1 never even produces a comment as a literal",
    )

    print("self-test — the HTML reader")
    units = html_units(SELF_TEST_HTML)
    hkept, hdropped = [], []
    for u in units:
        if not carries_em_dash(u["text"]):
            continue
        (hdropped if is_bare_glyph(u["text"]) else hkept).append(u["text"].strip())
    check(any("never held value" in t for t in hkept), "CATCHES a page's prose")
    check(any("sealed box" in t for t in hkept), "CATCHES a JS string literal inside <script>")
    check(any("and a tail" in t for t in hkept), "CATCHES a template-literal chunk")
    check(
        any("Couldn't reach the sandbox" in t for t in hkept),
        "the APOSTROPHE trap: prose after a `don't` still lexes as itself",
    )
    check(any("a receipt" in t for t in hkept), "CATCHES an `alt=` a reader is served")
    check(any(t == EM for t in hdropped), "R4 drops a bare-glyph readout")
    check(
        sum(1 for t in hdropped if t == EM) >= 3,
        "R4 sees the glyph as its own TEXT NODE beside a sentence, and inside `${…}`"
        f" — got {sum(1 for t in hdropped if t == EM)}",
    )
    check(
        not any("https?" in t or "[^`]" in t for t in hkept + hdropped),
        "the REGEX trap: `/…/` holding every quote character does not open a string",
    )
    check(not any("a comment" in t for t in hkept + hdropped), "R1 drops an HTML comment")
    check(not any("a JS comment" in t for t in hkept + hdropped), "R1 drops a JS comment")
    check(not any("content:" in t for t in hkept + hdropped), "a <style> block is not prose")

    print("self-test — R1 one level down (a page/script inside a Rust literal)")
    # This whole section exists because the class it guards was SHIPPED: 162 of 169
    # remaining dashes in `dreggnet-web` were CSS and JS comments inside Rust strings,
    # reported as player copy, and one lane rewrote 14 design comments before the reader
    # was fixed. A rule that was wrong once gets a test, not a comment.
    page = (
        '<style>/* THE BOARD — a design note */ .x{color:red}</style>'
        '<p>The pool never held value — say so plainly.</p>'
    )
    script = (
        "// THE TABS — a design note\n"
        "const a = 1; /* another — note */\n"
        'console.warn("stub — vendor the real bundle");\n'
        'el.textContent = "—";\n'
        'el.innerHTML = `<b>Seat A — OPEN</b>`;\n'
    )
    prose = "Automatafl — turn {}"

    def surviving(text: str) -> list[str]:
        keep = []
        for u in nested_units(text):
            if carries_em_dash(u["text"]) and not u.get("op") and not is_bare_glyph(u["text"]):
                keep.append(u["text"].strip())
        return keep

    pk, sk, prk = surviving(page), surviving(script), surviving(prose)
    check(pk == ["The pool never held value — say so plainly."], f"a page: prose only, not its CSS comment — {pk}")
    check(any("Seat A" in t for t in sk), "a script: CATCHES markup it builds in a template literal")
    check(not any("design note" in t for t in sk), "a script: R1 drops its `//` and `/* */` comments")
    check(not any("vendor the real bundle" in t for t in sk), "a script: R3 drops `console.warn`")
    check(not any(t == EM for t in sk), "a script: R4 drops `textContent = \"—\"`")
    check(len(sk) == 1, f"a script: those four are ALL of it — {sk}")
    # The dangerous direction: a plain sentence must NEVER be routed into a reader that
    # only surfaces string literals, or it vanishes instead of being reported.
    check(prk == [prose], f"a plain prose literal is NOT treated as code — {prk}")
    check(
        surviving('let s = "a — b";') == ['let s = "a — b";'],
        "…and neither is a one-liner that merely looks code-ish without comments",
    )

    print("self-test — the ratchet")
    # ⚠ THIS ASSERTION USED TO CARRY `or not DEFAULT_LIST.exists()`, which made it PASS in the
    # one state it needed to catch: the allowlist missing. The gate then reported red on every
    # clean checkout for 25.5 hours while this line reported green. An escape clause in a
    # can-it-go-red check is not a check.
    check(
        DEFAULT_LIST.exists() and read_allowlist(DEFAULT_LIST) != [],
        "the allowlist is ON DISK and parses to a non-empty row set",
    )
    # And it must be TRACKED — on disk is not enough, since that is exactly the author-only
    # state that hid this. `git archive HEAD | tar -x` is what CI actually gets.
    tracked = subprocess.run(
        ["git", "ls-files", "--error-unmatch", str(DEFAULT_LIST)],
        cwd=REPO,
        capture_output=True,
    )
    check(tracked.returncode == 0, "the allowlist is TRACKED, so a clone has it too")
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

    hits, skipped = findings()
    allow = read_allowlist(args.list)

    # A row matches a hit at the same path with the same text. Both directions matter.
    remaining = []
    used = set()
    for h in hits:
        key = (h["path"], escape(h["text"]))
        idx = next(
            (i for i, (p, t, _, _) in enumerate(allow) if p == key[0] and t == key[1]),
            None,
        )
        if idx is None:
            remaining.append(h)
        else:
            used.add(idx)
    stale = [(i, r) for i, r in enumerate(allow) if i not in used]

    rc = 0
    if remaining:
        rc = 1
        print(
            f"\n⛔ {len(remaining)} em-dash(es) reached PLAYER-FACING copy.\n"
            "   ` · ` for a joiner, a comma or parens for a parenthetical, a colon or a\n"
            "   semicolon or two sentences for a break. If this one is deliberate, add it to\n"
            f"   {shown(args.list)} with the reason.\n"
        )
        for h in sorted(remaining, key=lambda x: (x["path"], x["line"])):
            excerpt = escape(h["text"])
            if len(excerpt) > 140:
                excerpt = excerpt[:137] + "..."
            print(f"  {h['path']}:{h['line']}")
            print(f"      {excerpt}")
    if stale:
        rc = 1
        print(
            f"\n⛔ {len(stale)} STALE allowlist row(s) — the text is no longer there.\n"
            "   Fixing a string retires its exemption; delete the row.\n"
        )
        for _, (p, t, reason, lineno) in stale:
            print(f"  {shown(args.list)}:{lineno}  claims {p} still says")
            print(f"      {t[:120]}")
            print(f"      was allowed because: {reason}")

    if args.show_skipped or rc == 0:
        print(
            f"\nswept {len(PLAYER_SURFACES)} player surfaces · "
            + " · ".join(f"{v} {k}" for k, v in skipped.items())
            + f" · {len(allow)} allowed"
        )
    if rc == 0:
        print("no em-dash reaches player copy")
    return rc


if __name__ == "__main__":
    sys.exit(main())
