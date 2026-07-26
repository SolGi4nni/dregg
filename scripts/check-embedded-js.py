#!/usr/bin/env python3
"""check-embedded-js.py — the JavaScript inside a Rust string literal has to PARSE.

═══ THE HOLE THIS CLOSES ══════════════════════════════════════════════════════════
`dreggnet-web/src/telegram_miniapp.rs` shipped a SyntaxError in `showVerification`,
born in `b8bbbf204` on 2026-07-22 and alive for four days:

    … + report.detail, report.verified ? 'ok' : 'refused');   // stray tail, unbalanced (
    report(message, …);                                        // calls the RESPONSE object

A syntax error is not local. It kills the parse of the WHOLE file, so every handler in
`TG_SHELL_SCRIPT` died with it — the catalog fetch, the BackButton, the offering list,
the submit interceptor. A player got a shell that rendered and then sat on
"Loading the catalog…" forever. `/tg` returned 200 the entire time, `cargo test` was
green the entire time, and every gate in `scripts/local-gates.sh` was green the entire
time, because NOTHING IN THIS REPO EVER PARSED THE JAVASCRIPT. It is a `&str` to rustc
and a `&str` to every reader downstream of rustc.

That is the whole finding. ~20 lines of `node --check` over the `r##"…"##` bundles
catches it instantly; the absence of those 20 lines is why four days of a dead Mini App
were invisible ([[feedback-a-documented-wound-is-not-a-detected-one]] — the wound was
DOCUMENTED in a commit message within the hour and would have been DETECTED by nothing).

═══ WHAT IT SWEEPS, AND WHY THAT IS THE HARD PART ═════════════════════════════════
A hand-list of bundle names rots the moment someone adds one, so the bundles are found
by reading the Rust. `scripts/check-player-copy-punctuation.py` already has the reader
that distinguishes a literal from a comment and carries the enclosing call chain; this
file imports it rather than growing a second, differently-wrong Rust lexer.

Three detectors select a literal, and their UNION is the sweep:

  D1  <script>  a literal holding a complete `<script …>BODY</script>`. The tag IS the
                claim that BODY is JavaScript, so there is nothing to guess.
  D2  shape     a literal whose CODE (comments and strings blanked) reads as a program:
                statement-initial `function` / `const` / `return` / `if` …, closer lines,
                arrows and DOM calls, scored against `SHAPE_FLOOR`. This is what makes
                the gate survive a bundle named `SHELL_BODY`.
  D3  name      the `const`/`static` binding it is assigned to ends in `_JS` / `_SCRIPT`
                (or IS `JS`/`SCRIPT`). A 12-line placeholder module scores below D2's
                floor and is still JavaScript; the repo's own naming convention says so.

D2 is the one that decides whether the gate rots, so it is tuned with margin and
`--list` prints every unit's score. What it must NOT do is fire on prose:
`dregg-mirror`'s `HELP` text says `DREGG_MIRROR_COMMITTEE; empty => structural` and a
naive "does it contain `=>`" test called it a program.

SUBTRACTIONS, each for a reason a reader can argue with:
  * `#[cfg(test)]` / `#[test]` / `#[tokio::test]` / `#[ignore]` item bodies — a golden
    that PINS a snippet is not a bundle. (Reused from the punctuation gate: `R2`.)
  * `tests/`, `benches/`, `examples/` paths, same reason.
  * a literal shorter than `MIN_UNIT_CHARS` — `"</script>"` alone is not a program.

═══ HOW IT PARSES ═════════════════════════════════════════════════════════════════
`node --check`, over stdin, one process per unit. Chosen because it is the parser the
BROWSER's engine ships (V8), so a construct it accepts is a construct that runs, and
because it needs no npm install, no vendored parser and no lockfile.

⚠ NODE IS REQUIRED, NOT OPTIONAL. If `node` is not on PATH this exits 2 with
UNAVAILABLE, and `scripts/local-gates.sh` prints that as a FAIL. It does NOT skip. A
gate that silently passes when its tool is missing is the exact disease this file
exists to treat — a green that means "I looked" and a green that means "I could not
look" have to be different colours. Set `DREGG_NODE` to point at a specific binary.

Module vs script: a unit with a top-level `import`/`export` is parsed with
`--input-type=module`, everything else as a classic script. The mode is printed with
every finding, because "Cannot use import statement outside a module" is a mode bug and
not a code bug and the reader needs to be able to tell.

⚠ `format!` BUNDLES. `deos-view/src/web.rs` builds its wasm bootstrap with `format!`, so
its literal holds `{{`, `}}` and `{pkg}` — none of which is JavaScript. When the
enclosing call is a format macro those are rewritten to `{`, `}` and `0`, PADDED TO THE
SAME WIDTH so every byte offset (and therefore every reported line) still lands.

═══ THE SHADOWING HALF ════════════════════════════════════════════════════════════
`dreggnet-web/src/discord_activity.rs` carried the SAME defect one class over:

    function report(message, cls) { … }          // the helper
    .then(function (report) { … report(m, c) })  // the parameter SHADOWS it, then calls it

That is a TypeError, not a SyntaxError, so `node --check` is blind to it — it kills only
the verify action rather than the file, which is why it survived in the twin while the
Telegram one was found. `--shadowing` (on by default) lints for it directly: a function
parameter whose name is also a function DECLARED in the same bundle, and which is then
CALLED inside that parameter's own body. See `shadowed_helpers` for what it does and
does not see; it is a scope-approximating lint, not a resolver, and the docstring there
says exactly where it goes blind.

═══ CAN IT GO RED ═════════════════════════════════════════════════════════════════
`--self-test` drives the whole pipeline — Rust reader, unit selection, node, shadow lint
— over inputs it MUST catch and inputs it MUST NOT, including the two REAL defects
verbatim. And the sweep asserts `MIN_UNITS`: a negative assertion over an empty set is
the failure mode of every gate in this repo's history, so an extractor that quietly
stops finding bundles FAILS instead of reporting clean.

Usage:  python3 scripts/check-embedded-js.py [--list] [--self-test] [--no-shadowing]
Exit:   0 clean · 1 a unit failed to parse / a shadowed helper / too few units
        · 2 node unavailable, or usage error

Runs in ~2s (no cargo), so it goes in the CHEAP set of `scripts/local-gates.sh`. It
needs no wrapper script there: that runner takes the command's SECOND token as a path to
stat, and for `python3 scripts/check-…py` that token is this file.
"""

from __future__ import annotations

import argparse
import bisect
import importlib.util
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# ── the Rust reader, borrowed rather than re-grown ─────────────────────────────────
# `check-player-copy-punctuation.py` already lexes Rust well enough to skip comments,
# read every raw/byte/escaped string form and carry the enclosing call chain, and it is
# tested by its own `--self-test`. A second lexer here would be a second thing to be
# wrong. The hyphen in the filename is why this is importlib and not `import`.
_PCP_PATH = REPO / "scripts" / "check-player-copy-punctuation.py"
_spec = importlib.util.spec_from_file_location("_pcp", _PCP_PATH)
if _spec is None or _spec.loader is None:  # pragma: no cover
    sys.exit(f"UNAVAILABLE: cannot load the Rust reader at {_PCP_PATH}")
pcp = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pcp)


# ── SCOPE ──────────────────────────────────────────────────────────────────────────
# Every root here is a crate that SHIPS JavaScript to a browser out of a Rust literal.
# The reason is the load-bearing half: it is what a future reader checks a new crate
# against. Widening this is the cheap, correct move — the gate costs ~2s.
JS_BEARING_SURFACES: dict[str, str] = {
    "dreggnet-web/src": "every web page: the Telegram shell, the Discord activity, /you, the overlay",
    "discord-bot/src": "the bot's own HTTP surface and its linking pages",
    "deos-view/src": "the DEOS card renders and their wasm bootstrap",
    "dreggnet-telegram/src": "the Telegram web-app surface",
    "dregg-mirror/src": "the mirror's object pages",
    "dreggnet-surfaces/src": "the shared surface renders",
    "starbridge-apps": "the first-room scenario pages",
    "starbridge-web/src": "the starbridge web surface",
    "grain-verify-wasm/src": "the in-browser grain verifier's glue",
}
# Named so the omission is a decision on the record rather than a gap.
NOT_JS_BEARING: dict[str, str] = {
    "extension/src": "real .ts files — tsc already parses them, and it is wired in package.json",
    "site": "real .html/.js files on disk, not Rust literals; the browser is their gate",
    "portal/dist": "build output, not a source of truth",
    "node": "explicitly out of bounds",
}
NON_SOURCE_DIR = re.compile(r"(^|/)(target|\.lake|\.git|node_modules|\.claude)/")
TEST_PATH = re.compile(r"(^|/)(tests|benches|examples)/")

# A literal below this is not a program worth a node process. `STRIP_CODE_SCRIPT` is
# ~230 chars of real JavaScript inside a <script>, so the floor sits well under it.
MIN_UNIT_CHARS = 60

# ⚑ THE ANTI-VACUITY FLOOR. A gate whose extractor breaks reports "0 problems in 0
# units" and reads as green forever. Measured on 2026-07-26 the sweep finds 22 units;
# this is set with room for a lane deleting a page, and NOT with room for the reader
# silently dying.
MIN_UNITS = 18

# D2's floors, both measured on the tree rather than guessed. The whole score
# distribution in scope on 2026-07-26:
#   real JS bundles          15, 18, 19, 19, 19, 24, 26, 40, 84, 94, 120, 120, 144, 169, 426
#   everything else          5 (a `CREATE TABLE` in `descent_store.rs`), 4, 3, 3, 2, …
# 6..14 is EMPTY, so `SHAPE_FLOOR = 8` sits in a real gap with margin on both sides.
SHAPE_FLOOR = 8
# The absolute floor misses a SHORT program — `deos-view` builds a three-line
# `obtain_js` fragment that is entirely `const … = …;` lines and scores 3. Density
# separates those from the SQL and the stylesheets cleanly: at `score >= 3` the only
# literals in scope with density >= 0.5 are those two fragments and a placeholder
# module, all three real JavaScript, and the densest non-program is 0.17. 0.75 is the
# threshold, chosen inside that empty band.
SHAPE_MIN_LINES = 3
SHAPE_DENSITY = 0.75


# ══ selection ══════════════════════════════════════════════════════════════════════
SCRIPT_BLOCK = re.compile(r"<script\b([^>]*)>(.*?)</script\s*>", re.S | re.I)
# A `<script src=…>` with no body, or an import-map / JSON block, is not a program.
SCRIPT_NOT_JS = re.compile(r"""\btype\s*=\s*["']?(?!text/javascript|module)[^"'\s>]+""", re.I)
CONST_BINDING = re.compile(
    r"(?:const|static)\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*&(?:'static\s+)?str\s*=\s*$"
)
NAMED_JS = re.compile(r"(^|_)(JS|SCRIPT)$")

# Statement-initial keywords, closer lines, and the two DOM roots. Each is worth one
# point; `_shape_score` counts LINES that match, not occurrences, so one dense line of
# minified code cannot carry a literal over the floor on its own.
STMT_LINE = re.compile(
    r"^\s*(?:(?:async\s+)?function\b|const\s|let\s|var\s|import\s|export\s|return\b"
    r"|if\s*\(|for\s*\(|while\s*\(|switch\s*\(|try\s*\{|catch\s*\(|throw\s|class\s"
    r"|await\s|document\.|window\.|new\s+[A-Z])"
)
CLOSER_LINE = re.compile(r"^\s*[\}\)\]][\}\)\],;]*\s*$")
ARROW_LINE = re.compile(r"=>")
ESM_TOPLEVEL = re.compile(r"^\s*(?:import\s|export\s|import\()", re.M)
FORMAT_MACRO = re.compile(r"^(format|write|writeln|print|println|eprint|eprintln|panic)!$")
FORMAT_HOLE = re.compile(r"\{[A-Za-z0-9_]*(?::[^{}]*)?\}")


def _blank_code(js: str) -> str:
    """The unit with its comments and string CONTENTS blanked, offsets preserved.

    Both the shape score and the shadow lint have to read CODE. A page's prose sitting
    in a JS string is not evidence of a program, and a `report(` inside a template
    literal is not a call.
    """
    out = pcp._blank_out(js, pcp.CSS_JS_COMMENT)
    out = pcp._blank_out(out, pcp.JS_LINE_COMMENT)
    chars = list(out)
    for lit in pcp.js_string_literals(out, 0):
        for k in range(lit["pos"], min(lit.get("end", lit["pos"]), len(chars))):
            if chars[k] != "\n":
                chars[k] = " "
    return "".join(chars)


def _shape_score(js: str) -> tuple[int, int]:
    """D2: how much of this literal reads as a program. `(score, non-blank code lines)`."""
    code = _blank_code(js)
    score, lines = 0, 0
    for line in code.split("\n"):
        if not line.strip():
            continue
        lines += 1
        if STMT_LINE.match(line) or CLOSER_LINE.match(line) or ARROW_LINE.search(line):
            score += 1
    return score, lines


def is_program(js: str) -> tuple[bool, int]:
    """D2's verdict, and the score behind it."""
    score, lines = _shape_score(js)
    if score >= SHAPE_FLOOR:
        return True, score
    if score >= SHAPE_MIN_LINES and lines and score / lines >= SHAPE_DENSITY:
        return True, score
    return False, score


def _format_unescape(js: str) -> str:
    """`{{`→`{ `, `}}`→` }`, `{pkg}`→`    0` — a format string's holes, WIDTH-PRESERVED.

    Padding rather than shortening is the whole trick: every reported line number is a
    count of newlines up to a byte offset, and a substitution that changes width moves
    every offset after it.

    ⚠ THE PAD GOES ON THE LEFT, and that is not cosmetic. `deos-view` writes
    `new CardWorld({slot}, {initial}n)` — the `n` is a BIGINT SUFFIX. Right-padding
    yields `0    n`, which is two tokens and a SyntaxError, and the gate reports a
    defect it invented itself. Left-padding yields `    0n`, which is what the browser
    sees. Same reason `}}` becomes ` }` rather than `} `.
    """
    out = js.replace("{{", "{ ").replace("}}", " }")
    return FORMAT_HOLE.sub(lambda m: "0".rjust(len(m.group(0))), out)


class Unit:
    """One parseable JavaScript program, and the way back to the Rust that holds it."""

    def __init__(self, path: Path, name: str, js: str, srcpos: list[int],
                 line_starts: list[int], why: str, score: int):
        self.path, self.name, self.js = path, name, js
        self._srcpos, self._line_starts = srcpos, line_starts
        self.why, self.score = why, score
        self.module = bool(ESM_TOPLEVEL.search(_blank_code(js)))

    def line(self, off: int) -> int:
        """The 1-based line IN THE RUST FILE of character `off` of this unit."""
        off = max(0, min(off, len(self._srcpos) - 1))
        return bisect.bisect_right(self._line_starts, self._srcpos[off])

    @property
    def rel(self) -> str:
        return self.path.relative_to(REPO).as_posix()


def _line_starts(src: str) -> list[int]:
    out = [0]
    for m in re.finditer("\n", src):
        out.append(m.end())
    return out


def units_in(path: Path, src: str) -> list[Unit]:
    """Every JavaScript unit this Rust file ships, by D1 ∪ D2 ∪ D3."""
    starts = _line_starts(src)
    test_ranges = pcp.rust_test_ranges(src)
    out: list[Unit] = []

    for lit in pcp.rust_string_literals(src):
        pos, text = lit["pos"], lit["text"]
        if lit["attr"] or len(text) < MIN_UNIT_CHARS:
            continue
        if any(a <= pos < b for a, b in test_ranges):  # R2
            continue

        # Where the literal's TEXT starts in the source, and the decoded form with a map
        # back. A raw string decodes to itself; an escaped one goes through the
        # punctuation gate's unescaper, which hands back index-for-index provenance.
        head = src[pos:pos + 16]
        m = re.match(r'(b?r)(#*)"', head)
        if m:
            text_start = pos + m.end()
            decoded, idx = text, list(range(len(text)))
        else:
            text_start = pos + 1
            decoded, idx = pcp.rust_unescape(text)
        if len(idx) < len(decoded):  # unescaper ran short; refuse to guess offsets
            continue
        srcpos = [text_start + i for i in idx[:len(decoded)]] + [text_start + len(text)]

        callees = lit.get("callees", [])
        if any(FORMAT_MACRO.match(c.split("::")[-1]) for c in callees) and (
            "{{" in decoded or "}}" in decoded or FORMAT_HOLE.search(decoded)
        ):
            decoded = _format_unescape(decoded)

        # D3 — the binding this literal is assigned to.
        binding = ""
        mb = CONST_BINDING.search(src[max(0, pos - 200):pos].rstrip().rstrip("=").rstrip() + " = ")
        if mb:
            binding = mb.group(1)
        named = bool(binding and NAMED_JS.search(binding))

        # D1 — complete <script>…</script> blocks inside the literal.
        blocks = [
            b for b in SCRIPT_BLOCK.finditer(decoded)
            if not SCRIPT_NOT_JS.search(b.group(1)) and len(b.group(2).strip()) >= MIN_UNIT_CHARS
        ]
        if blocks:
            for b in blocks:
                body = b.group(2)
                a = b.start(2)
                label = binding or f"<script> at line {bisect.bisect_right(starts, srcpos[a])}"
                out.append(Unit(path, label, body, srcpos[a:a + len(body) + 1], starts,
                                "D1 <script>", _shape_score(body)[0]))
            continue

        # D2/D3 — the literal itself is the program.
        shaped, score = is_program(decoded)
        if shaped or named:
            why = "D2+D3" if (shaped and named) else ("D2 shape" if shaped else "D3 name")
            label = binding or f"literal at line {bisect.bisect_right(starts, pos)}"
            out.append(Unit(path, label, decoded, srcpos, starts, why, score))
    return out


def sources() -> list[Path]:
    """Tracked Rust files under a JS-bearing surface.

    ⚠ THE INDEX, NOT THE WORKING TREE, the same as the punctuation gate: `git ls-files`
    is the file set, so a NEW file you have not `git add`ed is invisible to a local run.
    In CI that is exact (a checkout of HEAD has nothing untracked); locally, `git add`
    first, then sweep.
    """
    listing = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.rs"], cwd=REPO,
        capture_output=True, text=True, check=True,
    ).stdout
    out = []
    for name in listing.split("\0"):
        if not name or NON_SOURCE_DIR.search(name) or TEST_PATH.search(name):
            continue
        if not any(name.startswith(root) for root in JS_BEARING_SURFACES):
            continue
        out.append(REPO / name)
    return sorted(out)


def sweep() -> list[Unit]:
    out: list[Unit] = []
    for path in sources():
        try:
            src = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        out += units_in(path, src)
    return out


# ══ the parser ═════════════════════════════════════════════════════════════════════
NODE_LINE = re.compile(r"^\[stdin\]:(\d+)$", re.M)
NODE_ERROR = re.compile(r"^((?:\w+)?(?:Syntax|Reference|Type)Error|SyntaxError): (.*)$", re.M)


def _probe(node: str) -> str:
    """`""` if this binary can do the job, else why it cannot.

    RUN it, do not stat it. Both modes, because a binary that does `--check` and not
    `--input-type=module` would report 11 invented syntax errors, which is worse than
    reporting none.
    """
    try:
        ok = subprocess.run([node, "--check"], input="0;\n",
                            capture_output=True, text=True, timeout=60)
        if ok.returncode != 0:
            return f"`--check` rejected a trivially valid program: {ok.stderr.strip()[:100]}"
        esm = subprocess.run([node, "--input-type=module", "--check"],
                             input="export const k = 1;\n",
                             capture_output=True, text=True, timeout=60)
        if esm.returncode != 0:
            return f"`--input-type=module --check` failed: {esm.stderr.strip()[:100]}"
    except (OSError, subprocess.SubprocessError) as exc:
        return f"did not execute: {exc}"
    return ""


def node_binary() -> str:
    """The parser, or a LOUD exit. Never a skip.

    A gate whose tool is missing must not be able to report clean — that green means
    "I could not look", and it is indistinguishable from "I looked and it is fine" the
    moment it lands in a table. So this exits 2, and `local-gates.sh` renders a non-zero
    exit as FAIL.

    ⚠ `node` ON PATH IS NOT NECESSARILY NODE. Measured on persvati 2026-07-26: `node`
    resolves to `~/.bun/bin/node`, Bun's wrapper, which answers `--check` with
    "Missing script to execute. Bun's provided 'node' cli wrapper does not support a
    repl." — a NON-ZERO exit on every unit, i.e. 22 fabricated syntax errors, or with
    the probe above a flat UNAVAILABLE on a box that has a perfectly good `nodejs`
    v20.19.4 sitting next to it. So the candidates are tried IN ORDER and the first one
    that demonstrably parses both a script and a module wins.

    `DREGG_NODE`, if set, is the ONLY candidate: an explicit override that does not work
    is an error to report, never something to quietly route around.
    """
    override = os.environ.get("DREGG_NODE")
    if override:
        candidates = [override]
    else:
        candidates = [c for c in (shutil.which("node"), shutil.which("nodejs"),
                                  "/usr/bin/nodejs", "/usr/local/bin/node",
                                  "/opt/homebrew/bin/node") if c]
    tried: list[str] = []
    for cand in candidates:
        why = _probe(cand)
        if not why:
            return cand
        tried.append(f"    {cand}: {why}")
    sys.stderr.write(
        "UNAVAILABLE: no working `node --check` was found, so the embedded JavaScript\n"
        "  was NOT parsed. This is a FAILURE, not a skip: a gate that passes when its\n"
        "  parser is missing is how a four-day dead Mini App stayed invisible. A green\n"
        "  that means 'I could not look' has to be a different colour from a green that\n"
        "  means 'I looked'.\n"
        + ("  candidates tried:\n" + "\n".join(tried) + "\n" if tried
           else "  no `node` or `nodejs` on PATH at all.\n")
        + "  Install node (brew install node / apt install nodejs), or point DREGG_NODE\n"
          "  at a real one — note that Bun's `node` shim is NOT one.\n"
    )
    sys.exit(2)


def check_syntax(node: str, unit: Unit) -> tuple[int, str] | None:
    """`None` if it parses; `(offset_into_the_unit, message)` if it does not.

    An OFFSET and not a line, because several bundles in this repo are written with
    Rust `\\`-continuations (`OVERLAY_JS`) and decode to a SINGLE line — node truthfully
    reports line 1 for all of them, and only the column tells you which Rust line the
    error is really on. So node's caret row is read too, and the offset it produces goes
    back through `Unit.line`.
    """
    argv = [node]
    if unit.module:
        argv.append("--input-type=module")
    argv.append("--check")
    proc = subprocess.run(argv, input=unit.js, capture_output=True, text=True)
    if proc.returncode == 0:
        return None
    err = proc.stderr
    me = NODE_ERROR.search(err)
    msg = f"{me.group(1)}: {me.group(2)}" if me else err.strip().split("\n")[0]

    line, col = 1, 0
    rows = err.split("\n")
    for k, row in enumerate(rows):
        m = NODE_LINE.match(row)
        if not m:
            continue
        line = int(m.group(1))
        caret = rows[k + 2] if k + 2 < len(rows) else ""
        if caret.strip() and set(caret.strip()) == {"^"}:
            col = len(caret) - len(caret.lstrip())
        break

    off = 0
    for _ in range(line - 1):
        nxt = unit.js.find("\n", off)
        if nxt < 0:
            break
        off = nxt + 1
    return min(off + col, max(0, len(unit.js) - 1)), msg


# ══ the shadowing lint ═════════════════════════════════════════════════════════════
FUNC_DECL = re.compile(r"\bfunction\s*\*?\s+([A-Za-z_$][\w$]*)\s*\(")
FUNC_EXPR_BINDING = re.compile(
    r"\b(?:const|let|var)\s+([A-Za-z_$][\w$]*)\s*=\s*(?:async\s+)?"
    r"(?:function\b|\([^()]*\)\s*=>|[A-Za-z_$][\w$]*\s*=>)"
)
PARAM_SITE = re.compile(
    r"(?:\bfunction\s*\*?\s*(?:[A-Za-z_$][\w$]*\s*)?\(([^()]*)\)\s*\{)"
    r"|(?:\(([^()]*)\)\s*=>\s*\{)"
)
PLAIN_PARAM = re.compile(r"^[A-Za-z_$][\w$]*$")


def shadowed_helpers(js: str) -> list[tuple[int, str]]:
    """A parameter that shadows a function of the same name and is then CALLED.

    The `/da` twin, verbatim:

        function report(message, cls) { … }              // the helper
        .then(function (report) { … report(m, c) … })    // shadowed, then called

    `node --check` cannot see this — it is a well-formed program that throws at RUNTIME
    ("report is not a function"), which is why it killed only the verify action instead
    of the file, and why it survived in the twin for as long as the Telegram one did.

    ⚠ WHAT IT DOES NOT SEE, so nobody reads more into a green than is there:
      * DESTRUCTURED and defaulted parameters (`function ({report})`) — the parameter
        list must be plain identifiers or the site is skipped.
      * a call reached through anything but a bare `name(` — `report.call(…)`,
        `f = report; f(…)`, `obj[name](…)`.
      * a concise arrow body (`(report) => report(x)`), which has no `{` to brace-match.
      * a helper declared AFTER the shadowing site inside an inner scope, i.e. it
        approximates scope by "declared anywhere in this bundle" rather than resolving.
    It is a lint for one measured defect class, not a resolver. The syntax half above is
    the total one.
    """
    code = _blank_code(js)
    helpers = {m.group(1) for m in FUNC_DECL.finditer(code)}
    helpers |= {m.group(1) for m in FUNC_EXPR_BINDING.finditer(code)}
    if not helpers:
        return []

    out: list[tuple[int, str]] = []
    for m in PARAM_SITE.finditer(code):
        params = m.group(1) if m.group(1) is not None else m.group(2)
        names = [p.strip() for p in params.split(",") if p.strip()]
        if not names or not all(PLAIN_PARAM.match(p) for p in names):
            continue
        hit = [p for p in names if p in helpers]
        if not hit:
            continue
        # Brace-match this function's body. `code` has strings and comments blanked, so
        # a `{` here is a real block. PARAM_SITE ends ON the `{`, but be defensive: a
        # missing brace here would be a silent skip, not an exception.
        open_at = m.end() - 1
        if open_at >= len(code) or code[open_at] != "{":
            open_at = code.find("{", m.end() - 1)
            if open_at < 0:
                continue
        depth, k = 0, open_at
        while k < len(code):
            if code[k] == "{":
                depth += 1
            elif code[k] == "}":
                depth -= 1
                if depth == 0:
                    break
            k += 1
        body = code[open_at:k]
        for name in hit:
            call = re.search(r"(?<![.\w$])" + re.escape(name) + r"\s*\(", body)
            if call:
                out.append((open_at + call.start(),
                            f"parameter `{name}` shadows a function of the same name "
                            f"declared in this bundle, and is CALLED at this site"))
    return out


# ══ the run ════════════════════════════════════════════════════════════════════════
def run(show_list: bool, shadowing: bool) -> int:
    node = node_binary()
    units = sweep()

    if show_list:
        print(f"{'PATH:LINE':<52} {'WHY':<12} {'MODE':<7} {'SCORE':>5}  NAME")
        for u in sorted(units, key=lambda x: (x.rel, x.line(0))):
            loc = f"{u.rel}:{u.line(0)}"
            mode = "module" if u.module else "script"
            print(f"{loc:<52} {u.why:<12} {mode:<7} {u.score:>5}  {u.name}")

    findings: list[str] = []
    for u in units:
        bad = check_syntax(node, u)
        if bad:
            off, msg = bad
            findings.append(
                f"{u.rel}:{u.line(off)}  [{u.name}, parsed as "
                f"{'module' if u.module else 'script'}]\n      {msg}"
            )
        if shadowing:
            for off, msg in shadowed_helpers(u.js):
                findings.append(f"{u.rel}:{u.line(off)}  [{u.name}]\n      {msg}")

    # The RESOLVED path, not "node": which binary parsed is load-bearing information the
    # day a box's `node` turns out to be a Bun shim and the gate silently used another.
    print(f"\nparsed {len(units)} embedded JavaScript units with {node} --check "
          f"({sum(1 for u in units if u.module)} as modules)")

    rc = 0
    if len(units) < MIN_UNITS:
        print(f"\nFAIL: found only {len(units)} units, floor is {MIN_UNITS}.")
        print("  The extractor, not the tree, is the suspect: a negative assertion over")
        print("  an empty set passes forever. If a page really was deleted, lower")
        print("  MIN_UNITS in the same commit that deletes it.")
        rc = 1
    if findings:
        print(f"\n{len(findings)} embedded-JavaScript defect(s):\n")
        for f in findings:
            print(f"  {f}")
        print("\nA syntax error in one of these is NOT local: it kills the parse of the")
        print("whole bundle, so every handler in it dies and the page serves 200 with no")
        print("JavaScript running at all.")
        rc = 1
    if rc == 0:
        print("clean: every embedded JavaScript unit parses.")
    return rc


# ══ can it go red ══════════════════════════════════════════════════════════════════
# The two REAL defects, verbatim from the commits that fixed them, plus the shapes the
# gate must NOT fire on. `--self-test` is what keeps a negative assertion honest.
TG_BREAK = """(function () {
  function notice(message, cls) { root.replaceChildren(message); }
  function showVerification(path) {
    tgRequest(path).then(function (report) {
        var message = (report.verified ? 'Replay verified' : 'Replay refused') + ' · ' +
          report.turns + ' turns · ' + report.detail, report.verified ? 'ok' : 'refused');
        report(message, report.verified ? 'ok' : 'refused');
      })
      .catch(failure);
  }
})();
"""

DA_BREAK = """const root = document.getElementById("da-root");
function report(message, cls) {
  root.prepend(message);
}
function showVerification(path) {
  daRequest(path)
    .then(readJson)
    .then(function (report) {
      const message = (report.verified ? "Replay verified" : "Replay refused");
      report(message, report.verified ? "ok" : "refused");
    })
    .catch(failure);
}
"""

DA_FIXED = """const root = document.getElementById("da-root");
function report(message, cls) {
  root.prepend(message);
}
function showVerification(path) {
  daRequest(path)
    .then(readJson)
    .then(function (verdict) {
      const message = (verdict.verified ? "Replay verified" : "Replay refused");
      report(message, verdict.verified ? "ok" : "refused");
    })
    .catch(failure);
}
"""

MUST_NOT_SELECT = {
    "help text with a fat arrow": """\
dregg-mirror: the tier-`server` view of a dregg:// object, for readers with no extension.

  --bind ADDR        listen address        (DREGG_MIRROR_BIND, default 127.0.0.1:8791)
  --root DIR         object directory      (DREGG_MIRROR_ROOT, default ./mirror-objects)
  --committee KEYS   comma-separated trusted Ed25519 pubkeys (hex) for the anchored
                     quorum gate           (DREGG_MIRROR_COMMITTEE; empty => structural)
  --seed-demo        serve one in-memory object of each kind instead of reading --root
""",
    "player prose in a page fragment": """\
<p class="prose">Re-verification decides which runs appear here, and it is about the
moves: every row was re-executed under the rules and reached the end. Who played it is a
separate question, and this board answers it separately. If you want your own runs to
carry the stronger mark, <a href="/identity/device">let this browser sign for you</a>.</p>
""",
    "a stylesheet": """\
:root { --bg: #0b0d12; --fg: #e8ecf4; --accent: #7aa2f7; }
.notice { border-radius: 10px; padding: 0.7rem 0.9rem; }
.notice.refused { background: rgba(220, 80, 90, 0.12); }
.card + .card { margin-top: 0.8rem; }
""",
}


def self_test() -> int:
    node = node_binary()
    fails: list[str] = []

    def check(cond: bool, msg: str) -> None:
        if not cond:
            fails.append(msg)

    def one_unit(rust: str) -> list[Unit]:
        return units_in(REPO / "scripts" / "_self_test.rs", rust)

    # ── 1. the /tg SyntaxError, through the WHOLE pipeline: Rust reader → selection →
    #       node. This is the four-day defect verbatim.
    rust = f'const TG_SHELL_SCRIPT: &str = r##"{TG_BREAK}"##;\n'
    us = one_unit(rust)
    check(len(us) == 1, f"the /tg bundle should select as exactly 1 unit, got {len(us)}")
    if us:
        bad = check_syntax(node, us[0])
        check(bad is not None, "node --check did NOT reject the real /tg SyntaxError")
        if bad:
            check("Error" in bad[1], f"the /tg finding carries no error class: {bad[1]}")
            # It must NAME A LINE IN THE RUST FILE, not line 1 of a temp buffer. The
            # stray `, report.verified ? …)` tail is on line 6 of the fixture, which is
            # line 6 of the Rust (the literal opens on line 1).
            check(us[0].line(bad[0]) == 6,
                  f"the /tg break should map to Rust line 6, got {us[0].line(bad[0])}")

    # ── 1b. the same break through a `\\`-CONTINUED literal, which decodes to ONE line.
    #        node can only say "line 1"; the caret column is what recovers the real line,
    #        and `OVERLAY_JS` is written this way in the tree.
    joined = "".join(f"{l}\\\n" for l in TG_BREAK.split("\n"))
    us = one_unit(f'const TG_SHELL_SCRIPT: &str = "{joined}";\n')
    check(len(us) == 1, f"the \\-continued bundle should select as 1 unit, got {len(us)}")
    if us:
        bad = check_syntax(node, us[0])
        check(bad is not None, "the \\-continued /tg break was not caught")
        if bad:
            check(us[0].line(bad[0]) == 6,
                  f"a one-line decoded bundle must still name Rust line 6, got "
                  f"{us[0].line(bad[0])} — the caret column is not being read")

    # ── 2. the /da TypeError twin. node CANNOT see it — that is the point — and the
    #       shadow lint MUST.
    rust = f'const DA_APP_JS: &str = r##"{DA_BREAK}"##;\n'
    us = one_unit(rust)
    check(len(us) == 1, f"the /da bundle should select as exactly 1 unit, got {len(us)}")
    if us:
        check(check_syntax(node, us[0]) is None,
              "the /da twin is a well-formed program; if node rejects it the fixture is wrong")
        hits = shadowed_helpers(us[0].js)
        check(len(hits) == 1, f"the shadow lint should find exactly 1 /da hit, got {len(hits)}")
        if hits:
            check("report" in hits[0][1], f"the /da finding names the wrong symbol: {hits[0][1]}")

    # ── 3. the FIXED /da must be silent. A lint that fires on the repair is a lint the
    #       next lane deletes.
    check(shadowed_helpers(DA_FIXED) == [],
          "the shadow lint fires on the REPAIRED /da bundle (false positive)")

    # ── 4. a parameter that shadows a helper but is NEVER called is not this defect.
    check(shadowed_helpers(
        "function report(m) {}\nfoo(function (report) { return report.detail; });\n") == [],
        "the shadow lint fires on a shadowed-but-not-called parameter")

    # ── 5. the three shapes that must NOT be selected as programs.
    for label, text in MUST_NOT_SELECT.items():
        rust = f'const SOMETHING_ELSE: &str = r##"{text}"##;\n'
        us = one_unit(rust)
        check(us == [], f"{label} was selected as a JavaScript unit (score/lines "
                        f"{_shape_score(text)}, floors {SHAPE_FLOOR}/{SHAPE_DENSITY})")

    # ── 6. D1: a <script> body inside a page literal is found, and its line maps.
    page = ('<!doctype html>\n<title>x</title>\n<body>\n<div id=root></div>\n'
            '<script>\nfunction boot() {\n  document.getElementById("root").textContent = "hi";\n'
            '}\nboot();\n</script>\n</body>\n')
    rust = f'const PAGE: &str = r##"{page}"##;\n'
    us = one_unit(rust)
    check(len(us) == 1, f"D1 should find the <script> body, got {len(us)} units")
    if us:
        check(check_syntax(node, us[0]) is None, "the healthy <script> body did not parse")
        broken = page.replace("boot();", "boot(;")
        us2 = one_unit(f'const PAGE: &str = r##"{broken}"##;\n')
        check(bool(us2), "the broken page produced no unit")
        if us2:
            bad = check_syntax(node, us2[0])
            check(bad is not None, "a SyntaxError inside a <script> body was not caught")
            # `boot(;` is on line 9 of the page, hence line 9 of the Rust file — the
            # offset has to survive BOTH the literal offset and the <script> slice.
            if bad:
                check(us2[0].line(bad[0]) == 9,
                      f"a <script>-body error should map to Rust line 9, got "
                      f"{us2[0].line(bad[0])}")

    # ── 7. R2: a bundle inside a `#[cfg(test)]` body is a fixture, not a shipped page.
    rust = ('#[cfg(test)]\nmod tests {\n'
            f'    const BROKEN: &str = r##"{TG_BREAK}"##;\n}}\n')
    check(one_unit(rust) == [], "a bundle inside #[cfg(test)] was swept as shipped code")

    # ── 8. format! holes: the bundle parses AFTER substitution, and line numbers hold.
    fmt_rust = (
        'fn page(pkg: &str) -> String {\n    format!(\n'
        '        "import init from \'{pkg}\';\\n\\\n'
        'async function boot() {{\\n\\\n'
        '  const card = new CardWorld(0);\\n\\\n'
        '  window.__deosCard = card;\\n\\\n'
        '}}\\n"\n    )\n}\n'
    )
    us = one_unit(fmt_rust)
    check(len(us) == 1, f"the format! bundle should select as 1 unit, got {len(us)}")
    if us:
        check(check_syntax(node, us[0]) is None,
              "a format! bundle did not parse after hole substitution — "
              "check `_format_unescape` width preservation")

    # ── 9. module mode: a top-level `import` is parsed as a module, not a script.
    esm = 'import * as ed from "/da/static/noble-ed25519.js";\nexport const k = 1;\n'
    us = one_unit(f'const LINK_APP_JS: &str = r##"{esm}"##;\n')
    check(bool(us) and us[0].module, "a top-level `import` bundle was not parsed as a module")
    if us:
        check(check_syntax(node, us[0]) is None, "a valid ES module was rejected")

    # ── 10. the anti-vacuity floor is real: the live sweep must clear it.
    live = sweep()
    check(len(live) >= MIN_UNITS,
          f"the live sweep found {len(live)} units, under the MIN_UNITS floor of {MIN_UNITS}")

    for f in fails:
        print(f"  SELF-TEST FAIL: {f}")
    if fails:
        print(f"\n{len(fails)} self-test failure(s): the checker cannot be trusted to bite.")
        return 1
    print(f"self-test: 11 groups pass — the gate bites on both real defects "
          f"({len(live)} live units swept).")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--list", action="store_true", help="print every unit it found")
    ap.add_argument("--self-test", action="store_true", help="prove the checker can go red")
    ap.add_argument("--no-shadowing", action="store_true",
                    help="syntax only; skip the shadowed-helper lint")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    return run(args.list, not args.no_shadowing)


if __name__ == "__main__":
    sys.exit(main())
