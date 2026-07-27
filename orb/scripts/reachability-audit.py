#!/usr/bin/env python3
"""reachability-audit.py — which proofs actually reach the shipped binary.

drorb proves a great deal of Lean and ships one native artifact
(`crates/dataplane/src/main.rs` linked against `libdrorb.a`, cut by
`ffi/build-dataplane-lib.sh`).  Between those two facts sits a gap nobody could
previously measure: a module can be fully proven, build green, and still be
*unreachable* — no `@[export]`, or an `@[export]` no host code calls, or a call
site that only fires behind an environment gate nobody sets.

This script measures that gap mechanically, from source, with no build required.

It answers two questions for the whole tree:

  (a) EXPORT REACHABILITY.  For every `@[export sym]` in Lean: does a host call
      site exist (Rust or the C marshalling shims)?  Is that call site reachable
      from `fn main` of the deployed binary with NO condition on the path
      (DEFAULT-PATH), only under named env-var / CLI / match-arm conditions
      (GATED — the gates are named), or not at all (ORPHANED)?

  (b) MODULE REACHABILITY.  For every Lean module carrying theorems: does it
      contribute an `@[export]`, and is it inside the export-object closure that
      `ffi/build-dataplane-lib.sh` archives into `libdrorb.a`?  A module outside
      that closure is not in the shipped artifact at all, however proven.

METHOD, and its limits (stated so the numbers are not over-read)

  * The host call graph is built by brace-matched parsing of `crates/**/*.rs`
    and `crates/**/ffi/*.c` + `ffi/*.c` with comments stripped (doc comments
    quote export names constantly; leaving them in would fabricate call sites).
    Call resolution is by NAME and is deliberately OVER-approximate: any
    identifier matching a known function name counts as an edge.  Over-
    approximation is the safe direction here — it can only make something look
    MORE reachable, so an ORPHANED verdict is strong evidence, while a
    DEFAULT-PATH verdict is an upper bound on reachability.

  * "DEFAULT-PATH" means: an unconditional path exists from `fn main` to the
    call site.  It does NOT mean "runs on every request" — startup, subcommand
    dispatch and reactor selection all sit on such paths.  The per-request
    subset is reported separately (REQUEST-PATH) by re-running the same
    reachability from the connection handlers of each IO reactor.

  * Gates are extracted syntactically: `env::var("X")` read into a local or a
    helper that a guarding `if`/`match` mentions, `--flag` string literals in a
    guarding condition, and match-arm patterns.  A gate this misses shows up as
    DEFAULT-PATH, so the DEFAULT-PATH bucket is again an upper bound.

  * Lean theorem counts are a `^theorem|^lemma` declaration count, not a
    semantic weight.

Usage:
    scripts/reachability-audit.py [--root DIR] [--json OUT.json]
                                  [--markdown OUT.md] [--quiet]
                                  [--check-orphan-max N]

Exit status is 0 unless --check-orphan-max is given and exceeded (the CI
regression-gate mode: orphan count may not grow).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import defaultdict, deque
from datetime import datetime, timezone

# --------------------------------------------------------------------------- #
# Repo layout
# --------------------------------------------------------------------------- #

DEPLOYED_CRATE = "crates/dataplane"
DEPLOYED_MAIN = "crates/dataplane/src/main.rs"
LIB_BUILD_SCRIPT = "ffi/build-dataplane-lib.sh"

# Directories that are never source of the shipped artifact.
SKIP_DIRS = {
    ".lake", ".git", ".git.broken-bak", "target", "target-h2verify", "venv",
    "node_modules", ".p0-backup", "docs", "rfcs", "conformance", "demo",
    "__pycache__", "dist",
}

# --------------------------------------------------------------------------- #
# INTENTIONAL exports — orphaned by the call graph, on purpose, with a reason
# --------------------------------------------------------------------------- #
#
# An `@[export]` with no host call site is normally a proof that reaches no binary,
# and the CI gate exists to make that cost a conversation. A handful are different:
# the symbol is DELIBERATELY not called, and the reason is a design decision someone
# wrote down. Counting those with the accidental ones inflates the number and, worse,
# creates pressure to DELETE a deliberate affordance to make the gate go green.
#
# So they get their own category, each with a REASON, counted separately from
# unintentional orphans. Three rules keep this from becoming a silencer:
#
#   * an entry is a diff with prose in it — adding one is visible and arguable;
#   * a STALE entry (the symbol got wired, or no longer exists) FAILS the gate, so
#     the list cannot quietly accumulate;
#   * the reason must say why the symbol is not called, not merely that it is not.
#
# Deleting an export to move the number is the thing this category exists to prevent.
INTENTIONAL_EXPORTS = {
    # The platform IO executables are Lean `main`s whose accept loop lives in an
    # untrusted C shell (`ffi/{linux,mac,win}_io.c`, `ffi/mac_multi.c`). The shell
    # receives the handler as a CLOSURE through the `@[extern]` serve-loop seam, so
    # the closure is how it is actually invoked — the `@[export]` exists so the shell
    # MAY also call it by its stable C symbol. Both accesses are documented on the
    # definitions themselves ("so the shell may call it by symbol as well as through
    # the closure the seam passes it"). A name-based call-graph audit cannot see a
    # closure passed across an `@[extern]`, so it reports the symbol orphaned; the
    # handler is nonetheless the entry point of that executable.
    #
    # These are ALSO not part of the deployed `crates/dataplane` artifact at all —
    # they are the separate platform IO exes — which is the second reason no
    # dataplane call site exists.
    "orb_linux_handle":
        "IoLinux executable entry: the C accept loop (ffi/linux_io.c) receives this "
        "handler as a CLOSURE through the @[extern] orb_linux_serve seam; the export "
        "is the documented dual access by symbol. Not a dataplane crossing.",
    "orb_mac_handle":
        "IoMac executable entry: same closure-through-@[extern] shape as "
        "orb_linux_handle, via ffi/mac_io.c. Not a dataplane crossing.",
    "orb_mac_multi_http":
        "IoMacMulti executable HTTP entry: passed to the ffi/mac_multi.c accept loop "
        "as a closure; the export is the documented dual access. Not a dataplane "
        "crossing.",
    "orb_mac_ws_handle":
        "IoMacMulti executable WebSocket-frame entry: closure through the same "
        "multi-protocol shell. Not a dataplane crossing.",
    "orb_mac_udp_handle":
        "IoMacMulti executable QUIC/H3 datagram entry: closure through the same "
        "multi-protocol shell. Not a dataplane crossing.",
    "orb_win_handle":
        "IoWin executable entry: same closure-through-@[extern] shape, via "
        "ffi/win_io.c. Not a dataplane crossing.",
}


# Crates other than the deployed dataplane.  Call sites here are real code but
# they do not ship in the artifact; they are reported separately so a symbol
# exercised only by a twin/bench is not mistaken for a deployed one.
NON_SHIPPING_CRATE_HINT = re.compile(r"^crates/(?!dataplane/)")

# --------------------------------------------------------------------------- #
# Generic source scaffolding
# --------------------------------------------------------------------------- #


def strip_comments(src: str, spans: list | None = None) -> str:
    """Blank out // and /* */ comments, preserving offsets and line structure.

    String literals are preserved (env::var("X") gates live in them).  Rust raw
    strings are handled well enough for this purpose.
    """
    out = list(src)
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        # Comments FIRST: a stray `"` inside a `// don't "quote" me` comment must
        # not open a string that swallows the rest of the file (it did, and it
        # silently deleted call sites from the graph).
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            j = src.find("\n", i)
            j = n if j == -1 else j
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "*":
            j = src.find("*/", i + 2)
            j = n if j == -1 else j + 2
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
            continue
        if c == '"':
            st = i
            i += 1
            while i < n:
                if src[i] == "\\":
                    i += 2
                    continue
                if src[i] == '"':
                    i += 1
                    break
                i += 1
            if spans is not None:
                spans.append((st, i))
            continue
        if c == "'":
            # char literal or lifetime; only skip a well-formed char literal
            m = re.match(r"'(\\.|[^\\'])'", src[i:])
            if m:
                i += m.end()
            else:
                i += 1
            continue
        i += 1
    return "".join(out)


def blank_literals(code: str, spans) -> str:
    """Same text with STRING and CHAR literal contents blanked to spaces.

    Brace matching must run on this: a `'\"'` char literal or a `"{}"` format
    string otherwise opens a string/brace the scanner never closes, and one such
    literal silently merged the next 700 lines of a file into one function.
    """
    out = list(code)
    for a, b in spans:
        for k in range(a + 1, max(a + 1, b - 1)):
            if out[k] != "\n":
                out[k] = " "
    for m in re.finditer(r"'(\\.|[^\\'])'", code):
        for k in range(m.start() + 1, m.end() - 1):
            out[k] = " "
    return "".join(out)


def line_index(src: str) -> list[int]:
    """Byte offset of the start of each line (1-indexed access via idx[l-1])."""
    idx, pos = [0], 0
    for line in src.split("\n"):
        pos += len(line) + 1
        idx.append(pos)
    return idx


def offset_to_line(idx: list[int], off: int) -> int:
    lo, hi = 0, len(idx) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if idx[mid] <= off:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1


def match_brace(src: str, open_pos: int) -> int:
    """Index just past the `}` matching the `{` at open_pos (comment-free src)."""
    depth, i, n = 0, open_pos, len(src)
    while i < n:
        c = src[i]
        if c == '"':
            i += 1
            while i < n:
                if src[i] == "\\":
                    i += 2
                    continue
                if src[i] == '"':
                    break
                i += 1
        elif c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return n


# --------------------------------------------------------------------------- #
# Host (Rust + C) parsing
# --------------------------------------------------------------------------- #

RUST_FN = re.compile(
    r"(?:^|\n)[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?"
    r"(?:default[ \t]+)?(?:const[ \t]+)?(?:async[ \t]+)?(?:unsafe[ \t]+)?"
    r'(?:extern[ \t]+"[A-Za-z-]+"[ \t]+)?'
    r"fn[ \t]+([A-Za-z_][A-Za-z0-9_]*)"
)

C_FN = re.compile(
    r"(?:^|\n)(?:static[ \t]+|inline[ \t]+)*"
    r"[A-Za-z_][A-Za-z0-9_ \t\*]*?"
    r"\b([A-Za-z_][A-Za-z0-9_]*)[ \t]*\([^;{]*\)[ \t]*\{"
)

EXTERN_BLOCK = re.compile(r'(?:^|\n)[ \t]*(?:pub[ \t]+)?(?:unsafe[ \t]+)?extern[ \t]+"[A-Za-z-]+"[ \t]*\{')

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
ENV_VAR = re.compile(r"\benv::var(?:_os)?\(\s*\"([A-Za-z_][A-Za-z0-9_]*)\"")
CLI_FLAG = re.compile(r'"(--[a-z0-9][a-z0-9-]*)"')


def find_body(code: str, pos: int) -> int | None:
    """Offset of the `{` opening the body of the signature starting at pos."""
    depth, i, n = 0, pos, len(code)
    while i < n:
        c = code[i]
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        elif depth <= 0:
            if c == "{":
                return i
            if c == ";":
                return None
        i += 1
    return None


class HostFn:
    __slots__ = ("key", "name", "file", "line", "start", "end", "body", "masked",
                 "env_reads", "gate_locals", "shipping")

    def __init__(self, key, name, file, line, start, end, body, shipping, masked=""):
        self.masked = masked
        self.key = key
        self.name = name
        self.file = file
        self.line = line
        self.start = start
        self.end = end
        self.body = body
        self.shipping = shipping
        self.env_reads: set[str] = set()
        self.gate_locals: dict[str, str] = {}


def collect_host_files(root: str) -> list[str]:
    files = []
    for base, dirs, names in os.walk(root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        rel_base = os.path.relpath(base, root)
        if rel_base == ".":
            rel_base = ""
        for nm in names:
            if nm.endswith(".rs") or nm.endswith(".c"):
                rel = os.path.join(rel_base, nm) if rel_base else nm
                rel = rel.replace(os.sep, "/")
                if rel.startswith("crates/") or rel.startswith("ffi/"):
                    if rel.endswith(".orig") or "/tests/" in rel:
                        continue
                    files.append(rel)
    return sorted(files)


def parse_host(root: str, files: list[str]):
    """-> (fns_by_key, fns_by_name, decl_regions, file_text)"""
    fns_by_key: dict[str, HostFn] = {}
    fns_by_name: dict[str, list[HostFn]] = defaultdict(list)
    decl_regions: dict[str, list[tuple[int, int]]] = {}
    str_spans: dict[str, list[tuple[int, int]]] = {}
    file_text: dict[str, str] = {}

    for rel in files:
        path = os.path.join(root, rel)
        try:
            raw = open(path, "r", errors="replace").read()
        except OSError:
            continue
        spans: list[tuple[int, int]] = []
        code = strip_comments(raw, spans)
        masked = blank_literals(code, spans)
        file_text[rel] = code
        str_spans[rel] = spans
        idx = line_index(code)
        shipping = rel.startswith(DEPLOYED_CRATE + "/") or rel.startswith("ffi/")

        # extern "C" { ... } blocks are DECLARATIONS, not call sites.
        regions = []
        for m in EXTERN_BLOCK.finditer(code):
            ob = code.index("{", m.start())
            regions.append((ob, match_brace(masked, ob)))
        decl_regions[rel] = regions

        pat = RUST_FN if rel.endswith(".rs") else C_FN
        for m in pat.finditer(code):
            name = m.group(1)
            # Find the body-opening brace: the first `{` at bracket-depth 0 after
            # the signature.  Depth matters — `fn seal(key: &[u8; 32])` carries a
            # `;` INSIDE the parameter list, and treating that as the end of a
            # declaration silently dropped whole functions from the graph.
            probe = find_body(masked, m.end())
            if probe is None:
                continue  # a declaration (extern block / trait method), no body
            # skip fn declarations inside extern blocks
            if any(a <= m.start() < b for a, b in regions):
                continue
            end = match_brace(masked, probe)
            key = f"{rel}::{name}@{m.start()}"
            fn = HostFn(key, name, rel, offset_to_line(idx, m.start()),
                        probe, end, code[probe:end], shipping, masked[probe:end])
            for ev in ENV_VAR.finditer(fn.body):
                fn.env_reads.add(ev.group(1))
            # `let X = ... env::var("G") ...` binds a gate to a local
            for lm in re.finditer(
                r"let\s+(?:mut\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*(?::[^=]{0,80})?=\s*([^;]{0,400});",
                fn.body,
            ):
                ev = ENV_VAR.search(lm.group(2))
                if ev:
                    fn.gate_locals[lm.group(1)] = ev.group(1)
            fns_by_key[key] = fn
            fns_by_name[name].append(fn)

    return fns_by_key, fns_by_name, decl_regions, file_text, str_spans


# --------------------------------------------------------------------------- #
# Guard (gate) extraction
# --------------------------------------------------------------------------- #

def _header_before(body: str, op: int, depth: int = 0) -> str:
    """The block header immediately preceding the `{` at op.

    `else` blocks are resolved back to the `if` they negate, so the guard reads
    `NOT <cond>` — that matters because an `else` of an env-var test is the
    DEFAULT branch, not a gated one.
    """
    head = body[max(0, op - 400):op]
    cut = max(head.rfind(";"), head.rfind("{"))
    head = head[cut + 1:] if cut >= 0 else head
    head = " ".join(head.split())
    if head.endswith("}"):
        head = head[:-1].strip()
    if re.match(r"^\}?\s*else\s*$", head) and depth < 3:
        # walk back over the `}` that closes the `if` block, find its `{`
        j = body.rfind("}", 0, op)
        if j == -1:
            return "else"
        d, k = 1, j - 1
        while k >= 0 and d:
            if body[k] == "}":
                d += 1
            elif body[k] == "{":
                d -= 1
            k -= 1
        if k >= 0:
            return "NOT " + _header_before(body, k + 1, depth + 1)
        return "else"
    if head.startswith("}"):
        head = head[1:].strip()
    return head


def guard_stack(fn: HostFn, off_in_body: int) -> list[str]:
    """Headers of every block enclosing off_in_body, plus a braceless match arm."""
    body = fn.body
    scan = fn.masked or body
    open_positions: list[int] = []
    i, n = 0, min(off_in_body, len(scan))
    while i < n:
        c = scan[i]
        if c == "{":
            open_positions.append(i)
        elif c == "}" and open_positions:
            open_positions.pop()
        i += 1
    headers = [_header_before(body, op) for op in open_positions]
    # braceless match arm on the call-site line: `Seam::Foo => drorb_x,`
    ls = body.rfind("\n", 0, off_in_body) + 1
    line_prefix = body[ls:off_in_body]
    am = re.search(r"([^{};]+?)\s*=>\s*$", line_prefix)
    if am:
        headers.append(am.group(1).strip() + " =>")
    return headers


# A condition only counts as a DEPLOYMENT GATE if it is decided by the
# operator (env var, CLI flag, build cfg, an optional resource that only exists
# when configured, an enum mode) — not by the bytes of the request.  Request
# predicates are the normal serving path and are recorded as informational
# guards instead.
OPTIONAL_RES = re.compile(
    r"let\s+Some\([^)]*\)\s*=\s*([A-Za-z_][A-Za-z0-9_.:]*(?:\(\))?)|"
    r"\b([A-Za-z_][A-Za-z0-9_.:]*)\.is_some\(\)")
CONFIG_HINT = re.compile(r"\b(args|opts|cfg|config|deployment|mode|io)\b")


def classify_guard(h: str, fn: HostFn, helper_gates: dict[str, set[str]]):
    """-> (gates, informational_guard_or_None)"""
    gates: set[str] = set()
    neg = h.startswith("NOT ")
    core = h[4:] if neg else h
    is_arm = core.rstrip().endswith("=>")
    if not (is_arm or re.match(r"^(if|else if|while|match)\b", core)):
        return gates, None

    for ev in ENV_VAR.finditer(core):
        gates.add(("env!:" if neg else "env:") + ev.group(1))
    for ident in IDENT.findall(core):
        if ident in fn.gate_locals:
            gates.add(("env!:" if neg else "env:") + fn.gate_locals[ident])
        elif ident in helper_gates:
            for g in helper_gates[ident]:
                gates.add(("env!:" if neg else "env:") + g)
    for fl in CLI_FLAG.finditer(core):
        gates.add(f"flag:{fl.group(1)}")
    if "cfg!(" in core:
        m = re.search(r"cfg!\(([^)]*)\)", core)
        gates.add(f"cfg:{m.group(1) if m else '?'}")
    if is_arm:
        arm = core.rstrip()[:-2].strip().split("|")[0].strip()
        if arm and arm != "_" and len(arm) < 70 and "::" in arm:
            gates.add(f"variant:{arm}")
    om = OPTIONAL_RES.search(core)
    if om and not gates:
        res = (om.group(1) or om.group(2) or "").replace("crate::", "")
        if res and res not in ("e", "err", "s"):
            gates.add(("config!:" if neg else "config:") + res)
    if not gates and CONFIG_HINT.search(core):
        toks = [t for t in IDENT.findall(core) if CONFIG_HINT.fullmatch(t)]
        if toks:
            gates.add(f"config:{toks[0]}")
    if gates:
        return gates, None
    return gates, " ".join(core.split())[:90]


def gates_of_headers(headers, fn, helper_gates):
    gates: set[str] = set()
    guards: list[str] = []
    for h in headers:
        if not h:
            continue
        g, info = classify_guard(h, fn, helper_gates)
        gates |= g
        if info:
            guards.append(info)
    # A negated env/config test is satisfied by the DEFAULT deployment (nothing
    # set), so it does not gate anything; keep it only as a note.
    hard = {g for g in gates if not g.startswith(("env!:", "config!:"))}
    return hard, sorted(gates - hard), guards


# --------------------------------------------------------------------------- #
# Lean side
# --------------------------------------------------------------------------- #

EXPORT_RE = re.compile(r"@\[(?:[^\]]*?[, ])?export\s+([A-Za-z_][A-Za-z0-9_']*)")

LEAN_COMMENT_OPEN = re.compile(r"/-|--")


def lean_code_only(src: str) -> str:
    """Blank out Lean comments, preserving byte offsets (so line numbers hold).

    Lean prose QUOTES export names constantly -- a retirement note reading
    ``-- the `@[export drorb_serve_metered_plus2]` was REMOVED`` fabricated an
    export for a symbol that no longer exists anywhere in the tree, and a
    module docstring listing its own export shifted that symbol's reported
    file:line onto the prose line.  Both are the Lean-side twin of the Rust
    string-literal masking (`str_spans`): a name inside a comment is TEXT, not
    a declaration.  Block comments nest in Lean (`/- ... /- ... -/ ... -/`),
    and a docstring `/-- ... -/` is a block comment for this purpose.
    Everything replaced by spaces, newlines kept, so every offset is stable.
    """
    out = list(src)
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0:
            m = LEAN_COMMENT_OPEN.search(src, i)
            if not m:
                break
            if m.group(0) == "--":
                j = src.find("\n", m.start())
                j = n if j < 0 else j
                for k in range(m.start(), j):
                    out[k] = " "
                i = j
            else:
                depth = 1
                for k in range(m.start(), m.start() + 2):
                    out[k] = " "
                i = m.start() + 2
        else:
            o, c = src.find("/-", i), src.find("-/", i)
            if c < 0:
                for k in range(i, n):
                    if out[k] != "\n":
                        out[k] = " "
                i = n
            elif 0 <= o < c:
                depth += 1
                for k in range(i, o + 2):
                    if out[k] != "\n":
                        out[k] = " "
                i = o + 2
            else:
                depth -= 1
                for k in range(i, c + 2):
                    if out[k] != "\n":
                        out[k] = " "
                i = c + 2
    return "".join(out)
THEOREM_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)*(theorem|lemma)\s+")
SORRY_RE = re.compile(r"(?m)^\s*.*\bsorry\b")
IMPORT_RE = re.compile(r"(?m)^import\s+([A-Za-z0-9_.]+)")


def collect_lean(root: str) -> dict[str, dict]:
    mods: dict[str, dict] = {}
    for base, dirs, names in os.walk(root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        rel_base = os.path.relpath(base, root)
        rel_base = "" if rel_base == "." else rel_base
        for nm in names:
            if not nm.endswith(".lean"):
                continue
            rel = (os.path.join(rel_base, nm) if rel_base else nm).replace(os.sep, "/")
            if rel.startswith("lakefile") or rel.startswith("crates/"):
                continue
            path = os.path.join(root, rel)
            try:
                src = open(path, "r", errors="replace").read()
            except OSError:
                continue
            mod = rel[:-5].replace("/", ".")
            # `@[export ...]` inside a comment/docstring is prose about a symbol,
            # not a declaration of one; mask comments before the scan.
            code = lean_code_only(src)
            exports = []
            for m in EXPORT_RE.finditer(code):
                exports.append({
                    "symbol": m.group(1),
                    "file": rel,
                    "line": src.count("\n", 0, m.start()) + 1,
                })
            mods[mod] = {
                "module": mod,
                "file": rel,
                "theorems": len(THEOREM_RE.findall(src)),
                "lines": src.count("\n") + 1,
                "exports": exports,
                "imports": IMPORT_RE.findall(src),
                "sorry": bool(re.search(r"(?m)^\s*sorry\b|\bsorry\s*$", src)),
            }
    return mods


def archive_closure(root: str, mods: dict[str, dict]) -> tuple[set[str], set[str], list[str]]:
    """Replay ffi/build-dataplane-lib.sh's export-object closure.

    Returns (serve_closure, archive_closure, seeds) where serve_closure is the
    transitive import closure of `Dataplane` alone (what `drorb_serve` needs)
    and archive_closure additionally contains every extra root the script builds
    an export object for (they are all globbed into libdrorb.a).
    """
    script = os.path.join(root, LIB_BUILD_SCRIPT)
    seeds: list[str] = []
    if os.path.exists(script):
        text = open(script, "r", errors="replace").read()
        m = re.search(r"stack\s*=\s*[^\[\n]*\[([^\]]*)\]", text)
        if m:
            seeds += re.findall(r"'([A-Za-z0-9_.]+)'", m.group(1))
        for lm in re.finditer(r"lake build\s+([^\n]*)", text):
            for tok in re.findall(r"\+?([A-Za-z0-9_.]+):c\.o\.export", lm.group(1)):
                seeds.append(tok)
    seeds = sorted(set(seeds))

    def closure(roots: list[str]) -> set[str]:
        seen: set[str] = set()
        stack = list(roots)
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            seen.add(m)
            if m in mods:
                stack += mods[m]["imports"]
        return {m for m in seen if m in mods}

    serve = closure(["Dataplane"])
    arch = closure(seeds if seeds else ["Dataplane"])
    return serve, arch, seeds


# --------------------------------------------------------------------------- #
# Reachability
# --------------------------------------------------------------------------- #

def in_spans(spans, off):
    lo, hi = 0, len(spans) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        a, b = spans[mid]
        if off < a:
            hi = mid - 1
        elif off >= b:
            lo = mid + 1
        else:
            return True
    return False


def build_callgraph(fns_by_key, fns_by_name, export_symbols, decl_regions, str_spans):
    # module-name -> file, so `uring::run` resolves to uring.rs and not to the
    # `run` of every other reactor.
    mod_files = {}
    for f in fns_by_key.values():
        base = f.file.rsplit("/", 1)[-1]
        if base.endswith(".rs"):
            mod_files.setdefault(base[:-3], f.file)
    """edges[key] -> list[(callee_key, frozenset(gates))]; sites[sym] -> list."""
    helper_gates: dict[str, set[str]] = {}
    for name, cands in fns_by_name.items():
        gs: set[str] = set()
        for f in cands:
            if len(f.body) < 900 and f.env_reads:
                gs |= f.env_reads
        if gs:
            helper_gates[name] = gs

    edges: dict[str, list[tuple[str, frozenset]]] = defaultdict(list)
    sites: dict[str, list[dict]] = defaultdict(list)
    variant_sites: dict[str, list[dict]] = defaultdict(list)
    exportset = set(export_symbols)

    for key, fn in fns_by_key.items():
        body = fn.body
        # enum-variant mentions: `Seam::Foo`, `Io::Uring`, … Constructing one is
        # how a dispatch table arm gets selected, so these are graph edges too.
        for vm in re.finditer(r"\b([A-Z][A-Za-z0-9_]*::[A-Z][A-Za-z0-9_]*)\b", body):
            tail = body[vm.end():vm.end() + 24].lstrip()
            # `Seam::Foo => …` / `Seam::Foo | Seam::Bar =>` are the dispatch
            # PATTERN, not a construction; they must not satisfy themselves.
            if tail.startswith("=>") or tail.startswith("|") or tail.startswith("(_)"):
                continue
            hard, soft, guards = gates_of_headers(guard_stack(fn, vm.start()), fn, helper_gates)
            variant_sites[vm.group(1)].append({
                "key": key, "fn": fn.name, "file": fn.file,
                "line": fn.line + body.count("\n", 0, vm.start()),
                "gates": sorted(hard), "soft": soft, "shipping": fn.shipping,
            })
        spans = str_spans.get(fn.file, ())
        decls = decl_regions.get(fn.file, ())
        for m in re.finditer(r"\b([A-Za-z_][A-Za-z0-9_]*)\b", body):
            name = m.group(1)
            hit_export = name in exportset
            hit_fn = name in fns_by_name
            if not (hit_export or hit_fn):
                continue
            abs_off = fn.start + m.start()
            # A name inside a STRING ("...handler NOT run)") is not a call, and a
            # name inside `extern "C" { … }` is a DECLARATION, not a call.
            if spans and in_spans(spans, abs_off):
                continue
            if any(a <= abs_off < b for a, b in decls):
                continue
            after = body[m.end():m.end() + 4].lstrip()
            called = after.startswith("(") or after.startswith("::<")
            # A bare mention (`{ drorb_serve_flat } else {`, `cross(drorb_wg_seal, …)`)
            # is a function-POINTER use and just as real a call site as `f(x)`; the
            # window has to be wide enough to reach the delimiter past a newline and
            # indentation, or whole dispatch arms vanish from the inventory.
            is_ref = bool(re.match(r"\s*[,;)\]}]", body[m.end():m.end() + 60]))
            if not (called or is_ref):
                continue
            hard, soft, guards = gates_of_headers(guard_stack(fn, m.start()), fn, helper_gates)
            gates = frozenset(hard)
            if hit_export:
                sites[name].append({
                    "fn": fn.name, "file": fn.file, "key": key,
                    "line": fn.line + body.count("\n", 0, m.start()),
                    "gates": sorted(gates), "soft": soft, "guards": guards[:3],
                    "shipping": fn.shipping, "called": called,
                })
            if hit_fn:
                for cal in resolve_callee(body, m.start(), name, fn,
                                          fns_by_name, mod_files):
                    if cal.key == key:
                        continue
                    edges[key].append((cal.key, gates))
    return edges, sites, variant_sites


def resolve_callee(body, pos, name, fn, fns_by_name, mod_files):
    """Pick the plausible definitions of `name` called at pos.

    Path-qualified calls (`uring::run(...)`) resolve to that module's file only —
    without this the three IO reactors all define `run` and every reactor appears
    to reach every other reactor's code.  Unqualified calls prefer a same-file
    definition and otherwise stay over-approximate (all definitions).
    """
    cands = fns_by_name[name]
    pre = body[max(0, pos - 80):pos]
    q = re.search(r"([A-Za-z_][A-Za-z0-9_]*)\s*::\s*$", pre)
    if q:
        f = mod_files.get(q.group(1))
        if f:
            scoped = [c for c in cands if c.file == f]
            if scoped:
                return scoped
    same = [c for c in cands if c.file == fn.file]
    if same:
        return same
    return cands


def resolve_variants(gates: frozenset, variant_sites, best) -> frozenset:
    """Replace `variant:Enum::V` (a dispatch-table arm) by the gates required to
    CONSTRUCT that variant somewhere reachable.  A variant nobody constructs is
    a dead dispatch entry and keeps an explicit marker."""
    out: set[str] = set()
    for g in gates:
        if not g.startswith("variant:"):
            out.add(g)
            continue
        v = g[len("variant:"):]
        cands = []
        for s in variant_sites.get(v, ()):
            if not s["shipping"]:
                continue
            b = best.get(s["key"])
            if b is None:
                continue
            cands.append(frozenset(b) | frozenset(s["gates"]))
        if not cands:
            out.add(f"dead-dispatch:{v}")
        else:
            cands.sort(key=len)
            out |= set(cands[0])
    return frozenset(out)


def reach(edges, roots, parents=None) -> dict[str, frozenset]:
    """Least-gated reachability: best[key] = smallest gate-set on any path."""
    best: dict[str, frozenset] = {}
    dq = deque()
    for r in roots:
        best[r] = frozenset()
        dq.append(r)
    while dq:
        k = dq.popleft()
        cur = best[k]
        for callee, gates in edges.get(k, ()):
            nxt = cur | gates
            prev = best.get(callee)
            if prev is None or len(nxt) < len(prev):
                best[callee] = nxt
                if parents is not None:
                    parents[callee] = (k, sorted(gates))
                dq.append(callee)
    return best


def explain(sym, sites, fns_by_key, edges, roots, label):
    """Print the least-gated call path from `roots` to every site of `sym`."""
    parents: dict[str, tuple] = {}
    best = reach(edges, roots, parents)
    print(f"--- {sym}: paths from {label} ---")
    hit = False
    for s in sites.get(sym, ()):
        mark = "REACHABLE" if s["key"] in best else "unreachable"
        print(f"  site {s['file']}:{s['line']} in {s['fn']}()  [{mark}]"
              + (f"  site-gates {','.join(s['gates'])}" if s["gates"] else ""))
        if s["key"] not in best:
            continue
        hit = True
        chain, k = [], s["key"]
        while k is not None:
            fn = fns_by_key[k]
            g = parents.get(k, (None, []))[1]
            chain.append(f"      {fn.file}:{fn.line} {fn.name}()"
                         + (f"   <- gates {','.join(g)}" if g else ""))
            k = parents.get(k, (None, None))[0]
        for line in reversed(chain):
            print(line)
    if not hit:
        print("  (no path)")


# --------------------------------------------------------------------------- #
# Main
# --------------------------------------------------------------------------- #

def git_head(root: str) -> str:
    try:
        return subprocess.run(["git", "-C", root, "rev-parse", "--short", "HEAD"],
                              capture_output=True, text=True, timeout=20).stdout.strip() or "?"
    except Exception:
        return "?"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    ap.add_argument("--json", dest="json_out")
    ap.add_argument("--markdown", dest="md_out")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--why", metavar="SYMBOL",
                    help="explain how SYMBOL is reached: print the least-gated "
                         "call path from fn main and from each IO reactor")
    ap.add_argument("--check-orphan-max", type=int, default=None,
                    help="CI gate: fail if the orphaned-export count exceeds N")
    args = ap.parse_args()
    root = os.path.abspath(args.root)

    lean = collect_lean(root)
    serve_cl, arch_cl, seeds = archive_closure(root, lean)

    exports: dict[str, dict] = {}
    for mod, info in lean.items():
        for e in info["exports"]:
            exports.setdefault(e["symbol"], {
                "symbol": e["symbol"], "module": mod,
                "file": e["file"], "line": e["line"],
                "in_serve_closure": mod in serve_cl,
                "in_archive_closure": mod in arch_cl,
            })

    host_files = collect_host_files(root)
    fns_by_key, fns_by_name, decl_regions, file_text, str_spans = parse_host(root, host_files)
    edges, sites, variant_sites = build_callgraph(
        fns_by_key, fns_by_name, exports.keys(), decl_regions, str_spans)

    main_roots = [k for k, f in fns_by_key.items()
                  if f.name == "main" and f.file == DEPLOYED_MAIN]
    best = reach(edges, main_roots)

    # Per-request roots: the connection handlers of each IO reactor.
    req_root_names = {
        "crates/dataplane/src/blocking.rs": ("handle_conn", "serve_conn", "handle_client"),
        "crates/dataplane/src/uring.rs": ("on_recv", "handle_recv", "drive", "step"),
        "crates/dataplane/src/kqueue.rs": ("on_readable", "handle_conn", "serve_conn"),
        "crates/dataplane/src/http.rs": ("handle", "handle_request", "respond"),
    }
    req_roots = [k for k, f in fns_by_key.items()
                 if f.file in req_root_names and f.name in req_root_names[f.file]]
    best_req = reach(edges, req_roots) if req_roots else {}

    # Per-reactor reachability: which IO reactor can reach each seam at all.
    reactors = {
        "blocking": ("crates/dataplane/src/blocking.rs", "run"),
        "uring": ("crates/dataplane/src/uring.rs", "run"),
        "kqueue": ("crates/dataplane/src/kqueue.rs", "run"),
    }
    best_reactor = {}
    for rname, (rfile, rfn) in reactors.items():
        roots = [k for k, f in fns_by_key.items() if f.file == rfile and f.name == rfn]
        best_reactor[rname] = reach(edges, roots) if roots else {}

    if args.why:
        explain(args.why, sites, fns_by_key, edges, main_roots, "fn main")
        for rname, (rfile, rfn) in reactors.items():
            roots = [k for k, f in fns_by_key.items()
                     if f.file == rfile and f.name == rfn]
            if roots:
                explain(args.why, sites, fns_by_key, edges, roots, f"{rname}::run")
        return 0

    buckets = {"default": [], "gated": [], "orphaned": [], "intentional": []}
    for sym, info in sorted(exports.items()):
        ss = sites.get(sym, [])
        shipping_sites = [s for s in ss if s["shipping"]]
        info["sites"] = ss
        reachable = []
        for s in shipping_sites:
            g = best.get(s["key"])
            if g is None:
                continue
            gs = resolve_variants(frozenset(g) | frozenset(s["gates"]),
                                  variant_sites, best)
            reachable.append((gs, s))
        live = [(g, s) for g, s in reachable
                if not any(x.startswith("dead-dispatch:") for x in g)]
        info["reactors"] = sorted(
            r for r in reactors
            if any(s["key"] in best_reactor[r] for _, s in (live or reachable))
        )
        if live:
            live.sort(key=lambda t: len(t[0]))
            gates, site = live[0]
            info["gates"] = sorted(gates)
            info["call_site"] = f"{site['file']}:{site['line']} ({site['fn']})"
            info["request_path"] = any(s["key"] in best_req for _, s in live)
            info["reason"] = None
            (buckets["gated"] if gates else buckets["default"]).append(info)
        else:
            info["request_path"] = False
            if reachable:
                info["reason"] = "dead-dispatch"
                info["gates"] = sorted(reachable[0][0])
                s = reachable[0][1]
                info["call_site"] = f"{s['file']}:{s['line']} ({s['fn']})"
            elif shipping_sites:
                info["reason"] = "dead-host"      # host code exists, main can't reach it
                info["gates"] = []
                s = shipping_sites[0]
                info["call_site"] = f"{s['file']}:{s['line']} ({s['fn']})"
            elif ss:
                info["reason"] = "non-shipping-crate"
                info["gates"] = []
                info["call_site"] = f"{ss[0]['file']}:{ss[0]['line']}"
            else:
                info["reason"] = "no-call-site"
                info["gates"] = []
                info["call_site"] = None
            if sym in INTENTIONAL_EXPORTS:
                info["intent"] = INTENTIONAL_EXPORTS[sym]
                buckets["intentional"].append(info)
            else:
                buckets["orphaned"].append(info)

    # An allowlist entry that no longer describes an orphan is STALE: the symbol got
    # wired (good — remove the entry) or vanished (also remove it). Either way the
    # reason no longer holds, and a list that may not be pruned is a silencer.
    intentional_named = set(INTENTIONAL_EXPORTS)
    intentional_live = {e["symbol"] for e in buckets["intentional"]}
    stale_intentional = sorted(intentional_named - intentional_live)

    # Module inventory
    mod_rows = []
    for mod, info in sorted(lean.items()):
        mod_rows.append({
            "module": mod, "file": info["file"], "theorems": info["theorems"],
            "lines": info["lines"], "exports": [e["symbol"] for e in info["exports"]],
            "in_serve_closure": mod in serve_cl,
            "in_archive_closure": mod in arch_cl,
        })
    with_thms = [m for m in mod_rows if m["theorems"] > 0]
    shipped_mods = [m for m in with_thms if m["in_archive_closure"]]
    orphan_mods = [m for m in with_thms if not m["in_archive_closure"]]

    result = {
        "generated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "root": root,
        "head": git_head(root),
        "totals": {
            "lean_modules": len(mod_rows),
            "lean_modules_with_theorems": len(with_thms),
            "theorems": sum(m["theorems"] for m in mod_rows),
            "theorems_in_archive": sum(m["theorems"] for m in shipped_mods),
            "theorems_orphaned": sum(m["theorems"] for m in orphan_mods),
            "modules_in_serve_closure": sum(1 for m in mod_rows if m["in_serve_closure"]),
            "modules_in_archive_closure": sum(1 for m in mod_rows if m["in_archive_closure"]),
            "exports": len(exports),
            "export_default": len(buckets["default"]),
            "export_gated": len(buckets["gated"]),
            "export_orphaned": len(buckets["orphaned"]),
            "export_intentional": len(buckets["intentional"]),
            "export_orphan_reasons": {
                r: sum(1 for e in buckets["orphaned"] if e["reason"] == r)
                for r in ("no-call-site", "dead-host", "dead-dispatch", "non-shipping-crate")},
            "export_by_reactor": {
                r: sum(1 for b in ("default", "gated") for e in buckets[b]
                       if r in e["reactors"]) for r in ("blocking", "uring", "kqueue")},
            "export_request_path": sum(
                1 for b in ("default", "gated") for e in buckets[b] if e["request_path"]),
            "host_fns": len(fns_by_key),
            "host_files": len(host_files),
            "closure_seeds": seeds,
        },
        "buckets": {k: [{kk: vv for kk, vv in e.items() if kk != "sites"} for e in v]
                    for k, v in buckets.items()},
        "modules": mod_rows,
        "orphan_modules": orphan_mods,
        "stale_intentional": stale_intentional,
    }

    if args.json_out:
        with open(args.json_out, "w") as fh:
            json.dump(result, fh, indent=1)

    if args.md_out:
        with open(args.md_out, "w") as fh:
            fh.write(render_markdown(result))

    if not args.quiet:
        t = result["totals"]
        print("=== drorb reachability audit ===")
        print(f"root {root}  HEAD {result['head']}  {result['generated']}")
        print(f"lean modules            {t['lean_modules']:>6}"
              f"   with theorems {t['lean_modules_with_theorems']:>6}"
              f"   theorems {t['theorems']:>6}")
        print(f"in libdrorb.a closure   {t['modules_in_archive_closure']:>6}"
              f"   ({100*t['modules_in_archive_closure']/max(1,t['lean_modules']):.1f}% of modules,"
              f" {100*t['theorems_in_archive']/max(1,t['theorems']):.1f}% of theorems)")
        print(f"  of which serve closure{t['modules_in_serve_closure']:>6}")
        print(f"@[export] symbols       {t['exports']:>6}")
        print(f"  DEFAULT-PATH          {t['export_default']:>6}")
        print(f"  GATED                 {t['export_gated']:>6}")
        print(f"  ORPHANED              {t['export_orphaned']:>6}   "
              + ", ".join(f"{k}={v}" for k, v in t["export_orphan_reasons"].items() if v))
        print(f"  INTENTIONAL           {t['export_intentional']:>6}   "
              "(deliberately uncalled, reason recorded per symbol)")
        print(f"reachable per reactor   "
              + "  ".join(f"{k}={v}" for k, v in t["export_by_reactor"].items()))
        print(f"host fns parsed         {t['host_fns']:>6}   files {t['host_files']}")
        print("ORPHANED exports:")
        for e in result["buckets"]["orphaned"]:
            print(f"  {e['symbol']:<42} {e['file']}:{e['line']:<5} [{e['reason']}]")
        print("INTENTIONAL exports (counted separately, not orphans):")
        for e in result["buckets"]["intentional"]:
            print(f"  {e['symbol']:<42} {e['file']}:{e['line']:<5} [{e['reason']}]")
            print(f"      {e['intent']}")
        print(f"REACHABILITY-AUDIT OK ({t['export_orphaned']} orphaned exports, "
              f"{len(result['orphan_modules'])} orphaned modules)")

    if args.check_orphan_max is not None:
        failed = False
        if result["totals"]["export_orphaned"] > args.check_orphan_max:
            print(f"REACHABILITY-AUDIT FAIL: orphaned exports "
                  f"{result['totals']['export_orphaned']} > {args.check_orphan_max}",
                  file=sys.stderr)
            failed = True
        if stale_intentional:
            print("REACHABILITY-AUDIT FAIL: stale INTENTIONAL_EXPORTS entries (the symbol "
                  "is wired now, or no longer exists) — remove them: "
                  + ", ".join(stale_intentional), file=sys.stderr)
            failed = True
        if failed:
            return 1
    return 0


def render_markdown(r: dict) -> str:
    t = r["totals"]
    L = []
    A = L.append
    A("# Reachability inventory — proven vs. shipped\n")
    A(f"*Generated by `scripts/reachability-audit.py --markdown docs/gateway/REACHABILITY.md` "
      f"at {r['generated']} against `{r['head']}`. Every number is computed from source by "
      f"parsing the tree; no build is required and nothing here is hand-maintained. "
      f"Re-run it and the file rewrites itself.*\n")
    A("drorb proves a great deal of Lean and ships exactly one native artifact: "
      "`crates/dataplane/src/main.rs` linked against `libdrorb.a`, which "
      "`ffi/build-dataplane-lib.sh` cuts from an import closure. Between those two "
      "facts sits the gap this file measures — a module can be fully proven, build "
      "green, and still reach no binary.\n")

    A("## The three buckets\n")
    A("| bucket | meaning |")
    A("|---|---|")
    A("| **DEFAULT-PATH** | the `@[export]`'s host call site is reachable from `fn main` "
      "of the deployed binary with no operator-set condition on the path |")
    A("| **GATED** | reachable only under a named condition — an env var, a CLI flag, or an "
      "optional resource that only exists when configured. The gate is named per symbol. |")
    A("| **ORPHANED** | proven, exported, and unreachable. Four distinct ways: "
      "`no-call-site` (no host code mentions it), `dead-host` (host code exists but nothing "
      "calls that host function — rustc agrees, it emits `never used`), `dead-dispatch` "
      "(the only call site is a dispatch-table arm whose enum variant is never constructed), "
      "`non-shipping-crate` (called only from a bench/twin crate). |")
    A("| **INTENTIONAL** | unreachable *by design*, with a reason recorded per symbol in "
      "`INTENTIONAL_EXPORTS` (`scripts/reachability-audit.py`). Counted separately so a "
      "deliberate affordance does not inflate the orphan number — and so nobody is pushed "
      "to DELETE one to make the gate go green. A stale entry (the symbol got wired, or "
      "vanished) fails the gate, so the list cannot quietly grow into a silencer. |")
    A("")

    A("## Totals\n")
    A("| metric | count |")
    A("|---|---:|")
    A(f"| Lean modules | {t['lean_modules']} |")
    A(f"| Lean modules carrying theorems | {t['lean_modules_with_theorems']} |")
    A(f"| theorems (declaration count) | {t['theorems']} |")
    A(f"| modules inside the `libdrorb.a` export closure | {t['modules_in_archive_closure']}"
      f" (**{100*t['modules_in_archive_closure']/max(1,t['lean_modules']):.1f}%**) |")
    A(f"| — of which the `Dataplane` serve closure | {t['modules_in_serve_closure']}"
      f" ({100*t['modules_in_serve_closure']/max(1,t['lean_modules']):.1f}%) |")
    A(f"| theorems inside the archive closure | {t['theorems_in_archive']}"
      f" (**{100*t['theorems_in_archive']/max(1,t['theorems']):.1f}%**) |")
    A(f"| theorems outside it | {t['theorems_orphaned']} |")
    A(f"| `@[export]` symbols | {t['exports']} |")
    A(f"| — DEFAULT-PATH | **{t['export_default']}** |")
    A(f"| — GATED | **{t['export_gated']}** |")
    A(f"| — ORPHANED | **{t['export_orphaned']}** "
      + " · ".join(f"{k} {v}" for k, v in t["export_orphan_reasons"].items() if v) + " |")
    A(f"| — INTENTIONAL | **{t['export_intentional']}** (uncalled by design, reason per symbol) |")
    A(f"| host functions parsed | {t['host_fns']} in {t['host_files']} files |")
    A("")
    A("Being inside the archive closure is necessary, not sufficient: it means the module's "
      "object is compiled into `libdrorb.a`, which the host linker then prunes to what the "
      "referenced symbols actually need. The export buckets below are the sufficient half.\n")

    A("## Which IO reactor can reach which seam\n")
    A("The deployed binary has three reactors (`--io blocking|uring|kqueue`; io_uring is the "
      "Linux default, kqueue the macOS one). A seam only one reactor reaches is a seam most "
      "deployments do not run.\n")
    A("| reactor | seams reachable |")
    A("|---|---:|")
    for k, v in t["export_by_reactor"].items():
        A(f"| `--io {k}` | {v} |")
    A("")
    only = defaultdict(list)
    for b in ("default", "gated"):
        for e in r["buckets"][b]:
            if len(e["reactors"]) == 1:
                only[e["reactors"][0]].append(e["symbol"])
    for k, v in sorted(only.items()):
        A(f"* reachable **only** from `--io {k}`: " + ", ".join(f"`{x}`" for x in sorted(v)))
    A("")

    dead = [e for e in r["buckets"]["orphaned"]
            if e["reason"] in ("dead-host", "dead-dispatch", "non-shipping-crate")]
    A(f"## Headline: proven, hosted, and still unreachable ({len(dead)})\n")
    A("These are the expensive ones — Lean proved it AND someone wrote the host marshalling, "
      "and it still never runs.\n")
    A("| symbol | Lean | host code | why unreachable |")
    A("|---|---|---|---|")
    for e in dead:
        A(f"| `{e['symbol']}` | `{e['file']}:{e['line']}` | `{e['call_site']}` | {e['reason']} |")
    A("")

    rows = r["buckets"]["intentional"]
    A(f"## INTENTIONAL exports — uncalled by design ({len(rows)})\n")
    A("These carry an `@[export]` that no host call site reaches, and that is the design, "
      "not an oversight. Each one names WHY. They are counted apart from the orphans so the "
      "gate measures what it is for — proofs that reach no binary by accident — and so the "
      "cheapest way to make the number fall is never *delete a documented affordance*.\n")
    if not rows:
        A("*(none)*\n")
    else:
        A("| symbol | Lean | why it is not called |")
        A("|---|---|---|")
        for e in rows:
            A(f"| `{e['symbol']}` | `{e['file']}:{e['line']}` | {e['intent']} |")
        A("")
    if r.get("stale_intentional"):
        A("**STALE allowlist entries** (the symbol is wired now, or gone — remove them; "
          "`--check` fails on these): "
          + ", ".join(f"`{x}`" for x in r["stale_intentional"]) + "\n")

    for key, title, note in (
        ("default", "DEFAULT-PATH exports", ""),
        ("gated", "GATED exports", "The gate column names what must be set for the proof to run."),
        ("orphaned", "ORPHANED exports", "")):
        rows = r["buckets"][key]
        A(f"## {title} ({len(rows)})\n")
        if note:
            A(note + "\n")
        if not rows:
            A("*(none)*\n")
            continue
        if key == "orphaned":
            A("| symbol | Lean | reason | in libdrorb.a? |")
            A("|---|---|---|---|")
            for e in rows:
                A(f"| `{e['symbol']}` | `{e['file']}:{e['line']}` | {e['reason']} | "
                  f"{'yes' if e['in_archive_closure'] else 'no'} |")
        else:
            A("| symbol | Lean | host call site | gates | reactors |")
            A("|---|---|---|---|---|")
            for e in rows:
                g = ", ".join(f"`{x}`" for x in e["gates"]) or "—"
                A(f"| `{e['symbol']}` | `{e['file']}:{e['line']}` | `{e['call_site']}` | {g} | "
                  f"{', '.join(e['reactors']) or '—'} |")
        A("")

    A(f"## Orphaned modules — proven, outside the shipped archive "
      f"({len(r['orphan_modules'])} of {t['lean_modules_with_theorems']} theorem-carrying modules)\n")
    A(f"{t['theorems_orphaned']} theorems live here. Sorted by theorem count: the biggest "
      "proof investments that reach no binary. Top 120 shown; the full list is in the "
      "`--json` output.\n")
    A("| module | theorems | lines | exports |")
    A("|---|---:|---:|---|")
    for m in sorted(r["orphan_modules"], key=lambda m: -m["theorems"])[:120]:
        ex = ", ".join(f"`{s}`" for s in m["exports"]) or "—"
        A(f"| `{m['module']}` | {m['theorems']} | {m['lines']} | {ex} |")
    A("")

    A("## Method, and what these numbers are not\n")
    A("* The host call graph is built by brace-matched parsing of `crates/**/*.rs` and the "
      "C shims, with comments **and string literals** excluded — doc comments quote export "
      "names constantly and `eprintln!(\"… NOT run)\")` contains the identifier `run`; "
      "counting either fabricates call sites (both bugs were live during development of "
      "this script and both were caught by `--why`).")
    A("* Call resolution is by name: path-qualified calls (`uring::run`) resolve to that "
      "module, unqualified ones prefer a same-file definition and otherwise stay "
      "over-approximate. Over-approximation makes things look MORE reachable, so an "
      "ORPHANED verdict is strong and a DEFAULT-PATH verdict is an upper bound.")
    A("* DEFAULT-PATH means *no operator-set condition on the path from `main`*. It does "
      "NOT mean \"runs on every request\": startup, subcommand dispatch and reactor "
      "selection all sit on such paths.")
    A("* Conditions that depend on the bytes of a request are not gates and are ignored; "
      "conditions that depend on env/flag/config are. A gate the classifier misses shows "
      "up as DEFAULT-PATH.")
    A("* Theorem counts are `theorem`/`lemma` declaration counts, not a semantic weight.")
    A("* Independent cross-check (hbox, from-scratch release build 2026-07-24): rustc's own "
      "dead-code warnings on the deployed crate name `drorb_serve_metered`, "
      "`drorb_serve_metered_cfg`, `drorb_serve_metered_braided`, `drorb_ws_close_ok` and "
      "their host wrappers as `never used` — four of the five `dead-host` findings, "
      "reached independently. The fifth, `drorb_serve_metered_conformant`, rustc does NOT "
      "report: its wrapper `serve_metered_conformant_into` carries `#[allow(dead_code)]` "
      "(`serve.rs:1339`). That is the case for this audit existing — the compiler can be "
      "silenced about an unreachable proof, and here it was.\n")

    A("## Re-running / CI gate\n")
    A("```")
    A("scripts/reachability-audit.py                       # summary to stdout")
    A("scripts/reachability-audit.py --why drorb_ws_header # explain one symbol")
    A("scripts/reachability-audit.sh                       # regenerate this file")
    A("scripts/reachability-audit.sh --check               # CI gate: orphan count may not grow")
    A("```")
    A("")
    A(f"The gate pins the UNINTENTIONAL orphan count at its current value "
      f"({t['export_orphaned']}); wiring a seam lowers it, adding an unwired `@[export]` "
      f"raises it and fails. The {t['export_intentional']} INTENTIONAL exports are outside "
      "that count, and a stale entry in that list fails the gate too — so the allowlist "
      "cannot be used to make an accidental orphan disappear.\n")
    return "\n".join(L)


if __name__ == "__main__":
    sys.exit(main())
