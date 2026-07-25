#!/usr/bin/env python3
"""gate-dataflow.py — INVARIANT 6: NO ACCEPTING FALLTHROUGH ON A MISSING VERIFIED GATE.

The upgrade of the Rust-twin guard from a NAME-GREP to a DATAFLOW check.

`lean-twins.tsv`'s `route` rows assert a SYMBOL is present in a file. That is blind to the
defect that actually matters: the symbol is right there, the route-through is intact, and yet
a `None` / `Err` from the verified gate FALLS THROUGH to a hand-written Rust decider that can
ACCEPT. `turn/src/executor/atomic.rs` shipped in exactly that state — `dregg_cross_cell_conserves`
present, `route` row green, and a native node with a stale Lean archive silently answering the
per-asset conservation question (the ASSET-INFLATION boundary) with the unverified Rust twin.

This checker asks the question a name-whitelist cannot: for each registered decision site, when
the verified gate is ABSENT, can control reach an ACCEPTING verdict?

## The check

For each row of `gate-dataflow.tsv` (`file  fn  acquire  allow  note`):

  1. Locate every non-`cfg(test)` definition of `fn <fn>` in `<file>` and slice its body
     (brace-matched, string/char/comment aware).
  2. Find the GATE ACQUISITION — the first occurrence of `<acquire>` (a regex) in that body.
  3. Extract the GATE-ABSENT REGION: the code that runs when the acquisition yields
     `None` / `Err`. Five recognized shapes:
       `if let Some(..) = <acq> { .. } else { R }`      -> R
       `if let Some(..) = <acq> { .. }` (no else)       -> the FALLTHROUGH after the if-block
       `match <acq> { .. None|Err(..) => R .. }`        -> R
       `let Some(..) = <acq> else { R }`                -> R
       `<acq>.unwrap_or*(R)`                            -> R
       `<acq>...?` / `.ok()?`                           -> PROPAGATES (disposition is the caller's)
  4. CLASSIFY the region, walking it in order and resolving local helper calls
     TRANSITIVELY (depth <= 2, skipping `#[cfg(test)]` definitions):
       * a REFUSAL terminal reached before any accepting terminal  -> PASS
       * a DECLARED DISCRIMINATION (a token from the row's `allow`, e.g. a
         `#[cfg(target_arch = "wasm32")]` or a named runtime escape) AND a refusal on the
         non-exempt arm                                            -> PASS (the token is printed)
       * a DECLARED NARROWING (`narrow:<token>` in `allow`) — the no-gate path is a named,
         deliberately narrowed local decision                      -> PASS (the token is printed)
       * an ACCEPTING terminal otherwise reachable                  -> FAIL (the fall-open)
       * no terminal verdict at all                                 -> FAIL (indeterminate; this
         guard fails CLOSED, because "I could not prove it refuses" is not a pass)

Every carve-out is therefore a DECLARED, DIFFABLE FACT in a TSV row — not an invisible property
of the code. Widening one is a reviewable diff; forgetting to declare it is RED. And a row that
declares a carve-out the code does not actually contain is still RED.

## What this is and is not

It is a STRUCTURAL dataflow check over the source at HEAD, not a theorem. It does not know
whether `false` means "refuse" for a given predicate's polarity, and it stops at depth 2. It
exists to make the KNOWN regression class impossible to land silently: a verified-gate site
whose gate-absent path can accept.

`--self-test` runs the checker against synthetic fail-open / fail-closed fixtures, so CI proves
the guard CAN GO RED on every run. A guard that cannot go red is not a guard.

EXIT: 0 all sites pass; 1 a site FAILED; 2 environment problem (a registry/source file moved,
or a `fn` is gone — never a silent green).
"""

from __future__ import annotations

import os
import re
import sys
import tempfile

# ── verdict vocabulary ──────────────────────────────────────────────────────────────
# A REFUSAL terminal: control cannot admit from here.
REFUSAL = re.compile(
    r"""(
      return \s+ Err\(
    | \breturn \s+ false\b
    | \breturn \s+ None\b
    | \bErr\s*\(
    | \bpanic!
    | \bunreachable!
    | \btodo!
    | \bunimplemented!
    | ::Abort\b
    | ::Reject
    | ::Refused
    | Unavailable\b
    | \bfalse\b
    )""",
    re.X,
)
# An ACCEPTING terminal: this region can hand back an ADMIT.
ACCEPTING = re.compile(
    r"""(
      \bOk\s*\(\s*\(\s*\)\s*\)  # Ok(())  — the unit ADMIT
    | \breturn \s+ Ok\s*\(
    | \breturn \s+ true\b
    | \bSome\(\s*true\s*\)
    | ::Commit\b
    | ::Accept
    | ::Admit
    | \.is_some\(\)
    | \btrue\b
    )""",
    re.X,
)
# `false` is a refusal token AND `true` an accepting one; when a line contains both, POSITION
# decides. A bare `Ok(x)` that is not `Ok(())` counts as accepting only in TAIL position — the
# value a `-> Result<..>` decider hands back as its verdict.
TAIL_OK = re.compile(r"^\s*Ok\s*\(")


def accepting(line: str):
    """The accepting-terminal match in `line`, if any (incl. a tail-position `Ok(..)`)."""
    m = ACCEPTING.search(line)
    if m:
        return m
    return TAIL_OK.match(line)

CFG_ATTR = re.compile(r"#\s*!?\[\s*cfg\s*\((?P<pred>.*)\)\s*\]|cfg!\s*\((?P<pred2>[^)]*(?:\)[^)]*)*)\)")
CFG_TEST = re.compile(r"#\s*\[\s*cfg\s*\(\s*test\s*\)\s*\]")
# A call to a same-file helper: `foo(`, `self.foo(`, `Self::foo(`, `super::m::foo(`.
LOCAL_CALL = re.compile(r"(?:\bself\.|\bSelf::|\b(?:[A-Za-z_][A-Za-z0-9_]*::)*)([a-z_][a-z0-9_]*)\s*\(")
PROPAGATES = re.compile(r"\?\s*[;,)]|\?\s*$|\.ok\(\)\s*\?")


# ── source slicing: brace matching that respects strings / chars / comments ──────────
def _skip_noise(src: str, i: int) -> int:
    """If `src[i]` starts a string/char/comment, return the index just past it; else `i`."""
    n = len(src)
    if src.startswith("//", i):
        j = src.find("\n", i)
        return n if j < 0 else j
    if src.startswith("/*", i):
        depth, j = 1, i + 2
        while j < n and depth:
            if src.startswith("/*", j):
                depth += 1
                j += 2
            elif src.startswith("*/", j):
                depth -= 1
                j += 2
            else:
                j += 1
        return j
    if src[i] == 'r' and i + 1 < n and src[i + 1] in '"#':  # raw string r"..." / r#"..."#
        j = i + 1
        hashes = 0
        while j < n and src[j] == "#":
            hashes += 1
            j += 1
        if j < n and src[j] == '"':
            close = '"' + "#" * hashes
            k = src.find(close, j + 1)
            return n if k < 0 else k + len(close)
        return i
    if src[i] == '"':
        j = i + 1
        while j < n:
            if src[j] == "\\":
                j += 2
                continue
            if src[j] == '"':
                return j + 1
            j += 1
        return n
    if src[i] == "'":  # char literal (or a lifetime, which has no closing quote — bail safely)
        if src.startswith("'\\", i):
            j = src.find("'", i + 2)
            return i + 1 if j < 0 else j + 1
        if i + 2 < n and src[i + 2] == "'":
            return i + 3
        return i + 1
    return i


def brace_block(src: str, open_idx: int) -> int:
    """Index just past the `}` matching the `{` at `open_idx`."""
    assert src[open_idx] == "{"
    depth, i, n = 0, open_idx, len(src)
    while i < n:
        j = _skip_noise(src, i)
        if j != i:
            i = j
            continue
        if src[i] == "{":
            depth += 1
        elif src[i] == "}":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return n


def strip_cfg_test(body: str) -> str:
    """Blank out `#[cfg(test)]`-gated items/blocks so the guard never reads a test-only decider."""
    out, i, n = list(body), 0, len(body)
    while i < n:
        m = CFG_TEST.search(body, i)
        if not m:
            break
        j = body.find("{", m.end())
        # `#[cfg(test)] mod tests { .. }` / `#[cfg(test)] fn f() { .. }` / `#[cfg(test)] { .. }`
        if j >= 0 and body.find(";", m.end(), j) < 0:
            end = brace_block(body, j)
        else:
            end = body.find(";", m.end())
            end = n if end < 0 else end + 1
        for k in range(m.start(), min(end, n)):
            if out[k] != "\n":
                out[k] = " "
        i = max(end, m.end())
    return "".join(out)


def fn_bodies(src: str, name: str) -> list[tuple[str, str]]:
    """Every non-`cfg(test)` definition of `fn <name>`: (attrs_above, body_text)."""
    found = []
    for m in re.finditer(r"\bfn\s+" + re.escape(name) + r"\s*(?:<[^>{(]*>)?\s*\(", src):
        # attributes / doc-comments immediately above the fn
        head = src.rfind("\n\n", 0, m.start())
        attrs = src[head + 1 : m.start()] if head >= 0 else src[: m.start()]
        if CFG_TEST.search(attrs):
            continue
        brace = src.find("{", m.end())
        if brace < 0:
            continue
        # a `where` clause or return type may contain braces? (`-> impl Fn() {`) — take the first
        # `{` that opens a block at depth 0 of the signature parens
        end = brace_block(src, brace)
        found.append((attrs, src[brace : end]))
    return found


# ── gate-absent region extraction ───────────────────────────────────────────────────
def gate_absent_region(body: str, acquire: re.Pattern[str]) -> tuple[str, str]:
    """(shape, region_text) for the code that runs when the gate acquisition yields None/Err."""
    m = acquire.search(body)
    if not m:
        return ("NO-ACQUISITION", "")
    # The whole STATEMENT the acquisition sits in — not just its line. A `let`-chain wraps
    # (`if let Some(t) = tally()\n  && let Some(d) = verified_decision(..)`), so a line-only
    # window loses the `if` and the shape becomes unparseable.
    stmt_start = 1 + max(
        body.rfind(";", 0, m.start()), body.rfind("{", 0, m.start()), body.rfind("}", 0, m.start())
    )
    stmt_brace = body.find("{", m.end())
    stmt = body[stmt_start : stmt_brace if stmt_brace >= 0 else m.end()]

    # `<acq>(..)?;` — the gate-absent value PROPAGATES out of this fn; the disposition is the
    # caller's. Checked on the acquisition's OWN line, before any shape guessing.
    eol = body.find("\n", m.start())
    if PROPAGATES.search(body[m.start() : eol if eol > 0 else len(body)]):
        return ("propagates", body[m.start() : eol if eol > 0 else len(body)])

    if re.search(r"\.unwrap_or(_else|_default)?\s*\(", body[m.start() : m.start() + 400]):
        um = re.search(r"\.unwrap_or(?:_else|_default)?\s*\(", body[m.start() :])
        if um:
            start = m.start() + um.end() - 1
            depth, i = 0, start
            while i < len(body):
                if body[i] == "(":
                    depth += 1
                elif body[i] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            return ("unwrap_or", body[start : i + 1])

    if re.match(r"\s*let\s+Some\s*\(", stmt) and "else" in body[m.end() : stmt_brace + 8 if stmt_brace > 0 else m.end()]:
        eb = body.find("else", m.end())
        ob = body.find("{", eb)
        return ("let-else", body[ob : brace_block(body, ob)])

    if re.search(r"\bif\b", stmt) and not re.search(r"=\s*match\b", stmt):
        # `if let Some(..) = <acq> {`, `&& let Some(..) = <acq> {`, or a plain `if <acq>() {`
        # (the `dregg-deploy` shape: `if <gate>_available() { return match .. } <fallthrough>`).
        if stmt_brace < 0:
            return ("UNPARSED", "")
        kind = "if-let" if re.search(r"let\s+Some", stmt) else "if-avail"
        after = brace_block(body, stmt_brace)
        tail = body[after:]
        if re.match(r"\s*else\s*\{", tail):
            ob = after + tail.index("{")
            return (kind + "-else", body[ob : brace_block(body, ob)])
        if re.match(r"\s*else\s+if\b", tail):
            return (kind + "-else-if", tail)
        return (kind + "-fallthrough", tail)

    if re.match(r"\s*(?:return\s+)?match\b", stmt) or re.search(r"=\s*match\b", stmt):
        if stmt_brace < 0:
            return ("UNPARSED", "")
        arms = body[stmt_brace : brace_block(body, stmt_brace)]
        keep = []
        # Gate-ABSENT arms only: `None`, `Err(..)`, `Err`, `_`. NOT `Ok(None)` — that is the gate
        # RUNNING and declining, a legitimate verified verdict, not a missing gate.
        for am in re.finditer(r"(?m)^\s*(None\b|Err\s*\([^)]*\)|Err\b|_)\s*(?:\|[^=]*)?=>", arms):
            rest = arms[am.end() :]
            if rest.lstrip().startswith("{"):
                ob = am.end() + rest.index("{")
                keep.append(arms[ob : brace_block(arms, ob)])
            else:
                nxt = rest.find("\n")
                keep.append(rest[: nxt if nxt > 0 else len(rest)])
        return ("match-none-arm", "\n".join(keep))

    if PROPAGATES.search(stmt):
        return ("propagates", stmt)
    return ("UNPARSED", stmt)


# ── classification ──────────────────────────────────────────────────────────────────
def resolve_calls(region: str, src: str, depth: int) -> str:
    """Inline the bodies of same-file helpers the region tail-calls (non-cfg(test) defs only)."""
    if depth <= 0:
        return region
    extra = []
    for cm in LOCAL_CALL.finditer(region):
        callee = cm.group(1)
        if callee in ("if", "match", "return", "unwrap_or", "some", "ok", "err", "clone", "len",
                      "iter", "map", "push", "insert", "get", "new", "collect", "to_string",
                      "unwrap_or_else", "unwrap_or_default", "is_some", "is_none", "as_ref"):
            continue
        for _attrs, cbody in fn_bodies(src, callee):
            extra.append(resolve_calls(strip_cfg_test(cbody), src, depth - 1))
    return region + "\n" + "\n".join(extra)


def _decomment(text: str) -> str:
    """Drop `//` line comments and `///`/`//!` docs (they narrate refusals that are not there)."""
    return "\n".join(re.sub(r"//.*", "", ln) for ln in text.splitlines())


def classify(region: str, shape: str, allow: list[str], src: str) -> tuple[str, str]:
    """-> (PASS|FAIL, reason)."""
    if shape == "propagates":
        return ("PASS", "the gate-absent value PROPAGATES (`?`) — the disposition is the caller's; "
                        "register the CALLER to check where it lands")
    if shape in ("NO-ACQUISITION", "UNPARSED", ""):
        return ("FAIL", f"could not extract the gate-absent region (shape={shape or 'none'}). "
                        "This guard fails CLOSED: re-point the row or teach the checker the shape.")
    region = _decomment(strip_cfg_test(region))
    deep = _decomment(resolve_calls(region, src, 2))
    narrowings = [t[len("narrow:"):] for t in allow if t.startswith("narrow:")]
    discriminators = [t for t in allow if not t.startswith("narrow:")]

    # A DECLARED NARROWING: the row says this site's no-gate path is a named, deliberately narrow
    # local decision (e.g. federation's "only genesis SEEDS", which needs no Lean).
    for tok in narrowings:
        if tok in deep:
            return ("PASS", f"gate-absent path is the DECLARED NARROWING `{tok}` "
                            f"(registry-declared, not an unverified re-implementation)")

    # Ordered walk of the region: whichever terminal comes first decides.
    for line in region.splitlines():
        if not line.strip():
            continue
        tok_here = next((t for t in discriminators if t and t in line), None)
        if tok_here:
            # A DECLARED DISCRIMINATION. The non-exempt arm must still REFUSE somewhere below.
            if REFUSAL.search(deep):
                return ("PASS", f"gate-absent path is DECLARED-discriminated on `{tok_here}` and "
                                f"the non-exempt arm REFUSES "
                                f"(`{REFUSAL.search(deep).group(0).strip()}`)")
            return ("FAIL", f"the row DECLARES the carve-out `{tok_here}` but the gate-absent path "
                            f"has NO refusal on the non-exempt arm — the declaration is decoration.")
        rm, am = REFUSAL.search(line), accepting(line)
        if rm and (not am or rm.start() <= am.start()):
            return ("PASS", f"gate-absent path REFUSES immediately (`{rm.group(0).strip()}`)")
        if am:
            return ("FAIL", f"gate-absent path reaches an ACCEPTING verdict "
                            f"(`{am.group(0).strip()}`) with no refusal and no declared carve-out "
                            f"— A MISSING VERIFIED GATE CAN ADMIT.")

    # Nothing terminal in the region itself: resolve same-file helpers (depth <= 2).
    for line in deep.splitlines():
        rm, am = REFUSAL.search(line), accepting(line)
        if am and (not rm or am.start() < rm.start()):
            return ("FAIL", f"gate-absent path tail-calls a same-file helper that can ACCEPT "
                            f"(`{am.group(0).strip()}`) — the unverified Rust decider is LIVE on "
                            f"the no-gate path.")
    if REFUSAL.search(deep):
        return ("PASS", "gate-absent path resolves (depth<=2) to a refusing helper only")
    return ("FAIL", "could not find ANY terminal verdict on the gate-absent path. This guard "
                    "fails CLOSED — prove the refusal, or declare the carve-out / narrowing.")


# ── driver ──────────────────────────────────────────────────────────────────────────
def read_rows(tsv: str):
    with open(tsv, encoding="utf-8") as fh:
        for lineno, raw in enumerate(fh, 1):
            line = raw.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            parts = line.split("\t")
            if len(parts) < 5:
                sys.stderr.write(f"gate-dataflow: FATAL — {tsv}:{lineno} needs 5 tab-separated "
                                 f"columns (file, fn, acquire, allow_cfg, note), got {len(parts)}\n")
                sys.exit(2)
            yield lineno, parts[0], parts[1], parts[2], parts[3], parts[4]


def check(root: str, tsv: str, quiet: bool = False) -> int:
    """`quiet` suppresses per-site lines — used by the self-test, whose fixture is red ON PURPOSE
    and must not print an alarming FAIL into the CI log."""
    failures = 0
    checked = 0
    for lineno, rel, fn, acquire, allow, note in read_rows(tsv):
        path = os.path.join(root, rel)
        if not os.path.isfile(path):
            sys.stderr.write(f"\ngate-dataflow: FATAL — decision site '{rel}' does not exist "
                             f"({tsv}:{lineno}). The live decider moved; this gate would check "
                             f"NOTHING. Re-point the row. ({note})\n")
            return 2
        src = open(path, encoding="utf-8").read()
        bodies = fn_bodies(src, fn)
        if not bodies:
            sys.stderr.write(f"\ngate-dataflow: FATAL — no non-cfg(test) `fn {fn}` in {rel} "
                             f"({tsv}:{lineno}). Re-point the row. ({note})\n")
            return 2
        acq = re.compile(acquire)
        allow_cfg = [t.strip() for t in allow.split("|") if t.strip() and t.strip() != "-"]
        for attrs, body in bodies:
            checked += 1
            shape, region = gate_absent_region(strip_cfg_test(body), acq)
            verdict, reason = classify(region, shape, allow_cfg, src)
            tag = f"{rel} :: {fn}"
            if verdict == "PASS":
                if not quiet:
                    print(f"  \033[32mPASS\033[0m  {tag}  [{shape}] {reason}")
            else:
                failures += 1
                if not quiet:
                    sys.stderr.write(f"  \033[31mFAIL\033[0m  {tag}  [{shape}] {reason}\n"
                                     f"        ({note})\n")
    if not quiet:
        print(f"  -- {checked} decision site(s) checked, {failures} failing.")
    return 1 if failures else 0


# ── self-test: prove the guard CAN GO RED ───────────────────────────────────────────
FIXTURE_OPEN = '''
impl E {
    pub fn decide(rows: &[u32]) -> Result<(), Error> {
        if let Some(oracle) = installed_thing_oracle() {
            return oracle.decide(rows);
        }
        Self::unverified_rust_fallback(rows)
    }
    fn unverified_rust_fallback(rows: &[u32]) -> Result<(), Error> {
        if rows.is_empty() { return Err(Error::Bad); }
        Ok(())
    }
}
'''
FIXTURE_CLOSED = '''
impl E {
    pub fn decide(rows: &[u32]) -> Result<(), Error> {
        if let Some(oracle) = installed_thing_oracle() {
            return oracle.decide(rows);
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            return Err(Error::GateUnavailable);
        }
        #[cfg(target_arch = "wasm32")]
        {
            Self::unverified_rust_fallback(rows)
        }
    }
    #[cfg(target_arch = "wasm32")]
    fn unverified_rust_fallback(rows: &[u32]) -> Result<(), Error> { Ok(()) }
}
'''


def self_test() -> int:
    print("\n\033[1m== gate-dataflow SELF-TEST (the guard must be able to go RED) ==\033[0m")
    bad = 0
    with tempfile.TemporaryDirectory() as td:
        for name, text, want in (("fail_open.rs", FIXTURE_OPEN, 1),
                                 ("fail_closed.rs", FIXTURE_CLOSED, 0)):
            open(os.path.join(td, name), "w", encoding="utf-8").write(text)
        tsv = os.path.join(td, "fixture.tsv")
        with open(tsv, "w", encoding="utf-8") as fh:
            fh.write("fail_open.rs\tdecide\tinstalled_thing_oracle\t"
                     'target_arch = "wasm32"\tsynthetic fall-open fixture\n')
        got = check(td, tsv, quiet=True)
        if got != 1:
            sys.stderr.write("  \033[31mFAIL\033[0m  the checker did NOT go red on the synthetic "
                             "fall-open fixture — it cannot detect the class it exists for.\n")
            bad += 1
        else:
            print("  \033[32mPASS\033[0m  checker goes RED on a synthetic fall-open decider.")
        with open(tsv, "w", encoding="utf-8") as fh:
            fh.write("fail_closed.rs\tdecide\tinstalled_thing_oracle\t"
                     'target_arch = "wasm32"\tsynthetic fail-closed fixture\n')
        got = check(td, tsv, quiet=True)
        if got != 0:
            sys.stderr.write("  \033[31mFAIL\033[0m  the checker went red on a correctly "
                             "fail-CLOSED decider — it would block the fix it asks for.\n")
            bad += 1
        else:
            print("  \033[32mPASS\033[0m  checker is GREEN on a synthetic fail-closed decider.")
    return 1 if bad else 0


def main(argv: list[str]) -> int:
    root = os.environ.get("CI_INVARIANTS_ROOT") or os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..")
    )
    tsv = os.environ.get("CI_INVARIANTS_DATAFLOW_TSV") or os.path.join(
        os.path.dirname(__file__), "gate-dataflow.tsv"
    )
    if "--self-test" in argv:
        return self_test()
    if not os.path.isfile(tsv):
        sys.stderr.write(f"gate-dataflow: FATAL — registry '{tsv}' is missing. This gate cannot "
                         f"run without it.\n")
        return 2
    rc = self_test()
    if rc:
        return rc
    print("\n\033[1m== Invariant 6 — NO ACCEPTING FALLTHROUGH ON A MISSING VERIFIED GATE ==\033[0m")
    return check(root, tsv)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
