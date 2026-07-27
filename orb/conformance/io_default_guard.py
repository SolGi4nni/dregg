#!/usr/bin/env python3
"""CI guard: every conformance runner must drive the reactor the binary ships.

WHY THIS EXISTS
---------------
Production defaults to `IoMode::Auto` (crates/dataplane/src/main.rs), which is
io_uring on Linux and the kqueue reactor on macOS/BSD. For a long time EVERY
conformance runner instead pinned `--io blocking`, the portable
thread-per-connection fallback. The whole gate therefore attested a reactor
nobody deploys.

That is not hypothetical. Two lanes were wired only on the portable path and the
harness could not see it, because the harness only ever drove the path where
they worked:

  * WebSocket upgrade — ~190 proven Ws/ theorems and a 514/517 Autobahn score
    were unreachable on the default reactor until the upgrade fork was wired
    into uring.rs / kqueue.rs.
  * the LEGACY proxy_hook lane — still blocking-only today
    (crates/dataplane/src/blocking.rs, `!interp::enabled() && is_proxy_path`);
    uring.rs has no counterpart, so with DRORB_EFFECT_SEAM unset a /api request
    404s on io_uring instead of forwarding. conformance/proxy/battery.py scored
    14/14 by pinning `--io blocking` AND unsetting the seam.

So: a runner that pins a reactor other than the shipped default is a silent
hole. This guard makes it loud.

WHAT IT CHECKS
--------------
Every `--io` argument in a conformance runner is resolved to the reactor it
would actually select on THIS platform, and compared to the binary's own
default. A runner that resolves to a different reactor FAILS unless it is
listed in EXEMPT below with a reason.

`auto` is the preferred spelling: it TRACKS the binary. Pinning `uring` on Linux
selects the same reactor today but stops tracking, so it is reported as PINNED
(a warning, not a failure).

USAGE
    python3 conformance/io_default_guard.py          # exit 1 on any drift
    python3 conformance/io_default_guard.py --list   # ledger, always exit 0
"""
import ast
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
MAIN_RS = os.path.join(ROOT, "crates", "dataplane", "src", "main.rs")

MODES = ("auto", "blocking", "uring", "kqueue")

# ---------------------------------------------------------------------------
# Runners that legitimately pin a non-default reactor. Every entry needs a REASON
# that says what blocking-only (or uring-only) code path it exercises. "It was
# red on auto" is NOT a reason — a red default-reactor gate is the finding, and
# re-pinning to green is exactly the failure mode this guard exists to prevent.
#
# `UNVALIDATED` marks a pin inherited from before the flip that nobody has yet
# run on the deployed reactor. It is tracked debt, not a justification.
# ---------------------------------------------------------------------------
EXEMPT = {
    # (EMPTY — and that is the point.)
    #
    # 2026-07-25: the ELEVEN inherited `UNVALIDATED` pins were each run on BOTH
    # reactors and compared. All eleven now default to the reactor that ships.
    # Nine were a clean no-delta. Two were not what this ledger claimed:
    #
    #   tls/battery_run.sh   its `--io` site is DEAD CODE. The script `exec`s to
    #                        tls13_battery_run.sh near the top, so the launch
    #                        below that forward never runs. The ledger was
    #                        carrying a phantom pin for a line with no behavior.
    #
    #   dos/battery.py       flipping it turned it RED: 8/8 on blocking, 6/8 on
    #                        io_uring, same binary, same configs. `dos-rate-429`
    #                        and `dos-conn-limit-503` do not fire on the shipped
    #                        reactor because the per-source standing state is a
    #                        PER-SHARD field there, not the process-wide table
    #                        the blocking host uses. That is a PRODUCT bug, not
    #                        a harness one — see dos/FINDING-per-shard-standing.md.
    #                        The runner therefore STAYS on the shipped reactor
    #                        and the battery STAYS red. Re-pinning it to
    #                        `blocking` to recover 8/8 would hide a
    #                        production-off DoS gate behind a green score, which
    #                        is exactly the failure this guard exists to catch.
    #
    # Adding a row back here needs the blocking-only code path it exercises,
    # named. "It was red on auto" is still not a reason.
}

SKIP_DIRS = {"__pycache__", "reports", "results", "dual_path_out", "site",
             "ref", "outside", "_tlspipe", "lane18990", "multi-run", "bin",
             "configs", "cgi-bin", "external", "_out"}


# ---------------------------------------------------------------------------
# What reactor does a mode string select on this platform?
# ---------------------------------------------------------------------------
def reactor_of(mode, platform=None):
    plat = platform or sys.platform
    linux = plat.startswith("linux")
    if mode == "auto":
        return "io_uring" if linux else "kqueue"
    if mode == "blocking":
        return "blocking"
    if mode == "uring":
        # main.rs falls back to io_uring on Linux; off Linux --io uring warns
        # and takes the kqueue reactor.
        return "io_uring" if linux else "kqueue"
    if mode == "kqueue":
        # Symmetrically, --io kqueue on Linux warns and falls back to io_uring.
        return "io_uring" if linux else "kqueue"
    return "?" + str(mode)


def binary_default_mode():
    """The `--io` default the shipped binary applies, read from main.rs."""
    try:
        src = open(MAIN_RS).read()
    except OSError:
        return None
    m = re.search(r"\.unwrap_or\(IoMode::(\w+)\)", src)
    return m.group(1).lower() if m else None


# ---------------------------------------------------------------------------
# Extraction: find every --io argument and resolve its default
# ---------------------------------------------------------------------------
def _py_env_default(node):
    """os.environ.get("X", "mode") -> ("X", "mode"); else None."""
    if not isinstance(node, ast.Call):
        return None
    f = node.func
    if not (isinstance(f, ast.Attribute) and f.attr == "get"):
        return None
    if len(node.args) != 2:
        return None
    key, dflt = node.args
    if isinstance(key, ast.Constant) and isinstance(dflt, ast.Constant):
        return (key.value, dflt.value)
    return None


def scan_python(path, rel):
    """Sites are `--io` inside an argv list/tuple, so docstrings never match."""
    try:
        tree = ast.parse(open(path).read())
    except (OSError, SyntaxError) as e:
        return [(rel, 0, "?", f"unparseable: {e}")]
    # module-level NAME = os.environ.get("K", "mode")
    consts = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name):
            ed = _py_env_default(node.value)
            if ed:
                consts[node.targets[0].id] = (ed[1], f"${ed[0]}")
            elif isinstance(node.value, ast.Constant) \
                    and node.value.value in MODES:
                consts[node.targets[0].id] = (node.value.value, "literal")
    out = []
    for node in ast.walk(tree):
        if not isinstance(node, (ast.List, ast.Tuple)):
            continue
        elts = list(node.elts)
        for i, e in enumerate(elts[:-1]):
            if not (isinstance(e, ast.Constant) and e.value == "--io"):
                continue
            nxt = elts[i + 1]
            line = getattr(nxt, "lineno", node.lineno)
            if isinstance(nxt, ast.Constant):
                out.append((rel, line, nxt.value, "literal"))
            elif isinstance(nxt, ast.Name) and nxt.id in consts:
                mode, via = consts[nxt.id]
                out.append((rel, line, mode, f"{nxt.id} <- {via}"))
            else:
                ed = _py_env_default(nxt)
                if ed:
                    out.append((rel, line, ed[1], f"${ed[0]}"))
                else:
                    out.append((rel, line, None, "unresolved expression"))
    return out


SH_VAR_DEFAULT = re.compile(r'^\s*(\w+)="?\$\{(\w+):-(\w+)\}"?\s*$', re.M)


def scan_shell(path, rel):
    try:
        text = open(path).read()
    except OSError:
        return []
    consts = {m.group(1): (m.group(3), f"${m.group(2)}")
              for m in SH_VAR_DEFAULT.finditer(text)}
    out = []
    for n, line in enumerate(text.splitlines(), 1):
        if line.lstrip().startswith("#"):
            continue
        for m in re.finditer(r'--io\s+("?\$\{?(\w+)\}?"?|[A-Za-z]+)', line):
            tok, var = m.group(1), m.group(2)
            if var:
                if var in consts:
                    mode, via = consts[var]
                    out.append((rel, n, mode, f"${var} <- {via}"))
                else:
                    out.append((rel, n, None, f"unresolved ${var}"))
            else:
                out.append((rel, n, tok.strip('"'), "literal"))
    return out


def collect():
    sites = []
    for dirpath, dirnames, filenames in os.walk(HERE):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for fn in sorted(filenames):
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, HERE)
            if fn.endswith(".py"):
                sites += scan_python(full, rel)
            elif fn.endswith(".sh"):
                sites += scan_shell(full, rel)
    return sorted(sites)


def main():
    list_only = "--list" in sys.argv
    dflt = binary_default_mode()
    if dflt is None:
        print("GUARD ERROR: could not read the binary's --io default from "
              f"{MAIN_RS}", file=sys.stderr)
        return 2
    want = reactor_of(dflt)
    print(f"binary default : IoMode::{dflt.capitalize()} -> {want} "
          f"on {sys.platform}")
    print(f"scanning       : {HERE}")
    print()

    bad, pinned, exempt, ok, unresolved = [], [], [], [], []
    for rel, line, mode, how in collect():
        if mode is None:
            unresolved.append((rel, line, how))
            continue
        got = reactor_of(mode)
        if got != want:
            (exempt if rel in EXEMPT else bad).append((rel, line, mode, how, got))
        elif mode != dflt:
            pinned.append((rel, line, mode, how))
        else:
            ok.append((rel, line, mode, how))

    if ok:
        print(f"OK ({len(ok)}) — track the binary default:")
        for rel, line, mode, how in ok:
            print(f"    {rel}:{line}  --io {mode}  ({how})")
        print()
    if pinned:
        print(f"PINNED ({len(pinned)}) — same reactor as the default here, but "
              f"hardcoded, so it stops tracking the binary:")
        for rel, line, mode, how in pinned:
            print(f"    {rel}:{line}  --io {mode}  ({how})")
        print()
    if unresolved:
        print(f"UNRESOLVED ({len(unresolved)}) — could not statically determine "
              f"the mode; review by hand:")
        for rel, line, how in unresolved:
            print(f"    {rel}:{line}  ({how})")
        print()
    if exempt:
        print(f"EXEMPT ({len(exempt)}) — pinned off the default WITH a recorded "
              f"reason. This is a debt ledger, not a clean bill:")
        for rel, line, mode, how, got in exempt:
            print(f"    {rel}:{line}  --io {mode} -> {got}")
            print(f"        {EXEMPT[rel]}")
        print()

    if bad:
        print(f"FAIL ({len(bad)}) — these runners drive a reactor the binary "
              f"does NOT ship, with no recorded reason:")
        for rel, line, mode, how, got in bad:
            print(f"    {rel}:{line}  --io {mode} -> {got}  (want {want})  "
                  f"({how})")
        print()
        print("  Fix by defaulting the runner to the shipped mode and keeping")
        print("  the old value selectable via its env var. If the runner really")
        print("  must pin, add it to EXEMPT with the blocking-only code path it")
        print("  exercises. Do NOT re-pin a runner just because it went red on")
        print("  the default reactor — that red IS the finding.")
        if not list_only:
            return 1

    print(f"summary: {len(ok)} ok, {len(pinned)} pinned, {len(exempt)} exempt, "
          f"{len(unresolved)} unresolved, {len(bad)} failing")
    return 0


if __name__ == "__main__":
    sys.exit(main())
