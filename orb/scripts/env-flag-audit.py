#!/usr/bin/env python3
"""env-flag-audit.py — no `DRORB_*` flag may be silently reactor-scoped, and no
`DRORB_SPAN` may silently lose ACME HTTP-01.

WHY THIS EXISTS
---------------
`DRORB_GATEWAY` was read by exactly one of the three IO reactors
(`blocking.rs`) while production runs the other one (io_uring). An operator who
set it got a different serve than the one they configured, and NOTHING was
logged. It took a driven audit to find, months later.

`docs/gateway/ENV-BY-REACTOR.md` now tables every flag against the reactors that
honor it, and `main.rs` carries `REACTOR_SCOPED_FLAGS` so the asymmetric ones warn
at startup. But BOTH are hand-maintained. A new reactor-specific flag added
without its row is invisible again — the exact original defect, one commit away.

The same shape bites `DRORB_SPAN`: only 4 of the 25 selectable spans answer
`GET /.well-known/acme-challenge/<token>` (docs/gateway/ACME-SPAN-AUDIT.md). The
other 21 are selectable with no warning, and an operator who picks one loses
certificate renewal and finds out ~90 days later. `main.rs` gates that on two
constants; those constants can rot exactly like the flag table can.

So this script is the ratchet for both hand-maintained tables. It is pure source
analysis — no build, no running server, well under a second.

WHAT IT CHECKS
--------------
A. flags
   A1 UNDOCUMENTED   every `"DRORB_*"` literal read in crates/dataplane/src must
                     appear in docs/gateway/ENV-BY-REACTOR.md.
   A2 CONST-VS-DOC   `REACTOR_SCOPED_FLAGS` (main.rs) and the doc's asymmetric
                     rows must name the same flags with the same honoring sets.
   A3 ASYMMETRIC     read-site analysis: a flag whose reading module is NOT
                     reachable from all three reactors must have a row. This is
                     the check that would have caught `DRORB_GATEWAY`.
   A4 NO-HOME        a flag no reactor reads (read only by `main.rs`, or by a
                     module on its own thread) must be declared EITHER a
                     reactor-mechanism knob (a `REACTOR_SCOPED_FLAGS` row) OR
                     process-level (the doc's process/listener/subsystem list).
                     `DRORB_SHARDS` failed this: read in main.rs, meaningless to
                     the thread-per-connection blocking host, no row, no warning.
   A5 OVERCLAIM      a row may not name a reactor whose dispatch cannot reach the
                     reading module at all.

B. spans
   B1 SELECTABLE     `SELECTABLE_SPANS` (main.rs) == the `Some("N") => Some(N)`
                     arms of `span_number()` (serve.rs). A sibling lane adding a
                     span arm without touching the guard fails here.
   B2 ACME-SET       `ACME_SERVING_SPANS` (main.rs) == the audit table rows whose
                     "serves ACME" cell is YES. The guard's allowlist is DERIVED
                     from the driven audit, not hand-asserted.
   B3 AUDITED        every selectable span has a row in the audit table.

REACHABILITY, AND ITS HONEST LIMIT
----------------------------------
A2/A3 need "which reactors call the module that reads this flag". That is
approximated by the `crate::<mod>` reference graph, closed transitively from the
three reactor files as roots, with every edge INTO `blocking`/`uring`/`kqueue`
CUT. The cut is load-bearing and deliberate:

  * `serve.rs` mentions `crate::uring` and `crate::kqueue` (shard staging), so
    without the cut every module would reach every reactor and the analysis
    would say nothing;
  * all three reactors hand a proxy-taken connection to
    `blocking::handle_conn_prefilled`, so without the cut `blocking`-only
    modules (`stream_serve`) would look symmetric.

Reference-graph reachability OVER-approximates (a `crate::m` mention is not a
call). So the two directions are treated differently, and only the sound one
fails:

  * computed set NOT all three  ->  hard: no reactor path exists even generously,
                                    so a row is REQUIRED (A3);
  * computed set all three but a row claims fewer  ->  informational: the const is
                                    stricter than the grep, which only ever makes
                                    the operator warning louder.

USAGE
    scripts/env-flag-audit.py            full report, exit 1 on any FAIL
    scripts/env-flag-audit.py --check    same, quiet on success (the CI mode)
    scripts/env-flag-audit.py --list     the derived tables, always exit 0
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SRC = os.path.join(ROOT, "crates", "dataplane", "src")
MAIN_RS = os.path.join(SRC, "main.rs")
SERVE_RS = os.path.join(SRC, "serve.rs")
ENV_DOC = os.path.join(ROOT, "docs", "gateway", "ENV-BY-REACTOR.md")
SPAN_DOC = os.path.join(ROOT, "docs", "gateway", "ACME-SPAN-AUDIT.md")

REACTORS = ("blocking", "io_uring", "kqueue")
# The reactor MODULE names (uring.rs is the io_uring reactor).
REACTOR_MODULE = {"blocking": "blocking", "io_uring": "uring", "kqueue": "kqueue"}
MODULE_REACTOR = {v: k for k, v in REACTOR_MODULE.items()}

FLAG_LIT = re.compile(r'"(DRORB_[A-Z0-9_]+)"')
CRATE_REF = re.compile(r"\bcrate::([a-z_][a-z_0-9]*)")

# Regions of a source file the flag scan must NOT treat as read sites: the
# ratchet tables themselves name flags as data. Delimited by markers in the
# source so this stays robust against the const being edited or moved.
REGION_BEGIN = "RATCHET-TABLE-BEGIN"
REGION_END = "RATCHET-TABLE-END"


# --------------------------------------------------------------------------- #
# source scanning
# --------------------------------------------------------------------------- #
def code_lines(path):
    """(lineno, text) for lines that are CODE: line comments and the marked
    ratchet-table regions are dropped. A flag named in a doc-comment or in the
    guard's own table is not a read site."""
    out = []
    in_region = False
    with open(path, encoding="utf-8", errors="replace") as fh:
        for n, raw in enumerate(fh, 1):
            if REGION_BEGIN in raw:
                in_region = True
                continue
            if REGION_END in raw:
                in_region = False
                continue
            if in_region:
                continue
            s = raw.lstrip()
            if s.startswith("//"):
                continue
            out.append((n, raw))
    return out


def rust_files():
    for dirpath, _dirs, names in os.walk(SRC):
        for nm in sorted(names):
            if nm.endswith(".rs"):
                yield os.path.join(dirpath, nm)


def module_of(path):
    """Module path for a source file: src/foo.rs -> 'foo', src/tls/ondemand.rs ->
    'tls::ondemand', src/main.rs -> 'main'."""
    rel = os.path.relpath(path, SRC)[: -len(".rs")]
    return rel.replace(os.sep, "::")


def scan_sources():
    """-> (flag -> {module: [(file, line)]}, module -> {referenced modules})"""
    reads = {}
    edges = {}
    modules = set()
    for path in rust_files():
        mod = module_of(path)
        modules.add(mod)
        lines = code_lines(path)
        refs = edges.setdefault(mod, set())
        for n, text in lines:
            for m in FLAG_LIT.finditer(text):
                reads.setdefault(m.group(1), {}).setdefault(mod, []).append(
                    (os.path.relpath(path, ROOT), n)
                )
            for m in CRATE_REF.finditer(text):
                refs.add(m.group(1))
    # A parent module owns its file-submodules (`mod ondemand;`), so a reference
    # to `crate::tls` reaches `tls::ondemand`.
    for mod in list(modules):
        for other in modules:
            if other.startswith(mod + "::"):
                edges.setdefault(mod, set()).add(other)
    return reads, edges, modules


def reachable(edges, modules, root_module):
    """Modules reachable from one reactor module. Every edge INTO a reactor
    module is CUT (see the module docstring); the root itself is included."""
    cut = set(REACTOR_MODULE.values())
    seen = {root_module}
    stack = [root_module]
    while stack:
        cur = stack.pop()
        for nxt in edges.get(cur, ()):  # noqa: B007
            if nxt in cut or nxt not in modules or nxt in seen:
                continue
            seen.add(nxt)
            stack.append(nxt)
    # Expand a bare parent reference to its submodules already handled above.
    return seen


# --------------------------------------------------------------------------- #
# main.rs: REACTOR_SCOPED_FLAGS + the span constants
# --------------------------------------------------------------------------- #
def parse_reactor_scoped_flags():
    text = open(MAIN_RS, encoding="utf-8").read()
    m = re.search(
        r"const\s+REACTOR_SCOPED_FLAGS\s*:.*?=\s*&\[(.*?)\n\];", text, re.S
    )
    if not m:
        die("could not find `const REACTOR_SCOPED_FLAGS` in crates/dataplane/src/main.rs")
    body = m.group(1)
    rows = {}
    for var, lst in re.findall(r'\("(DRORB_[A-Z0-9_]+)",\s*&\[([^\]]*)\]\)', body):
        rows[var] = tuple(sorted(re.findall(r'"([a-z_0-9]+)"', lst)))
    return rows


def parse_span_const(name):
    text = open(MAIN_RS, encoding="utf-8").read()
    m = re.search(r"const\s+%s\s*:\s*&\[u8\]\s*=\s*&\[(.*?)\];" % name, text, re.S)
    if not m:
        die(f"could not find `const {name}` in crates/dataplane/src/main.rs")
    return sorted(int(x) for x in re.findall(r"\b(\d+)\b", m.group(1)))


def parse_span_number_arms():
    """The selectable set as serve.rs actually parses it."""
    text = open(SERVE_RS, encoding="utf-8").read()
    m = re.search(r"fn span_number\(\).*?\n\}", text, re.S)
    if not m:
        die("could not find `fn span_number()` in crates/dataplane/src/serve.rs")
    return sorted(
        int(a)
        for a, b in re.findall(r'Some\("(\d+)"\)\s*=>\s*Some\((\d+)\)', m.group(0))
        if a == b
    )


# --------------------------------------------------------------------------- #
# docs
# --------------------------------------------------------------------------- #
def parse_env_doc():
    """-> (flags mentioned anywhere, {flag: honoring tuple} for table rows,
    process-level flag names, process-level wildcard prefixes)"""
    mentioned = set()
    rows = {}
    process = set()
    wildcards = set()
    section = ""
    with open(ENV_DOC, encoding="utf-8") as fh:
        for raw in fh:
            if raw.startswith("#"):
                section = raw.strip("# \n")
            for f in re.findall(r"DRORB_[A-Z0-9_]+", raw):
                mentioned.add(f)
            if section.lower().startswith("process /"):
                for f in re.findall(r"`(DRORB_[A-Z0-9_]+)`", raw):
                    process.add(f)
                for f in re.findall(r"`(DRORB_[A-Z0-9_]*)\*`", raw):
                    wildcards.add(f)
                continue
            if not raw.lstrip().startswith("|"):
                continue
            cells = [c.strip() for c in raw.strip().strip("|").split("|")]
            # The blocking/io_uring/kqueue check-mark tables:
            #   | `VAR` | ✔ | ✔ | ✘ | read site |
            if len(cells) < 5:
                continue
            fm = re.match(r"^`(DRORB_[A-Z0-9_]+)`$", cells[0])
            if fm:
                rows[fm.group(1)] = tuple(
                    r for r, cell in zip(REACTORS, cells[1:4]) if "✔" in cell
                )
    return mentioned, rows, process, wildcards


def parse_env_doc_mechanism():
    """The `| var | honored by | what it names |` table, parsed separately: its
    honoring set is prose, not check marks."""
    rows = {}
    with open(ENV_DOC, encoding="utf-8") as fh:
        for raw in fh:
            if not raw.lstrip().startswith("|"):
                continue
            cells = [c.strip() for c in raw.strip().strip("|").split("|")]
            if len(cells) != 3:
                continue
            fm = re.match(r"^`(DRORB_[A-Z0-9_]+)`$", cells[0])
            if not fm:
                continue
            honored = tuple(r for r in REACTORS if r in cells[1])
            if honored:
                rows[fm.group(1)] = honored
    return rows


def parse_span_audit():
    """The round-1 span table: {span or 'unset': serves-acme bool}."""
    table = {}
    header_seen = False
    with open(SPAN_DOC, encoding="utf-8") as fh:
        for raw in fh:
            if not raw.lstrip().startswith("|"):
                continue
            cells = [c.strip() for c in raw.strip().strip("|").split("|")]
            if not header_seen:
                if cells and cells[0].lower() == "span" and len(cells) >= 3:
                    header_seen = True
                continue
            if len(cells) < 3:
                continue
            key = cells[0].strip("*_ ")
            verdict = cells[2].replace("*", "").strip().lower()
            if verdict not in ("yes", "no"):
                continue
            if key == "(unset)":
                table["unset"] = verdict == "yes"
            elif key.isdigit():
                table[int(key)] = verdict == "yes"
            else:
                # a later table (the deployment crossings) — stop at the first
                # row that is not a span number.
                break
    if not header_seen:
        die(f"could not find the span table (a `| span |` header) in {SPAN_DOC}")
    return table


# --------------------------------------------------------------------------- #
# report
# --------------------------------------------------------------------------- #
FAILS = []
NOTES = []


def die(msg):
    print(f"ENV-FLAG-AUDIT: fatal: {msg}", file=sys.stderr)
    sys.exit(2)


def fail(code, msg):
    FAILS.append((code, msg))


def note(code, msg):
    NOTES.append((code, msg))


def main(argv):
    mode = "report"
    for a in argv[1:]:
        if a == "--check":
            mode = "check"
        elif a == "--list":
            mode = "list"
        elif a in ("-h", "--help"):
            print(__doc__)
            return 0
        else:
            print(f"env-flag-audit.py: unknown argument {a}", file=sys.stderr)
            return 2

    reads, edges, modules = scan_sources()
    reach = {
        r: reachable(edges, modules, REACTOR_MODULE[r]) for r in REACTORS
    }
    const_rows = parse_reactor_scoped_flags()
    mentioned, doc_rows, doc_process, doc_wildcards, = parse_env_doc()
    doc_rows.update(parse_env_doc_mechanism())

    def honored_by(flag):
        mods = set(reads.get(flag, {}))
        return tuple(r for r in REACTORS if mods & reach[r])

    def is_process_documented(flag):
        if flag in doc_process:
            return True
        return any(flag.startswith(w) for w in doc_wildcards)

    flags = sorted(reads)

    if mode == "list":
        print(f"{'flag':34} {'read in':44} {'reactors that can reach it':28} row")
        for f in flags:
            mods = ",".join(sorted(reads[f]))
            h = ",".join(honored_by(f)) or "-"
            row = ",".join(const_rows[f]) if f in const_rows else "-"
            print(f"{f:34} {mods:44} {h:28} {row}")
        print()
        print(f"selectable spans (serve.rs): {parse_span_number_arms()}")
        print(f"ACME-serving spans (audit):  "
              f"{sorted(k for k, v in parse_span_audit().items() if v is True and k != 'unset')}")
        return 0

    # ---- A1 undocumented ------------------------------------------------- #
    # The doc documents two subsystems by WILDCARD ("every `DRORB_TLS_*` (the TLS
    # listener thread), every `DRORB_ACME_*` (the renewal thread)") because they
    # run on their own threads and are reactor-independent by construction. A
    # wildcard satisfies A1; the count is reported so the blanket stays visible.
    by_wildcard = 0
    for f in flags:
        if f in mentioned:
            continue
        if any(f.startswith(w) for w in doc_wildcards):
            by_wildcard += 1
            continue
        where = ", ".join(f"{p}:{n}" for p, n in
                          [s for sites in reads[f].values() for s in sites][:3])
        fail("A1-UNDOCUMENTED",
             f"{f} is read ({where}) but appears nowhere in "
             f"docs/gateway/ENV-BY-REACTOR.md — add its row.")
    if by_wildcard:
        note("A1-WILDCARD",
             f"{by_wildcard} flag(s) are documented only by the "
             f"{', '.join(sorted(w + '*' for w in doc_wildcards))} blanket "
             f"(own-thread subsystems, reactor-independent) — named individually "
             f"by `--list`, not row-by-row in the doc.")

    # ---- A2 const vs doc -------------------------------------------------- #
    doc_scoped = {f: h for f, h in doc_rows.items() if len(h) != len(REACTORS)}
    for f, h in sorted(doc_scoped.items()):
        if f not in const_rows:
            fail("A2-CONST-MISSING",
                 f"{f} is tabled in ENV-BY-REACTOR.md as honored by "
                 f"{','.join(h) or 'nothing'} but has NO REACTOR_SCOPED_FLAGS row "
                 f"in main.rs — the operator gets no startup warning.")
        elif tuple(sorted(const_rows[f])) != tuple(sorted(h)):
            fail("A2-CONST-MISMATCH",
                 f"{f}: main.rs says honored by {','.join(sorted(const_rows[f]))}, "
                 f"ENV-BY-REACTOR.md says {','.join(sorted(h))}.")
    for f in sorted(const_rows):
        if f not in doc_rows:
            fail("A2-DOC-MISSING",
                 f"{f} has a REACTOR_SCOPED_FLAGS row in main.rs but no row in "
                 f"ENV-BY-REACTOR.md.")

    # ---- A3/A4/A5 read-site analysis -------------------------------------- #
    for f in flags:
        h = honored_by(f)
        if not h:
            # No reactor's dispatch reaches any module that reads this flag.
            if f in const_rows or is_process_documented(f):
                continue
            where = ", ".join(sorted(reads[f]))
            fail("A4-NO-HOME",
                 f"{f} is read only where no reactor reaches it ({where}) and is "
                 f"declared NEITHER a reactor-mechanism knob (a "
                 f"REACTOR_SCOPED_FLAGS row) NOR process-level (the "
                 f"'Process / listener / subsystem flags' list in "
                 f"ENV-BY-REACTOR.md). If a reactor consumes it, it is silently "
                 f"scoped — exactly the DRORB_GATEWAY defect.")
            continue
        if len(h) != len(REACTORS) and f not in const_rows:
            where = ", ".join(sorted(reads[f]))
            fail("A3-ASYMMETRIC",
                 f"{f} is read in {where}, which only the {','.join(h)} "
                 f"reactor(s) can reach — it is SILENTLY IGNORED on "
                 f"{','.join(r for r in REACTORS if r not in h)}. Add a "
                 f"REACTOR_SCOPED_FLAGS row (main.rs) and a row in "
                 f"ENV-BY-REACTOR.md.")
        if f in const_rows:
            over = [r for r in const_rows[f] if r not in h]
            if over and reads[f] != {"main"}:
                fail("A5-OVERCLAIM",
                     f"{f}: REACTOR_SCOPED_FLAGS claims {','.join(over)} honors "
                     f"it, but no {','.join(over)} dispatch path reaches "
                     f"{', '.join(sorted(reads[f]))}.")
            under = [r for r in h if r not in const_rows[f]]
            if under:
                note("A5-STRICTER",
                     f"{f}: the reference graph reaches {','.join(under)} too; "
                     f"the const is stricter (a louder warning, not a hole).")

    # ---- B spans ---------------------------------------------------------- #
    sel_const = parse_span_const("SELECTABLE_SPANS")
    sel_serve = parse_span_number_arms()
    acme_const = parse_span_const("ACME_SERVING_SPANS")
    audit = parse_span_audit()
    acme_audit = sorted(k for k, v in audit.items() if v and k != "unset")

    if sel_const != sel_serve:
        fail("B1-SELECTABLE",
             f"SELECTABLE_SPANS in main.rs is {sel_const} but serve.rs "
             f"span_number() accepts {sel_serve}. A span selectable but unknown "
             f"to the guard is a span whose ACME loss is silent again.")
    if acme_const != acme_audit:
        fail("B2-ACME-SET",
             f"ACME_SERVING_SPANS in main.rs is {acme_const} but "
             f"docs/gateway/ACME-SPAN-AUDIT.md's DRIVEN table says {acme_audit} "
             f"serve HTTP-01. The guard's allowlist must be the audit's.")
    unaudited = [s for s in sel_serve if s not in audit]
    if unaudited:
        fail("B3-UNAUDITED",
             f"span(s) {unaudited} are selectable via DRORB_SPAN but have no row "
             f"in docs/gateway/ACME-SPAN-AUDIT.md — drive them against "
             f"/.well-known/acme-challenge/<token> and table the result.")
    if audit.get("unset") is not True:
        fail("B3-DEFAULT",
             "the audit table does not record the UNSET default as serving "
             "HTTP-01; the guard stays silent on the default and would be wrong.")

    # ---- verdict ---------------------------------------------------------- #
    if mode != "check" or FAILS:
        print(f"env-flag-audit: {len(flags)} DRORB_* flags read in "
              f"crates/dataplane/src, {len(const_rows)} declared reactor-scoped, "
              f"{len(sel_serve)} selectable spans ({len(acme_const)} serve ACME "
              f"HTTP-01).")
        for code, msg in NOTES:
            print(f"  note  [{code}] {msg}")
    elif NOTES:
        print(f"env-flag-audit: {len(NOTES)} note(s) "
              f"(scripts/env-flag-audit.sh with no argument prints them).")
    for code, msg in FAILS:
        print(f"  FAIL  [{code}] {msg}", file=sys.stderr)
    if FAILS:
        print(f"ENV-FLAG-AUDIT FAILED ({len(FAILS)} finding(s))", file=sys.stderr)
        return 1
    print("ENV-FLAG-AUDIT GATE PASSED (no silently reactor-scoped flag; "
          "the DRORB_SPAN ACME guard matches serve.rs and the driven audit)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
