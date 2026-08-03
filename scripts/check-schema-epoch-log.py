#!/usr/bin/env python3
"""check-schema-epoch-log.py — `CANONICAL_STATE_SCHEMA_EPOCH` against `docs/VK-REGEN-LOG.md`.

⚑ KEYED ON THE CONSTANT, NOT ON THE EMIT — and that placement IS the finding.

`docs/VK-REGEN-LOG.md` is how a reader reconstructs what each schema epoch changed. On
2026-08-01 its last row said "Schema epoch UNCHANGED at 20" while `persist/src/lib.rs` read
**21**. The bump was `6441705e8`, which ran no emit. The structural defect, stated by the lane
that found it:

    An epoch is a Rust constant ANY COMMIT CAN BUMP, while ONLY the emit script appends to
    that log. A gate that runs inside the emit path REPRODUCES THE BLIND SPOT EXACTLY.

So this gate lives outside `scripts/emit_descriptors.py` entirely. It is a row of
`scripts/local-gates.sh`, and it has a second body one altitude closer to the constant —
`persist/src/tests.rs::schema_epoch_log_row`, which reds for anyone who edits the constant and
runs `cargo test -p dregg-persist` without ever thinking about a descriptor. Leg 6 below welds
that twin in place: deleting it reds this gate.

WHAT IT CHECKS (each leg is a separate finding; none of them is a threshold that can be tuned):

  L1  exactly one definition of the constant in `persist/src/lib.rs`; 0 or 2+ is a FAILURE.
  L2  every event row carries a well-formed `epoch:` cell, and the LAST `epoch:N` row equals
      the constant. This is the load-bearing comparison; the others exist so it cannot be
      quietly disabled.
  L3  the numeric epoch column never goes DOWN in file order.
  L4  the SCHEMA EPOCH LEDGER: strictly increasing, its last row equals the constant, and —
      read from an INDEPENDENT SOURCE, `git log -p -- persist/src/lib.rs` — every value the
      constant has ever held in committed history has a ledger row. A ledger value not in
      committed history is legal ONLY as the newest one and ONLY if it equals the working-tree
      constant (that is the state of a bump commit being authored right now).
  L5  FLOORS. A reader that harvests nothing must not read as clean.
  L6  the in-crate twin still exists and still names both the constant and this log.

⚠ FAIL-CLOSED IS THE POINT. A log with no parseable `epoch:N` row is a FAILURE, not a pass —
otherwise the first malformed row silently disables the gate, which is a class this repo has
~15 instances of. Same for: the log absent, the constant absent, a row with the wrong column
count, an `epoch:` cell that is neither a number nor `unchanged` nor `unknown`.

⚠ NEVER fix a red here by widening what is compared. If the constant moved, the flag day is
real: append an event row and a ledger row saying what re-genesised, per CLAUDE.md's "say what
you broke".

USAGE
  python3 scripts/check-schema-epoch-log.py                 # the gate
  python3 scripts/check-schema-epoch-log.py --self-test     # can it go red? (scratch copies only)
  python3 scripts/check-schema-epoch-log.py --log P --persist P --as-of REV   # a reconstruction

Exit 0 clean · 1 findings · 2 the gate could not run (which is also a failure).
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOG_REL = "docs/VK-REGEN-LOG.md"
PERSIST_REL = "persist/src/lib.rs"
TWIN_REL = "persist/src/tests.rs"

CONST_RE = re.compile(r"^\s*pub const CANONICAL_STATE_SCHEMA_EPOCH: u64 = (\d+);", re.M)
EPOCH_CELL_RE = re.compile(r"^epoch:(\d+|unchanged|unknown)$")

EVENT_HEADER = "| when (UTC) | operator |"
LEDGER_HEADER = "| epoch | set by |"

# A reader that harvests nothing must not read as clean. These are the tree's TODAY, minus
# nothing: 45 event rows, 22 of them numeric, 10 ledger rows.
MIN_EVENT_ROWS = 40
MIN_NUMERIC_ROWS = 15
MIN_LEDGER_ROWS = 8


class Fail(Exception):
    """The gate could not run. Exit 2 — never a pass."""


# ── readers ───────────────────────────────────────────────────────────────────────────────


def read_constant(persist: Path) -> int:
    if not persist.is_file():
        raise Fail(f"{persist} does not exist. The constant is the thing being checked.")
    hits = CONST_RE.findall(persist.read_text(errors="replace"))
    if len(hits) != 1:
        raise Fail(
            f"{persist} carries {len(hits)} definitions of `CANONICAL_STATE_SCHEMA_EPOCH` "
            f"({hits or 'none'}); this gate compares against exactly one. Two definitions are "
            f"two shapes that will disagree later — delete one."
        )
    return int(hits[0])


def _table(lines: list[str], header_prefix: str, what: str) -> list[list[str]]:
    """Rows of the markdown table whose header starts with `header_prefix`, as cell lists."""
    start = next((i for i, l in enumerate(lines) if l.startswith(header_prefix)), None)
    if start is None:
        raise Fail(
            f"{LOG_REL}: no {what} table (no line starting `{header_prefix}`). A log this gate "
            f"cannot parse is a FAILURE, not a pass — the whole point of the gate is that the "
            f"epoch history stays reconstructible from this file."
        )
    rows: list[list[str]] = []
    for l in lines[start + 1:]:
        if not l.startswith("|"):
            break
        # Split on UNESCAPED pipes only. Four rows of this log carry `\|` inside code spans
        # (`d8 \|\| iroot`, `lo \| mid1<<8`), which is what GFM requires and what a naive
        # `split("|")` mis-reads as extra columns — those rows had bare pipes and had never
        # rendered as table rows at all until 2026-08-01.
        cells = [c.strip() for c in re.split(r"(?<!\\)\|", l)]
        if cells and cells[0] == "":
            cells = cells[1:]
        if cells and cells[-1] == "":
            cells = cells[:-1]
        if all(set(c) <= set("-: ") and c for c in cells):
            continue                      # the |---|---| separator
        rows.append(cells)
    return rows


# ── legs ──────────────────────────────────────────────────────────────────────────────────


def committed_epoch_values(root: Path, as_of: str) -> list[int] | None:
    """Every value the constant has held, oldest first, straight out of git. None == no git."""
    probe = subprocess.run(["git", "-C", str(root), "rev-parse", "--verify", as_of],
                           capture_output=True, text=True)
    if probe.returncode != 0:
        return None
    out = subprocess.run(
        ["git", "-C", str(root), "log", as_of, "-p", "--follow", "--format=%H", "--", PERSIST_REL],
        capture_output=True, text=True,
    )
    if out.returncode != 0:
        return None
    vals: list[int] = []
    for line in out.stdout.splitlines():
        m = re.match(r"^\+\s*pub const CANONICAL_STATE_SCHEMA_EPOCH: u64 = (\d+);", line)
        if m:
            vals.append(int(m.group(1)))
    vals.reverse()                        # git log is newest-first
    return vals


def check(log: Path, persist: Path, root: Path, as_of: str) -> list[str]:
    findings: list[str] = []

    epoch = read_constant(persist)                                             # L1
    if not log.is_file():
        raise Fail(f"{log} does not exist. Absent is not clean.")
    lines = log.read_text(errors="replace").splitlines()

    # ── L2/L3 · the event table ───────────────────────────────────────────────────────────
    events = _table(lines, EVENT_HEADER, "event")
    ncol = None
    numeric: list[tuple[int, str]] = []          # (epoch, when)
    for cells in events:
        when = cells[0] if cells else "(empty row)"
        if ncol is None:
            ncol = len(cells)
        if len(cells) != ncol:
            findings.append(
                f"EVENT-ROW-SHAPE: row `{when}` has {len(cells)} cells, the table has {ncol}. "
                f"A row this gate cannot read is a failure — it is exactly how a gate gets "
                f"silently switched off."
            )
            continue
        cell = cells[-1]
        m = EPOCH_CELL_RE.match(cell)
        if not m:
            findings.append(
                f"EVENT-ROW-EPOCH: row `{when}` ends in `{cell}`, which is not `epoch:N`, "
                f"`epoch:unchanged` or `epoch:unknown`. Unparseable is RED, never green."
            )
            continue
        if m.group(1).isdigit():
            numeric.append((int(m.group(1)), when))

    if len(events) < MIN_EVENT_ROWS:                                           # L5
        findings.append(
            f"FLOOR-EVENTS: harvested {len(events)} event rows, floor is {MIN_EVENT_ROWS}. A "
            f"reader that finds nothing must not report clean."
        )
    if len(numeric) < MIN_NUMERIC_ROWS:
        findings.append(
            f"FLOOR-NUMERIC: harvested {len(numeric)} rows carrying `epoch:N`, floor is "
            f"{MIN_NUMERIC_ROWS}."
        )

    for (a, wa), (b, wb) in zip(numeric, numeric[1:]):                         # L3
        if b < a:
            findings.append(
                f"EPOCH-GOES-BACKWARDS: row `{wb}` records epoch {b} after row `{wa}` recorded "
                f"{a}. The epoch only ever ratchets up; a decrease means a row was edited or "
                f"the column was mis-filled."
            )

    if not numeric:                                                            # L2, fail-closed
        findings.append(
            f"NO-EPOCH-ROW: not one event row carries `epoch:N`, so there is nothing to compare "
            f"the constant ({epoch}) against. This is the fail-CLOSED leg: a log that lost its "
            f"epoch column reads as a failure, because otherwise one malformed row disables the "
            f"whole gate."
        )
    else:
        last, when = numeric[-1]
        if last != epoch:
            findings.append(
                f"EPOCH-UNLOGGED: `{PERSIST_REL}` reads CANONICAL_STATE_SCHEMA_EPOCH = {epoch}, "
                f"the last epoch-bearing row of {LOG_REL} (`{when}`) reads {last}. A schema "
                f"epoch moved and the log does not say so, so the epoch history no longer "
                f"reconstructs. THE FIX IS A ROW, NOT A WIDER COMPARISON: append an event row "
                f"and a ledger row naming what re-genesised, what must be re-emitted and what "
                f"now refuses to load."
            )

    # ── L4 · the ledger, against git ──────────────────────────────────────────────────────
    ledger = _table(lines, LEDGER_HEADER, "ledger")
    lvals: list[int] = []
    for cells in ledger:
        if not cells or not cells[0].isdigit():
            findings.append(
                f"LEDGER-ROW: `{cells[0] if cells else '(empty)'}` is not an epoch number. The "
                f"ledger's first column is the value the constant took."
            )
            continue
        lvals.append(int(cells[0]))

    if len(lvals) < MIN_LEDGER_ROWS:                                           # L5
        findings.append(
            f"FLOOR-LEDGER: harvested {len(lvals)} ledger rows, floor is {MIN_LEDGER_ROWS}."
        )
    for a, b in zip(lvals, lvals[1:]):
        if b <= a:
            findings.append(
                f"LEDGER-ORDER: {b} follows {a}; the ledger is one row per value the constant "
                f"took, in commit order, so it is STRICTLY increasing."
            )
    if lvals and lvals[-1] != epoch:
        findings.append(
            f"LEDGER-TAIL: the ledger ends at epoch {lvals[-1]}, the constant reads {epoch}. "
            f"Every value the constant takes gets a ledger row saying what it re-genesised."
        )

    seen = committed_epoch_values(root, as_of)
    if seen is None:
        print(
            f"check-schema-epoch-log: ⚠ LEG 4 (ledger vs git history) NOT RUN — `git` could not "
            f"resolve `{as_of}` in {root}. The load-bearing comparison (last epoch row vs the "
            f"constant) DID run; completeness against history did not."
        )
    else:
        if not seen:
            findings.append(
                f"GIT-BLIND: `git log {as_of} -p -- {PERSIST_REL}` found ZERO settings of the "
                f"constant. The reader is broken; a broken reader must not read as clean."
            )
        missing = [v for v in dict.fromkeys(seen) if v not in lvals]
        if missing:
            findings.append(
                f"LEDGER-INCOMPLETE: the constant has held {sorted(set(missing))} in committed "
                f"history with no ledger row. Reconstruct with `git log -p --follow -- "
                f"{PERSIST_REL}`."
            )
        for v in lvals:
            if v not in seen and v != epoch:
                findings.append(
                    f"LEDGER-INVENTED: ledger row {v} names a value no commit ever held, and it "
                    f"is not the working-tree constant either. The only legal uncommitted "
                    f"ledger value is the bump being authored right now."
                )

    # ── L6 · the in-crate twin ────────────────────────────────────────────────────────────
    twin = root / TWIN_REL
    body = twin.read_text(errors="replace") if twin.is_file() else ""
    if "schema_epoch_log_row" not in body or LOG_REL not in body:
        findings.append(
            f"TWIN-GONE: {TWIN_REL} no longer carries `schema_epoch_log_row` naming {LOG_REL}. "
            f"That test is the body of this gate that sits NEXT TO THE CONSTANT — it is what "
            f"reds for a lane that bumps the epoch and runs `cargo test -p dregg-persist` "
            f"without ever running a gate script. Deleting it is not a cleanup."
        )

    print(
        f"check-schema-epoch-log: constant={epoch} · {len(events)} event rows "
        f"({len(numeric)} epoch-bearing, last={numeric[-1][0] if numeric else 'NONE'}) · "
        f"{len(lvals)} ledger rows · git history "
        f"{'not read' if seen is None else str(len(set(seen))) + ' distinct values'}"
    )
    return findings


# ── self-test ─────────────────────────────────────────────────────────────────────────────


def _run(log: Path, persist: Path, root: Path, as_of: str = "HEAD") -> list[str]:
    try:
        return check(log, persist, root, as_of)
    except Fail as e:
        return [f"FAIL: {e}"]


def self_test() -> int:
    """Can it go red? Every scenario runs on a SCRATCH COPY; the shared tree is never touched.

    A fault that matches nothing is itself a failure — each mutation asserts it changed the text.
    """
    log0 = (ROOT / LOG_REL).read_text()
    persist0 = (ROOT / PERSIST_REL).read_text()
    bad = 0

    def scenario(name: str, log_text: str, persist_text: str, want_red: bool,
                 want_token: str | None = None, as_of: str = "HEAD") -> None:
        nonlocal bad
        with tempfile.TemporaryDirectory() as td:
            d = Path(td)
            (d / "log.md").write_text(log_text)
            (d / "lib.rs").write_text(persist_text)
            got = _run(d / "log.md", d / "lib.rs", ROOT, as_of)
        red = bool(got)
        ok = red == want_red and (want_token is None or any(want_token in g for g in got))
        if not ok:
            bad += 1
        print(f"  [{'ok ' if ok else 'BAD'}] {name}: {'RED' if red else 'green'} "
              f"(wanted {'RED' if want_red else 'green'})")
        for g in got[:2]:
            print(f"        · {g[:150]}")

    def mutate(text: str, old: str, new: str, count: int = 1) -> str:
        if text.count(old) < count:
            raise SystemExit(
                f"self-test: injection `{old[:60]}` matches {text.count(old)} sites, needed "
                f"{count}. An injection that matches nothing proves nothing — repair the "
                f"self-test rather than deleting the scenario."
            )
        return text.replace(old, new, count)

    print("check-schema-epoch-log --self-test (scratch copies; the working tree is untouched)")

    # 0 — CONTROL. The tree as it stands must be green, or every red below is meaningless.
    scenario("control (tree as-is)", log0, persist0, want_red=False)

    # 1 — THE ORIGIN STORY: bump the constant, write no row.
    bumped = mutate(persist0,
                    "pub const CANONICAL_STATE_SCHEMA_EPOCH: u64 = 22;",
                    "pub const CANONICAL_STATE_SCHEMA_EPOCH: u64 = 23;")
    scenario("bump the constant, no row", log0, bumped, want_red=True, want_token="EPOCH-UNLOGGED")

    # 2 — ...then write the row. Green again, and that is what makes leg 2 a gate and not a wall.
    rowed = log0.rstrip("\n") + (
        "\n| 2026-08-02T00:00:00Z | selftest@scratch | schema-epoch (no emit) | " + "0" * 40
        + " | " + "0" * 40 + " | no | SELF-TEST ROW | epoch:23 |\n"
    )
    rowed = mutate(
        rowed,
        "| 22 | `6342defa2` |",
        "| 23 | `(uncommitted)` | 2026-08-02T00:00:00Z | self-test scratch row. |\n| 22 | `6342defa2` |",
    )
    # ledger rows are commit-ordered, so the new one goes last, not first
    rowed = rowed.replace(
        "| 23 | `(uncommitted)` | 2026-08-02T00:00:00Z | self-test scratch row. |\n| 22 | `6342defa2` |",
        "| 22 | `6342defa2` |", 1)
    rowed = re.sub(r"(\| 22 \| `6342defa2` \|[^\n]*\n)",
                   r"\1| 23 | `(uncommitted)` | 2026-08-02T00:00:00Z | self-test scratch row. |\n",
                   rowed, count=1)
    scenario("...then append the row + ledger row", rowed, bumped, want_red=False)

    # 3 — FAIL-CLOSED: truncate the last epoch cell. Unparseable must be RED, never green.
    trunc = mutate(log0, "| epoch:22 |", "| epoch: |")
    scenario("truncate the last epoch cell", trunc, persist0, want_red=True,
             want_token="EVENT-ROW-EPOCH")

    # 4 — FAIL-CLOSED: corrupt it to something that parses as text but not as an epoch.
    corrupt = mutate(log0, "| epoch:22 |", "| epoch:twenty-two |")
    scenario("corrupt the last epoch cell", corrupt, persist0, want_red=True,
             want_token="EVENT-ROW-EPOCH")

    # 5 — FAIL-CLOSED, the whole column: the shape the gate exists to refuse.
    stripped = re.sub(r" \| epoch:(?:\d+|unchanged|unknown) \|$", " |", log0, flags=re.M)
    if stripped == log0:
        raise SystemExit("self-test: stripping the epoch column matched nothing.")
    scenario("delete the epoch column entirely", stripped, persist0, want_red=True,
             want_token="NO-EPOCH-ROW")

    # 6 — the log itself gone.
    scenario("epoch column present but every row `unknown`",
             re.sub(r"\| epoch:\d+ \|$", "| epoch:unknown |", log0, flags=re.M),
             persist0, want_red=True, want_token="NO-EPOCH-ROW")

    # 7 — the ledger deleted.
    noledger = re.sub(r"^\| epoch \| set by \|.*?(?=^## EVENT ROWS)", "", log0,
                      flags=re.M | re.S)
    if noledger == log0:
        raise SystemExit("self-test: deleting the ledger matched nothing.")
    scenario("delete the ledger table", noledger, persist0, want_red=True)

    # 8 — a ledger row removed: the bump is in git, the record no longer names it.
    holed = mutate(log0, "| 20 | `a62c48c7b` |", "| 20x | `a62c48c7b` |")
    scenario("drop epoch 20 from the ledger", holed, persist0, want_red=True,
             want_token="LEDGER-INCOMPLETE")

    # 9 — the epoch column made non-monotone.
    back = mutate(log0, "| epoch:21 |", "| epoch:5 |")
    scenario("make the column go backwards", back, persist0, want_red=True,
             want_token="EPOCH-GOES-BACKWARDS")

    # 10 — BLIND READER. An empty log must not read as clean.
    scenario("blind the reader (empty log)", "", persist0, want_red=True)

    # 11 — the constant deleted / duplicated.
    scenario("constant absent", log0, persist0.replace(
        "pub const CANONICAL_STATE_SCHEMA_EPOCH: u64 = 22;", "// gone", 1),
        want_red=True, want_token="0 definitions")

    # 12 — ⚑ ANTI-VACUITY. Reconstruct the state at `6441705e8` — the bump this gate was written
    # for — and require the gate to catch it. A gate that cannot catch its own origin story is
    # decoration. The log is truncated to the rows that existed then (the MapAbsent row, which
    # said "Schema epoch UNCHANGED at 20", is last) and the ledger to the values git could see
    # at that commit; the constant is read from that commit's own `persist/src/lib.rs`.
    hist_persist = subprocess.run(
        ["git", "-C", str(ROOT), "show", "6441705e8:persist/src/lib.rs"],
        capture_output=True, text=True)
    if hist_persist.returncode != 0:
        raise SystemExit("self-test: cannot read persist/src/lib.rs at 6441705e8.")
    keep = []
    for l in log0.splitlines():
        if l.startswith("| 2026-08-01T13:20:41Z") or l.startswith("| 2026-08-01T20:40:00Z"):
            continue                                   # written AFTER 6441705e8
        if l.startswith("| 21 | `6441705e8`") or l.startswith("| 22 | `6342defa2`"):
            continue                                   # the ledger did not exist yet
        keep.append(l)
    hist_log = "\n".join(keep) + "\n"
    scenario("⚑ reconstructed state at 6441705e8 (the bump that motivated this gate)",
             hist_log, hist_persist.stdout, want_red=True, want_token="EPOCH-UNLOGGED",
             as_of="6441705e8")

    print(f"\ncheck-schema-epoch-log --self-test: {'OK' if bad == 0 else str(bad) + ' SCENARIO(S) WRONG'}")
    return 1 if bad else 0


# ── main ──────────────────────────────────────────────────────────────────────────────────


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--log", default=None)
    ap.add_argument("--persist", default=None)
    ap.add_argument("--as-of", default="HEAD",
                    help="bound the git history walk (a reconstruction reads its own past)")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--rev", default=None,
                    help="grade a COMMIT instead of the working tree (e.g. --rev HEAD). "
                         "See the note below on why this exists.")
    a = ap.parse_args()

    if a.self_test:
        return self_test()

    # ⚑ WHY --rev EXISTS: this gate answers "is the committed record self-consistent?", and that
    # question is ONLY answerable about a commit. Read from the working tree it is hostage to every
    # co-tenant mid-edit — measured 2026-08-03, when it reported EPOCH-GOES-BACKWARDS and
    # EPOCH-UNLOGGED against a sibling lane's UNCOMMITTED 22→23 bump. HEAD read 22; the log row it
    # accused of "going backwards" was CORRECT for HEAD. Both findings were artifacts of the subject,
    # not defects in the record.
    #
    # ⚠ Same shape as `emit_descriptors.py --verify-provenance`, whose strict clause keyed on a tree
    # hash that moves on any commit to any of ~2300 modules — furniture by construction — and whose
    # non-strict form graded the working tree. That one was repaired by splitting the always-answerable
    # question from the working-tree one; this is that repair, here.
    #
    # Working-tree grading stays the DEFAULT (a developer wants to know before they commit); --rev is
    # what a gate wired into CI or a swarm should use.
    tmp = None
    if a.rev:
        import subprocess, tempfile
        tmp = tempfile.TemporaryDirectory(prefix="epochlog-")
        for rel in (LOG_REL, PERSIST_REL):
            dst = Path(tmp.name) / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            blob = subprocess.run(["git", "-C", str(ROOT), "show", f"{a.rev}:{rel}"],
                                  capture_output=True, text=True)
            if blob.returncode != 0:
                print(f"check-schema-epoch-log: CANNOT RUN — {rel} absent at {a.rev}", file=sys.stderr)
                return 2
            dst.write_text(blob.stdout)
        log = Path(tmp.name) / LOG_REL
        persist = Path(tmp.name) / PERSIST_REL
    else:
        log = Path(a.log) if a.log else ROOT / LOG_REL
        persist = Path(a.persist) if a.persist else ROOT / PERSIST_REL
    try:
        findings = check(log, persist, ROOT, a.as_of)
    except Fail as e:
        print(f"check-schema-epoch-log: CANNOT RUN — {e}", file=sys.stderr)
        return 2
    for f in findings:
        print(f"  - {f}")
    if findings:
        print(f"check-schema-epoch-log: FAIL ({len(findings)} finding(s))")
        return 1
    print("check-schema-epoch-log: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
