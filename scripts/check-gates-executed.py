#!/usr/bin/env python3
"""check-gates-executed.py — THE EXECUTION GATE: the critical tests actually RAN.

## The hole this closes (docs/WOUND-ci-gates-dead-since-2026-07-20.md)

On 2026-07-20 a commit about ML-KEM deleted a Lean->Rust FFI binding that two committed
`dregg-circuit-prove` tests still imported. `cargo test --workspace` COMPILES EVERY TARGET
BEFORE RUNNING ANY, so one un-compilable test file meant ZERO tests ran in that crate — for
five days. That silently disabled `law1_enforcement_gate` (the ratchet for this codebase's
central law: AIR is AUTHORED IN LEAN, never hand-written in Rust) and all 23 Lean<->Rust
`*_emit_gate` equality gates.

Nothing noticed, because ABSENCE OF EXECUTION SATISFIED EVERY SIGNAL WE HAD. A crate that
runs 0 tests and a crate that runs 191 green ones produce the same shape of success: a
number nobody reads, and a checkmark.

`armed-teeth.yml` survived the blackout for exactly one reason: it names its binaries with
`--test`, so it does not inherit the workspace's compile fate. This gate takes that shape and
adds the missing half — it does not merely INVOKE the gates, it PARSES what libtest reported
and matches it against a set RECORDED IN THE REPO.

## The check

  STATIC (no cargo; runs even if nothing in the tree compiles)
    S1  every stem in scripts/gates-executed.tsv has a file at circuit-prove/tests/<stem>.rs
        -> a DELETE or a RENAME is RED, not a smaller number.
    S2  the *_emit_gate.rs glob EQUALS the manifest's emit-gate stems, both directions.
        Missing -> RED (a gate vanished). EXTRA -> RED (a new gate exists and nothing arms
        it: a transcription of a growing set cannot go red, it just quietly covers less).
    S3  the manifest's own #! directives (file/gate/test counts) agree with its rows, so
        deleting rows to go green requires editing the recorded number too — a visible diff,
        never an accident.
    S4  the FLOORS BELOW are hardcoded HERE, in reviewed code, not read from the same data
        the accident could take out. LAW1_GATE must be in the manifest by name; the emit-gate
        count must be >= MIN_EMIT_GATES.

  EXECUTION (one `cargo test --test <stem>` per gate, so attribution is BY CONSTRUCTION and
  a dead gate names ITSELF instead of taking the whole run down with it)
    E1  each binary must emit BOTH a `running N tests` and a `test result:` line -- that pair
        is the only positive evidence that the binary was built, linked, and executed.
    E2  the parsed per-test lines must NUMBER exactly N (a test that prints a line shaped like
        libtest output cannot inflate the tally).
    E3  every manifest row marked `run` must appear with status `ok`. Absent -> DID NOT RUN
        (compile-out via #[cfg], a rename, a filter, an aborted binary). `ignored` where the
        manifest says `run` -> SILENCED.
    E4  a row marked `ignored` must be reported `ignored` or `ok` -- an expensive probe is
        allowed to be ignored, but its DISAPPEARANCE is still red via E3's existence check.

Tests present in the binary but absent from the manifest are NOTED, not failed: an unrecorded
test is a stale manifest, not an assurance hole. A MISSING one is the hole.

## Why this cannot be defeated by the accident it exists to catch

The expected set is a COMMITTED FILE plus FLOORS IN THIS SCRIPT. It is never inferred at
runtime from the thing that could be missing. The one runtime-derived input -- the glob -- is
used only as an EQUALITY cross-check, so it can add failures and never subtract them. And the
gate runs as its OWN CI job on its OWN named targets: a compile error in an unrelated crate's
test file cannot zero it, which is precisely how the original blackout worked.

## --self-test

Runs the STATIC checker and the OUTPUT PARSER against synthetic fixtures -- a tree with a gate
deleted, a tree with an unarmed extra gate, a log with a binary that never ran, a log with a
red test, a log with a silenced test, and an intact positive control. It runs on EVERY
invocation, before the real check, because a guard against unfalsifiable guards that cannot
itself be shown to go red would be the joke telling itself.

EXIT: 0 every named gate EXECUTED and is green
      1 a gate DID NOT EXECUTE, is MISSING, or is UNARMED (the blackout class)
      2 environment / manifest problem, or output that could not be parsed
        ("I could not prove it ran" is not a pass)
      3 every gate executed, but one is RED (a real failure -- not this gate's incident class,
        and deliberately a DIFFERENT code, because conflating "did not run" with "failed" is
        the confusion the whole wound is about)
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "scripts" / "gates-executed.tsv"

# ── THE FLOORS. In code, on purpose. ────────────────────────────────────────────
# These are the claims the wound doc makes about what went dark. They live here rather than
# only in the TSV so that emptying the TSV cannot make this gate agree that nothing was
# expected. Raising them is a deliberate edit; lowering one is a reviewable confession.
CRITICAL_CRATE = "dregg-circuit-prove"
CRITICAL_TESTS_DIR = Path("circuit-prove") / "tests"
LAW1_GATE = "law1_enforcement_gate"
EMIT_GLOB = "*_emit_gate.rs"
MIN_EMIT_GATES = 23  # counted 2026-07-25 (an earlier report said "about 25" -- it is 23)

# Crates whose DIRECTORY is not their package name. Anything absent from this map is looked
# for at <repo>/<crate>/tests, and a miss is a STATIC failure (a recorded gate with no file),
# never a silent skip.
CRATE_DIR_HINT = {CRITICAL_CRATE: Path("circuit-prove")}

BOLD, RED, GRN, YEL, DIM, OFF = (
    ("\033[1m", "\033[31m", "\033[32m", "\033[33m", "\033[2m", "\033[0m")
    if sys.stderr.isatty()
    else ("", "", "", "", "", "")
)

_failures: list[str] = []
_notes: list[str] = []
_did_not_run = False
_red_gate = False


def hdr(msg: str) -> None:
    print(f"\n{BOLD}== {msg} =={OFF}", flush=True)


def ok(msg: str) -> None:
    print(f"  {GRN}ok{OFF}   {msg}", flush=True)


def note(msg: str) -> None:
    _notes.append(msg)
    print(f"  {DIM}note{OFF} {msg}", flush=True)


def bad(msg: str) -> None:
    _failures.append(msg)
    print(f"  {RED}FAIL{OFF} {msg}", flush=True)


def fatal(msg: str) -> None:
    print(f"{RED}{BOLD}environment: {msg}{OFF}", file=sys.stderr, flush=True)
    sys.exit(2)


# ════════════════════════════════════════════════════════════════════════════════
# MANIFEST
# ════════════════════════════════════════════════════════════════════════════════
class Manifest:
    """rows: (crate, stem, test_path, expect in {run, ignored}); directives: #!KEY=VALUE"""

    def __init__(self, rows: list[tuple[str, str, str, str]], directives: dict[str, str], path: Path):
        self.rows = rows
        self.directives = directives
        self.path = path

    @property
    def binaries(self) -> list[tuple[str, str]]:
        """(crate, stem) in manifest order, deduplicated."""
        seen: dict[tuple[str, str], None] = {}
        for crate, stem, _, _ in self.rows:
            seen[(crate, stem)] = None
        return list(seen)

    def stems_of(self, crate: str) -> list[str]:
        return [s for c, s in self.binaries if c == crate]

    @property
    def emit_stems(self) -> set[str]:
        suffix = EMIT_GLOB[1:-3]  # "_emit_gate"
        return {s for s in self.stems_of(CRITICAL_CRATE) if s.endswith(suffix)}

    def for_binary(self, crate: str, stem: str) -> list[tuple[str, str]]:
        return [(t, e) for c, s, t, e in self.rows if c == crate and s == stem]


def read_manifest(path: Path) -> Manifest:
    if not path.is_file():
        fatal(f"manifest {path} is missing. It IS the expected set; without it this gate has no claim.")
    rows: list[tuple[str, str, str, str]] = []
    directives: dict[str, str] = {}
    for lineno, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.rstrip("\n")
        if line.startswith("#!"):
            k, _, v = line[2:].partition("=")
            directives[k.strip()] = v.strip()
            continue
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 4:
            fatal(f"{path}:{lineno}: expected 4 tab-separated columns, got {len(parts)}: {line!r}")
        crate, stem, test_path, expect = (p.strip() for p in parts)
        if expect not in ("run", "ignored"):
            fatal(f"{path}:{lineno}: column 4 must be 'run' or 'ignored', got {expect!r}")
        rows.append((crate, stem, test_path, expect))
    return Manifest(rows, directives, path)


# ════════════════════════════════════════════════════════════════════════════════
# STATIC PHASE
# ════════════════════════════════════════════════════════════════════════════════
def static_phase(
    root: Path, man: Manifest, *, min_emit: int = MIN_EMIT_GATES, quiet: bool = False
) -> list[str]:
    """Returns the list of failure strings (empty == pass). Pure filesystem + manifest."""
    fails: list[str] = []

    def f(msg: str) -> None:
        fails.append(msg)
        if not quiet:
            bad(msg)

    def o(msg: str) -> None:
        if not quiet:
            ok(msg)

    crit_dir = root / CRITICAL_TESTS_DIR

    # S4a — the named critical gate, hardcoded here, must be in the manifest.
    if LAW1_GATE not in man.stems_of(CRITICAL_CRATE):
        f(
            f"{LAW1_GATE} is NOT in {man.path.name} under {CRITICAL_CRATE}. That is the ratchet for "
            f"architectural law #1 (AIR is authored in Lean, never hand-written in Rust). Its row "
            f"is not optional."
        )
    else:
        o(f"{LAW1_GATE} is named in the manifest (law #1 ratchet, armed)")

    # S1 — every recorded binary still has a file.
    for crate, stem in man.binaries:
        rel = (CRATE_DIR_HINT.get(crate, Path(crate)) / "tests") / f"{stem}.rs"
        if not (root / rel).is_file():
            f(
                f"{crate}::{stem}: recorded in {man.path.name} but {rel} DOES NOT EXIST "
                f"(deleted or renamed). A gate that is gone is not a smaller number, it is a hole."
            )
    if not fails:
        o(f"all {len(man.binaries)} recorded gate files exist on disk")

    # S2 — glob <-> manifest EQUALITY for the emit gates.
    on_disk = {p.stem for p in sorted(crit_dir.glob(EMIT_GLOB))} if crit_dir.is_dir() else set()
    recorded = man.emit_stems
    for missing in sorted(recorded - on_disk):
        f(f"{missing}: recorded emit gate, but no {CRITICAL_TESTS_DIR}/{missing}.rs on disk.")
    for extra in sorted(on_disk - recorded):
        f(
            f"{extra}: an emit gate exists on disk that NOTHING ARMS — add a row to "
            f"{man.path.name} (and bump the #! counts). A hand-kept arming list that only ever "
            f"lags cannot go red; it just covers less, which is how gates go dark."
        )
    if recorded == on_disk:
        o(f"emit-gate set matches the {EMIT_GLOB} glob exactly ({len(recorded)} gates, both directions)")

    # S4b — the FLOOR, in code.
    if len(recorded) < min_emit:
        f(
            f"only {len(recorded)} emit gates recorded; the floor in this script is "
            f"{min_emit} (counted 2026-07-25). A shrink is a RATCHET BREAK: either a gate "
            f"was deleted, or the manifest was trimmed to match a smaller reality."
        )
    else:
        o(f"emit-gate count {len(recorded)} >= floor {min_emit} (ratchet holds)")

    # S3 — the manifest's recorded counts must match its own rows.
    for key, actual in (
        ("EXPECT_GATE_FILES", len(man.binaries)),
        ("EXPECT_EMIT_GATES", len(recorded)),
        ("EXPECT_TESTS", len(man.rows)),
    ):
        if key not in man.directives:
            f(f"{man.path.name} is missing the #!{key}= directive (the recorded count IS the ratchet).")
            continue
        try:
            want = int(man.directives[key])
        except ValueError:
            f(f"{man.path.name}: #!{key}={man.directives[key]!r} is not an integer.")
            continue
        if want != actual:
            f(
                f"{man.path.name}: #!{key}={want} but the rows say {actual}. Rows were added or "
                f"removed without updating the recorded number — make the change deliberate."
            )
    if all(k in man.directives for k in ("EXPECT_GATE_FILES", "EXPECT_EMIT_GATES", "EXPECT_TESTS")):
        o(
            f"manifest self-consistent: {man.directives.get('EXPECT_GATE_FILES')} gate files, "
            f"{man.directives.get('EXPECT_EMIT_GATES')} emit gates, {man.directives.get('EXPECT_TESTS')} tests"
        )

    return fails


# ════════════════════════════════════════════════════════════════════════════════
# OUTPUT PARSER — the only thing that turns "cargo exited 0" into "the tests RAN"
# ════════════════════════════════════════════════════════════════════════════════
TEST_LINE = re.compile(r"^test ([^\s]+) \.\.\. (ok|FAILED|ignored)\b")
RUNNING_N = re.compile(r"^running (\d+) tests?$")
RESULT_LN = re.compile(r"^test result: (ok|FAILED)\.")


class RunReport:
    def __init__(self) -> None:
        self.saw_running = False
        self.declared = 0
        self.saw_result = False
        self.status: dict[str, str] = {}
        self.parse_error: str | None = None


def parse_libtest(output: str) -> RunReport:
    """Parse ONE test binary's libtest output. Fails closed on anything it cannot account for."""
    rep = RunReport()
    inside = False
    for line in output.splitlines():
        m = RUNNING_N.match(line)
        if m:
            if rep.saw_running:
                rep.parse_error = "more than one `running N tests` block in a single-binary run"
                return rep
            rep.saw_running = True
            rep.declared = int(m.group(1))
            inside = True
            continue
        if RESULT_LN.match(line):
            rep.saw_result = True
            inside = False
            continue
        if inside:
            t = TEST_LINE.match(line)
            if t:
                rep.status[t.group(1)] = t.group(2)
    if rep.saw_running and rep.saw_result and len(rep.status) != rep.declared:
        rep.parse_error = (
            f"libtest declared {rep.declared} tests but {len(rep.status)} status lines were "
            f"parsed — the tally does not reconcile, so no claim about execution can be made"
        )
    return rep


def judge(stem: str, expected: list[tuple[str, str]], rep: RunReport, rc: int) -> tuple[list[str], list[str], bool, bool]:
    """-> (failures, notes, did_not_run, red)"""
    fails: list[str] = []
    notes: list[str] = []
    dnr = False
    red = False

    if rep.parse_error:
        fails.append(f"{stem}: UNPARSEABLE — {rep.parse_error} (fails closed).")
        return fails, notes, False, False

    # E1 — the positive evidence of execution.
    if not (rep.saw_running and rep.saw_result):
        dnr = True
        fails.append(
            f"{stem}: DID NOT EXECUTE — no `running N tests` / `test result:` pair in the output "
            f"(cargo rc={rc}). This is the blackout shape: the binary never built, never linked, "
            f"or aborted before libtest started. ZERO of its {len(expected)} recorded tests ran."
        )
        return fails, notes, dnr, red

    if rep.declared == 0:
        dnr = True
        fails.append(f"{stem}: ran ZERO tests (libtest said `running 0 tests`) while {len(expected)} are recorded.")

    for test_path, expect in expected:
        got = rep.status.get(test_path)
        if got is None:
            dnr = True
            fails.append(
                f"{stem}::{test_path}: DID NOT RUN — recorded in the manifest, absent from the "
                f"executed set (compiled out by #[cfg], renamed, filtered, or the binary aborted "
                f"mid-run)."
            )
        elif got == "FAILED":
            red = True
            fails.append(f"{stem}::{test_path}: RED — it executed and FAILED.")
        elif got == "ignored" and expect == "run":
            dnr = True
            fails.append(
                f"{stem}::{test_path}: SILENCED — recorded as `run`, reported `ignored`. "
                f"An #[ignore] on a gate is a gate that does not run."
            )
        elif got == "ok" and expect == "ignored":
            notes.append(f"{stem}::{test_path}: recorded `ignored` but it RAN and passed (manifest is conservative).")

    extra = sorted(set(rep.status) - {t for t, _ in expected})
    if extra:
        notes.append(
            f"{stem}: {len(extra)} test(s) executed that the manifest does not record "
            f"({', '.join(extra[:4])}{' …' if len(extra) > 4 else ''}) — a stale manifest, not a hole; append them."
        )
    return fails, notes, dnr, red


# ════════════════════════════════════════════════════════════════════════════════
# EXECUTION PHASE
# ════════════════════════════════════════════════════════════════════════════════
def run_gate(crate: str, stem: str, extra_cargo: list[str]) -> tuple[str, int]:
    cmd = ["cargo", "test", "-p", crate, "--test", stem, *extra_cargo]
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    return proc.stdout + "\n" + proc.stderr, proc.returncode


def execution_phase(man: Manifest, extra_cargo: list[str]) -> None:
    global _did_not_run, _red_gate
    hdr(f"EXECUTION — {len(man.binaries)} named binaries, one `cargo test --test <stem>` each")
    print(
        f"  {DIM}named explicitly with --test, exactly as armed-teeth.yml is: a compile error in an\n"
        f"  unrelated test target cannot zero this run, and a dead gate names itself.{OFF}",
        flush=True,
    )
    total = len(man.binaries)
    for i, (crate, stem) in enumerate(man.binaries, 1):
        expected = man.for_binary(crate, stem)
        # Printed BEFORE the subprocess: a job killed by a timeout must still name the binary it
        # was on. Silence for 24 opaque minutes is its own small version of this bug.
        print(f"  {DIM}[{i}/{total}] cargo test -p {crate} --test {stem}{OFF}", flush=True)
        started = time.monotonic()
        output, rc = run_gate(crate, stem, extra_cargo)
        elapsed = time.monotonic() - started
        rep = parse_libtest(output)
        fails, notes, dnr, red = judge(stem, expected, rep, rc)
        _did_not_run = _did_not_run or dnr
        _red_gate = _red_gate or red
        if not fails:
            ok(
                f"{stem}: {rep.declared} tests EXECUTED, {len(expected)} recorded all present "
                f"and green ({elapsed:.1f}s)"
            )
        else:
            for m in fails:
                bad(m)
            tail = [ln for ln in output.splitlines() if ln.strip()][-6:]
            for ln in tail:
                print(f"       {DIM}| {ln[:180]}{OFF}", flush=True)
        for m in notes:
            note(m)


# ════════════════════════════════════════════════════════════════════════════════
# SELF-TEST — this guard proves it can go RED, on every run
# ════════════════════════════════════════════════════════════════════════════════
_FIXTURE_MANIFEST = """\
#!EXPECT_GATE_FILES=3
#!EXPECT_EMIT_GATES=2
#!EXPECT_TESTS=4
dregg-circuit-prove\tlaw1_enforcement_gate\tratchet_holds\trun
dregg-circuit-prove\tlaw1_enforcement_gate\tratchet_can_go_red\trun
dregg-circuit-prove\talpha_emit_gate\tgolden_matches\trun
dregg-circuit-prove\tbeta_emit_gate\tgolden_matches\trun
"""

_GOOD_LOG = """\
   Compiling dregg-circuit-prove v0.1.0
    Finished `test` profile
     Running tests/alpha_emit_gate.rs (target/debug/deps/alpha_emit_gate-1)

running 1 test
test golden_matches ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s
"""

_DEAD_LOG = """\
   Compiling dregg-circuit-prove v0.1.0
error[E0432]: unresolved import `dregg_lean_ffi::FriLedger`
error: could not compile `dregg-circuit-prove` (test "alpha_emit_gate") due to 1 previous error
"""

_RED_LOG = _GOOD_LOG.replace("test golden_matches ... ok", "test golden_matches ... FAILED").replace(
    "test result: ok. 1 passed; 0 failed", "test result: FAILED. 0 passed; 1 failed"
)

_SILENCED_LOG = """\
     Running tests/alpha_emit_gate.rs (target/debug/deps/alpha_emit_gate-1)

running 1 test
test golden_matches ... ignored

test result: ok. 0 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 0.00s
"""

_FILTERED_LOG = """\
     Running tests/alpha_emit_gate.rs (target/debug/deps/alpha_emit_gate-1)

running 0 tests

test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 1 filtered out; finished in 0.00s
"""

_SPOOF_LOG = """\
     Running tests/alpha_emit_gate.rs (target/debug/deps/alpha_emit_gate-1)

running 1 test
test golden_matches ... ok
test golden_matches_but_printed_by_the_test ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s
"""


def _fixture_tree(tmp: Path, gates: list[str]) -> Path:
    d = tmp / CRITICAL_TESTS_DIR
    d.mkdir(parents=True, exist_ok=True)
    for g in gates:
        (d / f"{g}.rs").write_text("// fixture\n")
    return tmp


def self_test() -> bool:
    hdr("SELF-TEST — can this gate go RED? (synthetic fixtures; no cargo)")
    passed = True

    def check(label: str, cond: bool, detail: str = "") -> None:
        nonlocal passed
        if cond:
            ok(f"self-test: {label}")
        else:
            passed = False
            print(f"  {RED}FAIL{OFF} self-test: {label} {detail}", flush=True)

    tmpdir = Path(tempfile.mkdtemp(prefix="gates-selftest."))
    try:
        mpath = tmpdir / "fixture.tsv"
        mpath.write_text(_FIXTURE_MANIFEST)
        man = read_manifest(mpath)
        intact = ["law1_enforcement_gate", "alpha_emit_gate", "beta_emit_gate"]

        # The fixture manifest declares 2 emit gates, so its floor is 2. The REAL floor
        # (MIN_EMIT_GATES) gets its own pole below — it is checked, not merely bypassed.
        fx = dict(min_emit=2, quiet=True)

        # POLE A (the honest tree must be GREEN — a gate that reds on everything is not a gate).
        t = _fixture_tree(tmpdir / "intact", intact)
        check("intact fixture tree is GREEN", static_phase(t, man, **fx) == [], f"got {static_phase(t, man, **fx)}")

        # POLE B1 — a gate DELETED.
        t = _fixture_tree(tmpdir / "deleted", ["law1_enforcement_gate", "alpha_emit_gate"])
        f = static_phase(t, man, **fx)
        check("a DELETED emit gate goes RED", any("beta_emit_gate" in m for m in f), f"got {f}")

        # POLE B2 — the law-1 ratchet deleted.
        t = _fixture_tree(tmpdir / "nolaw1", ["alpha_emit_gate", "beta_emit_gate"])
        f = static_phase(t, man, **fx)
        check("a DELETED law-1 ratchet goes RED", any(LAW1_GATE in m for m in f), f"got {f}")

        # POLE B3 — a NEW, unarmed gate on disk.
        t = _fixture_tree(tmpdir / "extra", intact + ["gamma_emit_gate"])
        f = static_phase(t, man, **fx)
        check("an UNARMED new emit gate goes RED", any("gamma_emit_gate" in m for m in f), f"got {f}")

        # POLE B4 — the manifest trimmed without updating its recorded count.
        trimmed = mpath.with_name("trimmed.tsv")
        trimmed.write_text(
            _FIXTURE_MANIFEST.replace("dregg-circuit-prove\tbeta_emit_gate\tgolden_matches\trun\n", "")
        )
        man_t = read_manifest(trimmed)
        t = _fixture_tree(tmpdir / "trimmed", ["law1_enforcement_gate", "alpha_emit_gate"])
        f = static_phase(t, man_t, min_emit=1, quiet=True)
        check("TRIMMING the manifest without its #! count goes RED", any("EXPECT_" in m for m in f), f"got {f}")

        # POLE B5 — the COUNT FLOOR itself: a manifest smaller than the code's recorded floor,
        # with the tree agreeing with it (so only the floor can catch it).
        t = _fixture_tree(tmpdir / "intact2", intact)
        f = static_phase(t, man, min_emit=3, quiet=True)
        check("a manifest UNDER the hardcoded floor goes RED", any("floor" in m for m in f), f"got {f}")

        # ── the parser, against the shapes that actually happen ──
        exp = [("golden_matches", "run")]
        fa, _, dnr, red = judge("alpha_emit_gate", exp, parse_libtest(_GOOD_LOG), 0)
        check("a GREEN log is accepted", fa == [] and not dnr and not red, f"got {fa}")

        fa, _, dnr, red = judge("alpha_emit_gate", exp, parse_libtest(_DEAD_LOG), 101)
        check("THE INCIDENT (compile error, binary never ran) goes RED as DID-NOT-EXECUTE", dnr and not red, f"got {fa}")

        fa, _, dnr, red = judge("alpha_emit_gate", exp, parse_libtest(_RED_LOG), 101)
        check("a FAILING test goes RED as a real failure, not as did-not-run", red and not dnr, f"got {fa}")

        fa, _, dnr, red = judge("alpha_emit_gate", exp, parse_libtest(_SILENCED_LOG), 0)
        check("an #[ignore]'d gate goes RED as SILENCED", dnr, f"got {fa}")

        fa, _, dnr, red = judge("alpha_emit_gate", exp, parse_libtest(_FILTERED_LOG), 0)
        check("a FILTERED-TO-ZERO run (cargo exit 0!) goes RED", dnr, f"got {fa}")

        rep = parse_libtest(_SPOOF_LOG)
        fa, _, _, _ = judge("alpha_emit_gate", exp, rep, 0)
        check(
            "a tally that does not reconcile is UNPARSEABLE, not a pass",
            rep.parse_error is not None and fa != [],
            f"got {rep.parse_error!r} / {fa}",
        )
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)

    if passed:
        print(f"  {GRN}{BOLD}self-test: this gate demonstrably goes RED on every shape it claims to catch.{OFF}", flush=True)
    return passed


# ════════════════════════════════════════════════════════════════════════════════
def main() -> int:
    argv = sys.argv[1:]
    only_self_test = "--self-test" in argv
    extra_cargo = [a for a in argv if a.startswith("--cargo=")]
    extra_cargo = [a[len("--cargo=") :] for a in extra_cargo]

    print(f"{BOLD}check-gates-executed.py — did the critical gates actually RUN?{OFF}")
    print(f"{DIM}  docs/WOUND-ci-gates-dead-since-2026-07-20.md — the class this closes{OFF}")

    if not self_test():
        print(
            f"\n{RED}{BOLD}THE SELF-TEST FAILED.{OFF} This gate could not demonstrate that it goes red, "
            f"so nothing it says about the tree can be believed.",
            file=sys.stderr,
        )
        return 2
    if only_self_test:
        return 0

    man = read_manifest(MANIFEST)

    hdr(f"STATIC — {MANIFEST.relative_to(ROOT)} vs the tree (no cargo; runs even if nothing compiles)")
    static_fails = static_phase(ROOT, man)
    for m in static_fails:
        _failures.append(m)

    if static_fails:
        print(
            f"\n{RED}{BOLD}STATIC PHASE RED — not running the gates.{OFF} The armed set and the tree "
            f"disagree; executing a set that is already known to be wrong would only launder it.",
            file=sys.stderr,
        )
        return 1

    execution_phase(man, extra_cargo)

    hdr("VERDICT")
    if not _failures:
        print(
            f"  {GRN}{BOLD}{len(man.rows)} recorded tests across {len(man.binaries)} named gate "
            f"binaries EXECUTED and are green.{OFF}"
        )
        for m in _notes:
            print(f"  {YEL}note{OFF} {m}")
        return 0

    print(f"  {RED}{BOLD}{len(_failures)} failure(s):{OFF}", file=sys.stderr)
    for m in _failures:
        print(f"    - {m}", file=sys.stderr)
    if _did_not_run:
        print(
            f"\n{RED}{BOLD}A GATE DID NOT RUN.{OFF} This is the 2026-07-20 class verbatim: the suite "
            f"was not red, it was ABSENT. Do NOT fix this by trimming scripts/gates-executed.tsv to "
            f"match — restore the gate's ability to compile and execute.",
            file=sys.stderr,
        )
        return 1
    if _red_gate:
        print(
            f"\n{RED}{BOLD}EVERY GATE EXECUTED; one is RED.{OFF} That is a real, honest failure with a "
            f"real cause — different from the blackout class, hence a different exit code.",
            file=sys.stderr,
        )
        return 3
    return 1


if __name__ == "__main__":
    sys.exit(main())
