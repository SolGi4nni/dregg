#!/usr/bin/env python3
"""check-elab-cost.py — elaboration COST may only ratchet DOWN, per module.

═══ WHY THIS GATE IS NOT A STOPWATCH ══════════════════════════════════════════════
The obvious gate — "no module may take more than N seconds" — is the wrong shape here, and
we have the measurement that says so. On 2026-08-09, the same modules were timed twice on
hbox: once inside a full `lake build`, once standalone on idle cores.

    module                        in-build      standalone     ratio
    Dregg2.ForMathlib.PolishchukSpielman   565 s      51.3 s     11.0x
    Market.Fxc4ConsequenceBinding           86 s       8.3 s     10.4x
    Dregg2.Spike.TransferAirSoundness      119 s      12.0 s      9.9x
    Dregg2.Distributed.DirectoryLaws        70 s      10.2 s      6.9x
    Dregg2.Spike.EffectVmConstraints       120 s      19.0 s      6.3x

Same commit, same box, same hour. The difference is **co-tenancy**: ~50 concurrent `lean`
processes (22 from the measured build, 21 from another agent's unpinned session, the rest
from two more lanes), each carrying a ~2.4 GB working set from `import Mathlib.Tactic`,
against a box whose ZFS ARC was holding 56 of 123 GB. Memory PSI read `full avg10=27%` —
the machine was stalled on memory a quarter of the time.

A wall-clock ratchet on that box is a **coin flip**, and a gate that goes red for reasons
unrelated to the code is worse than no gate: it teaches everyone to re-run it until green.
So this gate ratchets on things that are **identical on every machine and every run**:
what a module DECLARES about its cost, and what SHAPE it has.

═══ THE FOUR ARMS ═════════════════════════════════════════════════════════════════
(a) `maxHeartbeats` per module may only ratchet DOWN. Heartbeats are a deterministic
    allocation count. A module that raises it to 4,000,000,000 is declaring it needs
    20,000x the default budget; to lower the number you must make the proof cheaper.
(b) `maxRecDepth` per module may only ratchet DOWN — same argument.
(c) Whole-library `import Mathlib` may only shrink. Measured on hbox, empty file,
    warm cache:  `import Mathlib` = 11.5 s / 3.77 GB peak RSS;
                 `import Mathlib.Tactic` = 6.8 s / 2.33 GB;
                 a narrow set (ZMod.Basic + Ring + Linarith) = 4.7 s / 1.65 GB.
    The ~1.4 GB delta per process is not a per-module annoyance — multiplied by the
    concurrent process count it IS the memory pressure that produces the 5-11x above.
(d) ⚑ THE SPLIT ARM — the structural one, and the reason this file exists rather than a
    number in a spreadsheet. See below.

═══ ⚑ ARM (d): DATA-FROM-GATES, THE PATTERN THIS GATE EXISTS TO CATCH ═════════════
Measured twice in one day, in the same import chain:

  * `MinaWrapPublicCommGate` carried a 40-point Pallas MSM proved by kernel `decide`
    (159 s / 14.5 GB peak RSS by its own docblock) **and** the literal `LAGRANGE`.
    `MinaStepPrevCommitments` imported it for `LAGRANGE` — a list of numbers — and that
    module sits in `KimchiStepMainCore`'s closure, so every cold step-emitter build
    reduced a 40-term MSM in the kernel to read a list of coordinates.
  * `MinaWrapGroupGate` carried FIFTEEN theorems, each a `by decide` over a 255-bit Pallas
    ladder (measured standalone: **278.5 s wall / 161.7 s CPU / 4.23 GB peak RSS**),
    **and** the type `Pt`, the group operations `smul`/`padd`/`chunkedComm`, and nine
    literal commitments. Every consumer of the whole Wrap stack imports it FOR THE TYPE.
  * `MinaWrapAggregationGate` carried seven theorems, four of them 47-term kernel MSMs,
    and the literals `XI`/`COMBINE_POINTS`/`COMBINED_GOLD`. **Not one of its five
    importers cited any of its seven theorems.**

The shape is always the same and it is mechanically detectable:

    A module that carries BOTH expensive theorems AND cheap declarations, imported by a
    hot cone FOR THE CHEAP DECLARATIONS, forcing every consumer to build the theorems.

The fix is equally mechanical: MOVE (never copy - a second `LAGRANGE` is the twin this
repo forbids) the data into a sibling `...Data` module in the SAME namespace, so no
consumer is renamed; the gate imports it and keeps every theorem; data-only consumers
import the data module and stop paying.

Arm (d) refuses a module that has the shape unless it is listed in the allow file with a
reason. It is the arm that turns a fix somebody did by hand into a property of the tree.

═══ ⛑ ARM (e): A `TiedAir` THAT RE-DERIVES WHAT ITS FILE ALREADY PROVES ═════════════════════
Same disease as (d), one layer INSIDE a module. `EffectLower.TiedAir` carries two decidable
verdicts in its type:

    structure TiedAir where
      air  : EffectAir
      ok   : air.mainRailOk = true := by decide
      tied : air.pinsTied   = true := by decide

Both are `autoParam`s. A field left blank is not free — it runs `decide` over the whole leg
list inside the ELABORATOR's `whnf`, at the point of the `def`. Measured 2026-08-09: a lane's
build was SIGKILLed at 15,674 s with a stack sample sitting in
`elabMutualDef -> synthesizeSyntheticMVars -> runTactic -> whnf`, deciding `mainRailOk` over
6,404 constraints — a fact the same file proved as a named theorem fifteen lines above.
Supplying the proved terms: 2,979 s green. On `PastaFieldSound`, standalone: 127.7 s -> 65.6 s.

So the arm is: **every `TiedAir` instance must SUPPLY `ok :=` and `tied :=`, and must supply a
TERM.** `ok := by decide` is refused too, and deliberately: it is the `autoParam` written out,
identical in cost, and it leaves no named theorem anything else can cite.

⚠ What the arm does NOT do, and must not: it does not weaken `TiedAir`. The two fields stay
proof obligations, and a decorative pin stays UNREPRESENTABLE. The arm says only that the
obligation is discharged by a theorem with a name rather than by a re-derivation nobody can
reuse. A file with no such theorem must PROVE one — that is the work, not the workaround.

═══ WHAT THIS GATE DOES NOT CATCH — read before trusting a green ══════════════════
  * A module that is slow for a reason it never declares. `MlKemNttFaithful` needs no
    heartbeat raise and takes 98 s standalone; its cost is 64.4 s of KERNEL type checking
    over 20 `decide` proof terms, and nothing here sees that. Arms (a)-(c) see only
    declarations; use `--report` on a real build log to find the rest.
  * WHICH `decide` is expensive. Arm (d) counts them; it does not read what any proves.
  * A split done as a COPY rather than a MOVE. The count falls either way and the tree
    gains a twin. Only the diff says which happened.
  * Whether a theorem is worth its cost. An expensive gate that nothing imports is fine.

═══ USAGE ═════════════════════════════════════════════════════════════════════════
    scripts/check-elab-cost.py                     # gate (arms a-d) against the baseline
    scripts/check-elab-cost.py --self-test         # prove each arm can go RED (synthetic)
    scripts/check-elab-cost.py --update-baseline   # refresh; REFUSES any upward move
    scripts/check-elab-cost.py --seed-allow        # refresh backlog; REFUSES to ADD a row
    scripts/check-elab-cost.py --report build.log  # rank a `lake build --no-ansi` log
    scripts/check-elab-cost.py --split-candidates  # arm (d) census, ranked, ungated

Baseline: scripts/elab-cost-baseline.tsv   Allow: scripts/elab-cost-split-allow.txt
Exit 0 green, 1 red, 2 usage.
"""
from __future__ import annotations
import argparse, collections, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MT = os.path.join(ROOT, "metatheory")
LIBS = ["Dregg2", "Metatheory", "Polis", "Market", "Bfv"]
BASELINE = os.path.join(ROOT, "scripts", "elab-cost-baseline.tsv")
ALLOW = os.path.join(ROOT, "scripts", "elab-cost-split-allow.txt")

# ── arm (d) trigger ────────────────────────────────────────────────────────────────
# A module is "expensive-shaped" when it DECLARES that it is: a raised `maxHeartbeats`
# or `maxRecDepth`. That is deliberate — an early draft of this gate triggered on a raw
# `decide` count (>= 6) and produced 295 findings, most of them modules whose `decide`s
# settle `Nat` decidability in microseconds. A gate with 295 findings is a gate nobody
# keeps green, which is the same as no gate.
#
# All three measured instances of the pattern declare a raise:
#   MinaWrapGroupGate        maxRecDepth 4,000,000     (278.5 s / 4.23 GB standalone)
#   MinaWrapAggregationGate  maxHeartbeats 4,000,000   (555.4 s / 8.99 GB standalone)
#                            maxRecDepth 20,000,000
# while `Dregg2.Circuit.GateExpr` (9 decides, 67 data-only importers) declares nothing
# and is cheap. The declaration is the signal; the decide count is only reported.
HEARTBEAT_FLOOR = 1_000_000
RECDEPTH_FLOOR = 1_000_000

RE_IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.M)
RE_HB = re.compile(r"set_option\s+maxHeartbeats\s+(\d+)")
RE_RD = re.compile(r"set_option\s+maxRecDepth\s+(\d+)")
RE_MATHLIB_ALL = re.compile(r"^import Mathlib$", re.M)
RE_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?]*)", re.M)
RE_TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")
# `by decide` / bare `decide` line, excluding native_decide
RE_DECIDE = re.compile(r"(?<!native_)\bdecide\b")

# ── arm (e): `TiedAir` instances and their supplied fields ─────────────────────────
# A `def <name> ... : ...TiedAir where` followed by an indented field block. The
# `structure TiedAir where` DECLARATION is not matched (it is not a `def`), so the
# module that defines the type is not a finding about itself.
RE_TIEDAIR = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*def\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?]*)[^\n:]*:[^\n]*\bTiedAir\b[ \t]*where[ \t]*\n"
    r"((?:[ \t]+\S[^\n]*\n)*)", re.M)
RE_TIEDAIR_FIELD = re.compile(r"^[ \t]+(air|ok|tied)\b[ \t]*:=", re.M)
TIEDAIR_REQUIRED = ("ok", "tied")


def tiedair_findings(name: str, code: str) -> list[str]:
    """Arm (e): a `TiedAir` instance that leaves a verdict to the `autoParam`, or writes
    the `autoParam` out as `by decide`, is re-deriving a fact that belongs in a theorem."""
    out = []
    # cheap guard: the expensive scan runs only on the ~30 modules that mention the type.
    # Without it the arm walks every `def` line in 2,600 files looking for a `TiedAir` that
    # is not there, which took the gate past its 300 s budget in `local-gates.sh`.
    if "TiedAir" not in code:
        return out
    for m in RE_TIEDAIR.finditer(code):
        inst, block = m.group(1), m.group(2)
        # split the field block into (field, value) pairs, values may span lines
        marks = list(RE_TIEDAIR_FIELD.finditer(block))
        fields = {}
        for i, fm in enumerate(marks):
            end = marks[i + 1].start() if i + 1 < len(marks) else len(block)
            fields[fm.group(1)] = block[fm.end():end]
        for f in TIEDAIR_REQUIRED:
            if f not in fields:
                out.append(f"(e) {name}.{inst}: `{f} :=` not supplied — the `TiedAir` "
                           f"autoParam re-derives it with `by decide` inside the "
                           f"elaborator's whnf. Supply the file's named theorem (prove one "
                           f"if it has none); do NOT weaken the field.")
            elif RE_DECIDE.search(fields[f]):
                out.append(f"(e) {name}.{inst}: `{f} :=` is a `decide`, which is the "
                           f"autoParam written out — same cost, and no named theorem to "
                           f"cite. Name the fact and pass the term.")
    return out


RE_COMMENT_TOK = re.compile(r"/-|-/|--")


def strip_comments(text: str) -> str:
    """Drop Lean comments, honouring NESTED `/- ... -/`.

    Scans by jumping between comment tokens rather than character by character: the tree
    is ~60 MB of Lean across 2,529 files (two generated SRS tables alone are 65k and 33k
    lines), and the per-character version of this function took ~2 minutes, which is too
    slow for a gate that should run in `local-gates.sh`.
    """
    out, pos, depth = [], 0, 0
    for m in RE_COMMENT_TOK.finditer(text):
        tok, i = m.group(0), m.start()
        if i < pos:
            continue
        if tok == "/-":
            if depth == 0:
                out.append(text[pos:i])
            depth += 1
        elif tok == "-/":
            if depth:
                depth -= 1
                if depth == 0:
                    pos = m.end()
        else:  # "--" line comment, only outside a block comment
            if depth == 0:
                out.append(text[pos:i])
                j = text.find("\n", i)
                pos = len(text) if j < 0 else j
    if depth == 0:
        out.append(text[pos:])
    return "".join(out)


class Mod:
    __slots__ = ("name", "path", "raw", "code", "imports", "defs", "thms",
                 "hb", "rd", "mathlib_all", "decides", "tokens")

    def __init__(self, name, path):
        self.name, self.path = name, path
        self.raw = open(path, encoding="utf-8", errors="replace").read()
        self.code = strip_comments(self.raw)
        self.imports = RE_IMPORT.findall(self.raw)
        self.defs, self.thms = set(), set()
        for kind, nm in RE_DECL.findall(self.code):
            (self.thms if kind in ("theorem", "lemma") else self.defs).add(nm)
        self.hb = max((int(x) for x in RE_HB.findall(self.code)), default=0)
        self.rd = max((int(x) for x in RE_RD.findall(self.code)), default=0)
        self.mathlib_all = 1 if RE_MATHLIB_ALL.search(self.raw) else 0
        self.decides = len(RE_DECIDE.findall(self.code))
        self.tokens = set(RE_TOKEN.findall(self.code))


def load_modules() -> dict[str, Mod]:
    mods: dict[str, Mod] = {}
    for lib in LIBS:
        base = os.path.join(MT, lib)
        for dp, _, fs in os.walk(base):
            if ".lake" in dp:
                continue
            for fn in fs:
                if fn.endswith(".lean"):
                    p = os.path.join(dp, fn)
                    nm = os.path.relpath(p, MT)[:-5].replace(os.sep, ".")
                    mods[nm] = Mod(nm, p)
        p = os.path.join(MT, lib + ".lean")
        if os.path.exists(p):
            mods[lib] = Mod(lib, p)
    return mods


def split_candidates(mods):
    """Arm (d): expensive-shaped modules whose importers cite only `def`s."""
    importers = collections.defaultdict(list)
    for m in mods.values():
        for i in m.imports:
            if i in mods:
                importers[i].append(m.name)
    out = []
    for m in mods.values():
        if not (m.hb >= HEARTBEAT_FLOOR or m.rd >= RECDEPTH_FLOOR):
            continue
        if not m.defs or not m.thms:
            continue
        data_only = []
        for imp in importers.get(m.name, []):
            tk = mods[imp].tokens
            if (m.defs & tk) and not (m.thms & tk):
                data_only.append(imp)
        if data_only:
            out.append((len(data_only), m.name, sorted(data_only), m.hb, m.decides,
                        len(m.defs), len(m.thms)))
    out.sort(key=lambda r: (-r[0], r[1]))
    return out


def read_baseline():
    rows = {}
    if not os.path.exists(BASELINE):
        return rows
    for line in open(BASELINE, encoding="utf-8"):
        line = line.rstrip("\n")
        if not line or line.startswith("#"):
            continue
        f = line.split("\t")
        rows[f[0]] = (int(f[1]), int(f[2]), int(f[3]))
    return rows


def write_baseline(mods):
    rows = [(m.name, m.hb, m.rd, m.mathlib_all) for m in mods.values()
            if m.hb or m.rd or m.mathlib_all]
    rows.sort()
    with open(BASELINE, "w", encoding="utf-8") as fh:
        fh.write("# module\tmaxHeartbeats\tmaxRecDepth\timport-Mathlib-whole\n")
        fh.write("# Generated by scripts/check-elab-cost.py --update-baseline.\n")
        fh.write("# These numbers may only go DOWN. See the module docstring for why this\n")
        fh.write("# gate ratchets declarations and not wall time.\n")
        for r in rows:
            fh.write("\t".join(str(x) for x in r) + "\n")
    return len(rows)


ALLOW_HEADER = """\
# elab-cost-split-allow.txt — the data-from-gates BACKLOG. It may only SHRINK.
#
# Every line is a module that carries BOTH expensive theorems (it declares a raised
# `maxHeartbeats`/`maxRecDepth`) AND declarations that importers want on their own —
# and has at least one importer that cites only its `def`s and never a theorem. Each
# line is therefore a cone that pays for proofs nobody in it reads.
#
# ⚑ A line here is a CHOICE TO KEEP PAYING, not an exoneration. Three instances measured
# on 2026-08-09 were split instead of listed:
#     MinaWrapGroupGate        278.5 s / 4.23 GB standalone   -> data module 15.9 s / 2.19 GB
#     MinaWrapAggregationGate  555.4 s / 8.99 GB standalone   -> data module  7.0 s / 2.22 GB
#     MinaWrapPublicCommGate   159 s / 14.5 GB (its own docblock), split by a sibling lane
# The recipe is mechanical: MOVE (never COPY — a second literal is the twin this repo
# forbids) the data into a sibling `...Data` module in the SAME namespace, so no consumer
# is renamed; the gate imports it and keeps every theorem; data-only importers repoint.
#
# Regenerate with `--seed-allow`, which REFUSES to add a row. Removing a row requires
# actually splitting the module. A row for a module that no longer has the shape is RED
# (arm d-stale), so fixing one FORCES retiring its line.
"""


def read_allow():
    allow = set()
    if os.path.exists(ALLOW):
        for line in open(ALLOW, encoding="utf-8"):
            line = line.split("#")[0].strip()
            if line:
                allow.add(line)
    return allow


TIME_RE = re.compile(r"Built ([A-Za-z0-9_.]+) \(([0-9.]+)(ms|s)\)")


def report(path, top):
    rows = []
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            m = TIME_RE.search(line)
            if m:
                v = float(m.group(2))
                rows.append((v / 1000.0 if m.group(3) == "ms" else v, m.group(1)))
    rows.sort(reverse=True)
    total = sum(v for v, _ in rows)
    print(f"modules timed: {len(rows)}   summed module wall time: {total/3600:.2f} h")
    print("⚠ in-build wall time is contention-inflated (measured 5-11x on hbox); this "
          "ranks, it does not price.\n")
    print(f"{'seconds':>9}  module")
    for v, n in rows[:top]:
        print(f"{v:9.1f}  {n}")
    return 0


def main():
    ap = argparse.ArgumentParser(add_help=False)
    ap.add_argument("--update-baseline", action="store_true")
    ap.add_argument("--report", metavar="BUILD_LOG")
    ap.add_argument("--split-candidates", action="store_true")
    ap.add_argument("--self-test", action="store_true",
                    help="prove each arm can go RED on a synthetic tree")
    ap.add_argument("--seed-allow", action="store_true",
                    help="write the allow file from the CURRENT census (backlog ledger)")
    ap.add_argument("--top", type=int, default=25)
    ap.add_argument("-h", "--help", action="store_true")
    a = ap.parse_args()
    if a.help:
        print(__doc__)
        return 0
    if a.report:
        return report(a.report, a.top)
    if a.self_test:
        print('=== check-elab-cost self-test ===')
        return self_test()

    mods = load_modules()

    if a.split_candidates:
        cands = split_candidates(mods)
        allow = read_allow()
        print(f"=== arm (d) census: {len(cands)} expensive-shaped modules with data-only "
              f"importers ({len(allow)} allowed) ===\n")
        for cnt, name, imps, hb, dec, nd, nt in cands[:a.top]:
            mark = "ALLOWED" if name in allow else "⚑"
            print(f"{mark} {name}  [hb={hb:,} decides={dec} defs={nd} thms={nt}]")
            print(f"    {cnt} data-only importer(s): " + ", ".join(imps[:8]))
        return 0

    if a.seed_allow:
        cands = split_candidates(mods)
        old = read_allow()
        new = {r[1] for r in cands}
        if old and (new - old):
            print("REFUSED: --seed-allow would ADD "
                  f"{len(new - old)} module(s) to the backlog: "
                  + ", ".join(sorted(new - old)))
            print("The backlog may only SHRINK. Split the module, or add its line by hand "
                  "in a commit that says why.")
            return 1
        with open(ALLOW, "w", encoding="utf-8") as fh:
            fh.write(ALLOW_HEADER)
            for cnt, name, imps, hb, dec, nd, nt in cands:
                fh.write(f"{name}\t# {cnt} data-only importer(s); hb={hb:,} decides={dec} "
                         f"defs={nd} thms={nt}\n")
        print(f"allow file seeded with {len(cands)} backlog rows -> "
              f"{os.path.relpath(ALLOW, ROOT)}")
        return 0

    if a.update_baseline:
        old = read_baseline()
        bad = []
        for m in mods.values():
            if m.name in old:
                ohb, ord_, omath = old[m.name]
                if m.hb > ohb or m.rd > ord_ or m.mathlib_all > omath:
                    bad.append((m.name, (ohb, ord_, omath), (m.hb, m.rd, m.mathlib_all)))
        if bad:
            print("REFUSED: --update-baseline may not raise a row. Lower the cost, or "
                  "state the raise in a commit that changes the baseline alone.")
            for n, o, w in bad:
                print(f"  {n}: {o} -> {w}")
            return 1
        n = write_baseline(mods)
        print(f"baseline written: {n} rows -> {os.path.relpath(BASELINE, ROOT)}")
        return 0

    base = read_baseline()
    if not base:
        print("no baseline; run --update-baseline first", file=sys.stderr)
        return 2
    allow = read_allow()
    red = evaluate(mods, base, allow)

    if red:
        print(f"RED — {len(red)} finding(s):")
        for r in sorted(red):
            print("  " + r)
        return 1
    print(f"GREEN — {len(base)} baselined modules, no cost raised, "
          f"no unallowed data-from-gates shape")
    return 0


def evaluate(mods, base, allow):
    """All four arms, over a module dict. Factored out so --self-test can drive it on a
    SYNTHETIC tree: the headline of this gate is a NEGATIVE assertion ("nothing rose,
    nothing has the shape"), and a negative assertion passes just as happily on a reader
    that is silently broken. The self-test is what makes a green mean something."""
    red = []
    for m in mods.values():
        cur = (m.hb, m.rd, m.mathlib_all)
        if m.name in base:
            old = base[m.name]
            for i, label in enumerate(("maxHeartbeats", "maxRecDepth", "import Mathlib")):
                if cur[i] > old[i]:
                    red.append(f"(a-c) {m.name}: {label} rose {old[i]:,} -> {cur[i]:,}")
                elif cur[i] < old[i]:
                    red.append(f"(stale) {m.name}: {label} is now {cur[i]:,} but the "
                               f"baseline still says {old[i]:,} — retire the row "
                               f"(--update-baseline)")
        elif any(cur):
            red.append(f"(new) {m.name}: unlisted module declares "
                       f"maxHeartbeats={m.hb:,} maxRecDepth={m.rd:,} "
                       f"import-Mathlib={m.mathlib_all}")
    for name in base:
        if name not in mods:
            red.append(f"(stale) {name}: baseline row for a module that no longer exists")

    for m in mods.values():
        red.extend(tiedair_findings(m.name, m.code))

    shaped = {r[1] for r in split_candidates(mods)}
    for name in sorted(allow - shaped):
        red.append(f"(d-stale) {name}: allow-listed as a data-from-gates backlog item, but "
                   f"it no longer has the shape — retire its line in "
                   f"{os.path.relpath(ALLOW, ROOT)} so the backlog stays monotone")
    for cnt, name, imps, hb, dec, nd, nt in split_candidates(mods):
        if name in allow:
            continue
        red.append(f"(d) {name}: expensive-shaped [hb={hb:,} decides={dec}] with "
                   f"{cnt} importer(s) that cite only its defs "
                   f"({', '.join(imps[:4])}) — split data from gates, same namespace, "
                   f"MOVE not COPY; or list it in "
                   f"{os.path.relpath(ALLOW, ROOT)} with a reason")
    return red


class FakeMod:
    """A module built from source text, without touching the filesystem."""
    def __init__(self, name, text):
        self.name, self.raw = name, text
        self.code = strip_comments(text)
        self.imports = RE_IMPORT.findall(text)
        self.defs, self.thms = set(), set()
        for kind, nm in RE_DECL.findall(self.code):
            (self.thms if kind in ("theorem", "lemma") else self.defs).add(nm)
        self.hb = max((int(x) for x in RE_HB.findall(self.code)), default=0)
        self.rd = max((int(x) for x in RE_RD.findall(self.code)), default=0)
        self.mathlib_all = 1 if RE_MATHLIB_ALL.search(text) else 0
        self.decides = len(RE_DECIDE.findall(self.code))
        self.tokens = set(RE_TOKEN.findall(self.code))


GATE_SRC = ("import Mathlib.Tactic\nset_option maxHeartbeats 4000000\n"
            "def LAGRANGE : List Nat := [1,2,3]\n"
            "theorem msm_is_gold : True := by decide\n")
CONSUMER_DATA_ONLY = "import G\ndef use := LAGRANGE\n"
CONSUMER_CITES_THM = "import G\ntheorem t := msm_is_gold\n"


def self_test():
    """Prove each arm can go RED, and that the controls stay GREEN."""
    fails = []

    def check(label, got_red, want_red, want_tag=None):
        ok = bool(got_red) == want_red and (
            want_tag is None or any(want_tag in r for r in got_red))
        print(f"  {'ok  ' if ok else 'FAIL'}  {label}"
              + ("" if ok else f"   -> {got_red}"))
        if not ok:
            fails.append(label)

    # control: a tree at its own baseline, shape allow-listed, is GREEN
    mods = {"G": FakeMod("G", GATE_SRC), "C": FakeMod("C", CONSUMER_DATA_ONLY)}
    base = {"G": (4_000_000, 0, 0)}
    check("control: at baseline + allow-listed shape is green",
          evaluate(mods, base, {"G"}), False)

    # arm (a): a heartbeat raise
    check("arm (a): maxHeartbeats rose",
          evaluate(mods, {"G": (2_000_000, 0, 0)}, {"G"}), True, "maxHeartbeats rose")

    # arm (b): a recDepth raise
    m2 = {"G": FakeMod("G", GATE_SRC + "set_option maxRecDepth 99\n")}
    check("arm (b): maxRecDepth rose",
          evaluate(m2, {"G": (4_000_000, 0, 0)}, {"G"}), True, "maxRecDepth rose")

    # arm (c): a whole-Mathlib import appearing
    m3 = {"G": FakeMod("G", "import Mathlib\n" + GATE_SRC)}
    check("arm (c): whole-Mathlib import appeared",
          evaluate(m3, {"G": (4_000_000, 0, 0)}, {"G"}), True, "import Mathlib")

    # arm (d): the data-from-gates shape, unallowed
    check("arm (d): data-only importer of an expensive-shaped module",
          evaluate(mods, base, set()), True, "split data from gates")

    # arm (d) control: an importer that CITES a theorem is not a finding
    mods_cite = {"G": FakeMod("G", GATE_SRC), "C": FakeMod("C", CONSUMER_CITES_THM)}
    check("arm (d) control: theorem-citing importer is not a finding",
          evaluate(mods_cite, base, set()), False)

    # arm (d) floor: a module with decides but NO declared raise is not a finding
    cheap = GATE_SRC.replace("set_option maxHeartbeats 4000000\n", "")
    check("arm (d) floor: no declared raise => not expensive-shaped",
          evaluate({"G": FakeMod("G", cheap), "C": FakeMod("C", CONSUMER_DATA_ONLY)},
                   {"G": (0, 0, 0)}, set()), False)

    # stale arms
    check("stale: baseline above the tree forces retirement",
          evaluate(mods, {"G": (9_000_000, 0, 0)}, {"G"}), True, "(stale)")
    check("stale: allow row for a module without the shape",
          evaluate({"G": FakeMod("G", cheap)}, {"G": (0, 0, 0)}, {"G"}), True, "(d-stale)")
    check("new: unlisted module declaring a raise",
          evaluate(mods, {}, {"G"}), True, "(new)")

    # arm (e): a `TiedAir` that leaves a verdict to the autoParam, and the two controls
    tied_blank = ("def fooTiedAir : EffectLower.TiedAir where\n"
                  "  air := fooAir\n")
    tied_decide = ("def fooTiedAir : EffectLower.TiedAir where\n"
                   "  air  := fooAir\n  ok   := by decide\n  tied := by decide\n")
    tied_good = ("def fooTiedAir : EffectLower.TiedAir where\n"
                 "  air  := fooAir\n  ok   := fooAir_mainRailOk\n"
                 "  tied := fooAir_pinsTied\n")
    check("arm (e): a TiedAir with no `ok :=` is a finding",
          evaluate({"T": FakeMod("T", tied_blank)}, {}, set()), True, "`ok :=` not supplied")
    check("arm (e): a TiedAir with no `tied :=` is a finding",
          evaluate({"T": FakeMod("T", "def fooTiedAir : EffectLower.TiedAir where\n"
                                      "  air := fooAir\n  ok  := fooAir_mainRailOk\n")},
                   {}, set()), True, "`tied :=` not supplied")
    check("arm (e): `ok := by decide` is the autoParam written out, still a finding",
          evaluate({"T": FakeMod("T", tied_decide)}, {}, set()), True, "is a `decide`")
    check("arm (e) control: both verdicts supplied as terms is green",
          evaluate({"T": FakeMod("T", tied_good)}, {}, set()), False)
    check("arm (e) control: the `structure TiedAir where` DECLARATION is not an instance",
          evaluate({"T": FakeMod("T", "structure TiedAir where\n  air : EffectAir\n"
                                      "  ok : air.mainRailOk = true := by decide\n")},
                   {}, set()), False)

    # the comment stripper must not be fooled — a `#guard`-free file whose PROSE
    # mentions maxHeartbeats must not register a raise
    prose = "/-! docs: we used to `set_option maxHeartbeats 900000000` here -/\ndef x := 1\n"
    check("stripper: a raise mentioned only in a docstring is not a raise",
          evaluate({"P": FakeMod("P", prose)}, {}, set()), False)

    print(("SELF-TEST GREEN" if not fails else f"SELF-TEST RED: {fails}"))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
