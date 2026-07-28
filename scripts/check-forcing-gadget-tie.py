#!/usr/bin/env python3
"""check-forcing-gadget-tie — a forcing module must mention the gates it claims to force.

WHY THIS EXISTS (2026-07-27, docs/AUDIT-CRYPTO-GADGETS.md findings F3 / F5 / F6)

`Blake2bFoldForcing.lean` — 895 lines, 47 theorems — contained the string `acceptB` **zero
times**. `Bls12381Forcing.lean` — 683 lines, 29 theorems — the same. Their headline results
(`blakeG_forces`, `blake2bF_forces`, `absorb_forces`, `g1Add_forces`, `g1Double_forces`) took raw
`evalH … = 0` equations over universally quantified column bases, or the conclusions of other
lemmas, and never named the generator they claimed to force. They were not statements about the
emitted circuit at all, and every one of them shipped under a commit subject saying it was.

Nothing in the tree could see that. The files built green, their `#assert_axioms` passed (an
implication with an unfilled antecedent is axiom-clean for free), and their names read exactly like
the honest sibling's. The one measurement that separates them is mechanical and is this script:

  RULE A — a forcing module must CONSUME gate acceptance at least once.
           Measured on the day the two broken files landed: Sha256FoldForcing 13,
           Sha256HfoldDischarge 7, Blake2bFoldForcing **0**, Bls12381Forcing **0**.

  RULE B — a theorem named `<G>_forces`, where `<G>` is a generator that emits constraints,
           must MENTION `<G>` in its statement. A name is a claim.

Rule B has a BASELINE (`scripts/forcing-tie-baseline.txt`): the offenders that already exist, each
with the audit finding that named it. The baseline RATCHETS — a new offender fails, and so does a
baseline entry that has been fixed, so the list can only shrink. It is debt made visible, not an
excuse: every line in it is a theorem whose name claims more than its statement delivers.

  scripts/check-forcing-gadget-tie.py              # the gate
  scripts/check-forcing-gadget-tie.py --self-test  # prove it can go RED
"""

from __future__ import annotations

import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
METATHEORY = ROOT / "metatheory"
BASELINE = ROOT / "scripts" / "forcing-tie-baseline.txt"

# A forcing module: the file's whole purpose is to relate emitted gates to a reference function.
# `*Forcing*.lean` anywhere, plus `*Discharge*.lean` UNDER THE EMIT DIRECTORY — `Sha256HfoldDischarge`
# is a forcing module in substance and would otherwise be unscanned, while the ~20 other
# `*Discharge*.lean` files in the tree (Authority, Crypto, …) are about proof obligations, not gates.
FORCING_NAME = re.compile(r"Forcing.*\.lean$")
EMIT_DISCHARGE = re.compile(r"Discharge.*\.lean$")


def is_forcing_module(f: Path) -> bool:
    if FORCING_NAME.search(f.name):
        return True
    return EMIT_DISCHARGE.search(f.name) is not None and "Circuit/Emit" in f.as_posix()

THEOREM = re.compile(r"^(?:private\s+|protected\s+|@\[[^\]]*\]\s*)*theorem\s+([A-Za-z0-9_.']+)")
# `def foo ... : ... List VmConstraint2 ...` — a generator, i.e. something that EMITS constraints.
GENERATOR = re.compile(r"^(?:private\s+|protected\s+)?def\s+([A-Za-z0-9_']+)")
ACCEPTANCE_HYP = re.compile(r":\s*acceptB\b")


def statement_of(lines: list[str], i: int) -> tuple[str, int]:
    """The theorem's SIGNATURE — from `theorem` to the `:=`/`by` that starts the proof."""
    out: list[str] = []
    j = i
    while j < len(lines):
        out.append(lines[j])
        if ":=" in lines[j] or re.search(r"\bby\s*$", lines[j]):
            break
        j += 1
    return "\n".join(out), j


def theorems_in(text: str) -> list[tuple[str, str]]:
    lines = text.split("\n")
    found: list[tuple[str, str]] = []
    i = 0
    while i < len(lines):
        m = THEOREM.match(lines[i])
        if m:
            stmt, j = statement_of(lines, i)
            found.append((m.group(1), stmt))
            i = j + 1
        else:
            i += 1
    return found


def generator_names(files: list[Path]) -> set[str]:
    """Every `def` whose declaration mentions `List VmConstraint2` — it emits gates."""
    names: set[str] = set()
    for f in files:
        lines = f.read_text(encoding="utf-8", errors="replace").split("\n")
        for i, line in enumerate(lines):
            m = GENERATOR.match(line)
            if not m:
                continue
            head = "\n".join(lines[i : i + 6])
            head = head.split(":=")[0]
            if "List VmConstraint2" in head:
                names.add(m.group(1))
    return names


def load_baseline() -> set[str]:
    if not BASELINE.exists():
        return set()
    out = set()
    for raw in BASELINE.read_text(encoding="utf-8").split("\n"):
        line = raw.split("#")[0].strip()
        if line:
            out.add(line)
    return out


def scan(tree: Path, extra_defs: list[Path] | None = None) -> tuple[list[str], set[str]]:
    """Returns (violations, rule-B keys actually seen) for the forcing modules under `tree`."""
    all_lean = sorted(tree.rglob("*.lean"))
    forcing = [f for f in all_lean if is_forcing_module(f)]
    gadgets = generator_names(all_lean + list(extra_defs or []))

    violations: list[str] = []
    seen_b: set[str] = set()

    for f in forcing:
        rel = f.relative_to(ROOT) if ROOT in f.parents or f.is_relative_to(ROOT) else f
        text = f.read_text(encoding="utf-8", errors="replace")
        thms = theorems_in(text)

        tied = [n for n, s in thms if ACCEPTANCE_HYP.search(s)]
        if not tied:
            violations.append(
                f"RULE A  {rel}: {len(thms)} theorem(s), NONE consumes gate acceptance "
                f"(no `: acceptB` in any statement). A forcing module that never mentions "
                f"acceptance is not about the emitted gates — audit F3/F5."
            )

        for name, stmt in thms:
            if not name.endswith("_forces"):
                continue
            gadget = name[: -len("_forces")]
            if gadget not in gadgets:
                continue
            key = f"{rel}::{name}"
            seen_b.add(key)
            # The theorem's OWN NAME contains the gadget name by construction; a name is a claim,
            # not a mention. Search the signature with the name itself removed.
            body = stmt.replace(name, "", 1)
            if gadget not in body and not ACCEPTANCE_HYP.search(body):
                violations.append(
                    f"RULE B  {key}: named for the generator `{gadget}` but its statement "
                    f"mentions neither `{gadget}` nor `acceptB`. Tie it, or rename it to what "
                    f"it is (`{gadget}_core_forces` / `{gadget}_of_…`)."
                )

    return violations, seen_b


SELF_TEST_BAD = """\
import Dregg2.Circuit.Emit.AirBuilder
namespace Fake
def widgetGadget (base : Nat) : List VmConstraint2 := []
theorem widgetGadget_forces (a : Assignment) (base out : Nat)
    (hg : evalH (someHead base out) a = 0) :
    Holds a out 0 := by
  sorry
end Fake
"""


def self_test() -> int:
    with tempfile.TemporaryDirectory() as d:
        tree = Path(d)
        (tree / "FakeForcing.lean").write_text(SELF_TEST_BAD, encoding="utf-8")
        violations, _ = scan(tree)
    got_a = any(v.startswith("RULE A") for v in violations)
    got_b = any(v.startswith("RULE B") for v in violations)
    if got_a and got_b:
        print("check-forcing-gadget-tie --self-test: OK — the gate goes RED on a forcing module "
              "with no acceptance and on a `<gadget>_forces` that does not mention its gadget.")
        return 0
    print("check-forcing-gadget-tie --self-test: FAILED — the gate could NOT be made to fire "
          f"(rule A fired: {got_a}, rule B fired: {got_b}). A gate that cannot go red is not a gate.",
          file=sys.stderr)
    for v in violations:
        print("  saw: " + v, file=sys.stderr)
    return 1


def main() -> int:
    if "--self-test" in sys.argv[1:]:
        return self_test()

    if not METATHEORY.is_dir():
        print(f"check-forcing-gadget-tie: no {METATHEORY} — nothing to check", file=sys.stderr)
        return 0

    violations, seen_b = scan(METATHEORY)
    baseline = load_baseline()

    unbaselined = []
    for v in violations:
        if v.startswith("RULE B"):
            key = v.split("RULE B  ", 1)[1].split(": named for", 1)[0]
            if key in baseline:
                continue
        unbaselined.append(v)

    # The ratchet: a baseline entry that no longer fires must be REMOVED, so the list only shrinks.
    still_failing = {
        v.split("RULE B  ", 1)[1].split(": named for", 1)[0]
        for v in violations
        if v.startswith("RULE B")
    }
    stale = sorted(b for b in baseline if b in seen_b and b not in still_failing)
    gone = sorted(b for b in baseline if b not in seen_b)

    if unbaselined or stale or gone:
        for v in unbaselined:
            print(f"check-forcing-gadget-tie: {v}", file=sys.stderr)
        for s in stale:
            print(
                f"check-forcing-gadget-tie: BASELINE STALE — `{s}` is now tied. Delete its line "
                f"from {BASELINE.relative_to(ROOT)}; the baseline only shrinks.",
                file=sys.stderr,
            )
        for g in gone:
            print(
                f"check-forcing-gadget-tie: BASELINE DEAD — `{g}` no longer exists. Delete its "
                f"line from {BASELINE.relative_to(ROOT)}.",
                file=sys.stderr,
            )
        return 1

    n_files = len([f for f in METATHEORY.rglob("*.lean") if is_forcing_module(f)])
    print(
        f"check-forcing-gadget-tie: OK — {n_files} forcing module(s), each consumes gate "
        f"acceptance; {len(seen_b)} `<gadget>_forces` theorem(s) checked, "
        f"{len(baseline)} baselined."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
