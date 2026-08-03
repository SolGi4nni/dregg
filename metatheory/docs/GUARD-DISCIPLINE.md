# `#guard` discipline — **a fact worth asserting is worth naming**

Policy for `metatheory/`. Gate: `scripts/check-guard-discipline.py` (in `scripts/local-gates.sh`).

---

## The rule

**Default to a named theorem. `#guard` is the exception, and it must earn itself.**

```lean
-- NO  ─ asserts one instance, produces nothing, invisible to axiom accounting
#guard emitVmJson2 d == GOLDEN

-- YES ─ same assertion, same object, same cost; now named, citable, axiom-visible
theorem d_emits_golden : emitVmJson2 d = GOLDEN := by rfl
#assert_axioms d_emits_golden
```

`#guard` is acceptable only for a genuinely throwaway sanity check that **nothing will ever cite**.
If nothing will ever cite it, ask why it exists.

---

## ⚑ The measurement that settles the argument

This is not a style preference. Lean 4.30, `Lean/Elab/Tactic/Guard.lean:154-167`:

```lean
@[builtin_command_elab guardCmd]
def evalGuardCmd : CommandElab
  | `(command| #guard $e:term) => liftTermElabM do
    let e ← Term.elabTermEnsuringType e (mkConst ``Bool)
    ...
    let v ← unsafe evalExpr (checkMeta := false) Bool (mkConst ``Bool) e
    unless v do throwError "…did not evaluate to `true`"
```

**`#guard` runs the unsafe compiled evaluator — the same engine `native_decide` runs on.**

So a `#guard` is *not* a cheaper or weaker check than a `native_decide` theorem. It is the **same
check with three things deleted**:

| | `#guard e` | `theorem foo : e = true := by native_decide` |
|---|---|---|
| evaluator | `unsafe evalExpr` | `unsafe evalExpr` |
| trust | the compiler | the compiler |
| **name** | none | `foo` |
| **term in the environment** | none | yes — later proofs can *use* it |
| **axiom record** | **none** | `foo._native.native_decide.ax_…`, visible to `#print axioms` |

The last row is the wound. **A `#guard` does not avoid trusting the compiler; it trusts the compiler
silently.** `#assert_axioms` sees theorems. It cannot account for a guard, so every guard is a fact
the axiom hygiene instrument is structurally blind to.

And where kernel reduction *is* reachable, `by decide` / `by rfl` is **strictly stronger** than the
guard ever was. Converting is not a rename; on those it is an upgrade in what is actually checked.

---

## ⚑ This is the sin `CLAUDE.md` already forbids in the other language

> A Rust test that "the AIR accepts iff `applyTurn` holds" on cases is just unit tests with **ZERO
> formal content** — NEVER call it translation validation / refinement / verification. Rust
> case-tests prove NOTHING about all inputs.

Moving case-tests into Lean did not make them verification. `#guard e` evaluates **one closed
instance at elaboration time**. A file with 848 of them has 848 case-tests and zero theorems about
its subject.

---

## What to convert first — the load-bearing criterion

Not all of them. In priority order, a guard is **load-bearing** if:

**(a) its failure would change a reported result** — a byte-golden equality, a real-block weld, a
conformance pin, a fixture sha. If a number in a commit message or a doc came out of it, it is
load-bearing.

**(b) it is cited as evidence** — in a docstring, a commit subject, a `HORIZONLOG` entry. Prose that
says "pinned byte-exact" and points at a `#guard` is citing a fact that has no name. The citation is
the tell: something already *wanted* to compose on it and could not.

**(c) it is the sole support for a definition** — a `def` whose only checked property is a `#guard`.
Nothing else in the tree says anything about it.

Everything else can wait. A throwaway `#guard 1 == 1` next to a scratch definition is not the
problem; the byte-golden pin with no name is.

---

## How to convert

### 1. If the kernel can reach it, use the kernel

```lean
theorem foo : lhs = rhs := by decide   -- or `rfl`, or a real proof
#assert_axioms foo
```

This is **stronger** than the guard was. Prefer it always. Raise `maxRecDepth` before giving up.

### 2. If only the compiler can reach it, say so out loud

```lean
theorem foo : lhs = rhs := by native_decide
#assert_compiled foo
```

`#assert_compiled` (`Dregg2/Tactics.lean`) passes iff every axiom `foo` rests on is either
kernel-clean or a `native_decide` oracle, **and at least one oracle is present**. Both halves red:

* a `sorry` or a fresh `axiom` is still a hard error — this is not a laxer `#assert_axioms`, it
  widens the allow-list by exactly one *named* class;
* **zero oracles is also an error** — a kernel-clean fact must take the stronger `#assert_axioms`,
  so the command cannot be used to launder a proof downward.

⚠ **`#assert_compiled` is a confession, not a certificate.** It says the fact rests on the compiler.
That was *already true* of the `#guard` it replaces — the pin makes it countable, not safer.

### 3. ⚑ If the guard was an instance of a general fact, **prove the general fact**

This is where the real gain is, and it is the reason to do this work at all.

* `#guard (tickShiftsFp 16).length == 7` cannot see *why* seven. The ∀ can:
  `sampleAux_length_le : ∀ fuel i acc, (sampleAux n fuel i acc).length ≤ max acc.length 6` — the
  early-out is what bounds the loop. The instance could not distinguish "the bound holds" from "64
  fuel happened to run out at seven".
* `powFast` — the exponentiation ladder under the whole Wrap leg — was tied to `^` by a `decide` on
  **four cases** until `powFast_eq_pow` was proved for every monoid and every exponent.

Keep the instance too, as a corollary, so **no assertion is lost**. State plainly in the docstring
which conversions gained a ∀ and which only gained a name.

---

## ⚠ Do not lose an assertion

* Every converted guard must assert **exactly** what it asserted, over the **same object**. If the
  guard read `getD 0 0`, the theorem reads `getD 0 0` — not `headD`, even when they agree.
* The emitted circuit must stay **byte-identical** (`scripts/check-descriptor-drift.sh`) and the
  conformance fixture shas unchanged. Converting an assertion touches no `def`; if the emission
  moves, something else moved with it.
* `scripts/check-guard-modules.py`'s census must not **grow**, and no assertion may fall out of a
  build target — a theorem in an unrooted module is exactly as unchecked as a guard in one.

## ⚠ The failure mode to watch for

A guard can be **vacuous in ways a theorem exposes**. A lane once shipped five pins described as
protecting a chain, of which the shape `classCells x ≥ 1` *holds with the whole chain deleted* —
because another consumer reads the variable 47 times. Writing it as a theorem forces you to name
what it quantifies over, and the vacuity becomes readable. That is a reason to convert, not a
reason to stop at "the guard was green".

Related: a guard's theorem-level support must **name its field**. `publicEval`/`ipaB0`/`ftComm` had
their entire theorem support at the rationals, standing in for claims about a 255-bit field.

---

## The ratchet

`scripts/check-guard-discipline.py` records a **per-module** `#guard` count in
`scripts/guard-discipline-baseline.txt`. The baseline may only **shrink**:

* a module **above** its baseline is RED — new guards in a converted module fail;
* a module **below** its baseline is RED **as a stale row** — you converted, so retire the number;
* a module with **no** row that carries guards is RED — the population cannot grow sideways.

Run it: `python3 scripts/check-guard-discipline.py` · red-proof: `--self-test` · retire rows:
`--update-baseline --only <path> --reason "…"`.

## ⚑⚑ The refresh is gated too — and it is what let 23 guards in

Every arm above grades a **census** against the **ledger**. Nothing graded the ledger, and
`--update-baseline` rewrote it unconditionally, so the one operation that exists to turn the ratchet
down could turn it up — and a green afterwards certified the *new* number.

**Measured 2026-08-02.** Between `a7d30783d` (the baseline commit) and `a819016de` (a refresh) the
ledger went 15,656 → 15,665. **No row was raised.** `KimchiStepMain.lean` (814) was removed and
thirteen `…Pins01–13` rows totalling **837** were added — a module **split**. Twenty-three guards a
concurrent rung had just written entered the baseline as two operations that each looked correct: a
burned-down module retiring its row, and arm (c) being obeyed by giving new guard-carrying modules
their rows. And the +23 was **net −5 on the visible total**, because the same refresh also carried a
real −14 burndown in `MinaMultiBlockConformance`. A genuine conversion paid for a laundered growth.

⚑ **A rename is how a population grows while no row grows. Only the TOTAL can see it.** So:

* **(d1)** a refresh may not raise **any surviving row**;
* **(d2)** a refresh may not raise the **total** — this is the arm that catches a split, since a
  genuine split's pieces sum to at most the original;
* **(d3)** every refresh records **provenance** — sha, whether the tree was **dirty**, the totals,
  and a mandatory `--reason` — stamped into the baseline header, so every movement is attributable
  by `git log`. Dirtiness is recorded because the laundered refresh *was* a lane rewriting the
  ledger from its own uncommitted churn.

⚑ **`--only <path>` is the default way to retire rows, not a convenience.** The tree is shared. A
whole-census refresh absorbs every *other* lane's in-flight guard-carrying module — the same
laundering shape with a sibling's work as the payload. `--only` retires exactly the rows you earned
and leaves the rest standing; the sibling's module keeps redding until its own lane owns it.

⚠ **The override is loud, not absent.** `--allow-increase` exists, still requires `--reason`, and
stamps `INCREASED` with the delta. A ban with no escape hatch gets routed around by hand-editing the
file, which is the silent outcome. The wound was never that the number went up — it was that
nothing said so.

Red-proofed in `--self-test` (28 arms), including the two green controls that keep the gate from
being a blanket refusal: a **level split** whose pieces sum to the original is accepted, and a
legitimate **downward** refresh is accepted.
