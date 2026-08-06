/-
# Dregg2.Circuit.Emit.ShieldedSpendExactMembershipDescriptor — the shielded-spend exact-linked
membership descriptor at the FSI2/FSN2/FSE2 domain (Fork B, pass 4: the NODE-INDICATOR soundness rung).

**This is Lean-authored AIR.** Fork B keeps the depth-16 arity-4 `next_addr`-linked indexed-Merkle
shielded accumulator (`cell/src/shielded_note_set.rs`) and makes the DESCRIPTOR commensurate with it.
Pass 3 (`Emit.ShieldedExactMembershipFold`) fixed the fold SEMANTICS at the deployed `hash_many_8`.
This pass authors the one rung that must not be rushed: the **general-position node indicator** — the
`v3ChildExpr`-shape expression that places `cur` at the bit-encoded child position among the four
children — and PROVES it realizes the deployed placement `exactChildren4` (`recompose`,
`circuit/src/exact_nullifier_aafi.rs:724-748`).

⚑ **Why this rung is load-bearing (and split out).** A wrong node indicator is a MEMBERSHIP HOLE —
worse than #15 — a soundness regression that builds green and passes an adversarial reader:
`ExactNullifierAafiDescriptorPlan` EMITS `v3ChildExpr` but nowhere PROVES it computes `exactChildren4`.
So it gets the campaign's discipline: **satisfiable AND refutable but not trivially true**:
  * `childExpr_pos0..3` — under position bits `b0, b1 ∈ {0,1}`, the four emitted child expressions
    evaluate to EXACTLY the position placement `(cur, s0, s1, s2)` reordered as `exactChildren4` does;
  * `exactChildren4_lane` — that placement IS the deployed `exactChildren4`, lane by lane;
  * `nonbit_forges_child` — the REFUTATION tooth: a NON-bit `b0 = 2` makes the slot-0 child a value
    that is NEITHER `cur` NOR any sibling — a forged child no `exactChildren4` slot admits. So the bit
    gate is load-bearing and the indicator is not trivially a permutation of arbitrary inputs.

## Scope (honest) — what this is NOT
This is the node-indicator rung ONLY. The emitted `EffectVmDescriptor2` (the FSN2 node sponge via
`spongePlan`, the FSI2 leaf sponge, the 8× `.piBinding .last` pin to an 8-lane `piCOMMITTED`, the
golden bytes) and `root_is_pinned8` over `Satisfied2` are pass 5 — they compose this proven indicator
with the pass-3 `shieldedParent`/`shieldedFoldPath`. The descriptor VK will be
`dregg-shielded-spend-exact-fsi2::v1`. No `native_decide`: nothing here evaluates Poseidon2 — the
indicator is pure position algebra. #15 does NOT flip here; that is the route pass, after pass 5.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan
import Dregg2.Circuit.Emit.BlindedMembershipEmit

namespace Dregg2.Circuit.Emit.ShieldedSpendExactMembershipDescriptor

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.BlindedMembershipEmit (ev ek eadd emul eneg esub)
open Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan
  (exactChildren4 siblingIndex0 siblingIndex1 siblingIndex2)
open Dregg2.Circuit.ExactNullifierAafiPlan (Root8 PathStep4)

set_option autoImplicit false

/-- `1 − x`, the bit complement. -/
def oneMinus (x : EmittedExpr) : EmittedExpr := esub (ek 1) x

/-- The 2-bit one-hot position indicators — `pos = b0 + 2·b1`, so `indPk` is `1` iff `pos = k`. -/
def indP0 (b0 b1 : EmittedExpr) : EmittedExpr := emul (oneMinus b0) (oneMinus b1)
def indP1 (b0 b1 : EmittedExpr) : EmittedExpr := emul b0 (oneMinus b1)
def indP2 (b0 b1 : EmittedExpr) : EmittedExpr := emul (oneMinus b0) b1
def indP3 (b0 b1 : EmittedExpr) : EmittedExpr := emul b0 b1

/-- The emitted child expression at slot `slot` — the `v3ChildExpr` shape
(`ExactNullifierAafiDescriptorPlan.v3ChildExpr`), placing `cur` at the bit-encoded position among the
four children and filling the other slots with siblings in order. Authored here so its correctness is
PROVED (below), not merely emitted. -/
def childExpr (slot : Nat) (b0 b1 cur s0 s1 s2 : EmittedExpr) : EmittedExpr :=
  match slot with
  | 0 => eadd s0 (emul (indP0 b0 b1) (esub cur s0))
  | 1 => eadd (eadd (emul s0 (indP0 b0 b1)) (emul cur (indP1 b0 b1)))
              (emul s1 (eadd (indP2 b0 b1) (indP3 b0 b1)))
  | 2 => eadd (eadd (emul s1 (eadd (indP0 b0 b1) (indP1 b0 b1))) (emul cur (indP2 b0 b1)))
              (emul s2 (indP3 b0 b1))
  | _ => eadd s2 (emul (indP3 b0 b1) (esub cur s2))

/-- The child placement `exactChildren4` computes, as a scalar 4-tuple keyed on the position: `cur`
at `pos`, siblings elsewhere in order. This is `exactChildren4` projected to one lane (`exactChildren4_lane`). -/
def childPattern (pos : Fin 4) (cur s0 s1 s2 : ℤ) : List ℤ :=
  match pos.val with
  | 0 => [cur, s0, s1, s2]
  | 1 => [s0, cur, s1, s2]
  | 2 => [s0, s1, cur, s2]
  | _ => [s0, s1, s2, cur]

/-! ## The indicator realizes `exactChildren4` — SATISFIABLE (correct for every bit position). -/

theorem childExpr_pos0 (a : Assignment) (b0 b1 cur s0 s1 s2 : EmittedExpr)
    (h0 : b0.eval a = 0) (h1 : b1.eval a = 0) :
    (childExpr 0 b0 b1 cur s0 s1 s2).eval a = cur.eval a
    ∧ (childExpr 1 b0 b1 cur s0 s1 s2).eval a = s0.eval a
    ∧ (childExpr 2 b0 b1 cur s0 s1 s2).eval a = s1.eval a
    ∧ (childExpr 3 b0 b1 cur s0 s1 s2).eval a = s2.eval a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [childExpr, indP0, indP1, indP2, indP3, oneMinus, ev, ek, eadd, emul, esub, eneg,
      EmittedExpr.eval, h0, h1] <;> ring

theorem childExpr_pos1 (a : Assignment) (b0 b1 cur s0 s1 s2 : EmittedExpr)
    (h0 : b0.eval a = 1) (h1 : b1.eval a = 0) :
    (childExpr 0 b0 b1 cur s0 s1 s2).eval a = s0.eval a
    ∧ (childExpr 1 b0 b1 cur s0 s1 s2).eval a = cur.eval a
    ∧ (childExpr 2 b0 b1 cur s0 s1 s2).eval a = s1.eval a
    ∧ (childExpr 3 b0 b1 cur s0 s1 s2).eval a = s2.eval a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [childExpr, indP0, indP1, indP2, indP3, oneMinus, ev, ek, eadd, emul, esub, eneg,
      EmittedExpr.eval, h0, h1] <;> ring

theorem childExpr_pos2 (a : Assignment) (b0 b1 cur s0 s1 s2 : EmittedExpr)
    (h0 : b0.eval a = 0) (h1 : b1.eval a = 1) :
    (childExpr 0 b0 b1 cur s0 s1 s2).eval a = s0.eval a
    ∧ (childExpr 1 b0 b1 cur s0 s1 s2).eval a = s1.eval a
    ∧ (childExpr 2 b0 b1 cur s0 s1 s2).eval a = cur.eval a
    ∧ (childExpr 3 b0 b1 cur s0 s1 s2).eval a = s2.eval a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [childExpr, indP0, indP1, indP2, indP3, oneMinus, ev, ek, eadd, emul, esub, eneg,
      EmittedExpr.eval, h0, h1] <;> ring

theorem childExpr_pos3 (a : Assignment) (b0 b1 cur s0 s1 s2 : EmittedExpr)
    (h0 : b0.eval a = 1) (h1 : b1.eval a = 1) :
    (childExpr 0 b0 b1 cur s0 s1 s2).eval a = s0.eval a
    ∧ (childExpr 1 b0 b1 cur s0 s1 s2).eval a = s1.eval a
    ∧ (childExpr 2 b0 b1 cur s0 s1 s2).eval a = s2.eval a
    ∧ (childExpr 3 b0 b1 cur s0 s1 s2).eval a = cur.eval a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [childExpr, indP0, indP1, indP2, indP3, oneMinus, ev, ek, eadd, emul, esub, eneg,
      EmittedExpr.eval, h0, h1] <;> ring

/-- **`exactChildren4_lane`.** The scalar placement `childPattern` IS the deployed `exactChildren4`,
lane by lane — so the emitted indicator (which `childExpr_pos*` prove realizes `childPattern`) absorbs
exactly the children `note_shielded.root8()`'s fold does. -/
theorem exactChildren4_lane (cur : Root8) (step : PathStep4) (l : Fin 8) :
    (exactChildren4 cur step).map (fun d => d l)
      = childPattern step.position (cur l) (step.siblings siblingIndex0 l)
          (step.siblings siblingIndex1 l) (step.siblings siblingIndex2 l) := by
  obtain ⟨pos, sibs⟩ := step
  fin_cases pos <;> simp [exactChildren4, childPattern]

/-! ## The indicator is REFUTABLE — a non-bit input forges a child no slot admits. -/

/-- **⚑ THE REFUTATION TOOTH (`nonbit_forges_child`).** Drop the bit constraint — set `b0 = 2` — and
the slot-0 child evaluates to `-1`, which is NEITHER `cur` (`1`) NOR the sibling `s0` (`0`): a forged
child `exactChildren4` never yields. So the position-bit gate is LOAD-BEARING, and the indicator is
not trivially a permutation of arbitrary inputs. The mutation (`b0 = 2`) is asserted present before
the verdict. -/
theorem nonbit_forges_child :
    ∃ (a : Assignment) (b0 b1 cur s0 s1 s2 : EmittedExpr),
      b0.eval a = 2
      ∧ (childExpr 0 b0 b1 cur s0 s1 s2).eval a ≠ cur.eval a
      ∧ (childExpr 0 b0 b1 cur s0 s1 s2).eval a ≠ s0.eval a := by
  refine ⟨fun _ => 0, ek 2, ek 0, ek 1, ek 0, ek 0, ek 0, ?_, ?_, ?_⟩ <;>
    simp only [childExpr, indP0, oneMinus, ek, eadd, emul, esub, eneg, EmittedExpr.eval] <;> norm_num

#assert_axioms childExpr_pos0
#assert_axioms childExpr_pos1
#assert_axioms childExpr_pos2
#assert_axioms childExpr_pos3
#assert_axioms exactChildren4_lane
#assert_axioms nonbit_forges_child

end Dregg2.Circuit.Emit.ShieldedSpendExactMembershipDescriptor
