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
import Dregg2.Circuit.ShieldedWideJoinPin

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

/-! ## §2 — THE PI LAYOUT: expose BOTH carriers in ONE descriptor (the Fork B coupling, verified at
source against the landed same-opening lane `4de4190ab`).

Since pass 4 the same-opening lane landed (`4de4190ab`): it DELETED the ~31-bit `legacy_binding` felt
and routed the ring↔wide join to a 16-lane wide-carrier same-opening (`ShieldedWideJoinPin.routedJoin`
— `verify_same_opening` over `[BabyBear; 16]`, two domain-separated `node8` images,
`WIDE_VALUE_BINDING_LANES = 16`). That routed join now **fails closed** in
`turn-prover/src/shielded_transfer_verifier.rs` (7 `shielded_executor` tests `#[ignore]`d) because it
needs the ring's full-`u64` value carrier INDEPENDENTLY BOUND by the spend proof — and today's spend
circuit exposes only the one-felt `value_binding` (`value mod p`), which cannot be same-opened without
the forbidden identity carrier.

So this descriptor's PI layout exposes BOTH carriers, so ONE re-authored spend proof un-fail-closes
BOTH #15 (the 8-lane committed root) AND the same-opening join (the 16-lane wide-`u64` carrier) —
never a second spend-circuit pass. The layout is locked HERE so pass 6 (the emitted golden +
`root_is_pinned8`) does not discover the coupling late. -/

/-- PI 0: the published nullifier. -/
def piNUL : Nat := 0
/-- PIs 1..8: the **8-lane committed shielded-accumulator root** — the #15 pin, executor-sourced from
`note_shielded.root8()`, NEVER the wire. Eight lanes, so §7's `route_fold_8to1_collides` collapse is
unrepresentable at the PI. -/
def PI_COMMITTED_BASE : Nat := 1
def PI_COMMITTED_LANES : Nat := 8
/-- PIs 9..24: the **16-lane wide-`u64` value carrier** — the object same-opening's routed join
compares (`ShieldedWideJoinPin.routedJoin`, a `Wide16 = Opening → (Fin 16 → ℤ)`). The spend proof must
bind this so the join has a spend-side carrier to same-open against. ⚠ It MUST be the real
`cap_node8` image (`ShieldedWideJoinPin.alias_separated_by_the_wide_carrier` /
`WideValueBindingRefine.WideCarrierCR`), a genuine non-identity `u64` opening — NEVER `value mod p`
relabelled. Binding the 16 lanes to that image is the pass-6 constraint work; here the slots are
RESERVED and the requirement is named. -/
def PI_WIDE_BASE : Nat := PI_COMMITTED_BASE + PI_COMMITTED_LANES
def PI_WIDE_LANES : Nat := 16
/-- Total PIs: `[nullifier] ++ committedRoot[8] ++ wideCarrier[16]` = 25. -/
def SPEND_PI_COUNT : Nat := PI_WIDE_BASE + PI_WIDE_LANES

/-- The 8 committed-root PI indices (the `.piBinding .last` targets pass 6 pins the fold's last-row
parent to). -/
def piCommitted (i : Fin PI_COMMITTED_LANES) : Nat := PI_COMMITTED_BASE + i.val
/-- The 16 wide-carrier PI indices. -/
def piWide (i : Fin PI_WIDE_LANES) : Nat := PI_WIDE_BASE + i.val

theorem spend_pi_count_val : SPEND_PI_COUNT = 25 := rfl

/-- **The layout is disjoint and exact** — nullifier, then the 8-lane root, then the 16-lane carrier,
back to back with no overlap and no gap. -/
theorem pi_layout_disjoint :
    piNUL < PI_COMMITTED_BASE
    ∧ PI_COMMITTED_BASE + PI_COMMITTED_LANES = PI_WIDE_BASE
    ∧ PI_WIDE_BASE + PI_WIDE_LANES = SPEND_PI_COUNT :=
  ⟨by decide, rfl, rfl⟩

/-- The committed-root pin is 8 lanes — the WIDTH closure of §7 realized at the descriptor PI. -/
theorem committed_root_is_8_lanes : PI_COMMITTED_LANES = 8 := rfl

/-- **⚑ The wide carrier is genuinely WIDE, not the narrow felt relabelled.** 16 lanes ≠ the one felt
`value mod p` the coordinator forbids exposing as a `u64` opening. -/
theorem wide_carrier_is_not_the_narrow_felt : PI_WIDE_LANES ≠ 1 := by decide

/-- **The exposed carrier has exactly the arity of same-opening's `routedJoin` image** (`Wide16`'s
`Fin 16`) — so binding these 16 PI lanes in the spend proof gives the routed join a spend-side carrier
to same-open against, un-fail-closing it. -/
theorem carrier_lanes_match_routedJoin_image :
    PI_WIDE_LANES = Fintype.card (Fin 16) := by
  simp [PI_WIDE_LANES]

/-- **⚑ BOTH CARRIERS IN ONE DESCRIPTOR (`both_carriers_exposed`).** The layout carries the 8-lane
committed root (#15) AND the disjoint 16-lane wide-`u64` carrier (the same-opening join), so one spend
proof un-fail-closes both — the Fork B coupling resolved in a single re-authored descriptor. -/
theorem both_carriers_exposed :
    PI_COMMITTED_LANES = 8 ∧ PI_WIDE_LANES = 16
    ∧ (∀ (i : Fin PI_COMMITTED_LANES) (j : Fin PI_WIDE_LANES), piCommitted i ≠ piWide j) := by
  refine ⟨rfl, rfl, ?_⟩
  intro i j
  have hi : i.val < 8 := i.isLt
  simp only [piCommitted, piWide, PI_COMMITTED_BASE, PI_COMMITTED_LANES, PI_WIDE_BASE]
  omega

#assert_axioms childExpr_pos0
#assert_axioms childExpr_pos1
#assert_axioms childExpr_pos2
#assert_axioms childExpr_pos3
#assert_axioms exactChildren4_lane
#assert_axioms nonbit_forges_child
#assert_axioms pi_layout_disjoint
#assert_axioms wide_carrier_is_not_the_narrow_felt
#assert_axioms carrier_lanes_match_routedJoin_image
#assert_axioms both_carriers_exposed

end Dregg2.Circuit.Emit.ShieldedSpendExactMembershipDescriptor
