/-
# Dregg2.Circuit.Emit.EffectActionBindingRung2 — the RUNG-2 discharge of the Burn schema's
BALANCE no-forgery on the PUBLIC INPUTS (`burnDesc`), closing the transition-zerofier last-row escape.

## What Rung 1 leaves (`EffectActionBindingRefine.lean`)

The BINDING half of the effect-action family is already CLOSED at Rung 1 as a genuine no-forgery IFF:
`revoke_satisfied2_iff` proves `Satisfied2 ⟺ EffectActionBinds t 10` — the accept-set is EXACTLY the
traces that faithfully carry the published parameter tuple in every row, with NO residual and NO
cryptographic carrier (this family has no hash sites / ranges / map ops, so no Poseidon2 CR ever
enters). Parameter forgery is impossible; that is DONE_AT_RUNG1.

The BURN ARITHMETIC half is NOT yet at no-forgery. `burn_satisfied2_conserves` concludes
`BurnSemantics (envAt t i)` — the u64 balance identity `new + amount = old` — but only about a LOCAL
row environment `envAt t i`, and only on an ACTIVE (non-last) row `i`. That is a residual on two axes:

  1. it speaks about a *local trace row*, not the PUBLISHED balance triple that a verifier actually
     discloses and that an adversary would forge; and
  2. the deployed AIR divides every Burn algebraic gate by the TRANSITION zerofier (`when_transition()`
     in `effect_action_air.rs`, mirrored by `baseGate_holdsAt`: `isLast = false → body = 0`), so the
     LAST row escapes the balance gate entirely — exactly the DFA `hterm` last-row-escape shape.

## What THIS file proves (Rung 2)

`burn_public_conserves`: a trace that `Satisfied2`s the whole `burnDesc` AND has at least one active
row (`2 ≤ t.rows.length`, i.e. row 0 is non-last) has its PUBLISHED balance triple genuinely
conserved: `new_balance + amount = old_balance` over the two u64 limbs, with the `was_burn` disclosure
pinned. The genuine no-forgery statement: a prover CANNOT publish a non-conserving burn and have it
accepted. It composes the whole-descriptor binding bridge (`burn_satisfied2_binds`: every column
0..15 of every row equals the published input) with the whole-descriptor arithmetic bridge
(`burn_satisfied2_conserves` on the active row 0), transporting the local-row identity onto the
PUBLIC inputs.

## Why the anchor is genuinely load-bearing (this is NOT laundering)

Unconditional `Satisfied2 ⟹ BurnPublicSemantics` is FALSE, and provably so. `cheatBurnTrace` is a
SINGLE-row trace whose only row (= the last row) carries a FORGED non-conserving balance
(`new_lo = 601, amount = 400, old = 1000`, so `601 + 400 = 1001 ≠ 1000`) with the `was_burn`
disclosure set honestly. Because the single row is the last row, the balance gate is vacuous (the
transition zerofier divides it out) while the first-row PI pins still force `loc = pub`; so the trace
PROVABLY `Satisfied2`s (`cheatBurnTrace_satisfied2`) yet its PUBLISHED balance is forged
(`cheat_public_forged : ¬ BurnPublicSemantics`). So the `2 ≤ length` (≥ one active row) anchor is a
REAL filter — the conclusion is impossible from `Satisfied2` alone.

## The discharged residual / "carrier"

There is NO cryptographic carrier here — the Burn schema has no hash sites, so no Poseidon2 CR /
`ChipTableSound` enters (unlike the DFA route-commitment anchor). The residual is the STRUCTURAL
transition-zerofier last-row arithmetic escape, discharged by the NAMED hypothesis
`2 ≤ t.rows.length` (an active row exists). Real proofs pad traces to a power-of-two ≥ 2, so the
anchor is deployment-true; the single-row cheat proves it is nonetheless necessary in the statement.

## Axiom hygiene / non-vacuity

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the structural anchor rides as a NAMED
hypothesis, never a Lean axiom. §5 exhibits the concrete satisfying witness `burnTrace` (`600 + 400 =
1000`) on which the Rung-2 conclusion FIRES with the genuine values, and the single-row cheat which
`Satisfied2`s but breaks the anchor. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.EffectActionBindingRefine

namespace Dregg2.Circuit.Emit.EffectActionBindingRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowConstraint WindowExpr Satisfied2 VmTrace TraceFamily
   TableId envAt zeroAsg memOpsOf mapOpsOf memLog mapLog opRow memCheck_nil)
open Dregg2.Circuit.Emit.EffectActionBindingEmit
  (contGate contGates piGate piGates burnDesc burnGates
   cSub0Body cSub1Body cSub2Body cSub3Body cBoolBody
   cWasBurn0Body cWasBurn1Body cWasBurn2Body cWasBurn3Body
   B_OLD0 B_OLD1 B_OLD2 B_OLD3 B_NEW0 B_NEW1 B_NEW2 B_NEW3 B_AMT0 B_AMT1 B_AMT2 B_AMT3
   B_WB0 B_WB1 B_WB2 B_WB3 B_BRW0 B_BRW1 B_BRW2 LIMB_BASE u64Of)
open Dregg2.Circuit.Emit.EffectActionBindingRefine

set_option autoImplicit false

/-! ## §1 — The PUBLIC-INPUT balance-conservation spec (the genuine no-forgery object). -/

/-- **`BurnPublicSemantics t`** — the u64 balance conservation the `Burn` schema asserts of its
PUBLISHED inputs: the COMBINED four-limb identity `new_balance + amount ≡ old_balance` on the
disclosed public columns (`u64Of`, the `2^16`-base recomposition), and the `was_burn` disclosure
pinned across all four of its limbs — all as BabyBear-field congruences (`≡ [ZMOD p]`), the
field-faithful denotation the deployed `assert_zero` gates enforce. The ℤ lift is
`EffectActionBindingRefine.burn_satisfied2_exact`, which takes `BurnLimbsCanonical`; this statement
takes nothing and is therefore stated mod `p`. The three borrows (columns 24, 25, 26) are PRIVATE aux
columns, not public inputs (`piCount = 24`) — and the four chain gates TELESCOPE them away exactly
(weights `1, 2^16, 2^32, 2^48`), which is why a public statement about them is both possible and
borrow-free. -/
def BurnPublicSemantics (t : VmTrace) : Prop :=
  u64Of (t.pub B_NEW0) (t.pub B_NEW1) (t.pub B_NEW2) (t.pub B_NEW3)
      + u64Of (t.pub B_AMT0) (t.pub B_AMT1) (t.pub B_AMT2) (t.pub B_AMT3)
    ≡ u64Of (t.pub B_OLD0) (t.pub B_OLD1) (t.pub B_OLD2) (t.pub B_OLD3) [ZMOD 2013265921]
  ∧ t.pub B_WB0 ≡ 1 [ZMOD 2013265921]
  ∧ t.pub B_WB1 ≡ 0 [ZMOD 2013265921]
  ∧ t.pub B_WB2 ≡ 0 [ZMOD 2013265921]
  ∧ t.pub B_WB3 ≡ 0 [ZMOD 2013265921]

/-! ## §2 — THE RUNG-2 DISCHARGE: a satisfying trace with an active row conserves the PUBLIC balance. -/

/-- **`burn_public_conserves` — the Burn balance no-forgery on the PUBLIC inputs.** A trace that
`Satisfied2`s the whole `burnDesc` and has at least one active row (`2 ≤ t.rows.length`, so row 0 is
non-last) has its PUBLISHED balance triple genuinely conserved. Composes the whole-descriptor binding
bridge (published = every row) with the active-row arithmetic bridge (row 0 conserves), transporting
the local-row identity `burn_satisfied2_conserves` onto the public inputs — the genuine object of
forgery. WITHOUT `2 ≤ length` this is FALSE (§4). -/
theorem burn_public_conserves
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash burnDesc minit mfin maddrs t)
    (hlen : 2 ≤ t.rows.length) :
    BurnPublicSemantics t := by
  have h0pos : 0 < t.rows.length := by omega
  have h0ne : 0 + 1 ≠ t.rows.length := by omega
  -- the active-row chain congruences (local row env at row 0)
  obtain ⟨g0, g1, g2, g3, _, _, _, hw0, hw1, hw2, hw3⟩ :=
    burn_satisfied2_conserves hash minit mfin maddrs t h 0 h0pos h0ne
  -- the whole-descriptor binding: row 0's columns 0..23 are congruent (mod p) to the published inputs
  have hbind := burn_satisfied2_binds hash minit mfin maddrs t h 0 h0pos
  have b : ∀ c, c < 24 → (envAt t 0).loc c ≡ t.pub c [ZMOD 2013265921] := by
    intro c hc
    show (t.rows.getD 0 zeroAsg) c ≡ t.pub c [ZMOD 2013265921]
    exact hbind c hc
  -- TELESCOPE the four chain congruences with weights 1, 2^16, 2^32, 2^48: the three borrow terms
  -- cancel identically, leaving the borrow-free combined identity on the ROW's cells.
  have hrow :
      u64Of ((envAt t 0).loc B_NEW0) ((envAt t 0).loc B_NEW1) ((envAt t 0).loc B_NEW2)
          ((envAt t 0).loc B_NEW3)
        + u64Of ((envAt t 0).loc B_AMT0) ((envAt t 0).loc B_AMT1) ((envAt t 0).loc B_AMT2)
            ((envAt t 0).loc B_AMT3)
      ≡ u64Of ((envAt t 0).loc B_OLD0) ((envAt t 0).loc B_OLD1) ((envAt t 0).loc B_OLD2)
          ((envAt t 0).loc B_OLD3) [ZMOD 2013265921] := by
    rw [Int.modEq_iff_dvd] at g0 g1 g2 g3 ⊢
    obtain ⟨k0, e0⟩ := g0; obtain ⟨k1, e1⟩ := g1
    obtain ⟨k2, e2⟩ := g2; obtain ⟨k3, e3⟩ := g3
    refine ⟨k0 + 65536 * k1 + 4294967296 * k2 + 281474976710656 * k3, ?_⟩
    simp only [u64Of, LIMB_BASE] at *
    omega
  -- transport it onto the PUBLIC inputs by the binding congruence.
  have hpubN :
      u64Of ((envAt t 0).loc B_NEW0) ((envAt t 0).loc B_NEW1) ((envAt t 0).loc B_NEW2)
          ((envAt t 0).loc B_NEW3)
        ≡ u64Of (t.pub B_NEW0) (t.pub B_NEW1) (t.pub B_NEW2) (t.pub B_NEW3)
          [ZMOD 2013265921] :=
    (((b B_NEW0 (by decide)).add ((Int.ModEq.refl 65536).mul (b B_NEW1 (by decide)))).add
      ((Int.ModEq.refl 4294967296).mul (b B_NEW2 (by decide)))).add
      ((Int.ModEq.refl 281474976710656).mul (b B_NEW3 (by decide)))
  have hpubA :
      u64Of ((envAt t 0).loc B_AMT0) ((envAt t 0).loc B_AMT1) ((envAt t 0).loc B_AMT2)
          ((envAt t 0).loc B_AMT3)
        ≡ u64Of (t.pub B_AMT0) (t.pub B_AMT1) (t.pub B_AMT2) (t.pub B_AMT3)
          [ZMOD 2013265921] :=
    (((b B_AMT0 (by decide)).add ((Int.ModEq.refl 65536).mul (b B_AMT1 (by decide)))).add
      ((Int.ModEq.refl 4294967296).mul (b B_AMT2 (by decide)))).add
      ((Int.ModEq.refl 281474976710656).mul (b B_AMT3 (by decide)))
  have hpubO :
      u64Of ((envAt t 0).loc B_OLD0) ((envAt t 0).loc B_OLD1) ((envAt t 0).loc B_OLD2)
          ((envAt t 0).loc B_OLD3)
        ≡ u64Of (t.pub B_OLD0) (t.pub B_OLD1) (t.pub B_OLD2) (t.pub B_OLD3)
          [ZMOD 2013265921] :=
    (((b B_OLD0 (by decide)).add ((Int.ModEq.refl 65536).mul (b B_OLD1 (by decide)))).add
      ((Int.ModEq.refl 4294967296).mul (b B_OLD2 (by decide)))).add
      ((Int.ModEq.refl 281474976710656).mul (b B_OLD3 (by decide)))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hpubN.add hpubA).symm.trans (hrow.trans hpubO)
  · exact (b B_WB0 (by decide)).symm.trans hw0
  · exact (b B_WB1 (by decide)).symm.trans hw1
  · exact (b B_WB2 (by decide)).symm.trans hw2
  · exact (b B_WB3 (by decide)).symm.trans hw3

#assert_axioms burn_public_conserves

/-! ## §3 — Non-vacuity, TRUE half: the Rung-2 conclusion FIRES on a genuine witness.

`burnTrace` (from Rung 1) is a concrete 2-row burn-valid trace (`600 + 400 = 1000`) that `Satisfied2`s
the whole `burnDesc`. It has an active row, so `burn_public_conserves` recovers the PUBLIC balance
conservation with the GENUINE values — not a constant `0 = 0`. -/

/-- **The Rung-2 discharge fires on the genuine witness.** -/
theorem burnTrace_public_conserves : BurnPublicSemantics burnTrace :=
  burn_public_conserves (fun _ => 0) (fun _ => 0) (fun _ => (0, 0)) [] burnTrace
    burnTrace_satisfied2 (by decide)

/-- The recovered values are the genuine burn `old = 65536, new = 65535, amount = 1` — the conserved
identity is `65535 + 1 = 65536`, a real balance ACROSS A LIMB BOUNDARY, not a trivial `0 = 0`. -/
theorem burnTrace_public_value :
    u64Of (burnTrace.pub B_OLD0) (burnTrace.pub B_OLD1) (burnTrace.pub B_OLD2)
        (burnTrace.pub B_OLD3) = 65536
    ∧ u64Of (burnTrace.pub B_NEW0) (burnTrace.pub B_NEW1) (burnTrace.pub B_NEW2)
        (burnTrace.pub B_NEW3) = 65535
    ∧ u64Of (burnTrace.pub B_AMT0) (burnTrace.pub B_AMT1) (burnTrace.pub B_AMT2)
        (burnTrace.pub B_AMT3) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §4 — Non-vacuity, FALSE half: `Satisfied2` alone does NOT force `BurnPublicSemantics`.

The single-row trace `[badBurnRow]` carries a FORGED non-conserving balance (`601 + 400 = 1001 ≠
1000`) with the `was_burn` disclosure set honestly. Its only row IS the last row, so the balance gate
is vacuous (the transition zerofier divides it out), while the first-row PI pins still force
`loc = pub`. The trace PROVABLY `Satisfied2`s, yet its PUBLISHED balance is forged. So the
`2 ≤ length` (≥ one active row) anchor is LOAD-BEARING — the conclusion is impossible from
`Satisfied2` alone. -/

/-- The forged PUBLIC balance: the honest row with `new_0` moved to `1`, so the disclosed
`new + amount = 1 + 1 = 2` does not equal the disclosed `old = 65536`. ⚑ It is a PUBLIC forgery
(`Refine.badBurnRow` forges the PRIVATE borrow instead, which the public statement cannot see). -/
def cheatRow : Assignment := fun c => if c = B_NEW0 then 1 else burnRow c

/-- The single-row cheating trace: the only row (= the last row) carries the forged balance. -/
def cheatBurnTrace : VmTrace := { rows := [cheatRow], pub := cheatRow, tf := fun _ => [] }

/-- **The cheat PROVABLY `Satisfied2`s** — the balance gate is vacuous on the single (= last) row (the
transition zerofier), the first-row PI pins are met because `pub = row`, and continuity is vacuous. -/
theorem cheatBurnTrace_satisfied2 :
    Satisfied2 (fun _ => 0) burnDesc (fun _ => 0) (fun _ => (0, 0)) [] cheatBurnTrace := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show burnDesc.constraints = contGates 27 ++ piGates 24 ++ burnGates from rfl] at hc
    have hi1 : i < 1 := hi
    interval_cases i
    rcases List.mem_append.mp hc with hcp | hburn
    · rcases List.mem_append.mp hcp with hcont | hpi
      · obtain ⟨c', _, rfl⟩ := List.mem_map.mp hcont
        rw [contGate_holdsAt]; intro hl; exact absurd hl (by decide)
      · obtain ⟨c', _, rfl⟩ := List.mem_map.mp hpi
        rw [piGate_holdsAt]; intro _
        -- pub = the row itself, so `loc c' ≡ pub c'` is reflexive (both are `badBurnRow c'`).
        rfl
    · fin_cases hburn <;>
        (rw [baseGate_holdsAt]; intro hl; exact absurd hl (by decide))
  · intro i hi; trivial
  · intro i hi r hr; simp only [burnDesc, List.not_mem_nil] at hr
  · intro op hop; rw [burn_memLog cheatBurnTrace] at hop; simp at hop
  · rw [burn_memLog cheatBurnTrace]; exact (by decide)
  · rw [burn_memLog cheatBurnTrace]; exact memCheck_nil _ _
  · have hm : cheatBurnTrace.tf TableId.memory = [] := rfl
    simp [hm, burn_memLog]
  · have hmp : cheatBurnTrace.tf TableId.mapOps = [] := rfl
    simp [hmp, burn_mapLog]

/-- **The cheat's PUBLISHED balance is forged.** `1 + 1 = 2 ≠ 65536` — the disclosed balance does
NOT conserve, so no `Satisfied2`-only theorem could conclude `BurnPublicSemantics`. -/
theorem cheat_public_forged : ¬ BurnPublicSemantics cheatBurnTrace := by
  intro h
  -- the forged published balance `601 + 400 = 1001 ≢ 1000 [ZMOD p]` (differs by 1, and `p ∤ 1`).
  exact absurd h.1 (by decide)

/-! ### Shape pins. -/

#guard decide (cheatBurnTrace.rows.length = 1)
#guard decide (burnTrace.rows.length = 2)

#assert_axioms burnTrace_public_conserves
#assert_axioms burnTrace_public_value
#assert_axioms cheatBurnTrace_satisfied2
#assert_axioms cheat_public_forged

end Dregg2.Circuit.Emit.EffectActionBindingRung2
