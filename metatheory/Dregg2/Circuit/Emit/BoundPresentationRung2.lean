/-
# Dregg2.Circuit.Emit.BoundPresentationRung2 — the RUNG-2 no-forgery discharge for the
bound-presentation descriptor (`BoundPresentationEmit.boundPresentationDesc`).

## What this file proves (the load-bearing anti-forgery gate)

The Golden-Lift soundness fix makes the presentation's authorization commitments genuinely
CONSTRAINED public inputs. This file exhibits CONCRETE forge traces proving each binding BITES —
a prover cannot expose a public input that disagrees with the committed witness, and cannot exhibit
a presentation tag that is not the genuine Poseidon2 image of its preimage:

* `forge_action_rejected` — a trace whose `action_binding` witness column (col 1) is forged AWAY
  from the committed public action is NOT `Satisfied2`: the summary PiBinding forces
  `loc[1] = pub[1]`, i.e. `777 = 1`, which fails. (The `carried-but-not-constrained` class the audit
  flagged: here it genuinely constrains.)
* `forge_facts_rejected` — likewise for the `revealed_facts` commitment (col 11): a forged fact
  column is rejected because the facts PiBinding forces `loc[11] = pub[11]`, i.e. `888 = 11`.
* `forge_tag_rejected` — **THE TAG-BINDING TOOTH.** A trace with a forged presentation tag
  (`tag = 999`, published as PI `999` so the copy pin still holds) is NOT `Satisfied2`: the tag chip
  lookup demands the tuple with out0 = `999` be a row of the sound Poseidon2 table, but the only
  genuine row carries out0 = `Poseidon2[final_root, randomness, nonce, DSK] = 1067461553`. A tag that
  is not the real hash of its preimage has no serving chip row → UNSAT. This is exactly the binding
  the deployed descriptor left to an off-circuit STARK leaf, now internal and light-client-visible.

* Non-vacuity TRUE pole: `honest_satisfied2` shows the honest trace IS `Satisfied2`, and
  `honest_fires` fires the whole-descriptor bridge on it, deriving the genuine `BoundPresentation`
  relation. So the descriptor ACCEPTS the honest presentation and REJECTS each forgery — both poles.

`forge_action_was_rejected` / `forge_facts_was_rejected` / `forge_tag_was_rejected` package each
forgery with the honest-acceptance witness.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The sole cryptographic carrier is the
NAMED chip-table faithfulness `ChipTableSound hash (t.tf .poseidon2)`, never a Lean axiom. NEW file;
all imports read-only.
-/
import Dregg2.Circuit.Emit.BoundPresentationRefine

namespace Dregg2.Circuit.Emit.BoundPresentationRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace TableId envAt Lookup
   ChipTableSound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES memLog mapLog memCheck_nil)
open Dregg2.Circuit.Emit.BoundPresentationEmit
  (boundPresentationDesc summaryPins noncePin tagLookup
   REQUEST_PREDICATE_BASE PRESENTATION_TAG REVEALED_FACTS_BASE SUMMARY_WIDTH
   FINAL_ROOT RANDOMNESS VERIFIER_NONCE TAG_LANES PI_NONCE PRESENTATION_TAG_DSK)
open Dregg2.Circuit.Emit.BoundPresentationRefine
  (BoundPresentation boundPresentation_sat_refines firstPiG summaryPin_mem tagSound)

set_option autoImplicit false

/-! ## §0 — membership tactic + the concrete honest world. -/

/-- Membership of the non-summary constraints in the descriptor. -/
local macro "bp_mem" : tactic =>
  `(tactic| (show _ ∈ boundPresentationDesc.constraints;
             simp [boundPresentationDesc, noncePin, tagLookup]))

/-- The order-sensitive little-endian digit hash — `[a,b,c,d] ↦ ((a·100+b)·100+c)·100+d`. -/
private def fHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- The genuine tag of the honest preimage `[1,2,3,DSK]`: `1020300 + 1066441253 = 1067461553`. -/
private def genuineTag : ℤ := 1067461553

/-- The honest height-1 row: summary cols `0..18` carry their index (tag col 10 = the genuine tag),
hidden `final_root = 1`, `randomness = 2`, `verifier_nonce = 3`, lanes `0`. -/
private def honestRow : Assignment := fun c =>
  if c = PRESENTATION_TAG then genuineTag
  else if c = FINAL_ROOT then 1
  else if c = RANDOMNESS then 2
  else if c = VERIFIER_NONCE then 3
  else if c < SUMMARY_WIDTH then (c : ℤ)
  else 0

/-- The honest public inputs: summary PIs `0..18` mirror the row, the nonce PI (19) is `3`. -/
private def honestPub : Assignment := fun k =>
  if k = PRESENTATION_TAG then genuineTag
  else if k = PI_NONCE then 3
  else if k < SUMMARY_WIDTH then (k : ℤ)
  else 0

/-- The sound chip table: the one genuine `[final_root, randomness, nonce, DSK] → tag` row. -/
private def honestTbl : List (List ℤ) :=
  [chipRow fHash [1, 2, 3, PRESENTATION_TAG_DSK] (List.replicate 7 0)]

private def honestTrace : VmTrace :=
  { rows := [honestRow], pub := honestPub
    tf := fun tid => match tid with | .poseidon2 => honestTbl | _ => [] }

/-- The honest chip table is genuinely SOUND (its one row is a real `chipRow fHash`). -/
theorem honest_chipSound : ChipTableSound fHash (honestTrace.tf .poseidon2) := by
  intro r hr
  simp only [honestTrace, honestTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  exact ⟨[1, 2, 3, PRESENTATION_TAG_DSK], List.replicate 7 0, by decide, by decide, hr⟩

/-- **NON-VACUITY (TRUE pole): the honest trace IS `Satisfied2`.** The 19 summary pins close, the
nonce pin closes, and the tag chip lookup lands on the genuine row. So the descriptor does NOT
over-constrain: an honest presentation is accepted. -/
theorem honest_satisfied2 :
    Satisfied2 fHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] honestTrace := by
  have hmemlog : memLog boundPresentationDesc honestTrace = [] := rfl
  have hmaplog : mapLog boundPresentationDesc honestTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show honestTrace.rows.length = 1 from rfl] at hi
    interval_cases i
    rw [show boundPresentationDesc.constraints
          = summaryPins ++ [noncePin, tagLookup] from rfl] at hc
    rcases List.mem_append.mp hc with hsum | hextra
    · simp only [summaryPins, List.mem_map, List.mem_range] at hsum
      obtain ⟨k, hk, rfl⟩ := hsum
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
      intro _
      have hk19 : k < 19 := hk
      simp only [envAt, honestTrace, List.getD_cons_zero]
      interval_cases k <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hextra
      rcases hextra with rfl | rfl
      · simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, noncePin]
        intro _; decide
      · simp only [VmConstraint2.holdsAt, Lookup.holdsAt, tagLookup]
        decide
  · intro i _; trivial
  · intro i _ r hr; simp [boundPresentationDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **The whole-descriptor bridge FIRES on the honest trace** — the genuine `BoundPresentation`
relation is DERIVED (SAT ⟹ SEM, non-vacuously). -/
theorem honest_fires : BoundPresentation fHash (envAt honestTrace 0).loc honestTrace.pub :=
  boundPresentation_sat_refines (by decide) honest_satisfied2 honest_chipSound

/-! ## §1 — forge (a): a forged `action_binding` witness column is REJECTED. -/

/-- The action forgery: honest, except the `action_binding` col 1 is forged to `777` (the committed
public action is still `1`). -/
private def forgeActionRow : Assignment := fun c =>
  if c = REQUEST_PREDICATE_BASE then 777 else honestRow c
private def forgeActionTrace : VmTrace := { honestTrace with rows := [forgeActionRow] }

/-- **The forged action is genuinely wrong** — the witness column (`777`) disagrees with the
committed public action (`1`). -/
theorem forge_action_mismatch :
    (envAt forgeActionTrace 0).loc REQUEST_PREDICATE_BASE ≠ forgeActionTrace.pub REQUEST_PREDICATE_BASE := by
  simp only [envAt, forgeActionTrace, honestTrace, forgeActionRow, List.getD_cons_zero]; decide

/-- **The action PiBinding BITES.** No `Satisfied2` exists for the forged-action trace: the summary
PiBinding forces `loc[1] = pub[1]`, i.e. `777 = 1`. -/
theorem forge_action_rejected :
    ¬ Satisfied2 fHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeActionTrace := by
  intro h
  have hpin := firstPiG h (by decide) REQUEST_PREDICATE_BASE REQUEST_PREDICATE_BASE
    (summaryPin_mem REQUEST_PREDICATE_BASE (by decide))
  exact forge_action_mismatch hpin

/-! ## §2 — forge (b): a forged `revealed_facts` commitment column is REJECTED. -/

/-- The facts forgery: honest, except the `revealed_facts` col 11 is forged to `888` (committed
public fact still `11`). -/
private def forgeFactsRow : Assignment := fun c =>
  if c = REVEALED_FACTS_BASE then 888 else honestRow c
private def forgeFactsTrace : VmTrace := { honestTrace with rows := [forgeFactsRow] }

/-- **The forged fact is genuinely wrong** — the witness column (`888`) disagrees with the committed
public fact (`11`). -/
theorem forge_facts_mismatch :
    (envAt forgeFactsTrace 0).loc REVEALED_FACTS_BASE ≠ forgeFactsTrace.pub REVEALED_FACTS_BASE := by
  simp only [envAt, forgeFactsTrace, honestTrace, forgeFactsRow, List.getD_cons_zero]; decide

/-- **The facts PiBinding BITES.** No `Satisfied2` exists for the forged-facts trace: the facts
PiBinding forces `loc[11] = pub[11]`, i.e. `888 = 11`. -/
theorem forge_facts_rejected :
    ¬ Satisfied2 fHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeFactsTrace := by
  intro h
  have hpin := firstPiG h (by decide) REVEALED_FACTS_BASE REVEALED_FACTS_BASE
    (summaryPin_mem REVEALED_FACTS_BASE (by decide))
  exact forge_facts_mismatch hpin

/-! ## §3 — forge (c): THE TAG-BINDING TOOTH — a forged tag not equal to Poseidon2 is REJECTED. -/

/-- The tag forgery: honest preimage + genuine chip row, but the tag column AND its PI are forged to
`999`. The copy pin `loc[10] = pub[10]` still holds (`999 = 999`) — the ONLY thing wrong is that
`999` is not the genuine Poseidon2 image, so the tag chip lookup cannot land. -/
private def forgeTagRow : Assignment := fun c => if c = PRESENTATION_TAG then 999 else honestRow c
private def forgeTagPub : Assignment := fun k => if k = PRESENTATION_TAG then 999 else honestPub k
private def forgeTagTrace : VmTrace :=
  { rows := [forgeTagRow], pub := forgeTagPub
    tf := fun tid => match tid with | .poseidon2 => honestTbl | _ => [] }

/-- **The forged tag is genuinely NOT the hash** — `999 ≠ Poseidon2[1,2,3,DSK] = 1067461553`. -/
theorem forge_tag_nonhash : (999 : ℤ) ≠ fHash [1, 2, 3, PRESENTATION_TAG_DSK] := by
  unfold fHash; decide

/-- **THE TAG-BINDING TOOTH BITES.** No `Satisfied2` exists for the forged-tag trace: the tag chip
lookup demands the evaluated tuple (out0 = `999`) be a row of the sound Poseidon2 table, but the only
genuine row carries out0 = `1067461553`. A tag that is not the real Poseidon2 image of
`[final_root, randomness, nonce, DSK]` has no serving chip row → UNSAT. This is the Golden-Lift
binding: the presentation tag is now constrained IN-CIRCUIT, visible to a light client / the fold. -/
theorem forge_tag_rejected :
    ¬ Satisfied2 fHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeTagTrace := by
  intro h
  have hc := h.rowConstraints 0 (by decide) tagLookup (by bp_mem)
  simp only [tagLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at hc
  revert hc
  decide

/-! ## §4 — the forgeries packaged with the honest-acceptance pole. -/

/-- Action forgery closed: rejected under the descriptor, while the honest presentation is accepted. -/
theorem forge_action_was_rejected :
    ¬ Satisfied2 fHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeActionTrace
      ∧ Satisfied2 fHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] honestTrace :=
  ⟨forge_action_rejected, honest_satisfied2⟩

/-- Facts forgery closed. -/
theorem forge_facts_was_rejected :
    ¬ Satisfied2 fHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeFactsTrace
      ∧ Satisfied2 fHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] honestTrace :=
  ⟨forge_facts_rejected, honest_satisfied2⟩

/-- Tag forgery closed (the load-bearing tooth). -/
theorem forge_tag_was_rejected :
    ¬ Satisfied2 fHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeTagTrace
      ∧ Satisfied2 fHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] honestTrace :=
  ⟨forge_tag_rejected, honest_satisfied2⟩

/-! ## §5 — shape pins + axiom hygiene. -/

#guard decide (honestTrace.rows.length = 1)
#guard decide (fHash [1, 2, 3, PRESENTATION_TAG_DSK] = genuineTag)
#guard decide (fHash [1, 2, 3, PRESENTATION_TAG_DSK] ≠ 999)

#assert_axioms honest_chipSound
#assert_axioms honest_satisfied2
#assert_axioms honest_fires
#assert_axioms forge_action_mismatch
#assert_axioms forge_action_rejected
#assert_axioms forge_facts_mismatch
#assert_axioms forge_facts_rejected
#assert_axioms forge_tag_nonhash
#assert_axioms forge_tag_rejected
#assert_axioms forge_action_was_rejected
#assert_axioms forge_facts_was_rejected
#assert_axioms forge_tag_was_rejected

end Dregg2.Circuit.Emit.BoundPresentationRung2
