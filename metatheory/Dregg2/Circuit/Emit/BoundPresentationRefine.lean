/-
# Dregg2.Circuit.Emit.BoundPresentationRefine — the WHOLE-DESCRIPTOR bridge for the bound-presentation
family (`BoundPresentationEmit.boundPresentationDesc`).

## What this file adds over Rung 0

`BoundPresentationEmit` byte-pins the descriptor and proves a shape lemma. What was MISSING: the
WHOLE-DESCRIPTOR bridge — that a trace SATISFYING the descriptor (`Satisfied2`) corresponds to the
GENUINE bound-presentation relation the circuit certifies. This file proves it (SAT ⟹ SEM, the
load-bearing soundness direction).

## The functional spec (`BoundPresentation`, authored here)

`BoundPresentation hash loc pub` is the trace-independent relation the descriptor certifies:
* every one of the 19 summary felts (`federation_root`, the 8 `action_binding` felts, `timestamp`,
  the tag, the 8 `revealed_facts` felts) EQUALS its verified public input — the exposed PIs are the
  committed witness columns (no carried-but-not-asserted felt);
* the `verifier_nonce` column equals its public input;
* the presentation-tag PUBLIC INPUT is a GENUINE Poseidon2 image
  `hash [final_root, presentation_randomness, verifier_nonce, DSK]` — the binding the deployed
  descriptor left to an off-circuit STARK leaf, now internal.

## The bridge (whole descriptor)

`boundPresentation_sat_refines` (SAT_IMPLIES_SEM): a `Satisfied2` of `boundPresentationDesc`, against
the NAMED Poseidon2 chip carrier `ChipTableSound hash (t.tf .poseidon2)`, binds `BoundPresentation`
between the row-0 witness columns and the committed public inputs. It composes ALL constraints: the
19 summary PiBindings, the nonce PI pin, and the tag-binding chip lookup (through
`chip_lookup_sound`). Every constraint the descriptor declares fires on the single deployed summary
row (`0 < height`), so the bound-presentation relation holds even at the height-1 deployed trace.

## Non-vacuity (the anti-scar)

`concrete_sat` builds a CONCRETE height-1 trace + a sound chip table (`concrete_chipSound`) for which
`Satisfied2` holds AND `ChipTableSound` holds — the hypothesis chain is genuinely INHABITED;
`witness_spec` fires the bridge end-to-end, deriving a true nontrivial tag identity. `spec_true` /
`spec_false` show the SPEC separates (a wrong tag is NOT `BoundPresentation`), and
`concrete_fail_tag` exhibits a CONCRETE trace that FAILS `Satisfied2` because the tag chip lookup
BITES. So the target is TRUE and FALSE, never a `P → P` stub.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The sole cryptographic carrier is the
NAMED chip soundness `ChipTableSound hash (t.tf .poseidon2)` (the deployed chip AIR's faithfulness),
never a Lean axiom. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.BoundPresentationEmit

namespace Dregg2.Circuit.Emit.BoundPresentationRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt Lookup TableId
   ChipTableSound chip_lookup_sound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES
   memLog mapLog memCheck_nil)
open Dregg2.Circuit.Emit.BoundPresentationEmit
  (boundPresentationDesc summaryPins noncePin tagLookup
   FEDERATION_ROOT REQUEST_PREDICATE_BASE TIMESTAMP PRESENTATION_TAG REVEALED_FACTS_BASE
   SUMMARY_WIDTH FINAL_ROOT RANDOMNESS VERIFIER_NONCE TAG_LANES BOUND_PRES_WIDTH
   PI_NONCE PI_COUNT PRESENTATION_TAG_DSK)

set_option autoImplicit false

/-! ## §1 — the functional spec (trace-independent). -/

/-- **`BoundPresentation hash loc pub`** — THE FUNCTIONAL SPEC the bound-presentation descriptor
certifies (see the module doc). -/
def BoundPresentation (hash : List ℤ → ℤ) (loc pub : Assignment) : Prop :=
  (∀ i, i < SUMMARY_WIDTH → loc i = pub i)
  ∧ loc VERIFIER_NONCE = pub PI_NONCE
  ∧ pub PRESENTATION_TAG
      = hash [loc FINAL_ROOT, loc RANDOMNESS, loc VERIFIER_NONCE, PRESENTATION_TAG_DSK]

/-! ## §2 — extracting the row facts from `Satisfied2`. -/

/-- Membership tactic for the two non-summary constraints. -/
local macro "bp_mem" : tactic =>
  `(tactic| (show _ ∈ boundPresentationDesc.constraints;
             simp [boundPresentationDesc, noncePin, tagLookup]))

/-- Every summary PiBinding `col i → pi i` (for `i < 19`) is literally in the descriptor. -/
theorem summaryPin_mem (i : Nat) (hi : i < SUMMARY_WIDTH) :
    VmConstraint2.base (.piBinding VmRow.first i i) ∈ boundPresentationDesc.constraints := by
  show _ ∈ summaryPins ++ [noncePin, tagLookup]
  apply List.mem_append_left
  simp only [summaryPins, List.mem_map, List.mem_range]
  exact ⟨i, hi, rfl⟩

/-- A declared first-row PI binding pins `loc[col] = pub[k]` on row 0. -/
theorem firstPiG {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash boundPresentationDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) (col k : Nat)
    (hmem : VmConstraint2.base (.piBinding VmRow.first col k) ∈ boundPresentationDesc.constraints) :
    (envAt t 0).loc col = t.pub k := by
  have h := hsat.rowConstraints 0 hlen _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  exact h (by decide)

/-- **The tag-binding tooth extracted.** Against the NAMED sound chip table, the tag lookup forces
the tag column to be the genuine Poseidon2 image of `[final_root, randomness, verifier_nonce, DSK]`
on row 0. This is where the Poseidon2 CR carrier enters, through `chip_lookup_sound`. -/
theorem tagSound {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash boundPresentationDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) (hlen : 0 < t.rows.length) :
    (envAt t 0).loc PRESENTATION_TAG
      = hash [(envAt t 0).loc FINAL_ROOT, (envAt t 0).loc RANDOMNESS,
              (envAt t 0).loc VERIFIER_NONCE, PRESENTATION_TAG_DSK] := by
  have h := hsat.rowConstraints 0 hlen _ (by bp_mem :
    tagLookup ∈ boundPresentationDesc.constraints)
  simp only [tagLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at h
  have hs := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
    [.var FINAL_ROOT, .var RANDOMNESS, .var VERIFIER_NONCE, .const PRESENTATION_TAG_DSK]
    PRESENTATION_TAG TAG_LANES (by show (4 : Nat) ≤ CHIP_RATE; decide) h
  simpa [EmittedExpr.eval] using hs

/-! ## §3 — the whole-descriptor refinement (SAT_IMPLIES_SEM). -/

/-- **`boundPresentation_sat_refines` — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM).**
A `Satisfied2` of `boundPresentationDesc`, against the NAMED Poseidon2 chip carrier, binds
`BoundPresentation` between the row-0 witness columns and the committed public inputs — for ANY
non-empty trace (including the deployed height-1 summary row). Composes the 19 summary PiBindings,
the nonce pin, and the tag-binding chip lookup. -/
theorem boundPresentation_sat_refines {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash boundPresentationDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) :
    BoundPresentation hash (envAt t 0).loc t.pub := by
  refine ⟨?_, ?_, ?_⟩
  · -- every summary felt equals its PI
    intro i hi
    exact firstPiG hsat hlen i i (summaryPin_mem i hi)
  · -- the nonce column equals its PI
    exact firstPiG hsat hlen VERIFIER_NONCE PI_NONCE (by bp_mem)
  · -- the tag PI is the genuine Poseidon2 image
    have htag := tagSound hsat hChip hlen
    have h10 : (envAt t 0).loc PRESENTATION_TAG = t.pub PRESENTATION_TAG :=
      firstPiG hsat hlen PRESENTATION_TAG PRESENTATION_TAG (summaryPin_mem PRESENTATION_TAG (by decide))
    rw [← h10]; exact htag

/-! ## §4 — non-vacuity of the SPEC + an inhabited satisfying witness (the anti-scar). -/

/-- A concrete little-endian digit hash — `[a,b,c,d] ↦ ((a·100+b)·100+c)·100+d`. -/
private def cHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- The genuine tag for the honest preimage `[1, 2, 3, DSK]`:
`cHash [1,2,3,1066441253] = 1020300 + 1066441253 = 1067461553`. -/
private def cGenuineTag : ℤ := 1067461553

/-- The honest height-1 row: summary cols `0..18` carry their index (tag col 10 = the genuine tag),
hidden `final_root = 1`, `randomness = 2`, `verifier_nonce = 3`, lanes `0`. -/
private def hRow : Assignment := fun c =>
  if c = PRESENTATION_TAG then cGenuineTag
  else if c = FINAL_ROOT then 1
  else if c = RANDOMNESS then 2
  else if c = VERIFIER_NONCE then 3
  else if c < SUMMARY_WIDTH then (c : ℤ)
  else 0

/-- The honest public inputs: summary PIs `0..18` mirror the row, the nonce PI (19) is `3`. -/
private def hPub : Assignment := fun k =>
  if k = PRESENTATION_TAG then cGenuineTag
  else if k = PI_NONCE then 3
  else if k < SUMMARY_WIDTH then (k : ℤ)
  else 0

/-- The chip table: the one genuine `[final_root, randomness, nonce, DSK] → tag` `chipRow`. -/
private def hTbl : List (List ℤ) :=
  [chipRow cHash [1, 2, 3, PRESENTATION_TAG_DSK] (List.replicate 7 0)]

/-- The concrete HEIGHT-1 honest trace (`rows = [hRow]`). -/
private def hTrace : VmTrace :=
  { rows := [hRow], pub := hPub
    tf := fun tid => match tid with | .poseidon2 => hTbl | _ => [] }

/-- **The honest chip table is genuinely SOUND** — its one row is a real `chipRow cHash`, so the
NAMED carrier is realizable, not just assumed. -/
theorem concrete_chipSound : ChipTableSound cHash (hTrace.tf .poseidon2) := by
  intro r hr
  simp only [hTrace, hTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  exact ⟨[1, 2, 3, PRESENTATION_TAG_DSK], List.replicate 7 0, by decide, by decide, hr⟩

/-- **The `Satisfied2` HYPOTHESIS IS INHABITED.** The concrete height-1 trace genuinely satisfies the
whole descriptor: the 19 summary pins close (`loc i = pub i`), the nonce pin closes (`3 = 3`), and the
tag chip lookup lands on the genuine table row. The empty memory / map legs close. -/
theorem concrete_sat :
    Satisfied2 cHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] hTrace := by
  have hmemlog : memLog boundPresentationDesc hTrace = [] := rfl
  have hmaplog : mapLog boundPresentationDesc hTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show hTrace.rows.length = 1 from rfl] at hi
    interval_cases i
    rw [show boundPresentationDesc.constraints
          = summaryPins ++ [noncePin, tagLookup] from rfl] at hc
    rcases List.mem_append.mp hc with hsum | hextra
    · simp only [summaryPins, List.mem_map, List.mem_range] at hsum
      obtain ⟨k, hk, rfl⟩ := hsum
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm]
      intro _
      have hk19 : k < 19 := hk
      simp only [envAt, hTrace, List.getD_cons_zero]
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

/-- **The bridge fires end-to-end on the concrete inhabited witness** (SAT ⟹ SEM, non-vacuously). -/
theorem witness_spec : BoundPresentation cHash (envAt hTrace 0).loc hTrace.pub :=
  boundPresentation_sat_refines (by decide) concrete_sat concrete_chipSound

/-- **Witness TRUE — the spec is INHABITED (closed form).** The tag clause is the concrete, nontrivial
identity `cGenuineTag = cHash [1,2,3,DSK]`. -/
theorem spec_true : BoundPresentation cHash (envAt hTrace 0).loc hTrace.pub := witness_spec

/-- The fired tag identity IS the closed-form true instance. -/
theorem spec_tag_is_closed :
    (envAt hTrace 0).pub PRESENTATION_TAG
      = cHash [(envAt hTrace 0).loc FINAL_ROOT, (envAt hTrace 0).loc RANDOMNESS,
               (envAt hTrace 0).loc VERIFIER_NONCE, PRESENTATION_TAG_DSK] := by
  simp only [envAt, List.getD_cons_zero, hTrace, hRow, hPub]; decide

/-- **Witness FALSE — the spec CONSTRAINS.** The same preimage with a WRONG published tag is NOT
`BoundPresentation`: the tag clause forces the PI to be the genuine hash. A `P → P` bridge could not
separate this. -/
theorem spec_false :
    ¬ BoundPresentation cHash hRow (fun k => if k = PRESENTATION_TAG then 999 else hPub k) := by
  rintro ⟨_, _, htag⟩
  revert htag
  decide

/-! ## §5 — a CONCRETE trace that FAILS `Satisfied2` because the tag tooth BITES. -/

/-- A trace with a FORGED tag: `PRESENTATION_TAG = 999 ≠ cGenuineTag`, PI likewise `999` (so the pin
holds), but the genuine chip row still carries `cGenuineTag` — the lookup cannot land. -/
private def hRowBadTag : Assignment := fun c => if c = PRESENTATION_TAG then 999 else hRow c
private def hPubBadTag : Assignment := fun k => if k = PRESENTATION_TAG then 999 else hPub k
private def hTraceBadTag : VmTrace :=
  { rows := [hRowBadTag], pub := hPubBadTag
    tf := fun tid => match tid with | .poseidon2 => hTbl | _ => [] }

/-- **The descriptor genuinely REJECTS a forged tag (tag chip lookup BITES).** No `Satisfied2` exists
for the forged-tag trace: the tag lookup tuple carries out0 = `999`, but the only sound chip row
carries out0 = `cGenuineTag = 1067461553`, so the evaluated tuple is not a table row. -/
theorem concrete_fail_tag :
    ¬ Satisfied2 cHash boundPresentationDesc (fun _ => 0) (fun _ => (0, 0)) [] hTraceBadTag := by
  intro h
  have hmem : tagLookup ∈ boundPresentationDesc.constraints := by bp_mem
  have hc := h.rowConstraints 0 (by decide) _ hmem
  simp only [tagLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at hc
  revert hc
  decide

/-! ## §6 — shape pins + axiom hygiene. -/

#guard decide (hTrace.rows.length = 1)
#guard decide (cHash [1, 2, 3, PRESENTATION_TAG_DSK] = cGenuineTag)
#guard decide (cHash [1, 2, 3, PRESENTATION_TAG_DSK] ≠ 999)

#assert_axioms summaryPin_mem
#assert_axioms firstPiG
#assert_axioms tagSound
#assert_axioms boundPresentation_sat_refines
#assert_axioms concrete_chipSound
#assert_axioms concrete_sat
#assert_axioms witness_spec
#assert_axioms spec_false
#assert_axioms concrete_fail_tag

end Dregg2.Circuit.Emit.BoundPresentationRefine
