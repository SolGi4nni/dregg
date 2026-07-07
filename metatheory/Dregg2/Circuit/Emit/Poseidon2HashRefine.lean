/-
# Dregg2.Circuit.Emit.Poseidon2HashRefine — the RUNG-1 functional-correctness refinement for the
emitted arity-2 Poseidon2-hash descriptor (`poseidon2HashDesc`).

## What this file IS

`Poseidon2HashEmit.lean` byte-pins the descriptor and proves the PER-GATE hash-binding lemma
`digest_forced` (against a sound chip table, the emitted chip lookup FORCES the digest column to carry
`hash [IN0, IN1]`). This file proves the missing WHOLE-DESCRIPTOR bridge: a trace SATISFYING the whole
emitted `poseidon2HashDesc` (via the deployed acceptance predicate `Satisfied2`) computes the GENUINE
semantic relation the `Poseidon2Air` circuit is meant to compute — the published digest `PI[2]` is the
arity-2 Poseidon2 hash of the two published preimage elements `PI[0]`, `PI[1]`.

The semantic model is the abstract Poseidon2 permutation `hash : List ℤ → ℤ`; the NAMED carrier that
binds the emitted lookup to it is the Poseidon2 chip-AIR faithfulness predicate
`DescriptorIR2.ChipTableSound hash (t.tf .poseidon2)` (the same lever `digest_forced` /
`chip_lookup_sound` consume). The functional spec itself, `IsHash2Instance`, is authored here (§1) as
the clean relation `dig = hash [pre0, pre1]`, and the bridge (§5) proves the descriptor's whole
accept-set refines it.

## The bridge composes the whole descriptor, not one gate

`Satisfied2` of `poseidon2HashDesc` supplies, on the first trace row: (a) the chip lookup — the
evaluated tuple is a member of the Poseidon2 chip table, so under the named soundness carrier the
digest column equals `hash` of the two preimage columns (`digest_forced`); and (b) the three boundary
pins — `IN0 = PI[0]`, `IN1 = PI[1]`, `DIGEST = PI[2]`. Composing the four, `PI[2] = hash [PI[0], PI[1]]`
(`poseidon2Hash_refines_computesHash2`, direction SAT_IMPLIES_SEM).

## Non-vacuity

`witTrace` (§6): a concrete 1-row instance — preimage `(5,7)`, digest `99 = hash0 [5,7]` — that
PROVABLY `Satisfied2 poseidon2HashDesc` (`witTrace_satisfies`) against a genuine chip table
(`witTf_chipSound`); feeding it the bridge recovers `PI[2] = 99 = hash0 [5,7]`
(`witTrace_computesHash2`). `badTrace`: the same preimage with the digest column forged to `100`
(and `PI[2]` pinned to the same lie, so the boundary pins pass) PROVABLY fails `Satisfied2`
(`badTrace_not_satisfied`) — a forged digest names no serving chip row, so the lookup tooth rejects it.
And the relation genuinely discriminates (`IsHash2Instance hash0 5 7 99` holds, `… 5 7 100` does not),
so the conclusion is not a constant.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The Poseidon2 CR carrier enters ONLY as the
NAMED hypothesis `ChipTableSound hash (t.tf .poseidon2)` (discharged in the witness by a genuine chip
table), never as an axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.Poseidon2HashEmit

namespace Dregg2.Circuit.Emit.Poseidon2HashRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.Poseidon2HashEmit

set_option autoImplicit false

/-! ## §1 — The GENUINE semantic relation this circuit computes (the functional spec). -/

/-- **`IsHash2Instance hash pre0 pre1 dig`** — the arity-2 Poseidon2-hash IO contract: the published
digest is the hash of the two published preimage elements. This is the relation the `Poseidon2Air` /
`hash_2_to_1` circuit is *meant* to compute; `hash` is the abstract permutation model. -/
def IsHash2Instance (hash : List ℤ → ℤ) (pre0 pre1 dig : ℤ) : Prop :=
  dig = hash [pre0, pre1]

/-- **`ComputesHash2 hash t`** — the relation lifted to the descriptor's public IO layout
(`PI[0] = pre0`, `PI[1] = pre1`, `PI[2] = digest`). -/
def ComputesHash2 (hash : List ℤ → ℤ) (t : VmTrace) : Prop :=
  IsHash2Instance hash (t.pub 0) (t.pub 1) (t.pub 2)

/-! ## §2 — The constraints of `poseidon2HashDesc` we consume are genuinely present. -/

theorem mem_hashLookup : hashLookup ∈ poseidon2HashDesc.constraints := by
  show hashLookup ∈ [hashLookup, in0Pin, in1Pin, digestPin]
  exact List.mem_cons_self

theorem mem_in0Pin : in0Pin ∈ poseidon2HashDesc.constraints := by
  show in0Pin ∈ [hashLookup, in0Pin, in1Pin, digestPin]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem mem_in1Pin : in1Pin ∈ poseidon2HashDesc.constraints := by
  show in1Pin ∈ [hashLookup, in0Pin, in1Pin, digestPin]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem mem_digestPin : digestPin ∈ poseidon2HashDesc.constraints := by
  show digestPin ∈ [hashLookup, in0Pin, in1Pin, digestPin]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-! ## §3 — THE WHOLE-DESCRIPTOR BRIDGE (soundness, SAT_IMPLIES_SEM). -/

/-- **`poseidon2Hash_refines_computesHash2` — the Rung-1 functional-correctness refinement.**

A trace `t` that SATISFIES the emitted descriptor `poseidon2HashDesc` (via the deployed acceptance
predicate `Satisfied2`), is non-empty, and whose Poseidon2 chip table is SOUND (the NAMED carrier
`ChipTableSound hash (t.tf .poseidon2)` — the Poseidon2 chip-AIR faithfulness), computes the genuine
arity-2 hash relation: the published digest `PI[2]` equals `hash [PI[0], PI[1]]`.

This welds the whole `Satisfied2` accept-set to the semantic relation `ComputesHash2`, by composing the
chip lookup (`digest_forced`: digest column = `hash` of the preimage columns) with the three boundary
pins (preimage/digest columns = the exposed public inputs) on the first row. -/
theorem poseidon2Hash_refines_computesHash2 {hash : List ℤ → ℤ} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hSound : ChipTableSound hash (t.tf .poseidon2))
    (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash poseidon2HashDesc minit mfin maddrs t) :
    ComputesHash2 hash t := by
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  -- (a) the chip lookup on row 0 → digest column = hash of the two preimage columns
  have hlk := hsat.rowConstraints 0 hpos hashLookup mem_hashLookup
  have hmem : (chipLookupTuple [.var IN0, .var IN1] DIGEST LANES).map (·.eval (envAt t 0).loc)
      ∈ t.tf .poseidon2 := by
    simpa only [VmConstraint2.holdsAt, hashLookup, Lookup.holdsAt] using hlk
  have hdig : (envAt t 0).loc DIGEST = hash [(envAt t 0).loc IN0, (envAt t 0).loc IN1] :=
    digest_forced hash (t.tf .poseidon2) hSound (envAt t 0).loc hmem
  -- (b) the three boundary pins fire on the first row
  have hin0 := hsat.rowConstraints 0 hpos in0Pin mem_in0Pin
  have hin1 := hsat.rowConstraints 0 hpos in1Pin mem_in1Pin
  have hdg := hsat.rowConstraints 0 hpos digestPin mem_digestPin
  have e_in0 : (envAt t 0).loc IN0 = (envAt t 0).pub 0 :=
    (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) IN0 0).mp hin0
  have e_in1 : (envAt t 0).loc IN1 = (envAt t 0).pub 1 :=
    (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) IN1 1).mp hin1
  have e_dig : (envAt t 0).loc DIGEST = (envAt t 0).pub 2 :=
    (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) DIGEST 2).mp hdg
  -- compose: PI[2] = digest = hash [IN0, IN1] = hash [PI[0], PI[1]]
  show t.pub 2 = hash [t.pub 0, t.pub 1]
  have hpub : ∀ k, (envAt t 0).pub k = t.pub k := fun _ => rfl
  rw [← hpub 2, ← e_dig, hdig, e_in0, e_in1, hpub 0, hpub 1]

/-! ## §4 — the empty memory / map logs of this descriptor (no mem/map ops). -/

theorem memOpsOf_p2 : memOpsOf poseidon2HashDesc = [] := rfl
theorem mapOpsOf_p2 : mapOpsOf poseidon2HashDesc = [] := rfl
theorem memLog_p2 (t : VmTrace) : memLog poseidon2HashDesc t = [] := by
  simp [memLog, memOpsOf_p2]
theorem mapLog_p2 (t : VmTrace) : mapLog poseidon2HashDesc t = [] := by
  simp [mapLog, mapOpsOf_p2]

/-! ## §5 — Non-vacuity: a concrete satisfying witness, a forged run that fails, a discriminating
relation. -/

/-- A row from an explicit column-prefix list (off-the-end = 0). -/
def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0

/-- The abstract hash pinned to the constant `99` — its only role is to be the digest the chip table
serves; any total function works (the descriptor reads the digest through the chip lookup). -/
def hash0 : List ℤ → ℤ := fun _ => 99

/-- The witness row: preimage `(5, 7)`, digest `99 = hash0 [5,7]`, the seven exposed lanes `0`
(main-trace width `HASH_WIDTH = 10`). -/
def wr0 : Assignment := rowOf [5, 7, 99, 0, 0, 0, 0, 0, 0, 0]

/-- The witness public inputs: `PI[0] = 5`, `PI[1] = 7`, `PI[2] = 99` (the exposed preimage + digest). -/
def wpub : Assignment := rowOf [5, 7, 99]

/-- The evaluated chip-lookup tuple of a row (what the lookup asserts is a table member). -/
def chipTupleAt (a : Assignment) : List ℤ :=
  (chipLookupTuple [.var IN0, .var IN1] DIGEST LANES).map (·.eval a)

/-- The witness trace family: the Poseidon2 chip table carries EXACTLY the row's genuine chip tuple
(so the lookup holds); every other table is empty (no mem/map content). -/
def witTf : TraceFamily := fun id =>
  match id with
  | .poseidon2 => [chipTupleAt wr0]
  | _ => []

/-- The concrete 1-row hash witness: preimage `(5,7)` hashing to digest `99`, all through the emitted
descriptor's own lookup + boundary-pin constraints. -/
def witTrace : VmTrace := { rows := [wr0], pub := wpub, tf := witTf }

/-- **The witness's chip table is SOUND** — its single row is the genuine `(arity, padded inputs,
hash inputs :: lanes)` tuple of the permutation at inputs `[5,7]`. This is the NAMED carrier discharged
concretely (no crypto axiom): the row IS a `chipRow`. -/
theorem witTf_chipSound : ChipTableSound hash0 (witTrace.tf .poseidon2) := by
  intro r hr
  simp only [witTrace, witTf, List.mem_singleton] at hr
  subst hr
  exact ⟨[5, 7], List.replicate 7 0, by decide, by decide, by decide⟩

/-- **The witness PROVABLY satisfies the emitted descriptor.** On the (single, first) row: the chip
lookup holds by membership in `witTf`; the three boundary pins hold (`loc = pub` at the pinned
columns); the memory legs are the empty-log balance. -/
theorem witTrace_satisfies :
    Satisfied2 hash0 poseidon2HashDesc (fun _ => 0) (fun _ => (0, 0)) [] witTrace where
  rowConstraints := by
    intro i hi c hc
    have hi1 : i < 1 := hi
    clear hi
    simp only [poseidon2HashDesc] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        hashLookup, in0Pin, in1Pin, digestPin, witTrace] <;>
      decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [poseidon2HashDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_p2] at hop; simp at hop
  memDisciplined := by rw [memLog_p2]; trivial
  memBalanced := by rw [memLog_p2]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_p2]; rfl
  mapTableFaithful := by rw [mapLog_p2]; rfl

/-- **The bridge FIRES on the witness (the true half of non-vacuity).** Feeding the concrete satisfying
trace + its sound chip table to `poseidon2Hash_refines_computesHash2` recovers the genuine relation:
`PI[2] = hash0 [PI[0], PI[1]]`. -/
theorem witTrace_computesHash2 : ComputesHash2 hash0 witTrace :=
  poseidon2Hash_refines_computesHash2 witTf_chipSound (by decide) witTrace_satisfies

/-- The recovered value is the concrete genuine digest `99` over the read preimage `(5, 7)`. -/
theorem witness_value :
    witTrace.pub 2 = 99 ∧ hash0 [witTrace.pub 0, witTrace.pub 1] = 99 ∧
      witTrace.pub 2 = hash0 [witTrace.pub 0, witTrace.pub 1] :=
  ⟨by decide, by decide, witTrace_computesHash2⟩

/-- The forged row: same preimage `(5, 7)` but a LIE in the digest column — `100 ≠ hash0 [5,7] = 99`. -/
def badRow0 : Assignment := rowOf [5, 7, 100, 0, 0, 0, 0, 0, 0, 0]

/-- The forged public inputs pin `PI[2]` to the same lie, so the boundary pins pass — only the chip
lookup bites. -/
def badPub : Assignment := rowOf [5, 7, 100]

/-- The forged trace: the GENUINE chip table (serving only the true digest `99`), the forged row. -/
def badTrace : VmTrace :=
  { rows := [badRow0], pub := badPub,
    tf := fun id => match id with
      | .poseidon2 => [chipTupleAt wr0]
      | _ => [] }

/-- **A FORGED digest PROVABLY fails the hypothesis (the false half of non-vacuity).** The row-0 chip
lookup forces the evaluated tuple (digest column `100`) into the genuine chip table (which serves only
the tuple with digest `99`), an impossibility — so no `Satisfied2` witness exists. The chip lookup
tooth rejects a forged digest. -/
theorem badTrace_not_satisfied :
    ¬ Satisfied2 hash0 poseidon2HashDesc (fun _ => 0) (fun _ => (0, 0)) [] badTrace := by
  intro h
  have hpos : (0 : Nat) < badTrace.rows.length := by decide
  have hlk := h.rowConstraints 0 hpos hashLookup mem_hashLookup
  revert hlk
  simp only [VmConstraint2.holdsAt, hashLookup, Lookup.holdsAt, badTrace]
  decide

/-- The relation genuinely discriminates: `dig = 99` is the true instance at preimage `(5,7)`,
`dig = 100` is a false one — so the bridge's conclusion is not a constant. -/
theorem hash2_relation_discriminates :
    IsHash2Instance hash0 5 7 99 ∧ ¬ IsHash2Instance hash0 5 7 100 := by
  refine ⟨?_, ?_⟩
  · show (99 : ℤ) = hash0 [5, 7]; decide
  · show ¬ ((100 : ℤ) = hash0 [5, 7]); decide

/-! ## §6 — Axiom tripwires. -/

#assert_axioms poseidon2Hash_refines_computesHash2
#assert_axioms witTf_chipSound
#assert_axioms witTrace_satisfies
#assert_axioms witTrace_computesHash2
#assert_axioms badTrace_not_satisfied
#assert_axioms hash2_relation_discriminates

end Dregg2.Circuit.Emit.Poseidon2HashRefine
