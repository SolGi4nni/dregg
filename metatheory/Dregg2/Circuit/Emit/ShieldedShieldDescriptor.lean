/-
# Dregg2.Circuit.Emit.ShieldedShieldDescriptor — the Lean-authored SHIELD-OPENING descriptor
(`dregg-shielded-shield::v1`): the on-ramp keystone that binds the minted note commitment to the
executor-debited PUBLIC value (Fork B on-ramp, pass A — the AIR that makes `Effect::Shield`'s append
SOUND).

**This is Lean-authored AIR.** Rust parses the emitted golden and supplies witnesses; it authors no
constraint. Per `docs/DESIGN-shielded-value-on-ramp.md §2.4` — and its non-negotiable "reuse the
existing shape verbatim, do not author a second note-commitment relation" — this descriptor's C6
opening is the SAME `hash_fact(value,[asset,owner,randomness])` relation the spend side opens
(`ShieldedSpendDescriptor.factIns`, `ShieldedSpendPortDischarge.OpensAs`/`IsCommittedNote`).

## Why this is the on-ramp keystone
`ShieldedOnRampPin §2` proves the deployed GATE-4 append is UNSOUND because it appends the prover's
wire bytes (a Pedersen point), so `deployed_append_is_free` and pinning against it RELOCATES #15
(`l4_pin_over_deployed_append_relocates_15`). §3 proves the fix: append `noteLeaf hash n` for a
preimage the boundary AUTHORIZED, and the pin CLOSES #15 (`shieldA_pin_closes_15`). The missing link
is: what forces the appended commitment to be the note commitment of the value the executor debits?
THIS descriptor. Its `Satisfied2` forces `piCM = hash_fact(cVAL,[cASSET,cOWNER,cRAND])` AND `cVAL ≡
piVALUE` (public) — so the minted leaf is the note commitment of the PUBLIC (debited) value. The
executor debits `value` from a clear-ledger cell the caller owns, verifies THIS proof, and appends
`piCM`; `shieldAppend_is_ledger_note` then fires by construction.

## What is proved
* `shield_opening_binds_public_value` — under a sound chip table, a satisfying trace forces the minted
  `cCM` to be `hash_fact(cVAL,[cASSET,cOWNER,cRAND])` AND the value/asset cells ≡ the PUBLIC PIs.
* `shield_mints_the_object_the_spend_opens` — the minted `piCM` is `OpensAs` the row's opening cells,
  i.e. exactly the object `ShieldedSpendPortDischarge` proves the spend side opens (one object, per §2.4).
* `shield_value_decouple_unsat` (THE REFUTATION) — a trace whose value cell decouples (mod p) from the
  public `piVALUE` is UNSAT: a prover cannot mint a note for a value different from the one the
  executor debits. Mint-a-note-worth-more is unrepresentable.
* `zero_witness_satisfies` — the constraint system is INHABITED, so the UNSAT tooth is not vacuous.

## Scope (honest) — named residuals
PIs here are `(piVALUE, piASSET, piCM)` — the C6 opening + public-value tie (DESIGN §2.4 blocks 1, 3).
The APPEND grow-gate (DESIGN §2.4 block 2, `piROOT_AFTER = append_at_free_index(piROOT_BEFORE, piCM)`,
`piROOT_BEFORE` executor-sourced) is the in-AIR light-client witness — a NAMED residual (the L2
grow-gate over `ShieldedWholeNoteSwapSubstrateDescriptor`), exactly as the deployed shielded transfer
names its light-client residual. For the deployed on-ramp's SOUNDNESS the executor computes the append
(state maintenance, `exact_linked_append_root8`) and this C6-opening proof is what authorizes the
minted leaf. The note-commitment is the deployed 1-felt (~31-bit) encoding — the felt-width widening
is the same separate campaign item as the spend side, not smuggled in here. Amount is PUBLIC at entry
(Shield-A); amount-hidden entry (Shield-B) is a NAMED residual, never routed over an identity carrier.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Circuit.Emit.ShieldedSpendDescriptor
import Dregg2.Circuit.ShieldedSpendPortDischarge

namespace Dregg2.Circuit.Emit.ShieldedShieldDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace zeroAsg envAt Satisfied2
   chipLookupTupleNarrow poseidon2narrow ChipTableSound emitVmJson2 memLog mapLog)
open Dregg2.Circuit.ChipNarrowLookup (narrowTable chip_lookup_narrow_sound_of_wide_table)
open Dregg2.Circuit.Emit.BlindedMembershipEmit (ev ek eadd emul eneg esub)
open Dregg2.Circuit.Emit.ShieldedSpendDescriptor
  (factIns factIns_eval_4 NS_FACT_MARK hzero zChipRow zTf zTrace)
open Dregg2.Circuit.ShieldedSpendPortDischarge (OpensAs)

set_option autoImplicit false

/-! ## §1 — columns and public inputs. -/

/-- Note value (PUBLIC at entry; pinned to `piVALUE`). -/
def cVAL : Nat := 0
/-- Asset type (PUBLIC; pinned to `piASSET`). -/
def cASSET : Nat := 1
/-- Owner (the recipient's; HIDDEN witness). -/
def cOWNER : Nat := 2
/-- Randomness (HIDDEN witness). -/
def cRAND : Nat := 3
/-- The minted note commitment `hash_fact(value,[asset,owner,randomness])` (pinned to `piCM`). -/
def cCM : Nat := 4

def SHIELD_WIDTH : Nat := 5

/-- PI 0: the public value being shielded (the executor debits exactly this from a clear-ledger cell
the caller owns). -/
def piVALUE : Nat := 0
/-- PI 1: the public asset type. -/
def piASSET : Nat := 1
/-- PI 2: the minted note commitment appended to `note_shielded`. -/
def piCM : Nat := 2
def SHIELD_PI_COUNT : Nat := 3

/-! ## §2 — the constraints and the descriptor. -/

/-- C6: the note-commitment recompute — `cCM = hash_fact(cVAL,[cASSET,cOWNER,cRAND])`, the SAME
`hash_fact` site the spend opens (DESIGN §2.4 block 1). -/
def lkCM : VmConstraint2 :=
  .lookup ⟨poseidon2narrow,
    chipLookupTupleNarrow (factIns [cVAL, cASSET, cOWNER, cRAND]) cCM⟩

/-- The full constraint list: C6 opening, plus the public pins (value/asset tie + the published
commitment). The value pin is DESIGN §2.4 block 3 — "it carries the entire conservation content." -/
def shieldConstraints : List VmConstraint2 :=
  [ lkCM
  , .base (.piBinding .first cVAL piVALUE)
  , .base (.piBinding .first cASSET piASSET)
  , .base (.piBinding .first cCM piCM) ]

/-- **`shieldedShieldDesc`** — the Lean-authored shield-opening descriptor. -/
def shieldedShieldDesc : EffectVmDescriptor2 :=
  { name        := "dregg-shielded-shield::v1"
  , traceWidth  := SHIELD_WIDTH
  , piCount     := SHIELD_PI_COUNT
  , tables      := []
  , constraints := shieldConstraints
  , hashSites   := []
  , ranges      := [] }

#guard shieldedShieldDesc.traceWidth == 5
#guard shieldedShieldDesc.piCount == 3
#guard shieldedShieldDesc.constraints.length == 4

/-! ## §3 — the opening binds the public value. -/

private theorem modeq_of_sub {x y : ℤ} (h : x + -1 * y ≡ 0 [ZMOD 2013265921]) :
    x ≡ y [ZMOD 2013265921] := by
  have hd := Int.modEq_iff_dvd.mp h
  have he : (0 : ℤ) - (x + -1 * y) = y - x := by ring
  rw [he] at hd
  exact Int.modEq_iff_dvd.mpr hd

/-- **⚑ THE KEYSTONE (`shield_opening_binds_public_value`).** Under a sound chip table, a satisfying
trace forces: (i) the minted `cCM` IS `hash_fact(cVAL,[cASSET,cOWNER,cRAND])` — the note commitment of
the row's opening cells; and (ii) the value/asset cells ≡ the PUBLIC `piVALUE`/`piASSET`, and `cCM ≡
piCM`. So the published commitment is the note commitment of the PUBLIC (executor-debited) value. -/
theorem shield_opening_binds_public_value (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedShieldDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2)) :
    let a := t.rows.getD 0 zeroAsg
    a cCM = hash [a cVAL, a cASSET, a cOWNER, a cRAND, 0, NS_FACT_MARK, 1]
    ∧ (a cVAL ≡ t.pub piVALUE [ZMOD 2013265921])
    ∧ (a cASSET ≡ t.pub piASSET [ZMOD 2013265921])
    ∧ (a cCM ≡ t.pub piCM [ZMOD 2013265921]) := by
  intro a
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons x l => simp
  have hkC := hsat.rowConstraints 0 hpos lkCM (by simp [shieldedShieldDesc, shieldConstraints])
  simp only [lkCM, Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] at hkC
  rw [hwire] at hkC
  have hlenC : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted
      (factIns [cVAL, cASSET, cOWNER, cRAND]).length := by chip_arity_admitted
  have eC := chip_lookup_narrow_sound_of_wide_table hash (t.tf TableId.poseidon2) hChip
    ((envAt t 0).loc) _ cCM hlenC hkC
  rw [factIns_eval_4] at eC
  have hpv := hsat.rowConstraints 0 hpos (.base (.piBinding .first cVAL piVALUE))
    (by simp [shieldedShieldDesc, shieldConstraints])
  have hpa := hsat.rowConstraints 0 hpos (.base (.piBinding .first cASSET piASSET))
    (by simp [shieldedShieldDesc, shieldConstraints])
  have hpc := hsat.rowConstraints 0 hpos (.base (.piBinding .first cCM piCM))
    (by simp [shieldedShieldDesc, shieldConstraints])
  simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at hpv hpa hpc
  exact ⟨eC, hpv rfl, hpa rfl, hpc rfl⟩

/-- **`shield_mints_the_object_the_spend_opens`.** The minted `piCM` is `OpensAs` the row's opening
cells — exactly the object `ShieldedSpendPortDischarge` proves the spend side opens (one object, two
gates: mint and spend, DESIGN §2.4's "do not author a second note-commitment relation"). -/
theorem shield_mints_the_object_the_spend_opens (hash : List ℤ → ℤ) (minit : ℤ → ℤ)
    (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedShieldDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2)) :
    OpensAs hash (t.pub piCM) (t.rows.getD 0 zeroAsg cVAL) (t.rows.getD 0 zeroAsg cASSET)
      (t.rows.getD 0 zeroAsg cOWNER) (t.rows.getD 0 zeroAsg cRAND) := by
  obtain ⟨hcm, _, _, hpc⟩ := shield_opening_binds_public_value hash minit mfin maddrs t hne hsat hChip hwire
  have : t.pub piCM ≡ t.rows.getD 0 zeroAsg cCM [ZMOD 2013265921] := hpc.symm
  rw [hcm] at this
  exact this

/-! ## §4 — THE REFUTATION: a value-decoupled mint is UNSAT. -/

/-- **⚑ THE REFUTATION (`shield_value_decouple_unsat`).** A trace whose value cell decouples (mod p)
from the PUBLIC `piVALUE` does not satisfy the descriptor: the `.piBinding .first cVAL piVALUE` pin
forces them equal. So a prover CANNOT mint a note whose value differs from the one the executor
debits — mint-worth-more is unrepresentable. (The value cell is the same cell C6 hashes into `cCM`,
so this pins the MINTED note's value, not a free label.) -/
theorem shield_value_decouple_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hforge : ¬ (t.rows.getD 0 zeroAsg cVAL ≡ t.pub piVALUE [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedShieldDesc minit mfin maddrs t := by
  intro hsat
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons x l => simp
  have hpv := hsat.rowConstraints 0 hpos (.base (.piBinding .first cVAL piVALUE))
    (by simp [shieldedShieldDesc, shieldConstraints])
  simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at hpv
  exact hforge (hpv rfl)

/-! ## §5 — non-vacuity: the all-zero witness satisfies. -/

/-- **The descriptor is SATISFIABLE** (the all-zero trace, reusing the spend descriptor's chip-table
witness), so the refutation tooth is not vacuously true of an empty relation. -/
theorem zero_witness_satisfies :
    Satisfied2 hzero shieldedShieldDesc (fun _ => 0) (fun _ => (0, 0)) [] zTrace := by
  have hmemlog : memLog shieldedShieldDesc zTrace = [] := rfl
  have hmaplog : mapLog shieldedShieldDesc zTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hi0 : i = 0 := by
      have : i < 1 := by simpa [zTrace] using hi
      omega
    subst hi0
    simp only [shieldedShieldDesc, shieldConstraints, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals
      simp only [lkCM, Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
        Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt,
        Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt, zTrace, zTf]
    all_goals trivial
  · intro i _; exact trivial
  · intro i _ r hr; simp [shieldedShieldDesc] at hr
  · simp
  · intro op hop; rw [hmemlog] at hop; cases hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; rfl
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-! ## §5.1 — the byte-pinned wire golden (`emitVmJson2 shieldedShieldDesc`). Rust reads this raw
string at the `Effect::Shield` verifier step (the `wide_value_binding.rs` pattern: `include_str!` +
split the `def … : String := r#"…"#` golden + `parse_vm_descriptor2` + verify through
`Plonky3HidingFriReference`). -/

def SHIELDED_SHIELD_GOLDEN : String := r#"{"name":"dregg-shielded-shield::v1","ir":2,"trace_width":5,"public_input_count":3,"challenges":0,"tables":[],"constraints":[{"t":"lookup","table":8,"tuple":[{"t":"const","v":7},{"t":"var","v":0},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":3},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":4}]},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":4,"pi_index":2}],"hash_sites":[],"ranges":[]}"#

#guard emitVmJson2 shieldedShieldDesc == SHIELDED_SHIELD_GOLDEN

/-! ## §6 — axiom hygiene. -/

#assert_axioms shield_opening_binds_public_value
#assert_axioms shield_mints_the_object_the_spend_opens
#assert_axioms shield_value_decouple_unsat
#assert_axioms zero_witness_satisfies

end Dregg2.Circuit.Emit.ShieldedShieldDescriptor
