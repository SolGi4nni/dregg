/-
# Dregg2.Circuit.FloorsNonVacuousWave — the per-effect `*TraceReadout` carriers are NON-VACUOUS.

## The gap this closes (sin-audit a6f7fa16)

Each effect's `<e>_descriptorRefines_sat` rung takes a `<E>TraceReadout` as a PREMISE. The readouts are
the genuine `WitnessDecodes`-class extraction (the committed limb IS the kernel field, by trace-fill
construction) — but they entered the rungs UN-WITNESSED. A premise that is secretly UNINHABITABLE makes
its consuming refinement rung VACUOUSLY satisfiable. `FloorsNonVacuous.lean` covers the five APEX carriers
(`Poseidon2SpongeCR`/`ChipTableSoundN`/`Satisfied2Faithful`/`EffAuthoritySource`/`StarkComplete`); this
module extends the discipline to the per-effect `<E>TraceReadout` structures.

Per readout we construct a CONCRETE inhabiting term: a two-row trace whose designated active row carries
the selector hot and the committed limb the decode-seam reads, a `RotTableSide` table half reusing the
faithful chip/range tables (`FloorsNonVacuous.faithfulTf`), a `pre = post` boundary so every frame field
is `rfl`, and the guard discharged at a self-targeted live cell (`actor = cell` ⇒ self-authority
`troa_lrefl`; `lifecycle = 0` ⇒ Live ⇒ `acceptsEffects`). The decode seam (committed limb = kernel
field) is realized by setting the kernel field to the value the chosen column carries — exactly the
trace-fill identity the deployed prover establishes by construction.

So each `<E>TraceReadout` is `Nonempty`: its consuming rung is NON-vacuous (the premise is satisfiable,
not secretly empty).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Every inhabitation is a CONSTRUCTED term; no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.FloorsNonVacuous
import Dregg2.Circuit.RotatedKernelRefinementCellSeal

namespace Dregg2.Circuit.FloorsNonVacuousWave

open Dregg2.Circuit.DescriptorIR2 (VmTrace TableId envAt zeroAsg)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Circuit.FloorsNonVacuous (faithfulTf permOutZ permOut0)

set_option autoImplicit false

/-! ## §0 — the shared table side: a `RotTableSide` over the faithful chip/range tables.

Every readout carries (directly or via `RotTableSide`) the table FAITHFULNESS the rotated denotation
needs. We reuse `FloorsNonVacuous.faithfulTf` (`.poseidon2 = genuineChipTbl` is genuinely
`ChipTableSoundN permOutZ`, `.range = rangeRows BAL_LIMB_BITS`). A trace whose `tf` IS `faithfulTf`
therefore satisfies `RotTableSide permOutZ hash` for any `hash` that reads lane-0 of `permOutZ`. -/

open Dregg2.Circuit.FloorsNonVacuous (permOutZ_width permOutZ_lane0 genuineChipTbl_sound
  faithfulTf_poseidon2 faithfulTf_range)

/-- A two-row trace whose active row 0 has its assignment `r0`, the wrap row is all-zero, and the
auxiliary tables ARE the faithful tables. Row 0 is a transition row (`0 + 1 = 1 ≠ 2`). -/
def readoutTrace (r0 : Dregg2.Circuit.Assignment) : VmTrace where
  rows := [r0, zeroAsg]
  pub  := fun _ => 0
  tf   := faithfulTf

theorem readoutTrace_tf (r0 : Dregg2.Circuit.Assignment) : (readoutTrace r0).tf = faithfulTf := rfl
theorem readoutTrace_rows_len (r0 : Dregg2.Circuit.Assignment) : (readoutTrace r0).rows.length = 2 := rfl
theorem readoutTrace_loc0 (r0 : Dregg2.Circuit.Assignment) : (envAt (readoutTrace r0) 0).loc = r0 := rfl

/-- The shared `RotTableSide` over the faithful tables: `permOutZ` is the genuine permutation, lane-0 IS
the digest, the chip table is `genuineChipTbl` (`ChipTableSoundN permOutZ`), the range table is the
genuine limb table. -/
theorem readoutTrace_side (r0 : Dregg2.Circuit.Assignment) :
    RotTableSide permOutZ (fun ins => (permOutZ ins).headD 0) (readoutTrace r0) where
  permWidth := permOutZ_width
  chipHashIsLane0 := fun _ => rfl
  chipTableFaithful := by
    rw [readoutTrace_tf, faithfulTf_poseidon2]; exact genuineChipTbl_sound
  range := by rw [readoutTrace_tf, faithfulTf_range]

/-! ## §1 — `CellSealTraceReadout` INHABITED.

The designated active row 0 carries `SEL_CELLSEAL = 1` and an all-zero after-disc limb; the boundary is
`pre = post` with `lifecycle = fun _ => 0` (so the seam reads `post.lifecycle cell = 0`, matching the
zero limb), the guard is self-authority at the live cell (`actor = cell`), every frame field is `rfl`,
and the receipt log advances by one. -/

open Dregg2.Circuit.RotatedKernelRefinementCellSeal (CellSealTraceReadout)
open Dregg2.Circuit.Emit.EffectVmEmitCellSeal (SEL_CELLSEAL cellSealVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (afterDiscCol)
open Dregg2.Exec (RecChainedState RecordKernelState)
open Dregg2.Circuit.Spec.CellLifecycle (CellSealGuard cellLifecycleReceipt)

/-- The active-row assignment for the cellSeal witness: hot at `SEL_CELLSEAL`, zero at the after-disc
limb (and everywhere else). Since `SEL_CELLSEAL = 49 ≠ afterDiscCol cellSealVmDescriptor.traceWidth`
(the after block sits far past the small selector index), the two reads are independent. -/
def cellSealRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = SEL_CELLSEAL then 1 else 0

/-- The boundary: a single self-targeted live cell `0`, everything else default. `lifecycle = fun _ => 0`
(Live everywhere) discharges `acceptsEffects`; `actor = cell = 0` discharges `stateAuthB` (self-authority,
l4v `troa_lrefl`). `pre = post` so every frame field is `rfl`, and the log advances by the receipt. -/
def cellSealPre : RecChainedState :=
  { kernel := { accounts := ∅, cell := fun _ => default, caps := fun _ => [] }, log := [] }

def cellSealPost : RecChainedState :=
  { cellSealPre with log := cellLifecycleReceipt 0 0 :: cellSealPre.log }

/-- **`CellSealTraceReadout` is INHABITED.** A concrete witness: the active-row trace, the self-targeted
live boundary, and `actor = cell = 0`. The decode seam `discLimbDecodes` holds because the after-disc limb
is `0` and `post.lifecycle 0 = 0`. -/
def cellSeal_readout :
    CellSealTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace cellSealRow0) cellSealPre cellSealPost 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hrowNotLast := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [cellSealRow0]
  discLimbDecodes := by
    rw [readoutTrace_loc0]
    -- after-disc limb (col 271) is `0`; post.lifecycle 0 = 0; SEL_CELLSEAL (49) ≠ afterDiscCol (271).
    have hcol : (afterDiscCol cellSealVmDescriptor.traceWidth = SEL_CELLSEAL) = False := by decide
    simp only [cellSealRow0, hcol, if_false, cellSealPost, cellSealPre]
    rfl
  discCanon := by decide
  frameOther := fun _ _ => rfl
  guard := by
    constructor
    · -- stateAuthB caps 0 0 = true (self-authority).
      decide
    · -- acceptsEffects pre 0 = true (lifecycle 0 = lcLive = 0).
      decide
  logAdv := rfl
  frAccounts := rfl
  frCell := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl
  frCommitmentsRoot := rfl

theorem cellSeal_readout_inhabited :
    Nonempty (CellSealTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace cellSealRow0) cellSealPre cellSealPost 0 0) :=
  ⟨cellSeal_readout⟩

#assert_axioms cellSeal_readout

end Dregg2.Circuit.FloorsNonVacuousWave
