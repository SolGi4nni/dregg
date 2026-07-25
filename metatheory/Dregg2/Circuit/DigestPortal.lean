/-
# Dregg2.Circuit.DigestPortal — Wave 4: bridge abstract digest portals to Poseidon2 emit.

Connects the abstract `cellLeafInjective` / `logHashInjective` carriers used in `StateCommit` to the
in-circuit Poseidon2 sponge gadget (`Poseidon2Emit`). The refinement direction composes
`emit_faithful_poseidon2_compress` with `GadgetRefinement`; the CR→injectivity discharges are
`cellLeafInjective_from_poseidon2_cr` and `logHashInjective_from_poseidon2_emit`, from the single
Poseidon2 collision-resistance assumption (`Poseidon2Binding.Poseidon2SpongeCR`).

## ⚑ 2026-07-25 BUNDLE CUTOVER — what this module now claims, honestly

`Poseidon2SpongeCR` and `cellLeafInjective` are PROVABLY FALSE at deployed BabyBear parameters
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`,
`StateCommitFloorRegrounded.cellLeafInjective_false_babyBear`). Three declarations here carried them
and are GONE (§1, §4):

  * `PortalBundle` — a structure whose FIRST FIELD was `cellLeafInjective CH`, hence uninhabitable at
    deployment; plus a `Prop`-as-data field. Zero references outside this file. DELETED with its two
    constructors and `ofPoseidon2CR`; its one real fact survives as `emitted_poseidon2_registered`.
  * `compressNInjective_from_poseidon2_emit` — a floor-to-itself relabel (the two predicates are
    `Iff.rfl`-equal). DELETED; `Poseidon2Binding.compressNInjective_of_poseidon2CR` is the identical
    surviving statement.

The two survivors are TRUE but VACUOUS at deployment (their `LeafRealization`/`LogRealization`
premises are uninhabitable there) and are labelled as such at each declaration; that cutover is a
separate transaction across 8 and 5 files. See `Dregg2.Shielded.RealCrypto` §2.0 for the bundle-family
design decision this file follows.
-/
import Dregg2.Circuit.Poseidon2Emit
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.GadgetRefinement
import Dregg2.Circuit.Refinement
import Dregg2.Crypto.PortalFloor

namespace Dregg2.Circuit.DigestPortal

open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Poseidon2Emit
open Dregg2.Circuit.GadgetRefinement
open Dregg2.Circuit.Refinement (Refines)
open Dregg2.Exec.CircuitEmit
open Dregg2.Crypto.PortalFloor
open Dregg2.Exec (CellId Value Turn)

/-! ## §1 — the emit-registration pin.

⚑ **`PortalBundle` IS DELETED (2026-07-25 bundle cutover).** It was a `structure` whose first field was
`cellLeafInj : cellLeafInjective CH` — a floor `StateCommitFloorRegrounded.cellLeafInjective_false_babyBear`
REFUTES at deployed parameters (a cell's `Value` is infinite; a leaf hash pins it into ONE BabyBear
felt). A structure carrying a FALSE field is UNINHABITABLE, so the bundle and its two constructors
(`ofCellLeafInjective`, `ofPoseidon2Emit`) plus `ofPoseidon2CR` carried no content: nothing outside this
module ever referenced them, no theorem was stated over them, and the only genuine fact they held was
the `rfl` registration pin — kept below, so the deletion gives up nothing.

The bundle's third field also typed a Prop AS DATA (`poseidon2CR : Prop`, set to `False` by
`ofCellLeafInjective`), which is not a carrier of anything at all. Per the `RealCrypto` §2.0 bundle
decision, a bundle gets no Prop field; here the whole bundle was scaffolding, so it is REMOVED rather
than re-shaped. -/

/-- **The emitted sponge descriptor is registered under `poseidon2CompressAirName`** — the pin the
deleted `PortalBundle.emitRegistered` field carried, restated standalone. -/
theorem emitted_poseidon2_registered :
    emittedPoseidon2Compress.name = poseidon2CompressAirName := rfl

/-! ## §2 — refinement composition (proved). -/

/-- **`digest_emit_refines_merkle_portal`** — the emitted sponge step refines to the Merkle
portal; inherited from `Poseidon2Emit.poseidon2_emitted_refines_merkle_portal`. -/
theorem digest_emit_refines_merkle_portal {Digest : Type}
    (compress : Digest → Digest → Digest) :
    Refines (Poseidon2Emit.poseidon2CompressEmittedStep compress)
      (GadgetRefinement.merklePortalStep compress) :=
  poseidon2_emitted_refines_merkle_portal compress

/-! ## §3 — Poseidon2 CR ⇒ the three injectivity portals.

These are PROVED bridges from the SINGLE
Poseidon2 sponge collision-resistance assumption (`Poseidon2Binding.Poseidon2SpongeCR`), composed
with the proved injective serializations, to the abstract injectivity portals the whole
`StateCommit`/`EffectCommit` soundness tower carries. No abstract `ℤ` injectivity is assumed: CR is
the one crypto carrier, and a leaf/log realization (`LeafRealization`/`LogRealization`) supplies the
provably-injective encoder. -/

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR LeafRealization LogRealization
  compressNInjective_of_poseidon2CR cellLeafInjective_of_realization
  logHashInjective_of_realization)

/-- **`cellLeafInjective_from_poseidon2_cr`** (was HOLE W4). Discharge `cellLeafInjective CH` from a
Poseidon2 leaf realization: CR of the shared sponge composed with the injective leaf serialization.
The CR is the SOLE crypto content (carried in `R.spongeCR`); no abstract `ℤ` injectivity is assumed.

⚑ VACUOUS AT DEPLOYED PARAMETERS, and named as such: `LeafRealization` carries
`spongeCR : Poseidon2SpongeCR sponge` as a FIELD, so
`StateCommitFloorRegrounded.leafRealization_uninhabitable_babyBear` proves no deployed `R` exists. See
§4 for why this is kept rather than deleted in this transaction. -/
theorem cellLeafInjective_from_poseidon2_cr {CH : CellId → Value → ℤ} (R : LeafRealization CH) :
    cellLeafInjective CH :=
  cellLeafInjective_of_realization R

/-- **`logHashInjective_from_poseidon2_emit`** (was HOLE W4). Discharge `logHashInjective LH` for the
growing receipt-chain sponge from a Poseidon2 log realization (CR + injective turn-list encoder).

⚑ Same caveat as `cellLeafInjective_from_poseidon2_cr`: `LogRealization` is UNINHABITABLE at deployed
parameters (`StateCommitFloorRegrounded.logRealization_uninhabitable_babyBear`). -/
theorem logHashInjective_from_poseidon2_emit {LH : List Turn → ℤ} (R : LogRealization LH) :
    logHashInjective LH :=
  logHashInjective_of_realization R

/-! ## §4 — what was DELETED here, and what it means for the two survivors above.

⚑ `compressNInjective_from_poseidon2_emit` is DELETED. It was `compressNInjective compressN` from a
`Poseidon2SpongeCR compressN` hypothesis — but those two predicates are DEFINITIONALLY EQUAL
(`Poseidon2Binding.compressNInjective_iff_poseidon2CR` is `Iff.rfl`), so it renamed a refuted floor
into itself and carried a tier-A binder for no content. `Poseidon2Binding.compressNInjective_of_poseidon2CR`
— the identical statement, imported here — survives, so nothing is lost; and the honest, deployed-parameter
form of frame-sponge binding is `Poseidon2Binding.group4Find_spec` (an extractor that HANDS BACK the
colliding pair) rather than either of these. `PortalBundle.ofPoseidon2CR` went with the bundle in §1.

⚑ HONESTY ABOUT THE TWO SURVIVORS: `cellLeafInjective_from_poseidon2_cr` and
`logHashInjective_from_poseidon2_emit` are TRUE theorems that are VACUOUS at deployed parameters —
their `LeafRealization`/`LogRealization` premises are uninhabitable there, proved by
`StateCommitFloorRegrounded.{leafRealization,logRealization}_uninhabitable_babyBear`. They are kept
because the `LeafRealization`/`LogRealization` cutover is a distinct transaction spanning 8 and 5 files
(including `Verify.KeystoneAuditArgusReceipt`, whose `cellLeafInjective`/`logHashInjective` discharges
route through them) and deleting them here without that cutover would delete a discharge whose
replacement is not built. NAMED as the next bundle cutover, not laundered as fine. -/

#assert_axioms digest_emit_refines_merkle_portal
#assert_axioms emitted_poseidon2_registered
#assert_axioms cellLeafInjective_from_poseidon2_cr
#assert_axioms logHashInjective_from_poseidon2_emit

end Dregg2.Circuit.DigestPortal