/-
# Dregg2.Circuit.DigestPortal — Wave 4: bridge abstract digest portals to Poseidon2 emit.

Connects the abstract `cellLeafInjective` / `compressNInjective` carriers used in
`StateCommit` to the in-circuit Poseidon2 sponge gadget (`Poseidon2Emit`). The PROVED
direction composes `emit_faithful_poseidon2_compress` with `GadgetRefinement`; the
CR→injectivity discharge remains an explicit `sorry` HOLE (collision-resistance is the
correct assumption — not idealized `ℤ` injectivity).

No silent holes: unfinished binding lemmas are named `sorry` theorems below.
-/
import Dregg2.Circuit.Poseidon2Emit
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

/-! ## §1 — portal bundle (abstract OR emitted). -/

/-- **`PortalBundle`** — the Wave-4 bridge record: abstract leaf injectivity (current portal),
the §8 Poseidon2 CR carrier, and the proved emit-registration pin. -/
structure PortalBundle (CH : CellId → Value → ℤ) where
  /-- Abstract per-cell leaf injectivity (the current `StateCommit` portal). -/
  cellLeafInj : cellLeafInjective CH
  /-- §8 Poseidon2 collision-resistance carrier (the correct crypto assumption). -/
  poseidon2CR : Prop
  /-- Emitted sponge descriptor is registered under `poseidon2CompressAirName`. -/
  emitRegistered : emittedPoseidon2Compress.name = poseidon2CompressAirName
  deriving Repr

/-- Build a portal from the abstract injectivity alone (CR not yet discharged). -/
def PortalBundle.ofCellLeafInjective (CH : CellId → Value → ℤ) (h : cellLeafInjective CH) :
    PortalBundle CH :=
  { cellLeafInj := h, poseidon2CR := False, emitRegistered := rfl }

/-- Build a portal from Poseidon2 CR + the proved emit faithfulness pin. -/
def PortalBundle.ofPoseidon2Emit (CH : CellId → Value → ℤ) (hcr : Prop)
    (hleaf : cellLeafInjective CH) : PortalBundle CH :=
  { cellLeafInj := hleaf, poseidon2CR := hcr, emitRegistered := rfl }

/-! ## §2 — refinement composition (proved). -/

/-- **`digest_emit_refines_merkle_portal`** — the emitted sponge step refines to the Merkle
portal; inherited from `Poseidon2Emit.poseidon2_emitted_refines_merkle_portal`. -/
theorem digest_emit_refines_merkle_portal {Digest : Type}
    (compress : Digest → Digest → Digest) :
    Refines (Poseidon2Emit.poseidon2CompressEmittedStep compress)
      (GadgetRefinement.merklePortalStep compress) :=
  poseidon2_emitted_refines_merkle_portal compress

/-! ## §3 — explicit HOLE: CR ⇒ leaf injectivity (or full emit binding). -/

/-- **HOLE W4:** discharge `cellLeafInjective` from Poseidon2 CR + a canonical leaf encoding,
OR from the emitted in-circuit sponge (no abstract `ℤ` injectivity assumed). -/
def hole_cellLeafInjective_from_poseidon2_cr (CH : CellId → Value → ℤ) (hcr : Prop) : Prop :=
  sorry

/-- **HOLE W4:** discharge `compressNInjective` for the `StateCommit` frame sponge via
`emittedPoseidon2Compress` (replaces the abstract list-injectivity portal). -/
def hole_compressNInjective_from_poseidon2_emit (compressN : List ℤ → ℤ) : Prop :=
  sorry

/-- **HOLE W4:** discharge `logHashInjective` for the growing receipt-chain sponge. -/
def hole_logHashInjective_from_poseidon2_emit (LH : List Turn → ℤ) : Prop :=
  sorry

#assert_axioms digest_emit_refines_merkle_portal

end Dregg2.Circuit.DigestPortal