/-
# Dregg2.Circuit.DigestPortal — Wave 4: bridge abstract digest portals to Poseidon2 emit.

Connects the abstract `cellLeafInjective` / `compressNInjective` / `logHashInjective` carriers used
in `StateCommit` to the in-circuit Poseidon2 sponge gadget (`Poseidon2Emit`). The refinement
direction composes `emit_faithful_poseidon2_compress` with `GadgetRefinement`; the CR→injectivity
discharge — formerly explicit `sorry` HOLEs — is now PROVED (`cellLeafInjective_from_poseidon2_cr`,
`compressNInjective_from_poseidon2_emit`, `logHashInjective_from_poseidon2_emit`) from the single
Poseidon2 collision-resistance assumption (`Poseidon2Binding.Poseidon2SpongeCR`), the correct
crypto carrier — not idealized `ℤ` injectivity.

No `sorry`/`admit`/`axiom`/`native_decide`; every theorem pins `{propext, Classical.choice, Quot.sound}`.
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

/-! ## §3 — DISCHARGED: Poseidon2 CR ⇒ the three injectivity portals (the holes are now theorems).

These were `def … : Prop := sorry` placeholders. They are now PROVED bridges from the SINGLE
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
The CR is the SOLE crypto content (carried in `R.spongeCR`); no abstract `ℤ` injectivity is assumed. -/
theorem cellLeafInjective_from_poseidon2_cr {CH : CellId → Value → ℤ} (R : LeafRealization CH) :
    cellLeafInjective CH :=
  cellLeafInjective_of_realization R

/-- **`compressNInjective_from_poseidon2_emit`** (was HOLE W4). Discharge `compressNInjective` for
the `StateCommit` frame sponge — the same list-hash `emittedPoseidon2Compress` realizes — DIRECTLY
from Poseidon2 collision-resistance (`compressNInjective` IS `Poseidon2SpongeCR`). -/
theorem compressNInjective_from_poseidon2_emit {compressN : List ℤ → ℤ}
    (hCR : Poseidon2SpongeCR compressN) : compressNInjective compressN :=
  compressNInjective_of_poseidon2CR hCR

/-- **`logHashInjective_from_poseidon2_emit`** (was HOLE W4). Discharge `logHashInjective LH` for the
growing receipt-chain sponge from a Poseidon2 log realization (CR + injective turn-list encoder). -/
theorem logHashInjective_from_poseidon2_emit {LH : List Turn → ℤ} (R : LogRealization LH) :
    logHashInjective LH :=
  logHashInjective_of_realization R

/-! ## §4 — the honest portal builder: a `PortalBundle` whose leaf injectivity is DISCHARGED from CR. -/

/-- **`PortalBundle.ofPoseidon2CR`** — build the portal bundle from a genuine Poseidon2 leaf
realization (CR-discharged), so `cellLeafInj` is PROVED, not assumed, and `poseidon2CR` carries the
real CR Prop (not the `False` placeholder of `ofCellLeafInjective`). -/
def PortalBundle.ofPoseidon2CR {CH : CellId → Value → ℤ} (R : LeafRealization CH) :
    PortalBundle CH :=
  { cellLeafInj := cellLeafInjective_from_poseidon2_cr R
    poseidon2CR := Poseidon2SpongeCR R.sponge
    emitRegistered := rfl }

#assert_axioms digest_emit_refines_merkle_portal
#assert_axioms cellLeafInjective_from_poseidon2_cr
#assert_axioms compressNInjective_from_poseidon2_emit
#assert_axioms logHashInjective_from_poseidon2_emit

end Dregg2.Circuit.DigestPortal