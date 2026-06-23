/-
# Dregg2.Apps.Gallery — the art gallery as a verified cell-program (WriteOnce item identity).

`apps/gallery/src/artwork.rs` and `starbridge-apps/gallery/` model a federated artwork registry: an artist
**registers** (mints) a content-addressed artwork id (`WriteOnce` — no re-mint over `AlreadyRegistered`),
**transfers** ownership to the auction winner, and **sets metadata** freely. This module is the **ungated
cell-program dual** of `GalleryGated` — the SAME gallery ops run through the shipped credential-blind
executor `execFullForestA`, with load-bearing guarantees enforced by `stateStepGuarded` reading the
artwork cell's factory-installed `WriteOnce item` caveat.

Headline guarantees (kernel-native, no §8 credential leg):

  * **ITEM IMMUTABLE** — re-minting over an already-bound `item` slot is rejected (`WriteOnce`).
  * **CONSERVATION** — every committed gallery write is balance-neutral (`SetField` Δ = 0).
  * **NON-VACUITY** — concrete `gal0`/`galFresh` states with `#guard` witnesses mirroring the gated app.

Templates: `Apps/GalleryGated.lean` (domain + caveats), `Apps/GovernedNamespace.lean` (ungated shape).
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForest

namespace Dregg2.Apps.Gallery

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState (stateStepGuarded caveatsAdmit fieldOf
  stateStepGuarded_caveat_violation_fails stateStepDev_caveat_violation_fails)

/-! ## §1 — The gallery DOMAIN (artwork cell, slots, WriteOnce item caveat). -/

abbrev artworkCell : CellId := 0
abbrev galleryActor : CellId := 0

abbrev itemSlot : FieldName := "item"
abbrev ownerSlot : FieldName := "owner"
abbrev metadataSlot : FieldName := "metadata"

def galleryCaveats : List SlotCaveat :=
  [ .writeOnce itemSlot ]

/-! ## §2 — Gallery ops as REAL executor turns (`setFieldA` through `execFullForestA`). -/

def galOp (slot : FieldName) (value : Int) : FullForestA :=
  ⟨ .setFieldA galleryActor artworkCell slot value, [] ⟩

def mint (itemVal : Int) : FullForestA :=
  galOp itemSlot itemVal

def transfer (newOwner : Int) : FullForestA :=
  galOp ownerSlot newOwner

def setMetadata (newMeta : Int) : FullForestA :=
  galOp metadataSlot newMeta

/-! ## §3 — Item-immutable teeth (executor-enforced WriteOnce, credential-blind). -/

theorem gallery_item_immutable (s : RecChainedState) (value : Int)
    (hbound : caveatsAdmit s.kernel itemSlot galleryActor artworkCell value = false) :
    execFullForestA s (mint value) = none := by
  have hnone := stateStepDev_caveat_violation_fails s itemSlot galleryActor artworkCell value hbound
  rw [execFullForestA_eq_execFullTurnA]
  simp only [mint, galOp, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hnone]

/-! ## §4 — Conservation (gallery metadata is balance-orthogonal). -/

theorem galOp_delta_zero (slot : FieldName) (value : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (galOp slot value)) b = 0 := by
  simp [galOp, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem gallery_conserves (s s' : RecChainedState) (slot : FieldName) (value : Int) (b : AssetId)
    (h : execFullForestA s (galOp slot value) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullForestA_conserves_per_asset s s' (galOp slot value) b h
    (galOp_delta_zero slot value b)

theorem gallery_mint_conserves (s s' : RecChainedState) (itemVal : Int) (b : AssetId)
    (h : execFullForestA s (mint itemVal) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  gallery_conserves s s' itemSlot itemVal b h

/-! ## §5 — NON-VACUITY: `gal0`/`galFresh` + `#guard` witnesses (mirrors `GalleryGated`). -/

def gal0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then
                  .record [("balance", .int 0), (itemSlot, .int 42), (ownerSlot, .int 7),
                           (metadataSlot, .int 0)]
                else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        slotCaveats := fun c => if c = 0 then galleryCaveats else [] }
    log := [] }

def galFresh : RecChainedState :=
  { gal0 with kernel := { gal0.kernel with
      cell := fun c => if c = 0 then
                .record [("balance", .int 0), (itemSlot, .int 0), (ownerSlot, .int 0),
                         (metadataSlot, .int 0)]
              else .record [("balance", .int 0)] } }

-- (i) a GOOD mint over a FRESH item slot COMMITS:
#guard ((execFullForestA galFresh (mint 42)).isSome)  --  true
#guard ((execFullForestA galFresh (mint 42)).map
        (fun s => fieldOf itemSlot (s.kernel.cell 0))) == some 42  --  some 42

-- (ii) ITEM IMMUTABLE: minting a DIFFERENT value over bound `item = 42` ⇒ none:
#guard (caveatsAdmit gal0.kernel itemSlot galleryActor artworkCell 99) == false  --  false
#guard ((execFullForestA gal0 (mint 99)).isSome) == false  --  false
#guard (caveatsAdmit gal0.kernel itemSlot galleryActor artworkCell 42)  --  true (no-op)

-- (iii) TRANSFER and set-metadata (no caveat) COMMIT:
#guard ((execFullForestA gal0 (transfer 8)).isSome)  --  true
#guard ((execFullForestA gal0 (transfer 8)).map
        (fun s => fieldOf ownerSlot (s.kernel.cell 0))) == some 8  --  some 8
#guard ((execFullForestA gal0 (setMetadata 5)).isSome)  --  true

-- (iv) CONSERVATION: committed mint/transfer move NO asset's supply:
#guard ((execFullForestA galFresh (mint 42)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)
#guard ((execFullForestA gal0 (transfer 8)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

/-! ## §6 — Axiom-hygiene pins. -/

#assert_axioms gallery_item_immutable
#assert_axioms galOp_delta_zero
#assert_axioms gallery_conserves
#assert_axioms gallery_mint_conserves

end Dregg2.Apps.Gallery