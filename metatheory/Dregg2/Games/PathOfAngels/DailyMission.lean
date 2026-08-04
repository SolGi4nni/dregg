/-
# Dregg2.Games.PathOfAngels.DailyMission — finalized-epoch daily selection.

The browser clock is not part of this state machine.  A signed content catalog
declares a finite, nonempty mission rotation and an inclusive finalized-epoch
window.  Selection is a total deterministic function inside that window and
refuses a stale epoch or a request for a different signed activation.

`DailyRequest.finalizedEpoch` is an input to this pure semantic layer.  The
network adapter remains responsible for deriving it from Dregg finality rather
than from a client claim; this module makes the exact value consumed by the
selector explicit and receipt-visible.
-/
import Dregg2.Games.PathOfAngels.Core

namespace Dregg2.Games.PathOfAngels.DailyMission

open Dregg2.Games.PathOfAngels

/-- One signed rotation.  The proof fields rule out the two states that would
make modulo selection partial: an empty catalog and a backwards activation
window. -/
structure Catalog where
  contentEpoch : EpochId
  contentRoot : Digest32
  activationDigest : Digest32
  catalogDigest : Digest32
  opensAt : EpochId
  closesAt : EpochId
  missions : List MissionId
  window_ordered : opensAt.value ≤ closesAt.value
  missions_nonempty : missions ≠ []
  missions_nodup : missions.Nodup
deriving DecidableEq

/-- The values the runtime presents to the selector.  Keeping all activation
identity here prevents a stale catalog with the same display mission ids from
being selected accidentally. -/
structure Request where
  contentEpoch : EpochId
  contentRoot : Digest32
  activationDigest : Digest32
  catalogDigest : Digest32
  finalizedEpoch : EpochId
deriving DecidableEq

/-- A daily selection is a receipt-shaped projection of every input that chose
the mission.  It is not a judged game receipt and grants no world contribution. -/
structure Selection where
  contentEpoch : EpochId
  contentRoot : Digest32
  activationDigest : Digest32
  catalogDigest : Digest32
  finalizedEpoch : EpochId
  rotationOffset : Nat
  mission : MissionId
deriving DecidableEq

def Request.matchesCatalog (request : Request) (catalog : Catalog) : Bool :=
  decide (
    request.contentEpoch = catalog.contentEpoch ∧
    request.contentRoot = catalog.contentRoot ∧
    request.activationDigest = catalog.activationDigest ∧
    request.catalogDigest = catalog.catalogDigest)

def Catalog.activeAt (catalog : Catalog) (epoch : EpochId) : Bool :=
  decide (catalog.opensAt.value ≤ epoch.value ∧ epoch.value ≤ catalog.closesAt.value)

theorem Catalog.missions_length_pos (catalog : Catalog) : 0 < catalog.missions.length := by
  exact List.length_pos_iff.mpr catalog.missions_nonempty

/-- Offset zero is the first active finalized epoch.  The subtraction occurs
only after `activeAt` has admitted the request. -/
def Catalog.rotationOffset (catalog : Catalog) (epoch : EpochId) : Nat :=
  (epoch.value - catalog.opensAt.value) % catalog.missions.length

theorem Catalog.rotationOffset_lt (catalog : Catalog) (epoch : EpochId) :
    catalog.rotationOffset epoch < catalog.missions.length := by
  exact Nat.mod_lt _ catalog.missions_length_pos

def Catalog.selectedMission (catalog : Catalog) (epoch : EpochId) : MissionId :=
  catalog.missions.get ⟨catalog.rotationOffset epoch, catalog.rotationOffset_lt epoch⟩

/-- Select exactly one mission, or refuse before producing any result. -/
def select (catalog : Catalog) (request : Request) : Option Selection :=
  if request.matchesCatalog catalog then
    if catalog.activeAt request.finalizedEpoch then
      some {
        contentEpoch := request.contentEpoch
        contentRoot := request.contentRoot
        activationDigest := request.activationDigest
        catalogDigest := request.catalogDigest
        finalizedEpoch := request.finalizedEpoch
        rotationOffset := catalog.rotationOffset request.finalizedEpoch
        mission := catalog.selectedMission request.finalizedEpoch
      }
    else none
  else none

theorem select_deterministic {catalog : Catalog} {request : Request}
    {first second : Selection}
    (hfirst : select catalog request = some first)
    (hsecond : select catalog request = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem select_refuses_wrong_activation (catalog : Catalog) (request : Request)
    (h : request.activationDigest ≠ catalog.activationDigest) :
    select catalog request = none := by
  simp [select, Request.matchesCatalog, h]

theorem select_refuses_wrong_catalog (catalog : Catalog) (request : Request)
    (h : request.catalogDigest ≠ catalog.catalogDigest) :
    select catalog request = none := by
  simp [select, Request.matchesCatalog, h]

theorem select_refuses_before_window (catalog : Catalog) (request : Request)
    (h : request.finalizedEpoch.value < catalog.opensAt.value) :
    select catalog request = none := by
  have hn : ¬ catalog.opensAt.value ≤ request.finalizedEpoch.value := Nat.not_le.mpr h
  simp [select, Catalog.activeAt, hn]

theorem select_refuses_after_window (catalog : Catalog) (request : Request)
    (h : catalog.closesAt.value < request.finalizedEpoch.value) :
    select catalog request = none := by
  have hn : ¬ request.finalizedEpoch.value ≤ catalog.closesAt.value := Nat.not_le.mpr h
  simp [select, Catalog.activeAt, hn]

theorem select_binds_finalized_epoch {catalog : Catalog} {request : Request}
    {selection : Selection} (h : select catalog request = some selection) :
    selection.finalizedEpoch = request.finalizedEpoch := by
  simp only [select] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]

theorem select_binds_catalog {catalog : Catalog} {request : Request}
    {selection : Selection} (h : select catalog request = some selection) :
    selection.catalogDigest = catalog.catalogDigest := by
  simp only [select] at h
  split at h <;> try contradiction
  · rename_i hm
    have hmatches :
        request.contentEpoch = catalog.contentEpoch ∧
        request.contentRoot = catalog.contentRoot ∧
        request.activationDigest = catalog.activationDigest ∧
        request.catalogDigest = catalog.catalogDigest := by
      simpa [Request.matchesCatalog] using hm
    split at h <;> try contradiction
    injection h with heq
    rw [← heq, hmatches.2.2.2]

theorem select_mission_mem {catalog : Catalog} {request : Request}
    {selection : Selection} (h : select catalog request = some selection) :
    selection.mission ∈ catalog.missions := by
  simp only [select] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  exact List.get_mem catalog.missions _

theorem select_offset_lt_length {catalog : Catalog} {request : Request}
    {selection : Selection} (h : select catalog request = some selection) :
    selection.rotationOffset < catalog.missions.length := by
  simp only [select] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  exact catalog.rotationOffset_lt request.finalizedEpoch

theorem adjacent_epochs_rotate (catalog : Catalog) (epoch : EpochId)
    (hopen : catalog.opensAt.value ≤ epoch.value) :
    catalog.rotationOffset ⟨epoch.value + 1⟩ =
      (catalog.rotationOffset epoch + 1) % catalog.missions.length := by
  have hsub : epoch.value + 1 - catalog.opensAt.value =
      (epoch.value - catalog.opensAt.value) + 1 := by
    omega
  simp [Catalog.rotationOffset, hsub, Nat.add_mod]

#assert_axioms Catalog.missions_length_pos
#assert_axioms Catalog.rotationOffset_lt
#assert_axioms select_deterministic
#assert_axioms select_refuses_wrong_activation
#assert_axioms select_refuses_wrong_catalog
#assert_axioms select_refuses_before_window
#assert_axioms select_refuses_after_window
#assert_axioms select_binds_finalized_epoch
#assert_axioms select_binds_catalog
#assert_axioms select_mission_mem
#assert_axioms select_offset_lt_length
#assert_axioms adjacent_epochs_rotate

end Dregg2.Games.PathOfAngels.DailyMission
