/-
# Salvage Crate authored rotation

This downstream module is deliberately outside `SalvageCrate.lean`: besides
providing a concrete three-period rotation for the web/game layer, it proves that
ordinary consumers cannot construct persistent states or successful results.
-/
import Dregg2.Games.PathOfAngels.SalvageCrate

namespace Dregg2.Games.PathOfAngels.SalvageCrateExamples

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.SalvageCrate

set_option autoImplicit false

def digest (tag : Nat) : Digest32 where
  bytes := List.replicate 32 (SalvageCrate.byte tag)
  length_eq := by simp

def missionArtifact : ArtifactRef where
  missionId := ⟨740⟩
  artifactId := ⟨741⟩
  sourceDigest := digest 1
  contentDigest := digest 2

def threadSpool : RelicId := ⟨55⟩

def mission : MissionSpec where
  missionId := ⟨740⟩
  artifact := missionArtifact
  epoch := ⟨4⟩
  federationId := digest 3
  contentRoot := digest 4
  activationDigest := digest 5
  contentSession := digest 6
  runSeed := digest 7
  budget := {
    intel := 0
    supplies := 3
    cohesion := 0
    influence := 0
    score := 0
    relics := 1
  }
  allowedRelics := {threadSpool}
  privacy := .public
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := by simp

def communalThread : Contribution where
  intel := 0
  supplies := 1
  cohesion := 0
  influence := 0
  score := 0
  relics := {threadSpool}
  relics_bounded := by simp

/-- The deliberately unglamorous public table: common nothing, a badge, an
account record, and a small communal salvage result. -/
def table : List LootEntry :=
  [ { id := ⟨10⟩
      prize := .common .warmAir
      custody := .nonEconomic
      weight := 8
      contribution := .zero }
  , { id := ⟨11⟩
      prize := .cosmetic ⟨4⟩
      custody := .nonEconomic
      weight := 3
      contribution := .zero }
  , { id := ⟨12⟩
      prize := .record ⟨8⟩
      custody := .nonEconomic
      weight := 2
      contribution := .zero }
  , { id := ⟨13⟩
      prize := .communalSalvage threadSpool
      custody := .nonEconomic
      weight := 1
      contribution := communalThread }
  ]

def raw : RawConfig where
  mission
  contentSeed := digest 22
  curatorKey := digest 23
  opensAt := ⟨31⟩
  closesAt := ⟨35⟩
  eligiblePlayers := {digest 40, digest 41, digest 42}
  allowedCosmetics := {⟨4⟩}
  allowedRecords := {⟨8⟩}
  allowedSalvage := {threadSpool}
  table
  beacons :=
    [ { period := ⟨31⟩, value := digest 101 }
    , { period := ⟨32⟩, value := digest 151 }
    , { period := ⟨35⟩, value := digest 211 }
    ]

theorem authored_rotation_config_valid : configValidB raw = true := by
  native_decide

def config : Config := ⟨raw, authored_rotation_config_valid⟩

def officer : Digest32 := digest 40

/-- Static site data can render this directly.  It is a preview, not authority to
open: each `entry` is rederived by the cap-gated judge. -/
def officerRotation : List RotationEntry := generatedRotation config officer

theorem generated_rotation_has_every_authored_period :
    officerRotation.map RotationEntry.period = [⟨31⟩, ⟨32⟩, ⟨35⟩] := by
  native_decide

theorem generated_rotation_has_no_draw_exhaustion :
    officerRotation.all (fun day => day.entry.isSome) = true := by
  native_decide

theorem generated_rotation_is_deterministic :
    generatedRotation config officer = officerRotation := rfl

/-- External ADT teeth: making either constructor public turns these declarations
red even if all favorable fixtures continue to evaluate. -/
theorem persistent_state_constructor_is_private : True := by
  fail_if_success (have _constructor := @State.mk)
  trivial

theorem successful_result_constructor_is_private : True := by
  fail_if_success (have _constructor := @OpenResult.mk)
  trivial

/-- ⚑ The capability that gates `openCrate` cannot be minted from outside the
crate.  This is the whole reason the write path is "reachable-through-authorization,
not reachable-by-anyone": `genesis`/`genesisCapability` and an accepted transition's
successor capability are the only producers, all inside `SalvageCrate`.  Making
`CurrentStateCapability.mk` public turns this red — and would hand every importer a
capability for any state it could name. -/
theorem current_state_capability_constructor_is_private : True := by
  fail_if_success (have _constructor := @CurrentStateCapability.mk)
  trivial

/-- Likewise the finality adapter's capability: only `finalityCapability` (this
module's single producer) mints it. -/
theorem finality_capability_constructor_is_private : True := by
  fail_if_success (have _constructor := @FinalityCapability.mk)
  trivial

#assert_compiled authored_rotation_config_valid
#assert_compiled generated_rotation_has_every_authored_period
#assert_compiled generated_rotation_has_no_draw_exhaustion
#assert_compiled generated_rotation_is_deterministic
#assert_axioms persistent_state_constructor_is_private
#assert_axioms successful_result_constructor_is_private
#assert_axioms current_state_capability_constructor_is_private
#assert_axioms finality_capability_constructor_is_private

end Dregg2.Games.PathOfAngels.SalvageCrateExamples
