/-
# Crew field-mission admission — the teeth EVALUATION, out of the crypto archive's build

`CrewFieldMissionAdmission.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its teeth ran sixteen `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). The witnesses (`admittedRaw`, the
hostile mutations, their manifests and worlds) remain in `CrewFieldMissionAdmission.lean` as
evaluation-free `def`s; THIS module is where the pins are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Every theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. Fifteen pins move VERBATIM — their statements name only
public values, so the statements are unchanged too. The one exception is the hex-agreement
pin, stated over the private `uniformDigest`: its statement stays in the parent module as
`check_the_manifest_hex_and_the_signing_hex_agree_on_every_byte_value` and is pinned `= true`
here under the original theorem name.

⚠ Named residue in the parent module: none.
-/
import Dregg2.Games.PathOfAngels.CrewFieldMissionAdmission

namespace Dregg2.Games.PathOfAngels.CrewFieldMissionAdmission

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime

set_option autoImplicit false
set_option maxRecDepth 20000

theorem the_manifest_hex_and_the_signing_hex_agree_on_every_byte_value :
    check_the_manifest_hex_and_the_signing_hex_agree_on_every_byte_value = true := by
  native_decide

/-- The refusal sentinel is total: the empty document is not an activation.  Stated so
that the `""` an `@[export]` returns is never mistaken for a decodable input. -/
theorem the_empty_document_is_not_an_activation : decodeActivation "" = none := by
  native_decide

theorem the_admitted_activation_round_trips_through_the_codec :
    decodeActivation (activationJson admittedRaw) = some admittedRaw := by
  native_decide

theorem the_admitted_manifest_decodes_canonically :
    admittedValidatedManifest?.isSome = true := by
  native_decide

/-- The production seal MINTS for this crew — the satisfiability pole.  Without this
every refusal below would be vacuous. -/
theorem the_admitted_activation_mints_a_production_seal :
    (mintSeal? admittedRaw).isSome = true := by
  native_decide

/-- ⚑ The one that closes the hole: an activation the CURATOR published, located inside
the active world's own content root, is admitted — and the seal it runs under was minted
there, from those bytes. -/
theorem the_activated_world_admits_its_own_crew_activation :
    admittedMember?.isSome = true := by
  native_decide

/-- ⚑ THE MUTATION IS ASSERTED PRESENT BEFORE THE VERDICT.  Conjuncts 1–2: the document
really is suited to the PUBLIC fixture seal — its signing suite IS
`fixtureRunSeal.session`'s, and that differs from the production one, so the delta
exists and is the one named.  Conjuncts 3–4: it is otherwise a valid authored
activation in a world its manifest exactly matches.  Conjuncts 5–6: no seal mints, so
no member exists.  Without the first four this would be a refusal that could have come
from anywhere. -/
theorem a_fixture_suited_activation_in_an_exactly_matching_world_mints_no_seal :
    fixtureSuitedRaw.fieldSession.signingSuiteId
      = CrewFieldMission.fixtureRunSeal.session.signingSuiteId ∧
    fixtureSuitedRaw.fieldSession.signingSuiteId
      ≠ CrewFieldMission.ProductionSigning.signingSuiteId ∧
    activationValidB fixtureSuitedRaw = true ∧
    fixtureSuitedManifest.matchesWorldB fixtureSuitedWorld = true ∧
    mintSeal? fixtureSuitedRaw = none ∧
    fixtureSuitedMember? = none := by
  native_decide

theorem a_production_suited_activation_with_a_foreign_deck_commitment_mints_no_seal :
    wrongCommitmentRaw.fieldSession.signingSuiteId
      = CrewFieldMission.ProductionSigning.signingSuiteId ∧
    wrongCommitmentRaw.fieldSession.briefingCommitment
      ≠ admittedRaw.fieldSession.briefingCommitment ∧
    mintSeal? wrongCommitmentRaw = none := by
  native_decide

theorem a_free_salvage_table_rehashes_the_manifest_and_the_world_refuses_it :
    (mintSeal? forgedSalvageRaw).isSome = true ∧
    (ActivatedContent.decodeManifest forgedSalvageManifest.toJson).isSome = true ∧
    forgedSalvageManifest.matchesWorldB admittedWorld = false ∧
    forgedSalvageMember? = none := by
  native_decide

theorem a_component_under_another_name_is_not_this_organs_activation :
    misnamedManifest.matchesWorldB misnamedWorld = true ∧
    ActivatedContent.componentByName? misnamedManifest.components ACTIVATION_COMPONENT
      = none ∧
    misnamedMember? = none := by
  native_decide

theorem an_activation_cannot_be_carried_into_another_content_session :
    crossSessionMember? = none := by
  native_decide

theorem a_deck_naming_another_activation_envelope_is_refused :
    foreignDeckLineageManifest.matchesWorldB foreignDeckLineageWorld = true ∧
    (mintSeal? foreignDeckLineageRaw).isSome = true ∧
    foreignDeckLineageRaw.content.deck.activation.activationDigest
      ≠ foreignDeckLineageWorld.activationDigest ∧
    foreignDeckLineageMember? = none := by
  native_decide

theorem a_truncated_activation_refuses :
    decodeActivation truncatedActivationBytes = none := by
  native_decide

/-- ⚑ The DELETED `ReplayAuthority` cannot be spliced back in: `exactKeys` is exact in
both directions, so an otherwise byte-canonical document carrying a caller-supplied
verifier field refuses rather than being read with the field ignored. -/
theorem an_activation_carrying_a_replay_authority_field_refuses :
    decodeActivation spliceAppendedActivationBytes = none := by
  native_decide

theorem an_oversized_salvage_table_refuses :
    decodeActivation oversizedSalvageBytes = none := by
  native_decide

/-- The step envelope's own refusal poles, on the exported function.  `""` in, `""`
out; a canonical envelope naming a world with no manifest member, `""` out. -/
theorem the_export_refuses_the_empty_request : stepWire "" = "" := by
  native_decide

/-! ## ⚑ 2026-08-09 — the roster that could not play, and the entry point

Until today `admittedRawConfig` carried `CrewRelayExpedition.fixtureRoster` — player
keys `0a0a0a…`..`0d0d0d…` — against the PRODUCTION signing suite, whose `verifySeat`
demands `SHAKE256(publicKey, 32) = playerKey`.  No ML-DSA-65 public key digests to
`0a0a0a…`, so every theorem above was a REFUSAL tooth over a crew that had no accepting
pole at all: it minted, it was admitted, and it refused every step.  These two pins are
the accepting poles that were missing. -/

theorem every_admitted_seat_holds_a_real_ml_dsa_public_key :
    check_every_admitted_seat_holds_a_real_ml_dsa_public_key = true := by
  native_decide

theorem the_entry_point_answers_for_every_admitted_seat :
    check_the_entry_point_answers_for_every_admitted_seat = true := by
  native_decide

theorem the_entry_point_refuses_a_world_this_manifest_does_not_root :
    check_the_entry_point_refuses_a_world_this_manifest_does_not_root = true := by
  native_decide

theorem the_entry_point_refuses_the_empty_request : seatPreimageWire "" = "" := by
  native_decide

#assert_compiled the_manifest_hex_and_the_signing_hex_agree_on_every_byte_value
#assert_compiled the_empty_document_is_not_an_activation
#assert_compiled the_admitted_activation_round_trips_through_the_codec
#assert_compiled the_admitted_manifest_decodes_canonically
#assert_compiled the_admitted_activation_mints_a_production_seal
#assert_compiled the_activated_world_admits_its_own_crew_activation
#assert_compiled a_fixture_suited_activation_in_an_exactly_matching_world_mints_no_seal
#assert_compiled a_production_suited_activation_with_a_foreign_deck_commitment_mints_no_seal
#assert_compiled a_free_salvage_table_rehashes_the_manifest_and_the_world_refuses_it
#assert_compiled a_component_under_another_name_is_not_this_organs_activation
#assert_compiled an_activation_cannot_be_carried_into_another_content_session
#assert_compiled a_deck_naming_another_activation_envelope_is_refused
#assert_compiled a_truncated_activation_refuses
#assert_compiled an_activation_carrying_a_replay_authority_field_refuses
#assert_compiled an_oversized_salvage_table_refuses
#assert_compiled the_export_refuses_the_empty_request
#assert_compiled every_admitted_seat_holds_a_real_ml_dsa_public_key
#assert_compiled the_entry_point_answers_for_every_admitted_seat
#assert_compiled the_entry_point_refuses_a_world_this_manifest_does_not_root
#assert_compiled the_entry_point_refuses_the_empty_request

end Dregg2.Games.PathOfAngels.CrewFieldMissionAdmission
