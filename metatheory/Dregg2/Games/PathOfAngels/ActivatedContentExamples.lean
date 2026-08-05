/-
# ActivatedContentExamples — hostile manifest and Galley membership cases

These are named executable facts, not anonymous evaluator case tests.  The fixture uses
the real legacy whole-pack SHA-256 measured by the private pack's independent
Node canonicalizer on 2026-08-05:

`sha256:6660e19d53404d5d97081133be5dd2ef52c3cda93da6926ccfc0c7b86c12f607`.

That value is provenance only.  The activated fixture world uses the new
manifest root and the two are asserted different below.
-/
import Dregg2.Games.PathOfAngels.ActivatedContent

namespace Dregg2.Games.PathOfAngels.ActivatedContentExamples

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

private def digestByte (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def zeroDigest : Digest32 := digestByte 0

private def legacyWholePackRoot : Digest32 :=
  (Emit.parseBytes32Hex?
    "6660e19d53404d5d97081133be5dd2ef52c3cda93da6926ccfc0c7b86c12f607").getD
      (digestByte 250)

private def federation := digestByte 1
private def contentSession := digestByte 2
private def activationDigest := digestByte 3

private def fixturePolicy : GalleyMaintenanceDailyRuntime.PolicyWire := {
  deploymentId := digestByte 10
  federationId := federation
  dailyId := digestByte 11
  genesisHead := digestByte 12
  dreggMint := 13
  snapshotSlot := 14
  contentEpoch := 1
  eventId := digestByte 15
  rulesDigest := digestByte 16
  publicActivityId := digestByte 17
  sceneContentId := digestByte 18
  publicActionContentId := digestByte 19
  sponsorActionContentId := digestByte 20
  completeContentId := digestByte 21
  publicService := 3
  sponsorService := 2
  serviceTarget := 12
  powerRoot := digestByte 22
  lootRoot := digestByte 23
  canonRoot := digestByte 24
  canonRevision := 1
}

private def fixtureComponent : ActivatedContent.Component := {
  name := ActivatedContent.GALLEY_POLICY_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? fixturePolicy.toJson).getD zeroDigest
  bytesUtf8 := fixturePolicy.toJson
}

private def fixtureManifest : ActivatedContent.Manifest := {
  scope := {
    federationId := federation
    contentSession := contentSession
    contentEpoch := 1
  }
  legacyWholePackRoot := some legacyWholePackRoot
  components := [fixtureComponent]
}

private def fixtureManifestRoot : Digest32 :=
  (ActivatedContent.manifestRoot? fixtureManifest).getD zeroDigest

private def fixtureWorld (session : Digest32 := contentSession) : WorldActivation.WorldIdentity := {
  federationId := federation
  contentRoot := fixtureManifestRoot
  activationDigest := activationDigest
  contentSession := session
  contentEpoch := ⟨1⟩
}

private def fixtureValidated? : Option ActivatedContent.ValidatedManifest :=
  ActivatedContent.decodeManifest fixtureManifest.toJson

private def fixtureGalleyMember? :
    Option ActivatedContent.WorldScopedGalleyPolicyMember := do
  let manifest ← fixtureValidated?
  ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld? fixtureWorld manifest

theorem canonical_manifest_decodes : fixtureValidated?.isSome = true := by native_decide

theorem active_world_exact_manifest_accepts : fixtureGalleyMember?.isSome = true := by
  native_decide

theorem exact_galley_policy_is_a_member : fixtureGalleyMember?.isSome = true := by
  native_decide

private def substitutedPolicy : GalleyMaintenanceDailyRuntime.PolicyWire :=
  { fixturePolicy with rulesDigest := digestByte 99 }

private def staleDigestSubstitution : ActivatedContent.Manifest :=
  { fixtureManifest with components :=
      [{ fixtureComponent with bytesUtf8 := substitutedPolicy.toJson }] }

theorem substituted_bytes_with_stale_digest_refused :
    ActivatedContent.decodeManifest staleDigestSubstitution.toJson = none := by native_decide

private def rehashedSubstitutionComponent : ActivatedContent.Component := {
  name := ActivatedContent.GALLEY_POLICY_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? substitutedPolicy.toJson).getD zeroDigest
  bytesUtf8 := substitutedPolicy.toJson
}

private def rehashedSubstitution : ActivatedContent.Manifest :=
  { fixtureManifest with components := [rehashedSubstitutionComponent] }

theorem rehashed_substitution_is_internally_valid :
    (ActivatedContent.decodeManifest rehashedSubstitution.toJson).isSome = true := by
  native_decide

private def rehashedSubstitutionActivation? :
    Option ActivatedContent.WorldScopedGalleyPolicyMember := do
  let manifest ← ActivatedContent.decodeManifest rehashedSubstitution.toJson
  ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld? fixtureWorld manifest

/-- Updating the component digest is not enough: it changes the manifest root,
so the already activated world refuses it. -/
theorem rehashed_substitution_refused_by_active_root :
    rehashedSubstitutionActivation? = none := by native_decide

private def duplicateNameManifest : ActivatedContent.Manifest :=
  { fixtureManifest with components := [fixtureComponent, fixtureComponent] }

theorem duplicate_component_name_refused :
    ActivatedContent.decodeManifest duplicateNameManifest.toJson = none := by native_decide

private def legacyNamedComponent : ActivatedContent.Component := {
  fixtureComponent with name := ActivatedContent.LEGACY_ROOT_RESERVED_COMPONENT
}

private def legacyNamedManifest : ActivatedContent.Manifest :=
  { fixtureManifest with components := [legacyNamedComponent] }

theorem legacy_provenance_cannot_be_reinterpreted_as_component :
    ActivatedContent.decodeManifest legacyNamedManifest.toJson = none := by native_decide

theorem trailing_whitespace_is_noncanonical :
    ActivatedContent.decodeManifest (fixtureManifest.toJson ++ " ") = none := by native_decide

private def wrongSessionWorld := fixtureWorld (digestByte 77)

private def crossWorldActivation? :
    Option ActivatedContent.WorldScopedGalleyPolicyMember := do
  let manifest ← fixtureValidated?
  ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld? wrongSessionWorld manifest

/-- The root alone is not enough: an otherwise structurally valid world with
the same root but a different content session cannot consume the manifest. -/
theorem cross_world_session_substitution_refused : crossWorldActivation? = none := by
  native_decide

private def wrongEpochPolicy : GalleyMaintenanceDailyRuntime.PolicyWire :=
  { fixturePolicy with contentEpoch := 2 }

private def wrongEpochComponent : ActivatedContent.Component := {
  name := ActivatedContent.GALLEY_POLICY_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? wrongEpochPolicy.toJson).getD zeroDigest
  bytesUtf8 := wrongEpochPolicy.toJson
}

private def wrongEpochManifest : ActivatedContent.Manifest :=
  { fixtureManifest with components := [wrongEpochComponent] }

theorem wrong_epoch_manifest_is_internally_valid :
    (ActivatedContent.decodeManifest wrongEpochManifest.toJson).isSome = true := by
  native_decide

private def wrongEpochManifestRoot : Digest32 :=
  (ActivatedContent.manifestRoot? wrongEpochManifest).getD zeroDigest

private def wrongEpochWorld : WorldActivation.WorldIdentity :=
  { fixtureWorld with contentRoot := wrongEpochManifestRoot }

private def wrongEpochPolicyMember? :
    Option ActivatedContent.WorldScopedGalleyPolicyMember := do
  let manifest ← ActivatedContent.decodeManifest wrongEpochManifest.toJson
  ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld? wrongEpochWorld manifest

/-- Even exact manifest bytes cannot authorize a Galley policy from another
content epoch. -/
theorem exact_bytes_with_cross_epoch_policy_refused : wrongEpochPolicyMember? = none := by
  native_decide

theorem legacy_whole_pack_root_does_not_equal_new_manifest_root :
    fixtureManifestRoot ≠ legacyWholePackRoot := by native_decide

/-- `activationDigest` authenticates the signed activation record, not the
manifest preimage (including it there would be cyclic). Content equivalence
therefore survives re-signing. Persistence must retain and compare the exact
all-five-field world under its same-writer active-world audit. -/
private def resignedWorld : WorldActivation.WorldIdentity :=
  { fixtureWorld with activationDigest := digestByte 88 }

private def resignedWorldMember? :
    Option ActivatedContent.WorldScopedGalleyPolicyMember := do
  let manifest ← fixtureValidated?
  ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld? resignedWorld manifest

theorem activation_digest_is_external_to_content_equivalence :
    resignedWorldMember?.isSome = true := by native_decide

/-- Independent UTF-8/SHA-256 vector also checked with Node's `crypto` over the
same UTF-8 string. This catches accidental character-count hashing. -/
theorem independent_utf8_sha256_vector :
    ActivatedContent.sha256Utf8? "Ω/🚀\n" = Emit.parseBytes32Hex?
      "113efa2f2cbd5cf8422ae5fb1e6a1ac00de656ce0d95772ce0d2b6702f24f99a" := by
  native_decide

#assert_compiled canonical_manifest_decodes
#assert_compiled active_world_exact_manifest_accepts
#assert_compiled exact_galley_policy_is_a_member
#assert_compiled substituted_bytes_with_stale_digest_refused
#assert_compiled rehashed_substitution_is_internally_valid
#assert_compiled rehashed_substitution_refused_by_active_root
#assert_compiled duplicate_component_name_refused
#assert_compiled legacy_provenance_cannot_be_reinterpreted_as_component
#assert_compiled trailing_whitespace_is_noncanonical
#assert_compiled cross_world_session_substitution_refused
#assert_compiled wrong_epoch_manifest_is_internally_valid
#assert_compiled exact_bytes_with_cross_epoch_policy_refused
#assert_compiled legacy_whole_pack_root_does_not_equal_new_manifest_root
#assert_compiled activation_digest_is_external_to_content_equivalence
#assert_compiled independent_utf8_sha256_vector

end Dregg2.Games.PathOfAngels.ActivatedContentExamples
