/-
# AngelsEpoch2World — ONE epoch-2 world that carries BOTH organs

## The wound this exists to prevent

`persist/src/poa_world_activation.rs:23` keys the active head at the single string
`"active"`, and `audit_tables_in` refuses a table with more than one head.  There is
therefore exactly ONE active world per store, and `install_poa_activated_content_v1`
keys its manifest row by the FULL five-field world tuple.  Both `poa/artifacts/galley/
epoch-1/world.json` and `poa/artifacts/night-watch/epoch-1/world.json` declare
`content_epoch: 1` on the same federation, and `WorldActivation.applyStructural`
(`WorldActivation.lean:224`) requires a non-bootstrap `.advance` to carry
`contentEpoch = prev.contentEpoch + 1`.  So mounting night-watch at epoch 1 is
`.staleOrSkippedEpoch`, and mounting it at epoch 2 as a SINGLE-COMPONENT world moves
the head off the galley's world — after which `prepare_active_poa_galley_policy_v1_in`
finds no row for the new world and refuses.  That refusal is the "GALLEY SEALED" 503.

The exit is that manifests are natively multi-component (`ActivatedContent.
componentByName?`, made public 2026-08-05 for exactly this).  ONE epoch-2 world whose
manifest carries BOTH the galley policy component and the night-watch config component
serves both organs from one signed activation and evicts nothing.

## What is carried and what the gate FORCES to change

⚠ The brief for this work asked for the galley component "carried forward, byte
identical to what epoch-1 activated".  **That is impossible, and the reason is a
check, not an inconvenience.**  `ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld?`
carries the proof field

    epoch_exact : policy.contentEpoch = world.contentEpoch.value

and `GalleyMaintenanceDailyRuntime.PolicyWire` has its OWN `contentEpoch`, which the
shipped epoch-1 bytes set to `1`.  Under an epoch-2 world the gate demands `2`.  The
component's bytes therefore change, and so does its SHA-256.  The maximal honest carry
is what this module does: **decode the shipped bytes with the shipped codec and move
exactly one field.**  `daily_id`, `genesis_head`, `event_id`, `rules_digest` and every
content id survive verbatim, so the galley's daily does NOT restart — only its epoch
tag moves.  `the_galley_carry_moves_exactly_the_epoch` states that as a theorem over
every `PolicyWire`, not as a claim about one instance.

The night-watch config is the mirror image.  `NightWatchCampaignAdmission.
WorldScopedCampaignConfigMember` carries

    session_exact : raw.progression.contentSession = world.contentSession
    epoch_exact   : raw.progression.contentEpoch   = world.contentEpoch

and a world has ONE `contentSession`, so the two organs cannot keep `POA-GALLEY-1` and
`POA-NIGHT-1` side by side.  The config is re-emitted under the shared session at epoch
2 and NOTHING else moves — the roster, the rule table, the logbook stream coordinates
and the slot commitment are the epoch-1 values.

⚠ Consequence, stated rather than discovered later: the derived-label digests in both
components fold the epoch-1 `content_epoch` into their preimages (`POA-GALLEY-CONTENT-V1
\0 fed \0 1 \0 …` and `POA-NIGHT-WATCH-CONTENT-V1 \0 fed \0 1 \0 …`).  They are carried
DELIBERATELY, because the daily and the logbook are the SAME daily and the SAME
logbook; a reader recomputes them with `1` in the preimage, which is what the epoch-2
provenance file records.  Re-running `scripts/poa-galley-content.py` with
`CONTENT_EPOCH = 2` would derive a DIFFERENT `daily_id` and start a different daily.
That is not what this is.

## The shared session

`POA-ANGELS-2`, zero-padded to 32 bytes.  Neither organ's tag can name a world that
carries both, and `-1` on an epoch-2 world is a lie a later reader would believe.
Nothing pins the old sessions: the only tree-wide occurrences of `POA-GALLEY-1` outside
the epoch-1 artifacts are `scripts/poa-galley-content.py` (the emitter) and one literal
in a `node/src/poa_galley_genesis.rs` test.  `content_session` is an operator input to
`dregg-node poa-galley-world-preview` (`poa_galley_genesis.rs:144`) and is not derived
from anything, so moving it costs one flag on one command.

## The slot commitment is CARRIED, and that is safe by a theorem

`HiddenInstance.commit secret slot` depends on `(secret, slot)` only, so the epoch-1
commitment carries into epoch 2 with the curator's existing, repository-external
secret and no fresh ceremony draw.  It does not carry the SCHEDULE: a run seed is
`HiddenInstance.runSeedFor ⟨secret, slot, playerKey⟩ (missionContextOf config)` and
`NightWatchCampaign.missionContextOf` reads `progression.contentEpoch` and
`progression.contentSession` — both of which just moved.
`the_epoch2_run_seed_is_not_the_epoch1_run_seed` is that separation, decided over the
real sponge.  ⚠ Custody is still the curator's: drawing a FRESH secret at the ceremony
is equally supported and changes `content_root`, which re-signs the world statement.

⚠ Nothing in this module or the artifacts it emits lets a reader who has not played
reconstruct the instance.  The only closed instance here is the REHEARSAL one that
`NightWatchCampaignContent` already publishes for its own teeth, and
`the_shipped_commitment_is_not_the_published_rehearsal_one` keeps the two apart.

## Flag day

Nothing holds these bytes: no store has an epoch-2 world.  At the batched re-genesis
the epoch-1 activation (counter 1) is superseded by a counter-2 `.advance`; the
epoch-1 manifest row stays in `poa_activated_content_v1` under its own world key and
becomes unreachable through `prepare_active_poa_galley_policy_v1_in`, which is correct
— it is history, not authority.
-/
import Dregg2.Games.PathOfAngels.ActivatedContentRuntime
import Dregg2.Games.PathOfAngels.NightWatchCampaignContent

namespace Dregg2.Games.PathOfAngels.AngelsEpoch2World

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition
open Dregg2.Games.PathOfAngels.NightWatchCampaign
open Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission
open Dregg2.Games.PathOfAngels.NightWatchCampaignContent

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## The shared epoch-2 coordinates -/

abbrev CONTENT_EPOCH : Nat := 2

abbrev CONTENT_SESSION_TAG : String := "POA-ANGELS-2"

abbrev CONTENT_SESSION_HEX : String :=
  "504f412d414e47454c532d320000000000000000000000000000000000000000"

theorem epoch2_session_parses :
    (Emit.parseBytes32Hex? CONTENT_SESSION_HEX).isSome = true := by
  native_decide

def contentSession : Digest32 :=
  (Emit.parseBytes32Hex? CONTENT_SESSION_HEX).get epoch2_session_parses

/-- Two independent sources agree: the hex constant, and the ASCII string rendered byte
by byte.  A typo in either refuses here — the same discipline
`NightWatchCampaignContent.the_session_tag_is_the_ascii_spelling` applies to
`POA-NIGHT-1`. -/
theorem the_epoch2_session_tag_is_the_ascii_spelling :
    contentSession.bytes.map (fun byte => byte.val) =
      CONTENT_SESSION_TAG.toList.map Char.toNat ++ List.replicate 20 0 := by
  native_decide

/-- The federation is FORCED: `applyStructural` refuses an advance that changes it. -/
def federationId : Digest32 := NightWatchCampaignContent.authoredFederationId

/-! ## The two carries

Both are total functions on the shipped wire types, so the "only this field moved"
claims below are theorems about EVERY value, not about one instance. -/

def carryGalleyPolicy (policy : GalleyMaintenanceDailyRuntime.PolicyWire) :
    GalleyMaintenanceDailyRuntime.PolicyWire :=
  { policy with contentEpoch := CONTENT_EPOCH }

def carryCampaignConfig (raw : RawConfig) : RawConfig :=
  { raw with
      progression :=
        { raw.progression with
            contentSession := contentSession
            contentEpoch := ⟨CONTENT_EPOCH⟩ } }

/-- ⚑ The galley component is carried, not re-authored: put the old epoch back and the
policy is the shipped one, field for field.  `daily_id`, `genesis_head`, `event_id`,
`rules_digest` and every content id are therefore the epoch-1 values — the daily
continues. -/
theorem the_galley_carry_moves_exactly_the_epoch
    (policy : GalleyMaintenanceDailyRuntime.PolicyWire) :
    (carryGalleyPolicy policy).contentEpoch = CONTENT_EPOCH ∧
      { carryGalleyPolicy policy with contentEpoch := policy.contentEpoch } = policy :=
  ⟨rfl, rfl⟩

/-- ⚑ The campaign component likewise: the session and the epoch move, and putting
both back recovers the shipped config exactly — roster, rules, logbook stream and slot
commitment untouched. -/
theorem the_campaign_carry_moves_exactly_the_session_and_epoch (raw : RawConfig) :
    (carryCampaignConfig raw).progression.contentSession = contentSession ∧
      (carryCampaignConfig raw).progression.contentEpoch = ⟨CONTENT_EPOCH⟩ ∧
      { carryCampaignConfig raw with progression := raw.progression } = raw ∧
      { (carryCampaignConfig raw).progression with
          contentSession := raw.progression.contentSession
          contentEpoch := raw.progression.contentEpoch } = raw.progression :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## The multiplexed manifest

Component order is not decoration: `ActivatedContent.Manifest.validB` requires
`components.Pairwise componentNameLessP`, and `poa.galley-…` precedes
`poa.night-watch-…`. -/

def galleyComponent? (policyBytes : String) : Option ActivatedContent.Component := do
  let policy ← GalleyMaintenanceDailyRuntime.decodePolicy policyBytes
  let bytes := (carryGalleyPolicy policy).toJson
  let digest ← ActivatedContent.sha256Utf8? bytes
  pure { name := ActivatedContent.GALLEY_POLICY_COMPONENT, sha256 := digest, bytesUtf8 := bytes }

def campaignComponent? (raw : RawConfig) : Option ActivatedContent.Component := do
  let bytes := configJson (carryCampaignConfig raw)
  let digest ← ActivatedContent.sha256Utf8? bytes
  pure { name := CONFIG_COMPONENT, sha256 := digest, bytesUtf8 := bytes }

def epoch2Scope : ActivatedContent.ManifestScope where
  federationId := federationId
  contentSession := contentSession
  contentEpoch := CONTENT_EPOCH

def manifest? (policyBytes : String) (raw : RawConfig) : Option ActivatedContent.Manifest := do
  let galley ← galleyComponent? policyBytes
  let campaign ← campaignComponent? raw
  pure { scope := epoch2Scope, legacyWholePackRoot := none, components := [galley, campaign] }

def manifestBytes? (policyBytes : String) (raw : RawConfig) : Option String :=
  (manifest? policyBytes raw).map ActivatedContent.Manifest.toJson

def world? (policyBytes : String) (raw : RawConfig) (activationDigest : Digest32) :
    Option WorldActivation.WorldIdentity := do
  let built ← manifest? policyBytes raw
  let root ← ActivatedContent.manifestRoot? built
  pure {
    federationId := federationId
    contentRoot := root
    activationDigest := activationDigest
    contentSession := contentSession
    contentEpoch := ⟨CONTENT_EPOCH⟩ }

/-- The single-component epoch-2 world the exit exists to avoid: the night watch alone,
scoped to the same shared session and epoch. -/
def campaignOnlyManifest? (raw : RawConfig) : Option ActivatedContent.Manifest := do
  let campaign ← campaignComponent? raw
  pure { scope := epoch2Scope, legacyWholePackRoot := none, components := [campaign] }

/-! ## The shipped instance

`galleyEpoch1PolicyBytes` are the exact bytes of the `poa.galley-maintenance-daily.
policy.v1` component inside `poa/artifacts/galley/epoch-1/manifest.json`; the galley has
no Lean-side authoring module (it is `scripts/poa-galley-content.py`, a named twin), so
this is the one literal.  The emit driver's `check` mode compares it to that file and
refuses on drift.  The night-watch side needs no literal at all: it is
`NightWatchCampaignContent.authoredRaw` — the SAME source the epoch-1 artifact was
rendered from — applied to the shipped commitment. -/

def galleyEpoch1PolicyBytes : String :=
  "{\"deployment_id\":\"4db835cc36cd0d3b722e742334dc1dde9557601fe1334c7499ab023de4d6d45d\",\"federation_id\":\"70b7fa4cfbc3921bef2e1ddb1a42869c8dcef27539179c9cbdf6a6e6b1d07c1b\",\"daily_id\":\"608535a3c26465ba8160944290a32edd88462250a6b2eac1844c90cfa7afb773\",\"genesis_head\":\"343e2d930753c940233cb8f3d504908fae49e96b97c84f28d47c040cb9189805\",\"dregg_mint\":0,\"snapshot_slot\":0,\"content_epoch\":1,\"event_id\":\"bb61eb7e3ad230fb270d8b0843de5e188ab96daf64ed54b29d8f827d9f731abf\",\"rules_digest\":\"6ec7ac903e54fed8a8805974fd5169719c9ec271ab945696c719fde0fc40eff6\",\"public_activity_id\":\"2e7b46deb2070036bea0d201cb306b664b3896ea03b8a39137cbe9b39d6cd24f\",\"scene_content_id\":\"f046d422e6f083cc27fece6b55678b11a5dc9816f0df408dea8fd924d4348cf8\",\"public_action_content_id\":\"8e21eaffc27b665f28313684b0fcf8047c7385f95647e39d1da6adf254fe3f13\",\"sponsor_action_content_id\":\"45df481df9d14aead6e2c8d5d80a0bc1eef876eef0921bbbfa64d5bcd7298da5\",\"complete_content_id\":\"51a4cfdd0d83ec2bf5b7c0f6ce408c55646a584b18e4365d91ed26d54f8dfe37\",\"public_service\":1,\"sponsor_service\":1,\"service_target\":24,\"power_root\":\"0000000000000000000000000000000000000000000000000000000000000000\",\"loot_root\":\"0000000000000000000000000000000000000000000000000000000000000000\",\"canon_root\":\"0000000000000000000000000000000000000000000000000000000000000000\",\"canon_revision\":0}"

abbrev SHIPPED_SLOT_COMMITMENT_HEX : String :=
  "8ec4da984d1b3f9bc5838f4b2e174f71f8539693663ed137a0b4cd896f657fdf"

theorem shipped_commitment_parses :
    (Emit.parseBytes32Hex? SHIPPED_SLOT_COMMITMENT_HEX).isSome = true := by
  native_decide

/-- The commitment `poa/artifacts/night-watch/epoch-1/config.json` already publishes.
Carrying it is what makes the epoch-2 artifact reproducible without a secret. -/
def shippedSlotCommitment : Digest32 :=
  (Emit.parseBytes32Hex? SHIPPED_SLOT_COMMITMENT_HEX).get shipped_commitment_parses

/-- ⚑ The shipped commitment is NOT the rehearsal one this repository publishes, so no
reader of these files holds the instance.  `NightWatchCampaignContentEmitMain` refuses
to emit under the rehearsal secret for exactly this reason, and carrying the commitment
forward preserves that property rather than re-testing it. -/
theorem the_shipped_commitment_is_not_the_published_rehearsal_one :
    (shippedSlotCommitment == rehearsalCommitment) = false := by
  native_decide

def shippedRaw : RawConfig := authoredRaw shippedSlotCommitment

/-- ⚠ Provisional, exactly as at epoch 1: `dregg-node poa-galley-world-preview` derives
the real `activation_digest` from the verified POAG1 content-epoch envelope, and
`Manifest.matchesWorldB` never reads it, so the member witnesses below are insensitive
to which value it is (`the_members_are_insensitive_to_the_activation_digest`). -/
def provisionalActivationDigest : Digest32 :=
  NightWatchCampaignContent.authoredProvisionalActivationDigest

def shippedManifestBytes? : Option String :=
  manifestBytes? galleyEpoch1PolicyBytes shippedRaw

def shippedWorld? : Option WorldActivation.WorldIdentity :=
  world? galleyEpoch1PolicyBytes shippedRaw provisionalActivationDigest

/-! ## ⚑ Both organs, one world, one manifest, one activation

`bothOrgans?` binds ONE world and ONE decoded manifest and hands the SAME pair to both
witness constructors.  A reader does not have to take the `do` block's word for it:
`both_members_name_the_same_world_and_manifest` decides the equalities. -/

def bothOrgans? (policyBytes : String) (raw : RawConfig) (activationDigest : Digest32) :
    Option (ActivatedContent.WorldScopedGalleyPolicyMember × WorldScopedCampaignConfigMember) := do
  let bytes ← manifestBytes? policyBytes raw
  let validated ← ActivatedContent.decodeManifest bytes
  let worldId ← world? policyBytes raw activationDigest
  let galley ← ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld? worldId validated
  let campaign ← authorizeCampaignConfigForWorld? worldId validated
  pure (galley, campaign)

def shippedBothOrgans? :
    Option (ActivatedContent.WorldScopedGalleyPolicyMember × WorldScopedCampaignConfigMember) :=
  bothOrgans? galleyEpoch1PolicyBytes shippedRaw provisionalActivationDigest

/-- ⚑ THE DELIVERABLE.  One epoch-2 world admits the galley policy AND the night-watch
config.  Both witness types have private constructors whose only producers traverse the
manifest, so this is membership under the world's own `contentRoot`, not an assertion. -/
theorem one_epoch2_world_serves_both_organs : shippedBothOrgans?.isSome = true := by
  native_decide

/-- The two members are not two worlds that agree today. -/
theorem both_members_name_the_same_world_and_manifest :
    (shippedBothOrgans?.map fun pair =>
      (pair.1.world == pair.2.world, pair.1.manifest.raw == pair.2.manifest.raw)) =
      some (true, true) := by
  native_decide

/-- Neither witness read the provisional activation digest, so the node's world preview
supplies the real one at the ceremony with no re-emit and no re-hash. -/
theorem the_members_are_insensitive_to_the_activation_digest :
    (bothOrgans? galleyEpoch1PolicyBytes shippedRaw (markDigest 1)).isSome = true := by
  native_decide

/-! ## The DEPLOYED export, not a neighbouring one

`persist/src/poa_activated_content.rs:332` calls `authorize_poa_activated_content`,
which is `@[export dregg_poa_activated_content_authorize]` =
`ActivatedContentRuntime.authorizeWire` = `authorize?` under a canonical decode.  These
two pins are therefore about the function the node actually runs. -/

def activatedContentInput? (policyBytes : String) (raw : RawConfig)
    (activationDigest : Digest32) : Option ActivatedContentRuntime.InputWire := do
  let bytes ← manifestBytes? policyBytes raw
  let worldId ← world? policyBytes raw activationDigest
  pure { world := worldId, manifestJson := bytes }

theorem the_deployed_export_serves_the_galley_from_the_multiplexed_world :
    ((activatedContentInput? galleyEpoch1PolicyBytes shippedRaw provisionalActivationDigest).bind
      ActivatedContentRuntime.authorize?).isSome = true := by
  native_decide

/-! ## ⚑ The eviction the single-component world would have caused

Under a night-watch-only epoch-2 world the night watch IS served and the galley is NOT,
and the deployed export refuses outright — which is what turns
`prepare_active_poa_galley_policy_v1_in` into the "GALLEY SEALED" 503. -/

def campaignOnlyVerdict? (raw : RawConfig) (activationDigest : Digest32) :
    Option (Bool × Bool × Bool) := do
  let built ← campaignOnlyManifest? raw
  let bytes := built.toJson
  let validated ← ActivatedContent.decodeManifest bytes
  let root ← ActivatedContent.manifestRoot? built
  let worldId : WorldActivation.WorldIdentity :=
    { federationId := federationId
      contentRoot := root
      activationDigest := activationDigest
      contentSession := contentSession
      contentEpoch := ⟨CONTENT_EPOCH⟩ }
  pure ( (authorizeCampaignConfigForWorld? worldId validated).isSome
       , (ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld? worldId validated).isSome
       , (ActivatedContentRuntime.authorize? { world := worldId, manifestJson := bytes }).isSome )

theorem the_single_component_epoch2_world_evicts_the_galley :
    campaignOnlyVerdict? shippedRaw provisionalActivationDigest = some (true, false, false) := by
  native_decide

/-! ## The epoch-2 campaign is PLAYABLE, and its schedule is not epoch 1's

Under the published rehearsal instance — never the shipped one — the whole shipped path
runs at epoch 2: admission, a four-command watch, and the exported judge. -/

def rehearsalEpoch2Raw : RawConfig := authoredRaw rehearsalCommitment

def epoch2MissionContext : HiddenInstance.MissionContext where
  missionId := authoredMissionId
  epoch := ⟨CONTENT_EPOCH⟩
  federationId := federationId
  contentSession := contentSession

def rehearsalEpoch2Draw : RawActivation where
  slot := authoredSlot
  slotSecret := rehearsalSecret
  slotCommitment := rehearsalCommitment
  playerKey := rehearsalPlayer
  mission := epoch2MissionContext
  runSeed := HiddenInstance.runSeedFor
    { secret := rehearsalSecret, slot := authoredSlot, playerKey := rehearsalPlayer }
    epoch2MissionContext

def rehearsalEpoch2Member? : Option WorldScopedCampaignConfigMember := do
  let bytes ← manifestBytes? galleyEpoch1PolicyBytes rehearsalEpoch2Raw
  let validated ← ActivatedContent.decodeManifest bytes
  let worldId ← world? galleyEpoch1PolicyBytes rehearsalEpoch2Raw provisionalActivationDigest
  authorizeCampaignConfigForWorld? worldId validated

def rehearsalEpoch2Activation? : Option Activation := do
  let member ← rehearsalEpoch2Member?
  admitActivation? member.config rehearsalEpoch2Draw

def rehearsalEpoch2AfterWatch? : Option State := do
  let activation ← rehearsalEpoch2Activation?
  (replay activation (initialState activation) rehearsalWatch).toOption

/-- One watch settles on the epoch-2 world exactly as it does at epoch 1: four commands,
shift 1, one logbook intent, sequence 4. -/
theorem one_watch_settles_on_the_epoch2_world :
    (rehearsalEpoch2AfterWatch?.map fun state =>
      (state.shift, state.history.length, state.sequence, state.intents.length)) =
      some (1, 1, 4, 1) := by
  native_decide

def rehearsalEpoch2JudgeInput? : Option NightWatchCampaignWire.InputWire := do
  let bytes ← manifestBytes? galleyEpoch1PolicyBytes rehearsalEpoch2Raw
  let worldId ← world? galleyEpoch1PolicyBytes rehearsalEpoch2Raw provisionalActivationDigest
  pure {
    world := worldId
    manifest := bytes
    activation := rehearsalEpoch2Draw
    history := rehearsalWatch.take 3
    command := { sequence := 3, nullifier := rehearsalNullifier 3, action := .debrief } }

/-- ⚑ The EXPORTED boundary — the same bytes-in/bytes-out function
`dregg_poa_night_watch_campaign_judge` serves — settles the epoch-2 debrief against the
MULTIPLEXED manifest.  The galley component sitting beside it does not obstruct the
night watch, and the world it is judged under is the one the galley is served from. -/
theorem the_exported_judge_settles_a_watch_on_the_multiplexed_world :
    (rehearsalEpoch2JudgeInput?.bind fun input =>
      NightWatchCampaignWire.judgeJson (NightWatchCampaignWire.inputJson input)).isSome = true := by
  native_decide

/-- ⚑ Carrying the slot commitment does NOT carry the schedule.  Same secret, same
slot, same player — a different mission context, because `missionContextOf` reads the
progression's session and epoch, and both moved.  This is why an epoch-1 commitment is
safe to reuse. -/
theorem the_epoch2_run_seed_is_not_the_epoch1_run_seed :
    (HiddenInstance.runSeedFor
        { secret := rehearsalSecret, slot := authoredSlot, playerKey := rehearsalPlayer }
        epoch2MissionContext ==
      HiddenInstance.runSeedFor
        { secret := rehearsalSecret, slot := authoredSlot, playerKey := rehearsalPlayer }
        NightWatchCampaignContent.authoredMissionContext) = false := by
  native_decide

#assert_axioms the_galley_carry_moves_exactly_the_epoch
#assert_compiled the_campaign_carry_moves_exactly_the_session_and_epoch
#assert_compiled epoch2_session_parses
#assert_compiled shipped_commitment_parses
#assert_compiled the_epoch2_session_tag_is_the_ascii_spelling
#assert_compiled the_shipped_commitment_is_not_the_published_rehearsal_one
#assert_compiled one_epoch2_world_serves_both_organs
#assert_compiled both_members_name_the_same_world_and_manifest
#assert_compiled the_members_are_insensitive_to_the_activation_digest
#assert_compiled the_deployed_export_serves_the_galley_from_the_multiplexed_world
#assert_compiled the_single_component_epoch2_world_evicts_the_galley
#assert_compiled one_watch_settles_on_the_epoch2_world
#assert_compiled the_exported_judge_settles_a_watch_on_the_multiplexed_world
#assert_compiled the_epoch2_run_seed_is_not_the_epoch1_run_seed

end Dregg2.Games.PathOfAngels.AngelsEpoch2World
