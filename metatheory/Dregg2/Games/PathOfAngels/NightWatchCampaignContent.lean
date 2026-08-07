/-
# NightWatchCampaignContent — the authored epoch-1 config, single-sourced in Lean

`NightWatchCampaignAdmission` gave the night watch an authenticated route to a
config: `authorizeCampaignConfigForWorld?` admits only bytes found under
`poa.night-watch-campaign.config.v1` inside a manifest whose SHA-256 root IS the
audited world's `contentRoot`.  Its own docblock then records the vacancy: *nothing
EMITS such a component*, so the only manifests carrying one were its fixtures.  This
module is the emitter's CONTENT — the actual epoch-1 campaign for the devnet
federation — and `NightWatchCampaignContentEmitMain` is the driver that renders it.

## Why this is Lean and not a `poa-galley-content.py` twin

The galley authored its policy bytes in Python against the Lean codec, and that
script's own docblock spends thirty lines on the byte discipline needed to keep two
encoders agreeing.  The night-watch config cannot even attempt that split: its
`slot_commitment` is `HiddenInstance.commit` — a Poseidon2 sponge no Python script
should reimplement — and the codec (`configJson`/`decodeConfig`) already lives in
`NightWatchCampaignAdmission`.  So the content is authored HERE, in the same
language as the codec that judges it, and the only encoder is the one the judge
runs.  There is no second spelling to drift.

## What is authored vs what is a ceremony input

Everything below is static EXCEPT the slot commitment.  `authoredRaw` is a function
of one `Digest32`: the commitment the curator's slot secret opens.  The secret is
drawn OFF-LINE (`poa_signal_slot_ceremony.rs` describes the identical custody for
Signal), the driver computes `HiddenInstance.commit` from a secret FILE it never
echoes, and no artifact carries the secret.  A reader of every emitted byte holds
the rules, the roster, and one commitment — and can reconstruct NO roll: the
schedule is `runSeedFor (secret, slot, player) ctx` through the sponge, which is
exactly the property `NightWatchCampaignWire.a_run_drawn_under_the_wrong_secret_is_not_judged`
bites on.

The REHEARSAL secret below is published, deliberately, for the same reason
`NightWatchCampaignAdmission.fixtureSecret` is: theorems need a closed instance.
The teeth run the entire authored campaign — activation, admission, a full
four-command watch, the exported `judgeJson` — under the rehearsal commitment.  The
driver REFUSES to emit under it (`the rehearsal secret is not a deployable secret`),
so the published instance can never back a shipped artifact.

## Provenance discipline

Every authored digest that is not a hash of authored bytes is SHA-256 of a labelled
preimage (`derivedDigest`), the same `\x00`-joined convention as
`scripts/poa-galley-content.py`, domain `POA-NIGHT-WATCH-CONTENT-V1` — so any reader
can recompute any of them without trusting this file.  The two that ARE hashes of
authored bytes (component sha, manifest root) are recomputed by `ActivatedContent`
at decode time and byte-refused on drift.

## ⚠ Placeholders that re-emit, named

* **Roster player keys** are derived labels, not player-held keys.  Seating real
  players changes the config bytes, so it re-hashes the manifest, changes
  `content_root`, and requires a fresh signed world activation.  That is the
  ordinary flag day; the route hop that mounts the judge must bind each
  `playerKey` to an authenticated caller identity.
* **`authoredProvisionalActivationDigest`** stands where the node's world preview
  will derive the real activation digest (the galley's flows through
  `dregg-node poa-galley-world-preview`).  `authorizeCampaignConfigForWorld?`
  never reads it — `matchesWorldB` compares federation, session, epoch and root —
  so the member witness is insensitive to it, and the audited world's own value
  replaces it at install with no re-emit.
* **`logStream`** coordinates (aggregate kind 21, derived key/root) are where the
  campaign's logbook intents will append; the EventBatch-authority hop pins them.
* **`betaDiscovery` is `none` on every rule**: no canon artifact is claimed until
  the content contract authors one.

## Flag day

New component, new session: nothing held `poa.night-watch-campaign.config.v1`
before this module, so nothing breaks — this is the first emission the admission
seam was built to authenticate.  Whenever THIS file's authored values change, the
config bytes change, the manifest re-hashes, `content_root` moves, and the
night-watch world must be re-activated under a fresh curator signature.
-/
import Dregg2.Games.PathOfAngels.NightWatchCampaignWire

namespace Dregg2.Games.PathOfAngels.NightWatchCampaignContent

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition
open Dregg2.Games.PathOfAngels.NightWatchCampaign
open Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission

set_option autoImplicit false
set_option maxRecDepth 10000

/-! ## Deployment coordinates — `poa/deployments/epoch-1/poa-devnet.json` -/

/-- `deployment_id` of the epoch-1 devnet.  Provenance only: no config field
carries it, matching the shape of `RawConfig`. -/
abbrev DEPLOYMENT_ID_HEX : String :=
  "4db835cc36cd0d3b722e742334dc1dde9557601fe1334c7499ab023de4d6d45d"

/-- `federation_id` of the epoch-1 devnet — the same one the galley content and the
POAG1 catalog are scoped to. -/
abbrev FEDERATION_ID_HEX : String :=
  "70b7fa4cfbc3921bef2e1ddb1a42869c8dcef27539179c9cbdf6a6e6b1d07c1b"

/-- The night-watch content session: ASCII tag `POA-NIGHT-1`, zero-padded to 32
bytes — the same convention as Signal's `POA-SIG-1` and the galley's
`POA-GALLEY-1`.  `the_session_tag_is_the_ascii_spelling` ties this hex constant to
the string itself, so the two spellings cannot drift. -/
abbrev CONTENT_SESSION_HEX : String :=
  "504f412d4e494748542d31000000000000000000000000000000000000000000"

abbrev CONTENT_SESSION_TAG : String := "POA-NIGHT-1"

abbrev CONTENT_EPOCH : Nat := 1

theorem federation_id_parses : (Emit.parseBytes32Hex? FEDERATION_ID_HEX).isSome = true := by
  native_decide

theorem content_session_parses :
    (Emit.parseBytes32Hex? CONTENT_SESSION_HEX).isSome = true := by
  native_decide

def authoredFederationId : Digest32 :=
  (Emit.parseBytes32Hex? FEDERATION_ID_HEX).get federation_id_parses

def authoredContentSession : Digest32 :=
  (Emit.parseBytes32Hex? CONTENT_SESSION_HEX).get content_session_parses

/-- Two independent sources agree: the hex constant above, and the ASCII string
rendered byte by byte.  A typo in either refuses here. -/
theorem the_session_tag_is_the_ascii_spelling :
    authoredContentSession.bytes.map (fun byte => byte.val) =
      CONTENT_SESSION_TAG.data.map Char.toNat ++ List.replicate 21 0 := by
  native_decide

/-! ## Derived digests — recomputable by any reader

SHA-256 of `domain \x00 federation_hex \x00 epoch \x00 field \x00 label`, exactly
the galley script's convention under this organ's own domain tag. -/

abbrev DERIVE_DOMAIN : String := "POA-NIGHT-WATCH-CONTENT-V1"

def preimageOf (field label : String) : String :=
  DERIVE_DOMAIN ++ "\x00" ++ FEDERATION_ID_HEX ++ "\x00" ++ toString CONTENT_EPOCH ++
    "\x00" ++ field ++ "\x00" ++ label

def derivedDigest (field label : String) : Digest32 :=
  (ActivatedContent.sha256Utf8? (preimageOf field label)).getD (markDigest 0)

/-- Every `(field, label)` pair used below.  Listed once so the computability tooth
and the provenance emitter walk the SAME census rather than two. -/
def derivedDigestCensus : List (String × String) :=
  [ ("progression_owner", "progression-owner/the-khovokhi-night-watch")
  , ("log_stream_content_root", "khovokhi-logbook/epoch-1")
  , ("log_stream_activation_digest", "khovokhi-logbook/activation/epoch-1")
  , ("log_stream_key", "khovokhi-logbook/campaign-stream")
  , ("world_activation_digest", "activation-digest/provisional-until-world-preview")
  , ("seat_0_player_key", "seat-0/pathfinder-of-the-first-watch")
  , ("seat_1_player_key", "seat-1/engineer-of-the-first-watch")
  , ("seat_2_player_key", "seat-2/containment-of-the-first-watch")
  , ("seat_3_player_key", "seat-3/quartermaster-of-the-first-watch")
  , ("task_content", "task/bridge-plot-drift")
  , ("success_content", "scene/the-course-held")
  , ("failure_content", "scene/the-drift-uncorrected")
  , ("task_content", "task/engine-spine-coolant-balance")
  , ("success_content", "scene/the-spine-runs-cool")
  , ("failure_content", "scene/the-coolant-scalds")
  , ("task_content", "task/signal-gallery-trace")
  , ("success_content", "scene/the-signal-pinned")
  , ("failure_content", "scene/the-trace-gone-cold")
  , ("task_content", "task/containment-seal-inspection")
  , ("success_content", "scene/the-seal-holds")
  , ("failure_content", "scene/the-seal-weeps")
  , ("task_content", "task/galley-ration-audit")
  , ("success_content", "scene/the-ledger-balances")
  , ("failure_content", "scene/the-shortfall-found")
  , ("task_content", "task/infirmary-recovery-round")
  , ("success_content", "scene/the-watch-mended")
  , ("failure_content", "scene/the-round-cut-short")
  , ("rehearsal", "slot-secret/published-in-this-module")
  , ("rehearsal", "nullifier-0"), ("rehearsal", "nullifier-1")
  , ("rehearsal", "nullifier-2"), ("rehearsal", "nullifier-3")
  , ("rehearsal", "nullifier-4") ]

/-- `sha256Utf8?` answered for every preimage this module hashes, so no
`derivedDigest` below silently fell to its `getD` default. -/
theorem every_derived_digest_computes :
    derivedDigestCensus.all
      (fun pair => (ActivatedContent.sha256Utf8? (preimageOf pair.1 pair.2)).isSome) = true := by
  native_decide

/-! ## The authored identity -/

def authoredProgression : ShipLifeProgression.ProgressionIdentity where
  federationId := authoredFederationId
  contentSession := authoredContentSession
  contentEpoch := ⟨CONTENT_EPOCH⟩
  season := ⟨1⟩
  activationDigest := derivedDigest "world_activation_digest"
    "activation-digest/provisional-until-world-preview"
  owner := derivedDigest "progression_owner" "progression-owner/the-khovokhi-night-watch"

/-- ⚠ The stream's world CANNOT be the activated night-watch world: that world's
`contentRoot` is the SHA-256 of the manifest embedding this very config, so naming
it here would be a cycle (the same note `NightWatchCampaignAdmission.
fixtureStreamWorld` carries).  These are the coordinates the EventBatch-authority
hop pins when it starts appending the campaign's logbook intents. -/
def authoredLogStreamWorld : EventBatch.WorldIdentity where
  federationId := authoredFederationId
  contentRoot := derivedDigest "log_stream_content_root" "khovokhi-logbook/epoch-1"
  activationDigest := derivedDigest "log_stream_activation_digest"
    "khovokhi-logbook/activation/epoch-1"
  contentSession := authoredContentSession
  contentEpoch := ⟨CONTENT_EPOCH⟩

def authoredLogStream : EventBatch.StreamId where
  world := authoredLogStreamWorld
  aggregate := {
    namespaceId := authoredFederationId
    kind := 21
    key := derivedDigest "log_stream_key" "khovokhi-logbook/campaign-stream" }
  version := ⟨1⟩

/-! ## The roster — four derived-label seats

⚠ Placeholder keys, per the docblock: a seated PLAYER holds a key the route hop
authenticates, and seating one is a config re-emit plus a re-signed activation. -/

def authoredSeat (index : Nat) (field label : String) (role : CrewRole) : Seat where
  id := ⟨index⟩
  playerKey := derivedDigest field label
  credential := ⟨index⟩
  role := role
  initialCounter := 0

def authoredRoster : List Seat :=
  [ authoredSeat 0 "seat_0_player_key" "seat-0/pathfinder-of-the-first-watch" .pathfinder
  , authoredSeat 1 "seat_1_player_key" "seat-1/engineer-of-the-first-watch" .engineer
  , authoredSeat 2 "seat_2_player_key" "seat-2/containment-of-the-first-watch" .containment
  , authoredSeat 3 "seat_3_player_key" "seat-3/quartermaster-of-the-first-watch"
      .quartermaster ]

/-! ## The authored task table — all six stations, all six tasks, all four roles

Thresholds are odds in 256ths (`HAZARD_FACES`): 102 ≈ 60%, 128 = 50%, 77 ≈ 70%,
154 ≈ 40%, 51 ≈ 80%.  Every arm of every rule is affordable from
`authoredResources`, so the campaign's only refusals are the ones a player earns. -/

def contentIds (taskLabel successLabel failureLabel : String) :
    Digest32 × Digest32 × Digest32 :=
  ( derivedDigest "task_content" taskLabel
  , derivedDigest "success_content" successLabel
  , derivedDigest "failure_content" failureLabel )

def plotDriftRule : TaskRule :=
  let ids := contentIds "task/bridge-plot-drift" "scene/the-course-held"
    "scene/the-drift-uncorrected"
  { station := .bridge
    task := .plotDrift
    role := .pathfinder
    riskThreshold := 102
    successContribution := ⟨3, 0, 1, 0, 4⟩
    failureContribution := ⟨1, 0, 0, 0, 1⟩
    successEffects := { spendPropellant := 1, gainSupplies := 2, gainMorale := 1 }
    failureEffects := { spendMorale := 1 }
    successHealth := { strainAdded := 1 }
    failureHealth := { strainAdded := 2 }
    successEvidence := 3
    failureEvidence := 1
    localService := 0
    betaDiscovery := none
    discoveryEvidenceRequired := 0
    taskContentId := ids.1
    successContentId := ids.2.1
    failureContentId := ids.2.2 }

def coolantBalanceRule : TaskRule :=
  let ids := contentIds "task/engine-spine-coolant-balance" "scene/the-spine-runs-cool"
    "scene/the-coolant-scalds"
  { station := .engineSpine
    task := .coolantBalance
    role := .engineer
    riskThreshold := 128
    successContribution := ⟨2, 0, 2, 0, 5⟩
    failureContribution := ⟨0, 0, 1, 0, 1⟩
    successEffects := { spendSupplies := 1, gainPropellant := 4, gainMorale := 1 }
    failureEffects := { spendSupplies := 1, spendMorale := 2 }
    successHealth := { strainAdded := 1 }
    failureHealth := { woundsAdded := 1, strainAdded := 2 }
    successEvidence := 5
    failureEvidence := 1
    localService := 0
    betaDiscovery := none
    discoveryEvidenceRequired := 0
    taskContentId := ids.1
    successContentId := ids.2.1
    failureContentId := ids.2.2 }

def traceSignalRule : TaskRule :=
  let ids := contentIds "task/signal-gallery-trace" "scene/the-signal-pinned"
    "scene/the-trace-gone-cold"
  { station := .signalGallery
    task := .traceSignal
    role := .pathfinder
    riskThreshold := 77
    successContribution := ⟨5, 0, 0, 1, 6⟩
    failureContribution := ⟨1, 0, 0, 0, 1⟩
    successEffects := { spendPropellant := 1, gainMunitions := 1 }
    failureEffects := { spendMorale := 1 }
    successHealth := { strainAdded := 1 }
    failureHealth := { strainAdded := 2 }
    successEvidence := 6
    failureEvidence := 1
    localService := 0
    betaDiscovery := none
    discoveryEvidenceRequired := 0
    taskContentId := ids.1
    successContentId := ids.2.1
    failureContentId := ids.2.2 }

def inspectSealRule : TaskRule :=
  let ids := contentIds "task/containment-seal-inspection" "scene/the-seal-holds"
    "scene/the-seal-weeps"
  { station := .containment
    task := .inspectSeal
    role := .containment
    riskThreshold := 154
    successContribution := ⟨4, 1, 0, 0, 6⟩
    failureContribution := ⟨0, 0, 1, 0, 2⟩
    successEffects := { gainSupplies := 4 }
    failureEffects := { spendSupplies := 2, spendMorale := 2 }
    successHealth := { strainAdded := 1 }
    failureHealth := { woundsAdded := 2, strainAdded := 2 }
    successEvidence := 8
    failureEvidence := 2
    localService := 0
    betaDiscovery := none
    discoveryEvidenceRequired := 0
    taskContentId := ids.1
    successContentId := ids.2.1
    failureContentId := ids.2.2 }

def rationAuditRule : TaskRule :=
  let ids := contentIds "task/galley-ration-audit" "scene/the-ledger-balances"
    "scene/the-shortfall-found"
  { station := .galley
    task := .rationAudit
    role := .quartermaster
    riskThreshold := 51
    successContribution := ⟨0, 3, 2, 0, 7⟩
    failureContribution := ⟨0, 0, 0, 0, 1⟩
    successEffects := { spendPropellant := 1, gainSupplies := 6, gainMorale := 1 }
    failureEffects := { spendSupplies := 1 }
    successHealth := { strainAdded := 1 }
    failureHealth := { strainAdded := 3 }
    successEvidence := 3
    failureEvidence := 0
    localService := 25
    betaDiscovery := none
    discoveryEvidenceRequired := 0
    taskContentId := ids.1
    successContentId := ids.2.1
    failureContentId := ids.2.2 }

def recoveryRoundRule : TaskRule :=
  let ids := contentIds "task/infirmary-recovery-round" "scene/the-watch-mended"
    "scene/the-round-cut-short"
  { station := .infirmary
    task := .recoveryRound
    role := .containment
    riskThreshold := 77
    successContribution := ⟨0, 0, 4, 0, 6⟩
    failureContribution := ⟨0, 0, 0, 0, 1⟩
    successEffects := { spendSupplies := 2, gainMorale := 2 }
    failureEffects := { spendMorale := 1 }
    successHealth := { woundsRecovered := 2, strainRecovered := 2 }
    failureHealth := { strainAdded := 1 }
    successEvidence := 2
    failureEvidence := 0
    localService := 0
    betaDiscovery := none
    discoveryEvidenceRequired := 0
    taskContentId := ids.1
    successContentId := ids.2.1
    failureContentId := ids.2.2 }

def authoredRules : List TaskRule :=
  [ plotDriftRule, coolantBalanceRule, traceSignalRule, inspectSealRule
  , rationAuditRule, recoveryRoundRule ]

def authoredResources : ShipResources := ⟨80, 40, 80, 60⟩

abbrev AUTHORED_SLOT : Nat := 1
abbrev AUTHORED_MISSION : Nat := 1

def authoredSlot : EpochId := ⟨AUTHORED_SLOT⟩

/-- Mission 1 of the night-watch session.  It cannot collide with Signal's mission 1:
`HiddenInstance.MissionContext` carries the federation AND the content session, and
this session's tag is `POA-NIGHT-1`. -/
def authoredMissionId : MissionId := ⟨AUTHORED_MISSION⟩

def authoredMissionContext : HiddenInstance.MissionContext where
  missionId := authoredMissionId
  epoch := ⟨CONTENT_EPOCH⟩
  federationId := authoredFederationId
  contentSession := authoredContentSession

/-- The whole authored campaign, as a function of the ONE ceremony input.  Everything
except `slotCommitment` is fixed by this module. -/
def authoredRaw (commitment : Digest32) : RawConfig where
  schemaVersion := 1
  missionId := authoredMissionId
  progression := authoredProgression
  logStream := authoredLogStream
  slot := authoredSlot
  slotCommitment := commitment
  roster := authoredRoster
  rules := authoredRules
  initialResources := authoredResources
  maxShifts := 24

/-! ## The manifest and the world, derived from the bytes -/

def authoredComponent (commitment : Digest32) : ActivatedContent.Component :=
  let bytes := configJson (authoredRaw commitment)
  { name := CONFIG_COMPONENT
    sha256 := (ActivatedContent.sha256Utf8? bytes).getD (markDigest 0)
    bytesUtf8 := bytes }

def authoredManifest (commitment : Digest32) : ActivatedContent.Manifest where
  scope := {
    federationId := authoredFederationId
    contentSession := authoredContentSession
    contentEpoch := CONTENT_EPOCH }
  legacyWholePackRoot := none
  components := [authoredComponent commitment]

def authoredManifestBytes (commitment : Digest32) : String :=
  (authoredManifest commitment).toJson

/-- The provisional stand-in for the digest `dregg-node`'s world preview derives.
`matchesWorldB` never reads it, so the member witness holds for the audited world's
real value with no re-emit — that independence is
`the_member_witness_is_insensitive_to_the_activation_digest` below. -/
def authoredProvisionalActivationDigest : Digest32 :=
  derivedDigest "world_activation_digest" "activation-digest/provisional-until-world-preview"

def authoredWorld (commitment : Digest32) (activationDigest : Digest32) :
    WorldActivation.WorldIdentity where
  federationId := authoredFederationId
  contentRoot := (ActivatedContent.manifestRoot? (authoredManifest commitment)).getD
    (markDigest 0)
  activationDigest := activationDigest
  contentSession := authoredContentSession
  contentEpoch := ⟨CONTENT_EPOCH⟩

/-! ## The rehearsal instance — published, and refused by the emitter

One closed instance so the teeth can run the REAL admission and judge path over the
authored campaign.  The driver refuses this secret at emit time, so nothing shipped
is ever derivable from this file. -/

def rehearsalSecret : HiddenInstance.SlotSecret :=
  ⟨derivedDigest "rehearsal" "slot-secret/published-in-this-module"⟩

def rehearsalCommitment : Digest32 := HiddenInstance.commit rehearsalSecret authoredSlot

def rehearsalRaw : RawConfig := authoredRaw rehearsalCommitment

def rehearsalManifestBytes : String := authoredManifestBytes rehearsalCommitment

def rehearsalWorld : WorldActivation.WorldIdentity :=
  authoredWorld rehearsalCommitment authoredProvisionalActivationDigest

def rehearsalMember? : Option WorldScopedCampaignConfigMember := do
  let manifest ← ActivatedContent.decodeManifest rehearsalManifestBytes
  authorizeCampaignConfigForWorld? rehearsalWorld manifest

/-- Seat 0's key — the pathfinder stands the rehearsal watch. -/
def rehearsalPlayer : Digest32 :=
  derivedDigest "seat_0_player_key" "seat-0/pathfinder-of-the-first-watch"

def rehearsalDraw : RawActivation where
  slot := authoredSlot
  slotSecret := rehearsalSecret
  slotCommitment := rehearsalCommitment
  playerKey := rehearsalPlayer
  mission := authoredMissionContext
  runSeed := HiddenInstance.runSeedFor
    { secret := rehearsalSecret, slot := authoredSlot, playerKey := rehearsalPlayer }
    authoredMissionContext

def rehearsalActivation? : Option Activation := do
  let member ← rehearsalMember?
  admitActivation? member.config rehearsalDraw

def rehearsalNullifier (index : Nat) : Digest32 :=
  derivedDigest "rehearsal" s!"nullifier-{index}"

/-- One full watch at the bridge: claim, choose, resolve, debrief.
(`NightWatchCampaign.Command` spelled out: `CrewRelayExpedition` has a `Command`
of its own and both namespaces are open here.) -/
def rehearsalWatch : List NightWatchCampaign.Command :=
  [ { sequence := 0, nullifier := rehearsalNullifier 0
      action := .claimOfficer rehearsalPlayer ⟨0⟩ }
  , { sequence := 1, nullifier := rehearsalNullifier 1
      action := .chooseTask .bridge .plotDrift }
  , { sequence := 2, nullifier := rehearsalNullifier 2, action := .resolve }
  , { sequence := 3, nullifier := rehearsalNullifier 3, action := .debrief } ]

def rehearsalAfterWatch? : Option State := do
  let activation ← rehearsalActivation?
  (replay activation (initialState activation) rehearsalWatch).toOption

/-! ## Teeth — the authored campaign, end to end, under the rehearsal commitment

All `native_decide` (the chain runs SHA-256 and the Poseidon2 sponge), all pinned
`#assert_compiled`. -/

theorem the_authored_config_activates : (activate? rehearsalRaw).isSome = true := by
  native_decide

theorem the_authored_config_round_trips :
    decodeConfig (configJson rehearsalRaw) = some rehearsalRaw := by
  native_decide

theorem the_authored_manifest_decodes :
    (ActivatedContent.decodeManifest rehearsalManifestBytes).isSome = true := by
  native_decide

theorem the_authored_log_stream_is_a_valid_event_stream :
    EventBatch.StreamId.validB authoredLogStream = true := by
  native_decide

/-- ⚑ The emission closes the admission module's named vacancy: a manifest this
module renders, rooted as a world's `contentRoot`, ADMITS the authored config. -/
theorem the_authored_world_admits_the_authored_config :
    rehearsalMember?.isSome = true := by
  native_decide

/-- The same authorization under a world whose activation digest is something else
entirely (`markDigest 1`). -/
def rehearsalMemberUnderAnotherActivationDigest? :
    Option WorldScopedCampaignConfigMember := do
  let manifest ← ActivatedContent.decodeManifest rehearsalManifestBytes
  authorizeCampaignConfigForWorld?
    (authoredWorld rehearsalCommitment (markDigest 1)) manifest

/-- The witness never read the provisional digest: swap in any OTHER activation
digest and the member survives verbatim.  This is what lets the node's world
preview supply the real one with no re-emit. -/
theorem the_member_witness_is_insensitive_to_the_activation_digest :
    rehearsalMemberUnderAnotherActivationDigest?.isSome = true := by
  native_decide

theorem the_rehearsal_draw_is_admitted : rehearsalActivation?.isSome = true := by
  native_decide

/-- ⚑ One watch settles on the authored table: four commands reach shift 1, one
logbook entry, sequence 4. -/
theorem one_watch_settles_on_the_authored_table :
    (rehearsalAfterWatch?.map fun state =>
      (state.shift, state.history.length, state.sequence, state.intents.length)) =
      some (1, 1, 4, 1) := by
  native_decide

/-- The table's role discipline has teeth: the pathfinder who claimed seat 0 cannot
take the engineer's coolant watch. -/
theorem the_wrong_role_is_refused_on_the_authored_table :
    (rehearsalActivation?.map fun activation =>
      match replay activation (initialState activation)
        [ { sequence := 0, nullifier := rehearsalNullifier 0
            action := .claimOfficer rehearsalPlayer ⟨0⟩ }
        , { sequence := 1, nullifier := rehearsalNullifier 1
            action := .chooseTask .engineSpine .coolantBalance } ] with
      | .error .roleMismatch => true
      | _ => false) = some true := by
  native_decide

/-- ⚑ The EXPORTED boundary accepts the final debrief of the authored watch — the
same bytes-in/bytes-out function `dregg_poa_night_watch_campaign_judge` will serve
once mounted. -/
theorem the_exported_judge_settles_the_authored_watch :
    (NightWatchCampaignWire.judgeJson (NightWatchCampaignWire.inputJson
      { world := rehearsalWorld
        manifest := rehearsalManifestBytes
        activation := rehearsalDraw
        history := rehearsalWatch.take 3
        command := { sequence := 3, nullifier := rehearsalNullifier 3
                     action := .debrief } })).isSome = true := by
  native_decide

/-- The fifth command: a fresh claim on the settled state. -/
def rehearsalSecondClaim? : Option State := do
  let activation ← rehearsalActivation?
  let after ← rehearsalAfterWatch?
  (judge activation after
    { sequence := 4, nullifier := rehearsalNullifier 4
      action := .claimOfficer rehearsalPlayer ⟨0⟩ }).toOption

/-- A fifth command under a fresh nullifier begins the NEXT watch — the campaign
continues past its first settlement, so `maxShifts = 24` is not decoration. -/
theorem a_second_watch_opens_after_the_first :
    rehearsalSecondClaim?.isSome = true := by
  native_decide

#assert_compiled the_authored_config_activates
#assert_compiled the_authored_config_round_trips
#assert_compiled the_authored_manifest_decodes
#assert_compiled the_authored_log_stream_is_a_valid_event_stream
#assert_compiled the_authored_world_admits_the_authored_config
#assert_compiled the_member_witness_is_insensitive_to_the_activation_digest
#assert_compiled the_rehearsal_draw_is_admitted
#assert_compiled one_watch_settles_on_the_authored_table
#assert_compiled the_wrong_role_is_refused_on_the_authored_table
#assert_compiled the_exported_judge_settles_the_authored_watch
#assert_compiled a_second_watch_opens_after_the_first
#assert_compiled the_session_tag_is_the_ascii_spelling
#assert_compiled every_derived_digest_computes
#assert_compiled federation_id_parses
#assert_compiled content_session_parses

end Dregg2.Games.PathOfAngels.NightWatchCampaignContent
