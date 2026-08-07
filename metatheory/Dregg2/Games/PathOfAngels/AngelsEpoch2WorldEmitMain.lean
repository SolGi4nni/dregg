/-
# Epoch-2 multiplexed-world emit driver

Renders the ONE epoch-2 activated-content manifest that carries BOTH organs — the
galley policy component and the night-watch campaign config component — from
`AngelsEpoch2World`, plus the provenance file and the rehearsal fixtures the native
persistence test replays.

There is no second encoder anywhere in this path.  The galley bytes come out of
`GalleyMaintenanceDailyRuntime.PolicyWire.toJson`, the config bytes out of
`NightWatchCampaignAdmission.configJson`, and the manifest out of
`ActivatedContent.Manifest.toJson` — the same three functions the admission seam
re-encodes against.  The only thing this driver can do wrong is refuse.

## Fail-closed, and what it checks BEFORE anything is written

1. the module's `galleyEpoch1PolicyBytes` literal is byte-identical to the
   `poa.galley-maintenance-daily.policy.v1` component inside
   `poa/artifacts/galley/epoch-1/manifest.json`;
2. the module's `SHIPPED_SLOT_COMMITMENT_HEX` is the `slot_commitment` inside
   `poa/artifacts/night-watch/epoch-1/manifest.json`'s config component;
3. `NightWatchCampaignContent.authoredRaw` at that commitment re-encodes to exactly
   those on-disk epoch-1 config bytes — so the epoch-2 config really is the shipped
   epoch-1 campaign with two fields moved, not a re-authoring;
4. the carried galley policy differs from the shipped one in `content_epoch` ALONE;
5. the carried config differs in `progression.content_session` / `.content_epoch` ALONE;
6. both organs authorize under the ONE derived world, from the ONE decoded manifest;
7. the DEPLOYED export (`ActivatedContentRuntime.authorize?`, which persistence calls
   as `dregg_poa_activated_content_authorize`) accepts;
8. the single-component night-watch-only epoch-2 manifest is REFUSED by that same
   export — the eviction, exhibited rather than described.

Any refusal and no file moves.

## ⚠ No secret is read, and none is needed

The slot commitment is CARRIED from the epoch-1 artifact.  `HiddenInstance.commit`
depends on `(secret, slot)` only, so the curator's existing repository-external secret
still opens it — while `missionContextOf` folds the progression's session and epoch
into every run seed, so no epoch-1 schedule transfers.  This driver therefore needs no
`POA_NIGHT_WATCH_SECRET_FILE`, unlike the epoch-1 one, and it cannot echo a secret it
never reads.  A curator who prefers a fresh draw runs the epoch-1 driver's ceremony
instead and re-signs against the new `content_root`.

## Modes

    emit  (default)     write the epoch-2 artifacts and the rehearsal fixtures
    check               re-derive and refuse on any drift; writes nothing

Output dirs: `POA_EPOCH2_OUT` (default `poa/artifacts/angels-epoch-2`) and
`POA_EPOCH2_FIXTURE_OUT` (default `persist/tests/fixtures/angels-epoch-2-rehearsal`),
both relative to the working directory — run from the repository root.
-/
import Dregg2.Games.PathOfAngels.AngelsEpoch2World

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NightWatchCampaign
open Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission
open Dregg2.Games.PathOfAngels.NightWatchCampaignContent
open Dregg2.Games.PathOfAngels.AngelsEpoch2World

set_option autoImplicit false
set_option maxRecDepth 100000

def refuse {α : Type} (what : String) : IO α :=
  throw (IO.userError s!"REFUSED: {what}")

def require (what : String) : Bool → IO Unit
  | true => pure ()
  | false => refuse what

def writeAtomic (path : System.FilePath) (contents : String) : IO Unit := do
  let staged := System.FilePath.mk (path.toString ++ ".partial")
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

/-- Pull one component's exact `bytes_utf8` out of a shipped manifest file. -/
def componentBytesOf (manifestText componentName : String) : IO String := do
  let .ok json := Json.parse manifestText
    | refuse "a shipped epoch-1 manifest does not parse"
  let .ok components := json.getObjVal? "components" >>= Json.getArr?
    | refuse "a shipped epoch-1 manifest has no components array"
  for component in components do
    match component.getObjValAs? String "name", component.getObjValAs? String "bytes_utf8" with
    | .ok name, .ok bytes => if name == componentName then return bytes
    | _, _ => pure ()
  refuse s!"the shipped epoch-1 manifest carries no `{componentName}` component"

structure Emission where
  galleyBytes : String
  configBytes : String
  manifestBytes : String
  root : Digest32
  galleySha : Digest32
  configSha : Digest32
  rehearsalManifestBytes : String
  rehearsalRoot : Digest32
  rehearsalJudgeInput : String
  rehearsalSingleComponentBytes : String

/-- Every gate between the shipped epoch-1 artifacts and a written epoch-2 file. -/
def verifyChain : IO Emission := do
  let galleyManifestText ← IO.FS.readFile
    (System.FilePath.mk "poa/artifacts/galley/epoch-1/manifest.json")
  let campaignManifestText ← IO.FS.readFile
    (System.FilePath.mk "poa/artifacts/night-watch/epoch-1/manifest.json")

  let shippedGalleyBytes ←
    componentBytesOf galleyManifestText ActivatedContent.GALLEY_POLICY_COMPONENT
  let shippedConfigBytes ← componentBytesOf campaignManifestText CONFIG_COMPONENT

  require "the module's galley literal is not the shipped epoch-1 component bytes"
    (galleyEpoch1PolicyBytes == shippedGalleyBytes)
  let some shippedPolicy := GalleyMaintenanceDailyRuntime.decodePolicy galleyEpoch1PolicyBytes
    | refuse "the shipped galley policy does not decode canonically"
  require "the shipped galley policy is not at content epoch 1"
    (shippedPolicy.contentEpoch == 1)

  let some shippedConfig := decodeConfig shippedConfigBytes
    | refuse "the shipped night-watch config does not decode canonically"
  require "the module's shipped commitment is not the on-disk one"
    (shippedSlotCommitment == shippedConfig.slotCommitment)
  require "`authoredRaw` at the on-disk commitment is not the on-disk epoch-1 config"
    (shippedRaw == shippedConfig)
  require "the shipped commitment is the published rehearsal one and is not deployable"
    (shippedSlotCommitment != rehearsalCommitment)

  -- The two carries, on the actual shipped values.
  require "the carried galley policy moved more than its epoch"
    (({ carryGalleyPolicy shippedPolicy with contentEpoch := shippedPolicy.contentEpoch }
        == shippedPolicy) && (carryGalleyPolicy shippedPolicy).contentEpoch == AngelsEpoch2World.CONTENT_EPOCH)
  require "the carried config moved more than its session and epoch"
    ((({ carryCampaignConfig shippedRaw with progression := shippedRaw.progression }
         == shippedRaw)
      && ({ (carryCampaignConfig shippedRaw).progression with
              contentSession := shippedRaw.progression.contentSession
              contentEpoch := shippedRaw.progression.contentEpoch }
            == shippedRaw.progression)))

  let some galleyComponent := galleyComponent? galleyEpoch1PolicyBytes
    | refuse "the carried galley component did not build"
  let some campaignComponent := campaignComponent? shippedRaw
    | refuse "the carried campaign component did not build"
  let some built := manifest? galleyEpoch1PolicyBytes shippedRaw
    | refuse "the multiplexed manifest did not build"
  let manifestBytes := built.toJson
  let some _ := ActivatedContent.decodeManifest manifestBytes
    | refuse "the multiplexed manifest does not decode canonically"
  let some root := ActivatedContent.manifestRoot? built
    | refuse "the multiplexed manifest root did not compute"
  let some worldId := world? galleyEpoch1PolicyBytes shippedRaw provisionalActivationDigest
    | refuse "the epoch-2 world did not build"

  require "the epoch-2 world does not serve BOTH organs"
    (bothOrgans? galleyEpoch1PolicyBytes shippedRaw provisionalActivationDigest).isSome
  require "the deployed activated-content export refuses the multiplexed manifest"
    (ActivatedContentRuntime.authorize? { world := worldId, manifestJson := manifestBytes }).isSome

  -- The eviction, exhibited: the single-component epoch-2 world.
  require "the single-component epoch-2 world did not evict the galley"
    (campaignOnlyVerdict? shippedRaw provisionalActivationDigest == some (true, false, false))

  -- The rehearsal fixtures the native replay test consumes.  Published instance only.
  let some rehearsalBuilt := manifest? galleyEpoch1PolicyBytes rehearsalEpoch2Raw
    | refuse "the rehearsal multiplexed manifest did not build"
  let rehearsalManifestBytes := rehearsalBuilt.toJson
  let some rehearsalRoot := ActivatedContent.manifestRoot? rehearsalBuilt
    | refuse "the rehearsal manifest root did not compute"
  let some judgeInput := rehearsalEpoch2JudgeInput?
    | refuse "the rehearsal judge input did not build"
  let judgeInputBytes := NightWatchCampaignWire.inputJson judgeInput
  require "the exported judge refuses the rehearsal epoch-2 debrief"
    (NightWatchCampaignWire.judgeJson judgeInputBytes).isSome

  -- The single-component world the native replay test exhibits the eviction with.
  let some singleComponent := campaignOnlyManifest? rehearsalEpoch2Raw
    | refuse "the single-component epoch-2 manifest did not build"
  let singleComponentBytes := singleComponent.toJson
  require "the single-component rehearsal world did not evict the galley"
    (campaignOnlyVerdict? rehearsalEpoch2Raw provisionalActivationDigest
      == some (true, false, false))

  pure {
    galleyBytes := galleyComponent.bytesUtf8
    configBytes := campaignComponent.bytesUtf8
    manifestBytes := manifestBytes
    root := root
    galleySha := galleyComponent.sha256
    configSha := campaignComponent.sha256
    rehearsalManifestBytes := rehearsalManifestBytes
    rehearsalRoot := rehearsalRoot
    rehearsalJudgeInput := judgeInputBytes
    rehearsalSingleComponentBytes := singleComponentBytes }

/-! ## Provenance -/

def q (value : String) : String := String.quote value

def provenanceJson (emission : Emission) : String :=
  "{\n" ++
  "  \"schema\": \"POA-ANGELS-EPOCH-2-MULTIPLEXED-WORLD-PROVENANCE-V1\",\n" ++
  "  \"note\": \"Provenance only. ONE epoch-2 world carrying BOTH organs, so mounting the night watch does not evict the galley (persist/src/poa_world_activation.rs:23 keeps exactly one active head). The world identity the curator signs is emitted by `dregg-node poa-galley-world-preview`, which supplies the real activation_digest from the epoch-2 POAG1 content-epoch envelope; neither Manifest.matchesWorldB nor authorizeCampaignConfigForWorld? reads it. The slot secret behind slot_commitment is curator-held, lives outside every repository, and is CARRIED from epoch 1 unchanged.\",\n" ++
  "  \"deployment_id\": " ++ q DEPLOYMENT_ID_HEX ++ ",\n" ++
  "  \"federation_id\": " ++ q FEDERATION_ID_HEX ++ ",\n" ++
  "  \"content_session\": " ++ q AngelsEpoch2World.CONTENT_SESSION_HEX ++ ",\n" ++
  "  \"content_session_ascii_tag\": " ++ q AngelsEpoch2World.CONTENT_SESSION_TAG ++ ",\n" ++
  "  \"content_epoch\": " ++ toString AngelsEpoch2World.CONTENT_EPOCH ++ ",\n" ++
  "  \"content_root\": " ++ q (Emit.bytes32Hex emission.root) ++ ",\n" ++
  "  \"activation_digest\": null,\n" ++
  "  \"activation_digest_note\": \"Supplied at install by `dregg-node poa-galley-world-preview` from the epoch-2 POAG1 content-epoch envelope. The member witnesses are insensitive to it (the_members_are_insensitive_to_the_activation_digest), so it needs no re-emit.\",\n" ++
  "  \"components\": [\n" ++
  "    {\"name\": " ++ q ActivatedContent.GALLEY_POLICY_COMPONENT ++
  ", \"sha256\": " ++ q (Emit.bytes32Hex emission.galleySha) ++
  ", \"carried_from\": \"poa/artifacts/galley/epoch-1/manifest.json\"" ++
  ", \"fields_changed\": [\"content_epoch\"]},\n" ++
  "    {\"name\": " ++ q CONFIG_COMPONENT ++
  ", \"sha256\": " ++ q (Emit.bytes32Hex emission.configSha) ++
  ", \"carried_from\": \"poa/artifacts/night-watch/epoch-1/manifest.json\"" ++
  ", \"fields_changed\": [\"progression.content_session\", \"progression.content_epoch\"]}\n" ++
  "  ],\n" ++
  "  \"slot\": " ++ toString AUTHORED_SLOT ++ ",\n" ++
  "  \"slot_commitment\": " ++ q SHIPPED_SLOT_COMMITMENT_HEX ++ ",\n" ++
  "  \"slot_commitment_note\": \"CARRIED from epoch 1. HiddenInstance.commit reads (secret, slot) only, so the curator's existing off-repository secret still opens it; missionContextOf folds the progression session and epoch into every run seed, so no epoch-1 schedule transfers (the_epoch2_run_seed_is_not_the_epoch1_run_seed).\",\n" ++
  "  \"derived_digest_note\": \"Every derived-label digest in BOTH components is the EPOCH-1 derivation, carried deliberately: the galley daily and the night-watch logbook are the same daily and the same logbook. Recompute them with `1`, not `2`, in the preimage. Re-running scripts/poa-galley-content.py with CONTENT_EPOCH = 2 would derive a DIFFERENT daily_id and start a different daily; that is not what this is.\",\n" ++
  "  \"predecessor\": {\n" ++
  "    \"world\": \"poa/artifacts/galley/epoch-1/world.json\",\n" ++
  "    \"content_epoch\": 1,\n" ++
  "    \"note\": \"The signed activation must be counter = (epoch-1 counter + 1), kind advance, predecessor_head = SHA-256 of the epoch-1 signed envelope, same federation_id.\"\n" ++
  "  }\n" ++
  "}\n"

/-! ## Modes -/

def outDir : IO System.FilePath := do
  pure (System.FilePath.mk ((← IO.getEnv "POA_EPOCH2_OUT").getD "poa/artifacts/angels-epoch-2"))

def fixtureDir : IO System.FilePath := do
  pure (System.FilePath.mk ((← IO.getEnv "POA_EPOCH2_FIXTURE_OUT").getD
    "persist/tests/fixtures/angels-epoch-2-rehearsal"))

def emitMode : IO Unit := do
  let emission ← verifyChain
  let dir ← outDir
  IO.FS.createDirAll dir
  writeAtomic (dir / "galley-policy.json") emission.galleyBytes
  writeAtomic (dir / "night-watch-config.json") emission.configBytes
  writeAtomic (dir / "manifest.json") emission.manifestBytes
  writeAtomic (dir / "world.json") (provenanceJson emission)
  let fixtures ← fixtureDir
  IO.FS.createDirAll fixtures
  writeAtomic (fixtures / "manifest.json") emission.rehearsalManifestBytes
  writeAtomic (fixtures / "night-watch-judge-input.json") emission.rehearsalJudgeInput
  writeAtomic (fixtures / "single-component-manifest.json") emission.rehearsalSingleComponentBytes
  IO.println s!"wrote {dir}/manifest.json ({emission.manifestBytes.utf8ByteSize} bytes)"
  IO.println s!"content_root   = {Emit.bytes32Hex emission.root}"
  IO.println s!"galley_sha256  = {Emit.bytes32Hex emission.galleySha}"
  IO.println s!"config_sha256  = {Emit.bytes32Hex emission.configSha}"
  IO.println s!"content_session= {AngelsEpoch2World.CONTENT_SESSION_HEX} ({AngelsEpoch2World.CONTENT_SESSION_TAG})"
  IO.println s!"wrote {fixtures}/manifest.json (REHEARSAL instance, published secret)"
  IO.println s!"rehearsal_root = {Emit.bytes32Hex emission.rehearsalRoot}"

def requireFile (path : System.FilePath) (expected : String) (label : String) : IO Unit := do
  let actual ← IO.FS.readFile path
  require s!"on-disk {label} drifted" (actual == expected)

def checkMode : IO Unit := do
  let emission ← verifyChain
  let dir ← outDir
  requireFile (dir / "galley-policy.json") emission.galleyBytes "galley-policy.json"
  requireFile (dir / "night-watch-config.json") emission.configBytes "night-watch-config.json"
  requireFile (dir / "manifest.json") emission.manifestBytes "manifest.json"
  requireFile (dir / "world.json") (provenanceJson emission) "world.json"
  let fixtures ← fixtureDir
  requireFile (fixtures / "manifest.json") emission.rehearsalManifestBytes "rehearsal manifest.json"
  requireFile (fixtures / "night-watch-judge-input.json") emission.rehearsalJudgeInput
    "rehearsal night-watch-judge-input.json"
  requireFile (fixtures / "single-component-manifest.json")
    emission.rehearsalSingleComponentBytes "rehearsal single-component-manifest.json"
  IO.println "poa epoch-2 multiplexed-world artifacts are byte-exact"

def main : IO Unit := do
  match (← IO.getEnv "POA_EPOCH2_MODE").getD "emit" with
  | "emit" => emitMode
  | "check" => checkMode
  | other => refuse s!"unknown POA_EPOCH2_MODE `{other}`"
