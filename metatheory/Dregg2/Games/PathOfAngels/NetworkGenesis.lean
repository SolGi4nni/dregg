/-
# Path of Angels — Lean-owned Signal authority-head genesis

`processNetworkGenesisWire` is the semantic half of the operator ceremony that
installs a `PoaSignalHeadV1`.  It accepts only one exact Lean-emitted Signal
configuration and a genuinely empty Canon/history image, then emits the exact
config and Canon JSON strings Rust is permitted to persist.

The external ceremony remains responsible for deployment-manifest/genesis
verification and detached curator-signature verification.  Lean deliberately
does not accept a signature-shaped value as if syntax implied authenticity.
The externally atomically verified tuple enters here together. Lean rederives
the deployment id and binds every identity that reaches game state to its exact
emission, but deliberately does not relabel external signature verification as
a Lean proof.
-/
import Dregg2.Games.PathOfAngels.NetworkGenesisWire

namespace Dregg2.Games.PathOfAngels.NetworkGenesis

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire
open Dregg2.Games.PathOfAngels.NetworkGenesisWire

set_option autoImplicit false

private def zeroDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

abbrev DEPLOYMENT_IDENTITY_DOMAIN : String := "POA-SIGNAL-DEPLOYMENT-IDENTITY-V2"
abbrev PRODUCTION_POLICY_SHA256 : String :=
  "8346263cf2fd50210353dca763dfb8f1271e1154e766ca93553ef3abc12a65ca"

private def expectedConfig (input : GenesisInputWire) : SignalTriangulation.Config :=
  Emit.signalConfig input.deployment.federationId input.content.sourceDigest
    input.content.signalContentDigest input.content.contentRoot input.content.activationDigest

private def expectedConfigWire (input : GenesisInputWire) : SignalConfigWire :=
  SignalConfigWire.ofSemantic (expectedConfig input)

private def expectedCanon (input : GenesisInputWire) : CanonState :=
  CanonState.empty input.deployment.federationId input.content.contentRoot
    input.content.activationDigest (expectedConfig input).mission.contentSession
    (expectedConfig input).mission.epoch input.content.curatorKey

private def emptyInitialState : InitialStateWire := {
  world := WorldStateWire.ofSemantic WorldState.empty
  known := []
  alpha := []
  superseded := []
  consumedRuns := []
  playerCounters := []
  canonRevision := 0
  curatorCounter := 0
  transitionCount := 0
  lastTransitionDigest := zeroDigest
}

/-- Structural protocol tags are checked inside Lean even though an external
verifier already parsed them.  A ceremony cannot silently feed a future schema
to a v1 semantic evaluator. -/
def protocolTagChecks (input : GenesisInputWire) : Bool :=
  decide (input.deployment.schema = DEPLOYMENT_SCHEMA) &&
  decide (input.deployment.deploymentDomain = DEPLOYMENT_DOMAIN) &&
  decide (input.content.signatureSchema = CONTENT_SIGNATURE_SCHEMA)

/-- Exact deployment-id preimage used by `scripts/poa-devnet-manifest.mjs`.
Digest spellings come from Lean's lowercase canonical encoder, not caller text. -/
def deploymentIdPreimage (input : GenesisInputWire) : String :=
  let nul := String.singleton (Char.ofNat 0)
  DEPLOYMENT_DOMAIN ++ nul ++ Emit.bytes32Hex input.deployment.federationId ++
    nul ++ Emit.bytes32Hex input.deployment.genesisSha256

/-- The persisted Signal deployment coordinate commits to the exact public
manifest bytes and immutable production policy as well as the public
genesis-derived deployment id. -/
def deploymentDigestPreimage (input : GenesisInputWire) : String :=
  let nul := String.singleton (Char.ofNat 0)
  DEPLOYMENT_IDENTITY_DOMAIN ++ nul ++ Emit.bytes32Hex input.deployment.deploymentId ++
    nul ++ Emit.bytes32Hex input.deployment.manifestSha256 ++
    nul ++ Emit.bytes32Hex input.deployment.policySha256

/-- Recompute the public deployment identity inside Lean. External verification
must still hash and validate the actual genesis bytes named by `genesisSha256`. -/
def deploymentBindingChecks (input : GenesisInputWire) : Bool :=
  decide (sha256Wire? (deploymentIdPreimage input) = some input.deployment.deploymentId) &&
  decide (Emit.bytes32Hex input.deployment.policySha256 = PRODUCTION_POLICY_SHA256) &&
  decide (sha256Wire? (deploymentDigestPreimage input) =
    some input.deployment.deploymentDigest)

/-- Zero is excluded for every externally verified 32-byte identity consumed by
this ceremony. This predicate is only a precondition on an externally and
atomically verified tuple; it is not signature, manifest, or genesis-byte
verification. The activation counter also retains room for a successor. -/
def nonzeroExternalIdentityChecks (input : GenesisInputWire) : Bool :=
  decide (input.deployment.deploymentId ≠ zeroDigest) &&
  decide (input.deployment.deploymentDigest ≠ zeroDigest) &&
  decide (input.deployment.federationId ≠ zeroDigest) &&
  decide (input.deployment.genesisSha256 ≠ zeroDigest) &&
  decide (input.deployment.manifestSha256 ≠ zeroDigest) &&
  decide (input.deployment.policySha256 ≠ zeroDigest) &&
  decide (input.content.manifestSha256 ≠ zeroDigest) &&
  decide (input.content.contentRoot ≠ zeroDigest) &&
  decide (input.content.activationDigest ≠ zeroDigest) &&
  decide (input.content.sourceDigest ≠ zeroDigest) &&
  decide (input.content.signalContentDigest ≠ zeroDigest) &&
  decide (input.content.curatorKey ≠ zeroDigest) &&
  decide (0 < input.content.activationCounter) &&
  decide (input.content.activationCounter < WIRE_NAT_LIMIT)

/-- The complete caller-supplied config must be the exact Signal config emitted
from the authenticated identities.  This is the tooth that refuses a
caller-chosen target, mission id, artifact, session, seed, budget, reward,
privacy grade, ballot regime, or relic policy. -/
def missionScopeChecks (input : GenesisInputWire) : Bool :=
  decide (input.content.contentEpoch = (expectedConfig input).mission.epoch.value) &&
  decide (input.config = expectedConfigWire input)

/-- Genesis means no prior world mutation, canon action, run receipt, player
counter, transition, or predecessor digest.  Empty sparse tables are canonical;
an explicit zero player row is refused earlier by the syntax decoder. -/
def zeroStateChecks (input : GenesisInputWire) : Bool :=
  decide (input.initial = emptyInitialState)

def genesisChecks (input : GenesisInputWire) : Bool :=
  protocolTagChecks input && deploymentBindingChecks input &&
    nonzeroExternalIdentityChecks input &&
    missionScopeChecks input && zeroStateChecks input

theorem genesisChecks_requires_exact_config {input : GenesisInputWire}
    (accepted : genesisChecks input = true) : input.config = expectedConfigWire input := by
  simp only [genesisChecks, Bool.and_eq_true] at accepted
  have missionAccepted := accepted.1.2
  simp only [missionScopeChecks, Bool.and_eq_true, decide_eq_true_eq] at missionAccepted
  exact missionAccepted.2

theorem genesisChecks_requires_empty_state {input : GenesisInputWire}
    (accepted : genesisChecks input = true) : input.initial = emptyInitialState := by
  simp only [genesisChecks, Bool.and_eq_true] at accepted
  have stateAccepted := accepted.2
  simpa [zeroStateChecks] using stateAccepted

theorem genesisChecks_requires_positive_activation_counter {input : GenesisInputWire}
    (accepted : genesisChecks input = true) : 0 < input.content.activationCounter := by
  simp only [genesisChecks, Bool.and_eq_true] at accepted
  have identityAccepted := accepted.1.1.2
  simp only [nonzeroExternalIdentityChecks, Bool.and_eq_true,
    decide_eq_true_eq] at identityAccepted
  exact identityAccepted.1.2

/-! ## Proof-carrying emission -/

/-- A value of this type can only be produced after the strict checks and exact
SHA/Canon encoders succeed.  Its output bytes are the authority image; the
semantic values are retained so later proofs do not reason from reparsed Rust
objects. -/
structure AuthorizedGenesis where
  input : GenesisInputWire
  config : SignalTriangulation.Config
  canon : CanonState
  output : GenesisOutputWire
  checks : genesisChecks input = true
  config_from_lean : config = expectedConfig input
  canon_from_lean : canon = expectedCanon input
  output_authority_exact : output.authorityId = input.deployment.federationId
  output_deployment_exact : output.deploymentDigest = input.deployment.deploymentDigest
  output_declared_deployment_exact :
    output.declaredDeploymentId = input.deployment.deploymentId
  output_deployment_genesis_exact :
    output.deploymentGenesisSha256 = input.deployment.genesisSha256
  output_deployment_manifest_exact :
    output.deploymentManifestSha256 = input.deployment.manifestSha256
  output_deployment_policy_exact :
    output.deploymentPolicySha256 = input.deployment.policySha256
  output_manifest_exact : output.manifestSha256 = input.content.manifestSha256
  output_content_root_exact : output.contentRoot = input.content.contentRoot
  output_activation_exact : output.activationDigest = input.content.activationDigest
  output_curator_exact : output.curatorKey = input.content.curatorKey
  output_epoch_exact : output.contentEpoch = input.content.contentEpoch
  output_activation_counter_exact :
    output.activationCounter = input.content.activationCounter
  output_config_exact : output.configJson = (SignalConfigWire.ofSemantic config).toJson
  output_canon_exact : output.canonJson = (CanonStateWire.ofSemantic canon).toJson
  output_hashes_exact :
    sha256Wire? output.configJson = some output.configSha256 ∧
      sha256Wire? output.canonJson = some output.canonSha256
  output_coordinates_exact :
    output.authorityLanes9 = faithfulLanes9 output.authorityId ∧
    output.deploymentLanes9 = faithfulLanes9 output.deploymentDigest ∧
    output.deploymentGenesisLanes9 = faithfulLanes9 output.deploymentGenesisSha256 ∧
    output.manifestLanes9 = faithfulLanes9 output.manifestSha256 ∧
    output.contentRootLanes9 = faithfulLanes9 output.contentRoot ∧
    output.activationLanes9 = faithfulLanes9 output.activationDigest ∧
    output.curatorKeyLanes9 = faithfulLanes9 output.curatorKey ∧
    output.configSha256Lanes9 = faithfulLanes9 output.configSha256 ∧
      output.canonSha256Lanes9 = faithfulLanes9 output.canonSha256
  output_has_no_history :
    output.transitionCount = 0 ∧ output.worldSequence = 0 ∧ output.canonRevision = 0 ∧
      output.lastTransitionDigest = zeroDigest
  output_is_canonical_syntax : decodeGenesisOutputSyntax output.toJson = some output

/-- Build the one allowed authority head.  Notice that output config and Canon
are projected from `config`/`canon`, not copied from the request. -/
def authorizeGenesis (input : GenesisInputWire) : Option AuthorizedGenesis := do
  if checked : genesisChecks input then
    let config := expectedConfig input
    let canon := expectedCanon input
    let canonWire := CanonStateWire.ofSemantic canon
    let configJson := (SignalConfigWire.ofSemantic config).toJson
    let canonJson := canonWire.toJson
    match configDigestEq : sha256Wire? configJson with
    | none => none
    | some configSha256 =>
      match canonDigestEq : sha256Wire? canonJson with
      | none => none
      | some canonSha256 =>
        let output : GenesisOutputWire := {
          authorityId := input.deployment.federationId
          deploymentDigest := input.deployment.deploymentDigest
          declaredDeploymentId := input.deployment.deploymentId
          deploymentGenesisSha256 := input.deployment.genesisSha256
          deploymentManifestSha256 := input.deployment.manifestSha256
          deploymentPolicySha256 := input.deployment.policySha256
          manifestSha256 := input.content.manifestSha256
          contentRoot := input.content.contentRoot
          activationDigest := input.content.activationDigest
          curatorKey := input.content.curatorKey
          contentEpoch := input.content.contentEpoch
          activationCounter := input.content.activationCounter
          transitionCount := 0
          worldSequence := canon.world.sequence
          canonRevision := canon.revision
          lastTransitionDigest := zeroDigest
          configJson
          canonJson
          configSha256
          canonSha256
          authorityLanes9 := faithfulLanes9 input.deployment.federationId
          deploymentLanes9 := faithfulLanes9 input.deployment.deploymentDigest
          deploymentGenesisLanes9 := faithfulLanes9 input.deployment.genesisSha256
          manifestLanes9 := faithfulLanes9 input.content.manifestSha256
          contentRootLanes9 := faithfulLanes9 input.content.contentRoot
          activationLanes9 := faithfulLanes9 input.content.activationDigest
          curatorKeyLanes9 := faithfulLanes9 input.content.curatorKey
          configSha256Lanes9 := faithfulLanes9 configSha256
          canonSha256Lanes9 := faithfulLanes9 canonSha256
        }
        if canonical : decodeGenesisOutputSyntax output.toJson = some output then
          some {
            input, config, canon, output
            checks := checked
            config_from_lean := rfl
            canon_from_lean := rfl
            output_authority_exact := rfl
            output_deployment_exact := rfl
            output_declared_deployment_exact := rfl
            output_deployment_genesis_exact := rfl
            output_deployment_manifest_exact := rfl
            output_deployment_policy_exact := rfl
            output_manifest_exact := rfl
            output_content_root_exact := rfl
            output_activation_exact := rfl
            output_curator_exact := rfl
            output_epoch_exact := rfl
            output_activation_counter_exact := rfl
            output_config_exact := rfl
            output_canon_exact := rfl
            output_hashes_exact := by
              constructor
              · exact configDigestEq
              · exact canonDigestEq
            output_coordinates_exact := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            output_has_no_history := ⟨rfl, rfl, rfl, rfl⟩
            output_is_canonical_syntax := canonical
          }
        else none
  else none

theorem AuthorizedGenesis.config_is_exact_emission (genesis : AuthorizedGenesis) :
    genesis.input.config = SignalConfigWire.ofSemantic genesis.config := by
  calc
    genesis.input.config = expectedConfigWire genesis.input :=
      genesisChecks_requires_exact_config genesis.checks
    _ = SignalConfigWire.ofSemantic (expectedConfig genesis.input) := rfl
    _ = SignalConfigWire.ofSemantic genesis.config :=
      congrArg SignalConfigWire.ofSemantic genesis.config_from_lean.symm

theorem AuthorizedGenesis.canon_is_empty (genesis : AuthorizedGenesis) :
    genesis.canon = CanonState.empty genesis.input.deployment.federationId
      genesis.input.content.contentRoot genesis.input.content.activationDigest
      genesis.config.mission.contentSession genesis.config.mission.epoch
      genesis.input.content.curatorKey := by
  rw [genesis.canon_from_lean, genesis.config_from_lean]
  rfl

theorem AuthorizedGenesis.persisted_coordinates_are_lean_bytes (genesis : AuthorizedGenesis) :
    genesis.output.authorityId = genesis.input.deployment.federationId ∧
    genesis.output.deploymentDigest = genesis.input.deployment.deploymentDigest ∧
    genesis.output.configJson = (SignalConfigWire.ofSemantic genesis.config).toJson ∧
    genesis.output.canonJson = (CanonStateWire.ofSemantic genesis.canon).toJson := by
  exact ⟨genesis.output_authority_exact, genesis.output_deployment_exact,
    genesis.output_config_exact, genesis.output_canon_exact⟩

/-! ## Validated output and canonical `String → String` authority evaluator -/

/-- Semantic output validation is exact authorized re-emission, not a second
partial checklist. This recomputes nested config/Canon bytes, both SHA-256
digests, all nine-lane coordinates, the external tuple bindings, and zero
history from the input and compares the complete output. -/
def validateGenesisOutput (input : GenesisInputWire) (output : GenesisOutputWire) : Bool :=
  match authorizeGenesis input with
  | some authorized => decide (output = authorized.output)
  | none => false

/-- Strictly decode both byte strings, authorize the input, and accept output
only when it is the exact complete Lean re-emission. By contrast,
`decodeGenesisOutputSyntax` establishes canonical syntax only. -/
def decodeValidatedGenesisOutput (inputBytes outputBytes : String) : Option GenesisOutputWire := do
  let input ← decodeGenesisInput inputBytes
  let output ← decodeGenesisOutputSyntax outputBytes
  if validateGenesisOutput input output then some output else none

def processNetworkGenesisWire (bytes : String) : Option String := do
  let input ← decodeGenesisInput bytes
  let genesis ← authorizeGenesis input
  some genesis.output.toJson

/-- Export-ready refusal convention: empty string means rejection.  The future
FFI shim must transport this result and persist its embedded JSON strings
verbatim; it must not recreate either object with serde/Rust game logic. -/
@[export dregg_poa_network_genesis]
def networkGenesisFFI (bytes : String) : String :=
  (processNetworkGenesisWire bytes).getD ""

/-! ## Live epoch-1 fixture and independently computed byte pins -/

private def digestOrZero (hex : String) : Digest32 :=
  (Emit.parseBytes32Hex? hex).getD zeroDigest

abbrev FIXTURE_DEPLOYMENT_ID : String :=
  "d933b11beb5adb502cc0511b8124c98192dbbed143ffbb1b5242ff6e0cf97c9e"
abbrev FIXTURE_DEPLOYMENT_DIGEST : String :=
  "5891c919acca76af3c553d157768d9f274b71610ed3b09bb09c954da2c7aa67e"
abbrev FIXTURE_FEDERATION_ID : String :=
  "4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a"
abbrev FIXTURE_GENESIS_SHA256 : String :=
  "5766736201a9ede62c79fe9beac04df8f8b5367feec5400c073fd631132bdb7f"
abbrev FIXTURE_DEPLOYMENT_MANIFEST_SHA256 : String :=
  "427a7a33ae19e450e2b9eb86453ac247b94d47725e29f8d470f0e9cad8073510"
abbrev FIXTURE_DEPLOYMENT_POLICY_SHA256 : String := PRODUCTION_POLICY_SHA256
abbrev FIXTURE_MANIFEST_SHA256 : String :=
  "c4f34a6ef639c532965ee5c05ec9bbbd7ac722ad7350f1825915bf67f0b69d2b"
abbrev FIXTURE_CONTENT_ROOT : String :=
  "679706a06ae8546a96b369a70dd7c5ee1c93fe47c789368087ab167c7b7dcebc"
abbrev FIXTURE_ACTIVATION_DIGEST : String :=
  "a7434b7a3cf936a09aa571ce2dab1b0b4d7856d079d6df5b05e1d05d425abcad"
abbrev FIXTURE_SOURCE_DIGEST : String :=
  "53bef5c67f9b73fcf9595a9547046f17ea6789a6876c44c85f01d3385129b42f"
abbrev FIXTURE_SIGNAL_DIGEST : String :=
  "c3a9603f84f1e5918c6a46f30c507a39b6c9d5fd57c9f3edec3b03597eec49bf"
abbrev FIXTURE_CURATOR_KEY : String :=
  "a3e630900af50a8701387c9ab528e3db23a5650c3e1ff3b4b3ee09aa42c65e23"
abbrev FIXTURE_CONFIG_SHA256 : String :=
  "09509f00ace2908a3fa06c641361255a752c30669da0874b87e8265f4f53a1bf"
abbrev FIXTURE_CANON_SHA256 : String :=
  "aad848fbf40d82d3efb1f6f5fe6ea1fb7704bccc839710f0202951ec4ebd667a"

def fixtureDeploymentId := digestOrZero FIXTURE_DEPLOYMENT_ID
def fixtureDeploymentDigest := digestOrZero FIXTURE_DEPLOYMENT_DIGEST
def fixtureFederationId := digestOrZero FIXTURE_FEDERATION_ID
def fixtureGenesisSha256 := digestOrZero FIXTURE_GENESIS_SHA256
def fixtureDeploymentManifestSha256 := digestOrZero FIXTURE_DEPLOYMENT_MANIFEST_SHA256
def fixtureDeploymentPolicySha256 := digestOrZero FIXTURE_DEPLOYMENT_POLICY_SHA256
def fixtureManifestSha256 := digestOrZero FIXTURE_MANIFEST_SHA256
def fixtureContentRoot := digestOrZero FIXTURE_CONTENT_ROOT
def fixtureActivationDigest := digestOrZero FIXTURE_ACTIVATION_DIGEST
def fixtureSourceDigest := digestOrZero FIXTURE_SOURCE_DIGEST
def fixtureSignalDigest := digestOrZero FIXTURE_SIGNAL_DIGEST
def fixtureCuratorKey := digestOrZero FIXTURE_CURATOR_KEY
def fixtureConfigSha256 := digestOrZero FIXTURE_CONFIG_SHA256
def fixtureCanonSha256 := digestOrZero FIXTURE_CANON_SHA256

def fixtureInput : GenesisInputWire := {
  deployment := {
    schema := DEPLOYMENT_SCHEMA
    deploymentDomain := DEPLOYMENT_DOMAIN
    deploymentId := fixtureDeploymentId
    deploymentDigest := fixtureDeploymentDigest
    federationId := fixtureFederationId
    genesisSha256 := fixtureGenesisSha256
    manifestSha256 := fixtureDeploymentManifestSha256
    policySha256 := fixtureDeploymentPolicySha256
  }
  content := {
    signatureSchema := CONTENT_SIGNATURE_SCHEMA
    manifestSha256 := fixtureManifestSha256
    contentRoot := fixtureContentRoot
    activationDigest := fixtureActivationDigest
    sourceDigest := fixtureSourceDigest
    signalContentDigest := fixtureSignalDigest
    curatorKey := fixtureCuratorKey
    contentEpoch := 1
    activationCounter := 2
  }
  config := SignalConfigWire.ofSemantic
    (Emit.signalConfig fixtureFederationId fixtureSourceDigest fixtureSignalDigest
      fixtureContentRoot fixtureActivationDigest)
  initial := emptyInitialState
}

def fixtureInputBytes : String := fixtureInput.toJson

def fixtureConfigJson : String := fixtureInput.config.toJson

def fixtureCanonJson : String :=
  (CanonStateWire.ofSemantic (expectedCanon fixtureInput)).toJson

theorem fixture_deployment_id_rederived :
    sha256Wire? (deploymentIdPreimage fixtureInput) = some fixtureDeploymentId := by
  native_decide

theorem fixture_input_roundtrip : decodeGenesisInput fixtureInputBytes = some fixtureInput := by
  native_decide

theorem fixture_checks_accept : genesisChecks fixtureInput = true := by
  native_decide

/-- These two SHA-256 values were independently computed over the printed exact
UTF-8 strings (Node `crypto.createHash("sha256")`) before being pinned here.
They are not derived from `sha256Wire?` or from the expected-output definition. -/
theorem fixture_config_sha256_external_pin :
    sha256Wire? fixtureConfigJson = some fixtureConfigSha256 := by
  native_decide

theorem fixture_canon_sha256_external_pin :
    sha256Wire? fixtureCanonJson = some fixtureCanonSha256 := by
  native_decide

theorem fixture_authorizes : (authorizeGenesis fixtureInput).isSome = true := by
  native_decide

theorem fixture_authorized_hashes :
    (authorizeGenesis fixtureInput).map
      (fun genesis => (genesis.output.configSha256, genesis.output.canonSha256)) =
      some (fixtureConfigSha256, fixtureCanonSha256) := by
  native_decide

theorem fixture_processes : (processNetworkGenesisWire fixtureInputBytes).isSome = true := by
  native_decide

theorem fixture_ffi_nonempty : networkGenesisFFI fixtureInputBytes ≠ "" := by
  native_decide

def fixtureOutputBytes : String := networkGenesisFFI fixtureInputBytes

theorem fixture_output_is_semantically_validated :
    (decodeValidatedGenesisOutput fixtureInputBytes fixtureOutputBytes).isSome = true := by
  native_decide

def fixtureTamperedOutputHash : String :=
  fixtureOutputBytes.replace FIXTURE_CONFIG_SHA256 FIXTURE_DEPLOYMENT_ID

/-- Canonical syntax is deliberately not authority: a correctly shaped output
with a substituted config hash parses, then fails exact authorized re-emission. -/
theorem fixture_tampered_output_is_syntax_only :
    (decodeGenesisOutputSyntax fixtureTamperedOutputHash).isSome = true ∧
      decodeValidatedGenesisOutput fixtureInputBytes fixtureTamperedOutputHash = none := by
  native_decide

/-! ## Hostile ceremony fixtures -/

def wrongRewardInput : GenesisInputWire := {
  fixtureInput with config := { fixtureInput.config with
    reward := { fixtureInput.config.reward with score := 501 } }
}

def wrongSessionInput : GenesisInputWire := {
  fixtureInput with config := { fixtureInput.config with mission := {
    fixtureInput.config.mission with contentSession := fixtureDeploymentId } }
}

def wrongFederationInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with federationId := fixtureDeploymentId }
}

def wrongDeploymentIdInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with deploymentId := fixtureContentRoot }
}

def wrongDeploymentDigestInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with deploymentDigest := fixtureContentRoot }
}

def wrongDeploymentManifestInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with manifestSha256 := fixtureContentRoot }
}

def wrongDeploymentPolicyInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with policySha256 := fixtureContentRoot }
}

def wrongGenesisShaInput : GenesisInputWire := {
  fixtureInput with deployment := {
    fixtureInput.deployment with genesisSha256 := fixtureManifestSha256 }
}

def wrongEpochInput : GenesisInputWire := {
  fixtureInput with content := { fixtureInput.content with contentEpoch := 2 }
}

def wrongContentRootInput : GenesisInputWire := {
  fixtureInput with content := {
    fixtureInput.content with contentRoot := fixtureDeploymentId }
}

def wrongActivationInput : GenesisInputWire := {
  fixtureInput with content := {
    fixtureInput.content with activationDigest := fixtureDeploymentId }
}

def zeroActivationCounterInput : GenesisInputWire := {
  fixtureInput with content := { fixtureInput.content with activationCounter := 0 }
}

def terminalActivationCounterInput : GenesisInputWire := {
  fixtureInput with content := {
    fixtureInput.content with activationCounter := WIRE_NAT_LIMIT }
}

def nonzeroWorldInput : GenesisInputWire := {
  fixtureInput with initial := { fixtureInput.initial with world := {
    fixtureInput.initial.world with intel := 1 } }
}

def nonzeroSequenceInput : GenesisInputWire := {
  fixtureInput with initial := { fixtureInput.initial with world := {
    fixtureInput.initial.world with sequence := 1 } }
}

def nonzeroRevisionInput : GenesisInputWire := {
  fixtureInput with initial := { fixtureInput.initial with canonRevision := 1 }
}

def nonzeroCuratorCounterInput : GenesisInputWire := {
  fixtureInput with initial := { fixtureInput.initial with curatorCounter := 1 }
}

def nonzeroTransitionInput : GenesisInputWire := {
  fixtureInput with initial := { fixtureInput.initial with transitionCount := 1 }
}

def nonzeroLastDigestInput : GenesisInputWire := {
  fixtureInput with initial := {
    fixtureInput.initial with lastTransitionDigest := fixtureDeploymentId }
}

def fixtureCounterRow : PlayerCounterRowWire := {
  federationId := fixtureFederationId
  contentSession := Emit.signalContentSession
  contentEpoch := 1
  playerKey := fixtureCuratorKey
  value := 1
}

def nonemptyCounterInput : GenesisInputWire := {
  fixtureInput with initial := {
    fixtureInput.initial with playerCounters := [fixtureCounterRow] }
}

def duplicateCounterInput : GenesisInputWire := {
  fixtureInput with initial := {
    fixtureInput.initial with playerCounters := [fixtureCounterRow, fixtureCounterRow] }
}

theorem caller_chosen_reward_refused :
    processNetworkGenesisWire wrongRewardInput.toJson = none := by native_decide

theorem inconsistent_content_session_refused :
    processNetworkGenesisWire wrongSessionInput.toJson = none := by native_decide

theorem inconsistent_federation_refused :
    processNetworkGenesisWire wrongFederationInput.toJson = none := by native_decide

theorem substituted_deployment_id_refused :
    processNetworkGenesisWire wrongDeploymentIdInput.toJson = none := by native_decide

theorem substituted_deployment_digest_refused :
    processNetworkGenesisWire wrongDeploymentDigestInput.toJson = none := by native_decide

theorem substituted_deployment_manifest_refused :
    processNetworkGenesisWire wrongDeploymentManifestInput.toJson = none := by native_decide

theorem substituted_deployment_policy_refused :
    processNetworkGenesisWire wrongDeploymentPolicyInput.toJson = none := by native_decide

theorem substituted_genesis_sha_refused :
    processNetworkGenesisWire wrongGenesisShaInput.toJson = none := by native_decide

theorem inconsistent_epoch_refused :
    processNetworkGenesisWire wrongEpochInput.toJson = none := by native_decide

theorem inconsistent_content_root_refused :
    processNetworkGenesisWire wrongContentRootInput.toJson = none := by native_decide

theorem inconsistent_activation_refused :
    processNetworkGenesisWire wrongActivationInput.toJson = none := by native_decide

theorem zero_activation_counter_refused :
    processNetworkGenesisWire zeroActivationCounterInput.toJson = none := by native_decide

theorem terminal_activation_counter_refused :
    processNetworkGenesisWire terminalActivationCounterInput.toJson = none := by native_decide

theorem nonzero_genesis_world_refused :
    processNetworkGenesisWire nonzeroWorldInput.toJson = none := by native_decide

theorem nonzero_genesis_sequence_refused :
    processNetworkGenesisWire nonzeroSequenceInput.toJson = none := by native_decide

theorem nonzero_genesis_revision_refused :
    processNetworkGenesisWire nonzeroRevisionInput.toJson = none := by native_decide

theorem nonzero_genesis_curator_counter_refused :
    processNetworkGenesisWire nonzeroCuratorCounterInput.toJson = none := by native_decide

theorem nonzero_genesis_transition_refused :
    processNetworkGenesisWire nonzeroTransitionInput.toJson = none := by native_decide

theorem nonzero_genesis_last_digest_refused :
    processNetworkGenesisWire nonzeroLastDigestInput.toJson = none := by native_decide

theorem nonempty_player_counter_refused :
    processNetworkGenesisWire nonemptyCounterInput.toJson = none := by native_decide

theorem duplicate_player_counter_refused_by_syntax :
    decodeGenesisInput duplicateCounterInput.toJson = none := by native_decide

theorem trailing_bytes_refused :
    processNetworkGenesisWire (fixtureInputBytes ++ "\n") = none := by native_decide

theorem uppercase_digest_refused :
    processNetworkGenesisWire
      (fixtureInputBytes.replace FIXTURE_FEDERATION_ID (String.toUpper FIXTURE_FEDERATION_ID)) =
      none := by native_decide

theorem unknown_top_level_field_refused :
    processNetworkGenesisWire
      (fixtureInputBytes.replace
        ("{\"format\":\"" ++ NetworkGenesisWire.INPUT_FORMAT ++ "\"")
        ("{\"format\":\"" ++ NetworkGenesisWire.INPUT_FORMAT ++ "\",\"unknown\":0")) = none := by
  native_decide

#assert_axioms genesisChecks_requires_exact_config
#assert_axioms genesisChecks_requires_empty_state
#assert_axioms genesisChecks_requires_positive_activation_counter
#assert_axioms AuthorizedGenesis.config_is_exact_emission
#assert_axioms AuthorizedGenesis.canon_is_empty
#assert_axioms AuthorizedGenesis.persisted_coordinates_are_lean_bytes

#assert_compiled fixture_deployment_id_rederived
#assert_compiled fixture_input_roundtrip
#assert_compiled fixture_checks_accept
#assert_compiled fixture_config_sha256_external_pin
#assert_compiled fixture_canon_sha256_external_pin
#assert_compiled fixture_authorizes
#assert_compiled fixture_authorized_hashes
#assert_compiled fixture_processes
#assert_compiled fixture_ffi_nonempty
#assert_compiled fixture_output_is_semantically_validated
#assert_compiled fixture_tampered_output_is_syntax_only
#assert_compiled caller_chosen_reward_refused
#assert_compiled inconsistent_content_session_refused
#assert_compiled inconsistent_federation_refused
#assert_compiled substituted_deployment_id_refused
#assert_compiled substituted_deployment_digest_refused
#assert_compiled substituted_deployment_manifest_refused
#assert_compiled substituted_deployment_policy_refused
#assert_compiled substituted_genesis_sha_refused
#assert_compiled inconsistent_epoch_refused
#assert_compiled inconsistent_content_root_refused
#assert_compiled inconsistent_activation_refused
#assert_compiled zero_activation_counter_refused
#assert_compiled terminal_activation_counter_refused
#assert_compiled nonzero_genesis_world_refused
#assert_compiled nonzero_genesis_sequence_refused
#assert_compiled nonzero_genesis_revision_refused
#assert_compiled nonzero_genesis_curator_counter_refused
#assert_compiled nonzero_genesis_transition_refused
#assert_compiled nonzero_genesis_last_digest_refused
#assert_compiled nonempty_player_counter_refused
#assert_compiled duplicate_player_counter_refused_by_syntax
#assert_compiled trailing_bytes_refused
#assert_compiled uppercase_digest_refused
#assert_compiled unknown_top_level_field_refused

end Dregg2.Games.PathOfAngels.NetworkGenesis
