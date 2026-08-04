/-
# Path of Angels — Dark Bazaar v1 network judge

The exported evaluator is one fail-closed composition: strict canonical decode,
proof-carrying public-state reconstruction, concrete N=4/K=4 private descriptor
authorization, PoA admission/accounting, exact public successor reconstruction,
and labelled Lean-computed receipt digests.  The private opening is consumed by
the judge and absent from output.
-/
import Dregg2.Games.PathOfAngels.DarkBazaarJudgeWire

namespace Dregg2.Games.PathOfAngels.DarkBazaarJudge

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DarkBazaar
open Dregg2.Games.PathOfAngels.DarkBazaarJudgeWire

set_option autoImplicit false

structure Settlement where
  inputBytes : String
  input : SemanticInput
  evidence : VerifiedSettlementEvidence input.claim
  successor : BazaarState
  applied : applySettlement input.claim evidence input.state = some successor
  successorWire : StateWire
  successorSemantic : BazaarState
  successorWireDecodes : successorWire.toSemantic? = some successorSemantic
  successorExact : observeState successorSemantic = observeState successor

def settle (inputBytes : String) (input : SemanticInput) : Option Settlement := do
  let evidence ← verifyV1? input.claim input.root input.witness
  match applied : applySettlement input.claim evidence input.state with
  | none => none
  | some successor =>
      let successorWire := input.wire.state.successorCandidate input.wire.claim
      match decoded : successorWire.toSemantic? with
      | none => none
      | some successorSemantic =>
          if exact : observeState successorSemantic = observeState successor then
            some {
              inputBytes
              input
              evidence
              successor
              applied
              successorWire
              successorSemantic
              successorWireDecodes := decoded
              successorExact := exact
            }
          else none

def Settlement.output (settlement : Settlement) : OutputWire :=
  OutputWire.ofTransition settlement.inputBytes settlement.input.wire settlement.successorWire

def canonicalOutput? (output : OutputWire) : Option OutputWire :=
  if decodeOutput output.toJson = some output then some output else none

def process (bytes : String) : Option OutputWire := do
  let wire ← decodeInput bytes
  let input ← wire.toSemantic?
  let settlement ← settle bytes input
  canonicalOutput? settlement.output

def processWire (bytes : String) : Option String :=
  (process bytes).map OutputWire.toJson

/-- Empty is the sole semantic-refusal sentinel.  No Rust semantic twin or
caller-supplied authorization bit exists behind this export. -/
@[export dregg_poa_dark_bazaar_judge]
def darkBazaarJudgeFFI (bytes : String) : String :=
  (processWire bytes).getD ""

theorem darkBazaarJudgeFFI_success_iff {inputBytes outputBytes : String}
    (output_nonempty : outputBytes ≠ "") :
    darkBazaarJudgeFFI inputBytes = outputBytes ↔
      processWire inputBytes = some outputBytes := by
  cases processed : processWire inputBytes with
  | none =>
      constructor
      · intro accepted
        have empty : "" = outputBytes := by
          simpa [darkBazaarJudgeFFI, processed] using accepted
        exact (output_nonempty empty.symm).elim
      · intro accepted
        contradiction
  | some output => simp [darkBazaarJudgeFFI, processed]

theorem process_output_decodes {inputBytes : String} {output : OutputWire}
    (accepted : process inputBytes = some output) :
    decodeOutput output.toJson = some output := by
  cases hwire : decodeInput inputBytes with
  | none => simp [process, hwire] at accepted
  | some wire =>
      cases hsemantic : wire.toSemantic? with
      | none => simp [process, hwire, hsemantic] at accepted
      | some input =>
          cases hsettle : settle inputBytes input with
          | none => simp [process, hwire, hsemantic, hsettle] at accepted
          | some settlement =>
              by_cases hdecode :
                  decodeOutput settlement.output.toJson = some settlement.output
              · simp [process, hwire, hsemantic, hsettle, canonicalOutput?, hdecode] at accepted
                cases accepted
                exact hdecode
              · simp [process, hwire, hsemantic, hsettle, canonicalOutput?, hdecode] at accepted

/-! ## Complete executable fixture -/

private def repeatedDigest (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by decide)⟩
  length_eq := by simp

def fixtureFederation : Digest32 := repeatedDigest 1
def fixtureContentRoot : Digest32 := repeatedDigest 2
def fixtureActivation : Digest32 := repeatedDigest 3
def fixtureSession : Digest32 := repeatedDigest 4
def fixtureSeller : Digest32 := repeatedDigest 17
def fixtureBuyer : Digest32 := repeatedDigest 34
def fixtureSourceRoot : Digest32 := repeatedDigest 51
def fixtureBaseNullifier : Digest32 := repeatedDigest 113
def fixtureQuoteNullifier : Digest32 := repeatedDigest 114

def fixtureIdentity : IdentityWire where
  federationId := fixtureFederation
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivation
  contentSession := fixtureSession
  contentEpoch := 1
  seller := fixtureSeller
  buyer := fixtureBuyer
  baseAsset := { kind := "supplies", relicId := 0 }
  quoteAsset := { kind := "intel", relicId := 0 }

def fixtureOutput : ClearingOutputWire := ⟨1, 13⟩

def fixturePolicy : PolicyWire where
  buckets := 4
  quoteTick := 2
  maxOrders := 4
  maxOrderQuantity := 15
  maxPublicAssetInputs := 8
  allowedOutputs := [fixtureOutput]

def fixtureDescriptorRoot : Fin 8 → Int :=
  V1.hash8
    (Market.DarkBazaarPrivateDescriptor.rootPreimage V1.DESCRIPTOR_SESSION
      Market.DarkBazaarPrivateDescriptor.fixtureWitness)

def fixtureCommitment : Digest32 := V1.digestOfRoot fixtureDescriptorRoot

def fixtureOrderNullifiers : List Digest32 :=
  ((List.ofFn fun slot : Fin 4 =>
      (V1.orderId fixtureDescriptorRoot slot).nullifier.value).eraseDups).insertionSort
    (fun left right => Emit.bytes32Hex left < Emit.bytes32Hex right)

def fixtureBaseInput : AssetInputWire where
  nullifier := fixtureBaseNullifier
  owner := fixtureSeller
  asset := { kind := "supplies", relicId := 0 }
  amount := 13

def fixtureQuoteInput : AssetInputWire where
  nullifier := fixtureQuoteNullifier
  owner := fixtureBuyer
  asset := { kind := "intel", relicId := 0 }
  amount := 52

def fixtureClaim : ClaimWire where
  spec := {
    identity := fixtureIdentity
    batchId := 7
    sourceRoot := fixtureSourceRoot
    policy := fixturePolicy
  }
  privateBookCommitment := fixtureCommitment
  output := fixtureOutput
  baseInputs := [fixtureBaseInput]
  quoteInputs := [fixtureQuoteInput]
  orderNullifiers := fixtureOrderNullifiers

def fixtureState : StateWire where
  identity := fixtureIdentity
  policy := fixturePolicy
  baseNotes := [fixtureBaseInput]
  quoteNotes := [fixtureQuoteInput]
  buyerBaseCustody := 0
  sellerQuoteCustody := 0
  consumedAssetNullifiers := []
  consumedOrderNullifiers := []
  consumedBatches := []

def fixtureOpening : OpeningWire where
  format := AUTHORIZATION_FORMAT
  orders := [⟨2, 10⟩, ⟨1, 6⟩, ⟨4, 5⟩, ⟨5, 8⟩]
  blinding := [777, 778, 779, 780, 781, 782, 783, 784]

def fixtureInput : InputWire where
  state := fixtureState
  claim := fixtureClaim
  opening := fixtureOpening

def fixtureInputBytes : String := fixtureInput.toJson
def fixtureExpectedOutput : OutputWire :=
  OutputWire.ofTransition fixtureInputBytes fixtureInput
    (fixtureState.successorCandidate fixtureClaim)
def fixtureOutputBytes : String := fixtureExpectedOutput.toJson

theorem fixture_input_roundtrip : decodeInput fixtureInputBytes = some fixtureInput := by
  native_decide

theorem fixture_semantic_inhabited : fixtureInput.toSemantic?.isSome = true := by
  native_decide

theorem fixture_process_success : processWire fixtureInputBytes = some fixtureOutputBytes := by
  native_decide

theorem fixture_trailing_byte_refused : processWire (fixtureInputBytes ++ "\n") = none := by
  native_decide

def fixtureUnknownFieldBytes : String :=
  fixtureInputBytes.replace "\"opening\":" "\"unknown\":0,\"opening\":"

theorem fixture_unknown_field_refused : processWire fixtureUnknownFieldBytes = none := by
  native_decide

def fixtureUppercaseDigestBytes : String :=
  fixtureInputBytes.replace
    "e0a5c50385fa3b60e5ed0433b4c7075201b0b473b6afc4591d98ed7182d5102e"
    "E0a5c50385fa3b60e5ed0433b4c7075201b0b473b6afc4591d98ed7182d5102e"

theorem fixture_uppercase_digest_refused : processWire fixtureUppercaseDigestBytes = none := by
  native_decide

def fixtureReorderedNullifiers : InputWire :=
  { fixtureInput with claim := {
      fixtureInput.claim with orderNullifiers := fixtureInput.claim.orderNullifiers.reverse
    } }

theorem fixture_reordered_nullifiers_refused :
    processWire fixtureReorderedNullifiers.toJson = none := by
  native_decide

def fixtureOverboundOutput : InputWire :=
  { fixtureInput with claim := { fixtureInput.claim with output :=
      ⟨fixtureInput.claim.output.bucket, DarkBazaar.Wire.maxOutputVolume + 1⟩ } }

theorem fixture_overbound_output_refused : processWire fixtureOverboundOutput.toJson = none := by
  native_decide

def fixtureWrongOutput : InputWire :=
  { fixtureInput with claim := { fixtureInput.claim with output := ⟨2, 13⟩ } }

theorem fixture_wrong_clearing_refused : processWire fixtureWrongOutput.toJson = none := by
  native_decide

def fixtureWrongNullifiers : InputWire :=
  { fixtureInput with claim := {
      fixtureInput.claim with orderNullifiers := [repeatedDigest 200, repeatedDigest 201,
        repeatedDigest 202, repeatedDigest 203]
    } }

theorem fixture_wrong_nullifiers_refused : processWire fixtureWrongNullifiers.toJson = none := by
  native_decide

#assert_axioms darkBazaarJudgeFFI_success_iff
#assert_axioms process_output_decodes
#assert_compiled fixture_input_roundtrip
#assert_compiled fixture_semantic_inhabited
#assert_compiled fixture_process_success
#assert_compiled fixture_trailing_byte_refused
#assert_compiled fixture_unknown_field_refused
#assert_compiled fixture_uppercase_digest_refused
#assert_compiled fixture_reordered_nullifiers_refused
#assert_compiled fixture_overbound_output_refused
#assert_compiled fixture_wrong_clearing_refused
#assert_compiled fixture_wrong_nullifiers_refused

end Dregg2.Games.PathOfAngels.DarkBazaarJudge
