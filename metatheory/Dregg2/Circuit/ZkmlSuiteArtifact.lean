/-
# Dregg2.Circuit.ZkmlSuiteArtifact — a checked, first-order IR-v2 proof-suite export

This is the producer side of the breadstuffs/Dregg2 → Selvage/minidregg boundary.
It exports the deployed BabyBear/Poseidon2/FRI suite as deterministic JSON without
copying the permutation constants into a consumer repository.

The cryptographic data below is DERIVED from `Poseidon2BabyBearW16`: round constants
are the source definitions themselves, and the external/internal 16×16 linear-layer
tables are obtained by evaluating the source functions on the canonical basis.  The
meaning theorem is therefore a kernel-checked equality to the implementation, not a
comparison between two transcriptions.

Git provenance and the payload content identity deliberately live OUTSIDE the JSON
payload: a transport envelope records the exact source commit and
`sha256(payloadBytes)`.  Putting either value inside the bytes it identifies would be
circular.  `contentIdentityRule` and `sourceCommitRule` make that boundary explicit.

The artifact describes the production IR-v2 FRI rail.  It does not claim BaseFold,
does not turn Plonky3 into a Lean theorem, and does not discharge the named ROM,
collision-resistance, or deployed-verifier refinement floors.
-/

import Dregg2.Circuit.FriVerifier
import Dregg2.Circuit.Poseidon2BabyBearW16
import Dregg2.Tactics

namespace Dregg2.Circuit.ZkmlSuiteArtifact

namespace P2
abbrev P := Dregg2.Circuit.Poseidon2BabyBearW16.P
abbrev mdsLight := Dregg2.Circuit.Poseidon2BabyBearW16.mdsLight
abbrev internalRound := Dregg2.Circuit.Poseidon2BabyBearW16.internalRound
abbrev rcExtInitial := Dregg2.Circuit.Poseidon2BabyBearW16.rcExtInitial
abbrev rcInternal := Dregg2.Circuit.Poseidon2BabyBearW16.rcInternal
abbrev rcExtFinal := Dregg2.Circuit.Poseidon2BabyBearW16.rcExtFinal
abbrev perm := Dregg2.Circuit.Poseidon2BabyBearW16.perm
abbrev compress := Dregg2.Circuit.Poseidon2BabyBearW16.compress
end P2

open Dregg2.Circuit

set_option autoImplicit false

/-! ## 1. Source-derived first-order permutation data -/

/-- Canonical width-`n` basis vector `e_i`. -/
def basis (n i : Nat) : List Nat :=
  (List.range n).map (fun j => if i = j then 1 else 0)

/-- Columns of the deployed external linear map, derived by applying `mdsLight`
to the canonical basis.  No matrix entry is transcribed here. -/
def externalLinearColumns : List (List Nat) :=
  (List.range 16).map (fun i => P2.mdsLight (basis 16 i))

/-- Columns of the deployed internal linear map.  With round constant zero and
a basis input, lane zero enters the S-box as either zero or one, both fixed by
`x ↦ x^7`; `internalRound 0` therefore evaluates the linear layer on that basis.
Again, no diagonal entry is transcribed here. -/
def internalLinearColumns : List (List Nat) :=
  (List.range 16).map (fun i => P2.internalRound 0 (basis 16 i))

/-! ## 2. The first-order suite value -/

/-- Consumer-safe first-order data for one exact proof/checker suite.  Strings are
protocol identifiers, not prose to be interpreted heuristically. -/
structure Artifact where
  schemaVersion : Nat
  suiteId : String
  sourceRepository : String
  sourceSemanticModules : List String
  sourceCommitRule : String
  contentIdentityRule : String
  statementCodec : String
  proofCodec : String
  transcriptCodec : String
  baseFieldModulus : Nat
  baseFieldCodec : String
  extensionDegree : Nat
  extensionPolynomial : String
  extensionBasis : String
  extensionCodec : String
  poseidonWidth : Nat
  poseidonRate : Nat
  poseidonCapacity : Nat
  poseidonDigestLanes : Nat
  poseidonSboxExponent : Nat
  externalInitialRounds : Nat
  internalRounds : Nat
  externalFinalRounds : Nat
  externalInitialConstants : List (List Nat)
  internalConstants : List Nat
  externalFinalConstants : List (List Nat)
  externalLinearColumns : List (List Nat)
  internalLinearColumns : List (List Nat)
  leafRule : String
  nodeRule : String
  domainSeparationRule : String
  digestLayout : String
  merkleArity : Nat
  merkleCapHeight : Nat
  leafPacking : String
  pathCodec : String
  rootCodec : String
  protocolId : String
  protocolMode : String
  logBlowup : Nat
  codeRateDenominator : Nat
  domainLayout : String
  maxLogArity : Nat
  logFinalPolynomialLength : Nat
  queryCount : Nat
  commitGrindingBits : Nat
  queryGrindingBits : Nat
  fiatShamirAlphabet : List String
  fiatShamirOrdering : List String
  checkerId : String
  checkerVersion : Nat
  checkerContentIdentityRule : String
  claimCeiling : String
  namedResiduals : List String
  deriving Repr, DecidableEq

/-- The deployed IR-v2 suite.  All numeric crypto material comes from the source
Lean definitions or the source `ir2LeafWrapConfig`; the remaining fields name the
wire/config objects that those definitions model. -/
def deployedIr2Suite : Artifact :=
  { schemaVersion := 1
    suiteId := "dregg.ir2.babybear-ext4.poseidon2-w16.fri.v1"
    sourceRepository := "https://github.com/emberian/breadstuffs"
    sourceSemanticModules :=
      ["Dregg2.Circuit.Poseidon2BabyBearW16",
       "Dregg2.Circuit.FriVerifier",
       "Dregg2.Circuit.ProofByteDecoder",
       "Dregg2.Circuit.ExtFieldChallenge"]
    sourceCommitRule :=
      "transport envelope MUST bind the exact breadstuffs Git commit used to emit this payload"
    contentIdentityRule :=
      "sha256 of the canonical UTF-8 payload bytes emitted here, excluding the trailing newline"
    statementCodec := "DREGGIR2 canonical descriptor record v1 plus separately ordered public-input vector"
    proofCodec := "postcard-1.1.3 p3-batch-stark BatchProof v1; reject trailing bytes"
    transcriptCodec := "p3 DuplexChallenger overwrite mode v1"
    baseFieldModulus := P2.P
    baseFieldCodec :=
      "postcard varuint32 of p3 Montgomery word; reject raw >= modulus; semantic canonical value is raw*943718400 mod modulus"
    extensionDegree := FriVerifier.ir2LeafWrapConfig.extDeg
    extensionPolynomial := "X^4-11 over BabyBear"
    extensionBasis := "power basis [1,X,X^2,X^3] in coefficient order"
    extensionCodec := "four base-field wire words in power-basis coefficient order, with no sequence length"
    poseidonWidth := 16
    poseidonRate := 8
    poseidonCapacity := 8
    poseidonDigestLanes := 8
    poseidonSboxExponent := 7
    externalInitialRounds := P2.rcExtInitial.length
    internalRounds := P2.rcInternal.length
    externalFinalRounds := P2.rcExtFinal.length
    externalInitialConstants := P2.rcExtInitial
    internalConstants := P2.rcInternal
    externalFinalConstants := P2.rcExtFinal
    externalLinearColumns := externalLinearColumns
    internalLinearColumns := internalLinearColumns
    leafRule :=
      "PaddingFreeSponge: zero state; overwrite rate-8 blocks; permute after each nonempty block; output lanes 0..7; fixed-length inputs only"
    nodeRule :=
      "TruncatedPermutation<2,8,16>: concatenate left8||right8, permute once, output lanes 0..7"
    domainSeparationRule :=
      "no in-band tag; leaf widths and tree position are external typed structure; variable-length leaves forbidden"
    digestLayout := "eight BabyBear lanes in order; each uses the base-field wire codec"
    merkleArity := 2
    merkleCapHeight := 0
    leafPacking :=
      "MerkleTreeMmcs row values in matrix order; same-height matrices joined at leaves; shorter matrices injected at their height"
    pathCodec :=
      "postcard QueryProof sibling digests plus explicit per-round log_arity schedule and derived child positions"
    rootCodec := "postcard vector length one followed by one eight-lane digest"
    protocolId := "p3-batch-stark/TwoAdicFriPcs@82cfad73cd734d37a0d51953094f970c531817ec"
    protocolMode := "IR-v2 FRI"
    logBlowup := FriVerifier.ir2LeafWrapConfig.logBlowup
    codeRateDenominator := 2 ^ FriVerifier.ir2LeafWrapConfig.logBlowup
    domainLayout := "two-adic radix-2 DFT domain; LDE size is trace domain times codeRateDenominator"
    maxLogArity := FriVerifier.ir2LeafWrapConfig.maxLogArity
    logFinalPolynomialLength := FriVerifier.ir2LeafWrapConfig.logFinalPolyLen
    queryCount := FriVerifier.ir2LeafWrapConfig.numQueries
    commitGrindingBits := 0
    queryGrindingBits := FriVerifier.ir2LeafWrapConfig.powBits
    fiatShamirAlphabet :=
      ["canonical BabyBear scalar",
       "quartic extension challenge as four ordered BabyBear coefficients",
       "eight-lane Merkle cap digest",
       "canonical natural embedded into BabyBear"]
    fiatShamirOrdering :=
      ["degree_bits", "base_degree_bits", "preprocessed_width", "trace_commit",
       "preprocessed_commit", "public_segment", "sample_constraint_alpha",
       "quotient_commit", "sample_zeta", "opened_evaluations", "sample_pcs_alpha",
       "for_each_fri_commit_observe_then_sample_beta", "final_polynomial",
       "fri_log_arities", "query_pow_witness_then_masked_sample",
       "query_indices_by_repeated_masked_sample"]
    checkerId := "dregg.ir2.verify_vm_descriptor2_with_config"
    checkerVersion := 1
    checkerContentIdentityRule :=
      "the transport envelope source commit pins the Rust checker, Cargo.lock, and this Lean model together"
    claimCeiling :=
      "suite data and executable checker identity; not a theorem that Plonky3 verification implies the typed statement"
    namedResiduals :=
      ["Poseidon2 collision resistance and random-oracle instantiation",
       "deployed Rust checker refines the Lean verifier model",
       "word-to-proof extraction/committed-column bridge",
       "postcard metadata-tail reconstruction",
       "recursive verifier must pin child num_queries before any per-suite query-count change"] }

/-! ## 3. Checked meaning and named known-answer evidence -/

/-- The exported cryptographic and FRI parameters are the source implementation's
objects, not hand-copied lookalikes. -/
theorem deployedIr2Suite_checkedMeaning :
    deployedIr2Suite.baseFieldModulus = P2.P ∧
    deployedIr2Suite.extensionDegree = FriVerifier.ir2LeafWrapConfig.extDeg ∧
    deployedIr2Suite.externalInitialConstants = P2.rcExtInitial ∧
    deployedIr2Suite.internalConstants = P2.rcInternal ∧
    deployedIr2Suite.externalFinalConstants = P2.rcExtFinal ∧
    deployedIr2Suite.externalLinearColumns = externalLinearColumns ∧
    deployedIr2Suite.internalLinearColumns = internalLinearColumns ∧
    deployedIr2Suite.logBlowup = FriVerifier.ir2LeafWrapConfig.logBlowup ∧
    deployedIr2Suite.maxLogArity = FriVerifier.ir2LeafWrapConfig.maxLogArity ∧
    deployedIr2Suite.logFinalPolynomialLength = FriVerifier.ir2LeafWrapConfig.logFinalPolyLen ∧
    deployedIr2Suite.queryCount = FriVerifier.ir2LeafWrapConfig.numQueries ∧
    deployedIr2Suite.queryGrindingBits = FriVerifier.ir2LeafWrapConfig.powBits := by
  simp [deployedIr2Suite]

#assert_axioms deployedIr2Suite_checkedMeaning

/-- Both source-derived linear tables are exactly 16 columns of 16 canonical
BabyBear values.  This is compiled evaluation and is labelled accordingly. -/
theorem deployedIr2Suite_linearShapes :
    externalLinearColumns.length = 16 ∧
    (∀ row ∈ externalLinearColumns, row.length = 16) ∧
    internalLinearColumns.length = 16 ∧
    (∀ row ∈ internalLinearColumns, row.length = 16) := by
  native_decide

#assert_compiled deployedIr2Suite_linearShapes

/-- Named KAT for the deployed permutation over `[0,1,...,15]`. -/
theorem deployedIr2Suite_permutationKat :
    P2.perm (List.range 16) =
      [1906786279, 1737026427, 1959749225, 700325316, 1638050605, 1021608788,
       1726691001, 1761127344, 1552405120, 417318995, 36799261, 1215172152,
       614923223, 1300746575, 957311597, 304856115] := by
  native_decide

#assert_compiled deployedIr2Suite_permutationKat

/-- Named KAT for the exact 2-to-1 digest compression used by the MMCS. -/
theorem deployedIr2Suite_compressionKat :
    P2.compress (List.range 8) ((List.range 8).map (· + 8)) =
      [1906786279, 1737026427, 1959749225, 700325316,
       1638050605, 1021608788, 1726691001, 1761127344] := by
  native_decide

#assert_compiled deployedIr2Suite_compressionKat

/-! ## 4. Deterministic canonical JSON -/

private def q (s : String) : String := "\"" ++ s ++ "\""
private def nat (n : Nat) : String := toString n
private def arr (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"
private def natArr (xs : List Nat) : String := arr (xs.map nat)
private def natArr2 (xs : List (List Nat)) : String := arr (xs.map natArr)
private def strArr (xs : List String) : String := arr (xs.map q)
private def field (name value : String) : String := q name ++ ":" ++ value

/-- Canonical payload bytes.  Field order, whitespace (none), decimal rendering,
and UTF-8 strings are fixed by this function.  All strings above are JSON-safe
ASCII and contain neither quotes nor backslashes. -/
def canonicalJson (a : Artifact) : String :=
  "{" ++ String.intercalate ","
    [field "schema_version" (nat a.schemaVersion),
     field "suite_id" (q a.suiteId),
     field "source_repository" (q a.sourceRepository),
     field "source_semantic_modules" (strArr a.sourceSemanticModules),
     field "source_commit_rule" (q a.sourceCommitRule),
     field "content_identity_rule" (q a.contentIdentityRule),
     field "statement_codec" (q a.statementCodec),
     field "proof_codec" (q a.proofCodec),
     field "transcript_codec" (q a.transcriptCodec),
     field "base_field_modulus" (nat a.baseFieldModulus),
     field "base_field_codec" (q a.baseFieldCodec),
     field "extension_degree" (nat a.extensionDegree),
     field "extension_polynomial" (q a.extensionPolynomial),
     field "extension_basis" (q a.extensionBasis),
     field "extension_codec" (q a.extensionCodec),
     field "poseidon_width" (nat a.poseidonWidth),
     field "poseidon_rate" (nat a.poseidonRate),
     field "poseidon_capacity" (nat a.poseidonCapacity),
     field "poseidon_digest_lanes" (nat a.poseidonDigestLanes),
     field "poseidon_sbox_exponent" (nat a.poseidonSboxExponent),
     field "external_initial_rounds" (nat a.externalInitialRounds),
     field "internal_rounds" (nat a.internalRounds),
     field "external_final_rounds" (nat a.externalFinalRounds),
     field "external_initial_constants" (natArr2 a.externalInitialConstants),
     field "internal_constants" (natArr a.internalConstants),
     field "external_final_constants" (natArr2 a.externalFinalConstants),
     field "external_linear_columns" (natArr2 a.externalLinearColumns),
     field "internal_linear_columns" (natArr2 a.internalLinearColumns),
     field "leaf_rule" (q a.leafRule),
     field "node_rule" (q a.nodeRule),
     field "domain_separation_rule" (q a.domainSeparationRule),
     field "digest_layout" (q a.digestLayout),
     field "merkle_arity" (nat a.merkleArity),
     field "merkle_cap_height" (nat a.merkleCapHeight),
     field "leaf_packing" (q a.leafPacking),
     field "path_codec" (q a.pathCodec),
     field "root_codec" (q a.rootCodec),
     field "protocol_id" (q a.protocolId),
     field "protocol_mode" (q a.protocolMode),
     field "log_blowup" (nat a.logBlowup),
     field "code_rate_denominator" (nat a.codeRateDenominator),
     field "domain_layout" (q a.domainLayout),
     field "max_log_arity" (nat a.maxLogArity),
     field "log_final_polynomial_length" (nat a.logFinalPolynomialLength),
     field "query_count" (nat a.queryCount),
     field "commit_grinding_bits" (nat a.commitGrindingBits),
     field "query_grinding_bits" (nat a.queryGrindingBits),
     field "fiat_shamir_alphabet" (strArr a.fiatShamirAlphabet),
     field "fiat_shamir_ordering" (strArr a.fiatShamirOrdering),
     field "checker_id" (q a.checkerId),
     field "checker_version" (nat a.checkerVersion),
     field "checker_content_identity_rule" (q a.checkerContentIdentityRule),
     field "claim_ceiling" (q a.claimCeiling),
     field "named_residuals" (strArr a.namedResiduals)] ++ "}"

/-- Namespaced emission entry point.  The newline is transport framing and is
excluded from the payload identity by `contentIdentityRule`. -/
def emitMain : IO Unit := IO.println (canonicalJson deployedIr2Suite)

end Dregg2.Circuit.ZkmlSuiteArtifact

/-- Root entry point required by `lean --run`.  This module is direct-globbed as
its own Lake target, so the conventional root name cannot collide with another
emitter. -/
def main : IO Unit := Dregg2.Circuit.ZkmlSuiteArtifact.emitMain
