/-
# Dregg2.Logic.ProofFheDualCertificate -- fail-closed dual-backend bundles

This module packages the common-input bridge from `ProofFheSharedOpening` into
a versioned, deterministic certificate.  An accepted bundle binds all of:

* the bounded Boolean source and its exact `Fin n -> Int` opening schema;
* the exact JSON bytes emitted for the live DescriptorIR2 proof backend;
* the structurally lowered BFV `BooleanProgram`;
* the exact eight-axis BFV operation ledger from `BooleanProgram.cost`; and
* a canonical, framed Lean wire image of every preceding field.

The wire image is a list of mathematical integers, not a claim about a Rust
byte decoder.  It is an exact Lean canonical serialization: every variable
segment is length-framed, source and BFV trees are prefix-tagged, descriptor
characters use injective Unicode scalar codes, and the cost fields follow the
Rust `BfvCostManifest` declaration order.  Exact wire equality makes unknown
versions, appended trailing words, altered openings, and self-consistently
resealed backend substitutions fail closed.

Acceptance yields a stronger semantic result than checking the bundled
opening once: the bound proof descriptor and bound BFV program denote the same
source predicate for every canonical opening of the declared arity.

Pure.  No axioms.
-/

import Dregg2.Logic.ProofFheSharedOpening
import Dregg2.Tactics

namespace Dregg2.Logic.ProofFheDualCertificate

set_option autoImplicit false

open Dregg2.Circuit.DescriptorIR2 (envAt)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Logic.FiniteLogicDescriptorIR2
open Dregg2.Logic.FheLogicBfvModel
open Dregg2.Logic.ProofFheSharedOpening

namespace Shared

abbrev Source := ProofFheSharedOpening.Proof.Source
abbrev Opening := ProofFheSharedOpening.Opening
abbrev TypedSource := ProofFheSharedOpening.TypedSource
abbrev FheProgram := ProofFheSharedOpening.Fhe.Program

end Shared

/-! ## 1. Exact canonical field encodings -/

abbrev Wire := List Int

def currentVersion : Nat := 1

def magic : Wire := [68, 82, 69, 71, 68, 85, 65, 76] -- `DREGDUAL`

/-- Length framing makes concatenated variable-width fields unambiguous. -/
def frame (tag : Int) (payload : Wire) : Wire :=
  [tag, Int.ofNat payload.length] ++ payload

/-- Prefix encoding for the exact bounded source syntax. -/
def encodeSource : Shared.Source -> Wire
  | .atom name => [0, Int.ofNat name]
  | .top => [1]
  | .bot => [2]
  | .not formula => 3 :: encodeSource formula
  | .and left right => 4 :: (encodeSource left ++ encodeSource right)
  | .or left right => 5 :: (encodeSource left ++ encodeSource right)

/-- Prefix encoding for the executable BFV Boolean syntax. -/
def encodeFheProgram : Shared.FheProgram -> Wire
  | .constant false => [16, 0]
  | .constant true => [16, 1]
  | .input name => [17, Int.ofNat name]
  | .eq left right => 18 :: (encodeFheProgram left ++ encodeFheProgram right)
  | .not formula => 19 :: encodeFheProgram formula
  | .and left right => 20 :: (encodeFheProgram left ++ encodeFheProgram right)
  | .or left right => 21 :: (encodeFheProgram left ++ encodeFheProgram right)

/-- Exact `BfvCostManifest` field order from the Rust interpreter. -/
def encodeCost (cost : Cost) : Wire :=
  [ Int.ofNat cost.logicalInputReads
  , Int.ofNat cost.encryptedConstantReads
  , Int.ofNat cost.ciphertextAdditions
  , Int.ofNat cost.ciphertextSubtractions
  , Int.ofNat cost.ciphertextMultiplications
  , Int.ofNat cost.relinearizations
  , Int.ofNat cost.maximumMultiplicativeDepth
  , Int.ofNat cost.boundaryZeroDecisions ]

/-- Injective character representation of the exact DescriptorIR2 JSON string. -/
def encodeString (value : String) : Wire :=
  value.toList.map (fun character => Int.ofNat character.toNat)

def encodeOpening {n : Nat} (opening : Shared.Opening n) : Wire :=
  List.ofFn opening.word

/-- One canonical field order for the entire dual-backend certificate. -/
def encodeFields {n : Nat} (version : Nat) (source : Shared.Source)
    (opening : Shared.Opening n) (descriptorBytes : String)
    (bfvProgram : Shared.FheProgram) (bfvCost : Cost) : Wire :=
  magic ++
    frame 32 [Int.ofNat version] ++
    frame 33 [Int.ofNat n] ++
    frame 34 (encodeSource source) ++
    frame 35 (encodeOpening opening) ++
    frame 36 (encodeString descriptorBytes) ++
    frame 37 (encodeFheProgram bfvProgram) ++
    frame 38 (encodeCost bfvCost)

/-! ## 2. Versioned certificate and fail-closed checker -/

structure Certificate (n : Nat) where
  version : Nat
  source : Shared.Source
  opening : Shared.Opening n
  descriptorBytes : String
  bfvProgram : Shared.FheProgram
  bfvCost : Cost
  wire : Wire

def Certificate.canonicalWire {n : Nat} (certificate : Certificate n) : Wire :=
  encodeFields certificate.version certificate.source certificate.opening
    certificate.descriptorBytes certificate.bfvProgram certificate.bfvCost

/-- Recompute the outer wire seal after deliberately editing structured fields.
This helper is useful for showing that backend checks, not merely a stale wire,
reject a self-consistently resealed substitution. -/
def Certificate.reseal {n : Nat} (certificate : Certificate n) : Certificate n :=
  { certificate with wire := certificate.canonicalWire }

def check {n : Nat} (certificate : Certificate n) : Bool :=
  decide (certificate.version = currentVersion) &&
    atomsBelow n certificate.source &&
    decide certificate.opening.Canonical &&
    decide (certificate.descriptorBytes =
      emitVmJson2 (compileDescriptor n certificate.source)) &&
    decide (certificate.bfvProgram = lowerFhe certificate.source) &&
    decide (certificate.bfvCost = certificate.bfvProgram.cost) &&
    decide (certificate.wire = certificate.canonicalWire)

theorem check_spec {n : Nat} {certificate : Certificate n} :
    check certificate = true <->
      certificate.version = currentVersion /\
      atomsBelow n certificate.source = true /\
      certificate.opening.Canonical /\
      certificate.descriptorBytes =
        emitVmJson2 (compileDescriptor n certificate.source) /\
      certificate.bfvProgram = lowerFhe certificate.source /\
      certificate.bfvCost = certificate.bfvProgram.cost /\
      certificate.wire = certificate.canonicalWire := by
  simp [check, and_assoc]

def certify {n : Nat} (source : Shared.TypedSource n)
    (opening : Shared.Opening n) : Certificate n :=
  let descriptorBytes := emitVmJson2 (compileDescriptor n source.formula)
  let bfvProgram := lowerFhe source.formula
  let bfvCost := bfvProgram.cost
  { version := currentVersion
  , source := source.formula
  , opening := opening
  , descriptorBytes := descriptorBytes
  , bfvProgram := bfvProgram
  , bfvCost := bfvCost
  , wire := encodeFields currentVersion source.formula opening descriptorBytes
      bfvProgram bfvCost }

theorem check_certify {n : Nat} (source : Shared.TypedSource n)
    (opening : Shared.Opening n) (hcanonical : opening.Canonical) :
    check (certify source opening) = true := by
  apply check_spec.mpr
  simp [certify, source.bounded, hcanonical, Certificate.canonicalWire]

/-! ## 3. Accepted bundles bind both backends for every canonical opening -/

/-- All syntactic backend bindings exposed as a reusable theorem boundary. -/
theorem accepted_binds_backends {n : Nat} {certificate : Certificate n}
    (hcheck : check certificate = true) :
    certificate.opening.Canonical /\
    certificate.descriptorBytes =
      emitVmJson2 (compileDescriptor n certificate.source) /\
    certificate.bfvProgram = lowerFhe certificate.source /\
    certificate.bfvCost = (lowerFhe certificate.source).cost := by
  have hspec := check_spec.mp hcheck
  refine ⟨hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2.1, ?_⟩
  simpa [hspec.2.2.2.2.1] using hspec.2.2.2.2.2.1

/-- The exact polynomial values agree over any commutative ring, for every
canonical opening of the certified arity, not only the bundled specimen. -/
theorem accepted_denotations_agree {R : Type*} [CommRing R]
    {n : Nat} {certificate : Certificate n}
    (hcheck : check certificate = true) :
    forall opening : Shared.Opening n, opening.Canonical ->
      ((sourcePoly certificate.source).eval
          (envAt opening.proofTrace 0) : R) =
        certificate.bfvProgram.evalRing (R := R) opening.boolEnv := by
  have hspec := check_spec.mp hcheck
  let source : Shared.TypedSource n :=
    { formula := certificate.source, bounded := hspec.2.1 }
  intro opening hcanonical
  rw [hspec.2.2.2.2.1]
  exact descriptorDenotation_eq_fheRing source opening hcanonical

/-- Predicate-level coherence with the actual live proof relation.  The BFV
side is interpreted in the plaintext modulus used by the executable comparison
specimen; Boolean correctness is independent of that modulus beyond `0 != 1`. -/
theorem accepted_proof_iff_bfv_one {n : Nat} {certificate : Certificate n}
    (hcheck : check certificate = true) :
    forall opening : Shared.Opening n, opening.Canonical ->
      (CanonicalLogicSatisfied2 (fun _ => 0) n certificate.source
          (fun _ => 0) (fun _ => ((0 : Int), 0)) [] opening.proofTrace
        <-> certificate.bfvProgram.evalRing (R := ZMod 1032193)
          opening.boolEnv = 1) := by
  have hspec := check_spec.mp hcheck
  let source : Shared.TypedSource n :=
    { formula := certificate.source, bounded := hspec.2.1 }
  intro opening hcanonical
  let input : ProofFheSharedOpening.Instance n := { source := source, opening := opening }
  have hproof :
      CanonicalLogicSatisfied2 (fun _ => 0) n certificate.source
          (fun _ => 0) (fun _ => ((0 : Int), 0)) [] opening.proofTrace
        <-> Proof.eval opening.boolEnv certificate.source = true := by
    have hsource := proofAccepts_iff_sourceTrue input
    simpa [ProofAccepts, input, source, hcanonical] using hsource
  have hfhe :
      certificate.bfvProgram.evalRing (R := ZMod 1032193) opening.boolEnv = 1
        <-> Proof.eval opening.boolEnv certificate.source = true := by
    rw [hspec.2.2.2.2.1, BooleanProgram.evalRing_correct, lowerFhe_evalBool]
    have hzeroOne : (0 : ZMod 1032193) ≠ 1 := by decide
    cases Proof.eval opening.boolEnv certificate.source <;>
      simp [encodeBool, hzeroOne]
  rw [hproof, hfhe]

/-! ## 4. General rejection laws -/

theorem check_rejects_unknown_version {n : Nat} (certificate : Certificate n)
    (hversion : certificate.version ≠ currentVersion) :
    check certificate = false := by
  simp [check, hversion]

theorem check_rejects_noncanonical {n : Nat} (certificate : Certificate n)
    (hnoncanonical : Not certificate.opening.Canonical) :
    check certificate = false := by
  simp [check, hnoncanonical]

theorem check_rejects_descriptor_substitution {n : Nat}
    (certificate : Certificate n)
    (htampered : certificate.descriptorBytes ≠
      emitVmJson2 (compileDescriptor n certificate.source)) :
    check certificate = false := by
  simp [check, htampered]

theorem check_rejects_fhe_substitution {n : Nat}
    (certificate : Certificate n)
    (htampered : certificate.bfvProgram ≠ lowerFhe certificate.source) :
    check certificate = false := by
  simp [check, htampered]

def appendTrailing {n : Nat} (certificate : Certificate n)
    (trailing : Int) : Certificate n :=
  { certificate with wire := certificate.wire ++ [trailing] }

theorem check_rejects_trailing {n : Nat} (certificate : Certificate n)
    (trailing : Int) (hwire : certificate.wire = certificate.canonicalWire) :
    check (appendTrailing certificate trailing) = false := by
  have hne : certificate.wire ++ [trailing] ≠ certificate.canonicalWire := by
    rw [hwire]
    intro heq
    have hlength := congrArg List.length heq
    simp at hlength
  cases hvalue : check (appendTrailing certificate trailing) with
  | false => rfl
  | true =>
      have hclaimed := (check_spec.mp hvalue).2.2.2.2.2.2
      exfalso
      apply hne
      simpa [appendTrailing, Certificate.canonicalWire] using hclaimed

/-! ## 5. Concrete accept/reject specimens -/

def demoCertificate : Certificate 3 := certify demoSource demoOpening

theorem demoCertificate_accepts : check demoCertificate = true := by
  exact check_certify demoSource demoOpening demoOpening_canonical

def unknownVersion : Certificate 3 :=
  Certificate.reseal { demoCertificate with version := currentVersion + 1 }

theorem unknownVersion_rejected : check unknownVersion = false := by
  apply check_rejects_unknown_version
  simp [unknownVersion, Certificate.reseal, currentVersion]

def trailingByte : Certificate 3 := appendTrailing demoCertificate 255

theorem trailingByte_rejected : check trailingByte = false := by
  apply check_rejects_trailing
  simp [demoCertificate, certify, Certificate.canonicalWire]

def noncanonicalBundle : Certificate 3 :=
  Certificate.reseal { demoCertificate with opening := noncanonicalOpening }

theorem noncanonicalBundle_rejected : check noncanonicalBundle = false := by
  apply check_rejects_noncanonical
  exact noncanonicalOpening_not_canonical

/-- The attacker changes both the BFV tree and its operation ledger, then
recomputes the outer wire.  Canonical-source reconstruction still rejects it. -/
def tamperedFheBundle : Certificate 3 :=
  Certificate.reseal
    { demoCertificate with
      bfvProgram := .constant false
      bfvCost := (.constant false : BooleanProgram).cost }

theorem tamperedFheBundle_rejected : check tamperedFheBundle = false := by
  apply check_rejects_fhe_substitution
  decide

/-- The proof-backend bytes are changed and the wire is recomputed. -/
def tamperedDescriptorBundle : Certificate 3 :=
  Certificate.reseal
    { demoCertificate with descriptorBytes := demoCertificate.descriptorBytes ++ " " }

theorem tamperedDescriptorBundle_rejected :
    check tamperedDescriptorBundle = false := by
  apply check_rejects_descriptor_substitution
  change demoCertificate.descriptorBytes ++ " " ≠
    emitVmJson2 (compileDescriptor 3 demoCertificate.source)
  have hdescriptor := (check_spec.mp demoCertificate_accepts).2.2.2.1
  rw [← hdescriptor]
  intro heq
  have hchars := congrArg String.toList heq
  have hlength := congrArg List.length hchars
  simp [String.toList_append] at hlength

#assert_all_clean [
  check_spec,
  check_certify,
  accepted_binds_backends,
  accepted_denotations_agree,
  accepted_proof_iff_bfv_one,
  check_rejects_unknown_version,
  check_rejects_noncanonical,
  check_rejects_descriptor_substitution,
  check_rejects_fhe_substitution,
  check_rejects_trailing,
  demoCertificate_accepts,
  unknownVersion_rejected,
  trailingByte_rejected,
  noncanonicalBundle_rejected,
  tamperedFheBundle_rejected,
  tamperedDescriptorBundle_rejected
]

end Dregg2.Logic.ProofFheDualCertificate
