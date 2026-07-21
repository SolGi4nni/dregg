/-
# Market.PrivateBookEncryptionBinding — the honest BFV ↔ private-root proof seam

The current composite Dark Bazaar receipt checks a hiding clearing proof and an
authenticated quorum, but its four BFV ciphertext references are not inputs to
that proof relation.  `DarkBazaarAttestation` therefore correctly retains a RED
theorem: shape and key identity alone do not show that those rows encrypt the
orders committed by the private root.

This module states the stronger acceptance contract for a transferable
same-opening proof.  It deliberately does not define cryptographic soundness by
fiat.  A concrete backend supplies a `verify` function and an explicit
`sound` field saying that verifier acceptance extracts one witness which:

* recomputes the exact private statement root and clearing output; and
* encrypts, under the complete pinned BFV identity, to the exact four ordered
  ciphertext rows in the accepted claim.

The theorem below is therefore a protocol-composition theorem.  Instantiating
`sound` for the deployed Bulletproof/Halo2/lattice proof remains a cryptographic
reduction (and distributed production without a single book viewer remains a
separate protocol property).  No digest injectivity or proof-system soundness is
smuggled into Lean.
-/
import Market.DarkBazaarAttestation
import Dregg2.Tactics

namespace Market.PrivateBookEncryptionBinding

open Market.MpcClearingSecurity (CrossingLeakage)

set_option autoImplicit false

/-! ## 1. The complete public statement and exact semantic relation. -/

/-- The relying-party-selected BFV domain.  Every field which changes the
encryption equation or plaintext interpretation is part of the identity. -/
structure BfvIdentity where
  degree : Nat
  plaintextModulus : Nat
  coefficientModuli : List Nat
  publicKeyDigest : Nat
  codecDigest : Nat
  deriving DecidableEq, Repr

/-- The already existing private-clearing statement, made explicit here so the
BFV proof cannot silently change its session, rule, root, or public output. -/
structure PrivateStatement where
  session : Nat
  rule : Nat
  orderRoot : Nat
  output : CrossingLeakage
  deriving DecidableEq, Repr

/-- Exact public input to one transferable same-opening proof.  Ciphertexts are
ordered: exchanging two trader rows changes the statement. -/
structure PublicInput where
  identity : BfvIdentity
  ciphertextRows : List Nat
  privateStatement : PrivateStatement
  deriving DecidableEq, Repr

/-- Semantic functions supplied by the fixed N4K4 implementation.  Encryption
randomness and short RLWE witnesses belong inside `Witness`; they are not public
inputs and are not exposed by the theorem. -/
structure PrivateBookSemantics where
  Witness : Type
  orderRoot : Witness → Nat
  clearingOutput : Witness → CrossingLeakage
  encryptRows : BfvIdentity → Witness → List Nat

/-- The relation the cryptographic backend must prove.  It is stronger than
equality of statement digests: the exact same hidden witness determines both the
private root/output and every accepted BFV row. -/
structure ExactOpening (S : PrivateBookSemantics) (pub : PublicInput) where
  witness : S.Witness
  fourRows : pub.ciphertextRows.length = 4
  rootExact : S.orderRoot witness = pub.privateStatement.orderRoot
  outputExact : S.clearingOutput witness = pub.privateStatement.output
  encryptionExact : S.encryptRows pub.identity witness = pub.ciphertextRows

/-! ## 2. Transferable proof backend and host acceptance. -/

/-- A proof backend with its cryptographic boundary named rather than assumed.
`sound` is what a concrete Bulletproof/Halo2/lattice security argument must
instantiate.  The protocol theorem below merely transports that fact through
the host's conjunctive acceptance rule. -/
structure TransferableBackend (S : PrivateBookSemantics) where
  Proof : Type
  verify : PublicInput → Proof → Bool
  sound : ∀ pub proof, verify pub proof = true →
    Nonempty (ExactOpening S pub)

/-- Relying-party policy pins the complete BFV identity. -/
structure Policy where
  identity : BfvIdentity
  deriving DecidableEq, Repr

/-- The transferable proof and the independent authorization component which
must inhabit the same accepting receipt. -/
structure Receipt {S : PrivateBookSemantics} (backend : TransferableBackend S) where
  authenticatedQuorum : Bool
  proof : backend.Proof

/-- Strong accepting rule.  The proof verifies over the claim itself—not over a
detached digest—and the policy pins the full BFV parameter/key/codec identity. -/
def Receipt.Accepts {S : PrivateBookSemantics} {backend : TransferableBackend S}
    (receipt : Receipt backend) (policy : Policy) (claim : PublicInput) : Prop :=
  receipt.authenticatedQuorum = true ∧
  claim.identity = policy.identity ∧
  claim.ciphertextRows.length = 4 ∧
  backend.verify claim receipt.proof = true

/-- **The repaired apex law.**  Acceptance extracts one hidden opening for which
the same witness recomputes the accepted private root/output and encrypts to the
exact ordered BFV rows under the relying-party-pinned identity. -/
theorem acceptance_yields_exact_bfv_private_root_opening
    {S : PrivateBookSemantics} {backend : TransferableBackend S}
    {receipt : Receipt backend} {policy : Policy} {claim : PublicInput}
    (haccept : receipt.Accepts policy claim) :
    ∃ witness : S.Witness,
      claim.identity = policy.identity ∧
      claim.ciphertextRows.length = 4 ∧
      S.orderRoot witness = claim.privateStatement.orderRoot ∧
      S.clearingOutput witness = claim.privateStatement.output ∧
      S.encryptRows claim.identity witness = claim.ciphertextRows := by
  rcases haccept with ⟨hquorum, hidentity, hrows, hverify⟩
  have hopen := backend.sound claim receipt.proof hverify
  rcases hopen with ⟨opening⟩
  exact ⟨opening.witness, hidentity, hrows, opening.rootExact,
    opening.outputExact, opening.encryptionExact⟩

/-- Authorization is genuinely conjunctive: a proof-valid receipt with no
authenticated quorum cannot pass the strong rule. -/
theorem proof_without_quorum_refused
    {S : PrivateBookSemantics} {backend : TransferableBackend S}
    {receipt : Receipt backend} {policy : Policy} {claim : PublicInput}
    (hquorum : receipt.authenticatedQuorum = false) :
    ¬ receipt.Accepts policy claim := by
  intro haccept
  rw [Receipt.Accepts] at haccept
  simp_all

/-- A relying party never accepts a substituted BFV key/parameter/codec domain,
even if some backend proof verifies for that other statement. -/
theorem substituted_bfv_identity_refused
    {S : PrivateBookSemantics} {backend : TransferableBackend S}
    {receipt : Receipt backend} {policy : Policy} {claim : PublicInput}
    (hidentity : claim.identity ≠ policy.identity) :
    ¬ receipt.Accepts policy claim := by
  intro haccept
  exact hidentity haccept.2.1

/-- Noncanonical row counts fail before the proof can authorize a claim. -/
theorem non_four_row_claim_refused
    {S : PrivateBookSemantics} {backend : TransferableBackend S}
    {receipt : Receipt backend} {policy : Policy} {claim : PublicInput}
    (hrows : claim.ciphertextRows.length ≠ 4) :
    ¬ receipt.Accepts policy claim := by
  intro haccept
  exact hrows haccept.2.2.1

/-! ## 3. RED: statement authentication without the relation remains weak. -/

/-- The old proof/quorum join, abstracted to show exactly what it omits. -/
structure DetachedStatementReceipt where
  authenticatedQuorum : Bool
  privateProofVerified : Bool
  statement : PrivateStatement
  policyIdentity : BfvIdentity
  deriving DecidableEq, Repr

def DetachedStatementReceipt.Accepts (receipt : DetachedStatementReceipt)
    (claim : PublicInput) : Prop :=
  receipt.authenticatedQuorum = true ∧
  receipt.privateProofVerified = true ∧
  receipt.statement = claim.privateStatement ∧
  receipt.policyIdentity = claim.identity ∧
  claim.ciphertextRows.length = 4

def exampleIdentity : BfvIdentity :=
  { degree := 4096
    plaintextModulus := 1032193
    coefficientModuli := [68719403009, 68719230977, 137438822401]
    publicKeyDigest := 17
    codecDigest := 23 }

def exampleStatement : PrivateStatement :=
  { session := 31, rule := 1, orderRoot := 41, output := ⟨1, 8⟩ }

def detachedClaimA : PublicInput :=
  { identity := exampleIdentity
    ciphertextRows := [101, 102, 103, 104]
    privateStatement := exampleStatement }

def detachedClaimB : PublicInput :=
  { identity := exampleIdentity
    ciphertextRows := [201, 202, 203, 204]
    privateStatement := exampleStatement }

def detachedReceipt : DetachedStatementReceipt :=
  { authenticatedQuorum := true
    privateProofVerified := true
    statement := exampleStatement
    policyIdentity := exampleIdentity }

/-- The detached rule still accepts two different ciphertext vectors for one
private proof statement.  The transferable backend closes this at the relation
level by requiring an exact opening for each accepted vector. -/
theorem detached_statement_still_does_not_prove_bfv_opening :
    detachedClaimA.ciphertextRows ≠ detachedClaimB.ciphertextRows ∧
    detachedReceipt.Accepts detachedClaimA ∧
    detachedReceipt.Accepts detachedClaimB := by
  simp [DetachedStatementReceipt.Accepts, detachedClaimA, detachedClaimB,
    detachedReceipt, exampleIdentity, exampleStatement]

#guard detachedClaimA.ciphertextRows.length == 4
#guard detachedClaimB.ciphertextRows.length == 4

#assert_all_clean [
  Market.PrivateBookEncryptionBinding.acceptance_yields_exact_bfv_private_root_opening,
  Market.PrivateBookEncryptionBinding.proof_without_quorum_refused,
  Market.PrivateBookEncryptionBinding.substituted_bfv_identity_refused,
  Market.PrivateBookEncryptionBinding.non_four_row_claim_refused,
  Market.PrivateBookEncryptionBinding.detached_statement_still_does_not_prove_bfv_opening]

end Market.PrivateBookEncryptionBinding
