/-
# Market.DarkBazaarPrivateIngressCutover — one canonical private-book ingress

The transferable BFV/private-root proof closes the relation between four BFV
ciphertexts and the hidden clearing witness.  It does not, by itself, say that
those four ciphertexts are the rows accepted at trader ingress.  In particular,
putting an older source encoding and the proof encoding side by side in one
authenticated claim is only co-membership, not equality of their meanings.

This module specifies the honest cutover: there is one ordered four-row ingress
batch.  The ingress certificate opens those exact rows; the transferable proof
verifies over those exact rows; and the clearing claim begins with exactly their
four typed input references followed by the proved private root.  Any suffix is
commitment-only, so a second ciphertext encoding cannot be laundered into the
same claim as auxiliary evidence.

The cryptographic boundaries remain explicit:

* `IngressBackend.sound` is the source-authentication/encryption-opening
  obligation for the deployed ingress verifier;
* `TransferableBackend.sound` is the existing proof-system extraction
  obligation for the BFV/private-root backend; and
* `CiphertextMeaningBinding.sameMeaning` is the bounded-opening binding
  reduction needed to identify the two extracted private meanings.  It is an
  assumption supplied by the concrete BFV relation and its shortness bounds,
  not a false theorem that arbitrary BFV encryption is injective.

Pure.  This is the Lean-first acceptance law for the implementation cutover; it
does not claim that the current live-board dual encoding has already been
removed.
-/
import Market.PrivateBookEncryptionBinding
import Dregg2.Tactics

namespace Market.DarkBazaarPrivateIngressCutover

open Market.DarkBazaarAttestation
open Market.PrivateBookEncryptionBinding

set_option autoImplicit false

/-! ## 1. One exact ingress carrier. -/

/-- Typed claim inputs for an ordered ciphertext vector.  The order is part of
the statement; sorting or treating the result as a set is not permitted. -/
def ciphertextInputs (rows : List Nat) : List CompositePrivateInput :=
  rows.map CompositePrivateInput.ciphertext

/-- Public data certified by the private-book ingress verifier.  Both the
ciphertext objects (abstracted here by their canonical row identities) and the
typed claim-input encoding are explicit, so their equality is checked rather
than inferred from co-membership in a later claim. -/
structure IngressPublic where
  session : Nat
  identity : BfvIdentity
  ciphertextRows : List Nat
  inputRows : List CompositePrivateInput
  deriving DecidableEq, Repr

/-- Exact semantic opening extracted from an accepted ingress certificate.
`Witness` includes whatever source attribution, message, encryption randomness,
and bounded-noise evidence the concrete semantics requires. -/
structure ExactIngressOpening (S : PrivateBookSemantics) (pub : IngressPublic) where
  witness : S.Witness
  fourRows : pub.ciphertextRows.length = 4
  inputRowsExact : pub.inputRows = ciphertextInputs pub.ciphertextRows
  encryptionExact : S.encryptRows pub.identity witness = pub.ciphertextRows

/-- Authenticated ingress backend with its semantic soundness named.  Signature
verification or local re-encryption alone may instantiate this only if it really
extracts the `ExactIngressOpening` above. -/
structure IngressBackend (S : PrivateBookSemantics) where
  Certificate : Type
  verify : IngressPublic → Certificate → Bool
  sound : ∀ pub certificate, verify pub certificate = true →
    Nonempty (ExactIngressOpening S pub)

/-- External bounded-opening binding boundary.  Equality of exact ciphertext
rows under one complete BFV identity implies equality of the private meaning,
not necessarily equality of encryption randomness or of the whole witness. -/
structure CiphertextMeaningBinding (S : PrivateBookSemantics) where
  sameMeaning : ∀ identity left right,
    S.encryptRows identity left = S.encryptRows identity right →
    S.orderRoot left = S.orderRoot right ∧
      S.clearingOutput left = S.clearingOutput right

/-! ## 2. Exact ingress → proof → clearing-claim wiring. -/

/-- Encoding of the complete BFV identity into the legacy scalar identity slot
of `CompositePrivateClaim`.  The relying party still pins the full structured
identity; this function does not replace that equality check. -/
structure ClaimIdentityCodec where
  encode : BfvIdentity → Nat

/-- Relying-party-selected domain.  Session and rule are pinned independently
of proof bytes and of the claim. -/
structure Policy where
  identity : BfvIdentity
  session : Nat
  rule : Nat
  deriving DecidableEq, Repr

/-- The three public carriers which must be welded at acceptance.  Auxiliary
claim inputs are named separately so the cutover can require them to be
commitment-only. -/
structure PublicCutover where
  ingress : IngressPublic
  transferable : PublicInput
  clearingClaim : CompositePrivateClaim
  auxiliaryInputs : List CompositePrivateInput
  deriving DecidableEq, Repr

/-- Auxiliary evidence may carry commitments, but never a second ciphertext
encoding of the source book. -/
def IsCommitmentInput : CompositePrivateInput → Prop
  | .ciphertext _ => False
  | .commitment _ => True

/-- Exact, ordered public wiring.  Notice that every edge is equality: there is
no `List.Mem`, set inclusion, digest-bag equality, or independently selectable
source-row vector anywhere in this contract. -/
def PublicCutover.ExactWiring (codec : ClaimIdentityCodec) (policy : Policy)
    (pub : PublicCutover) : Prop :=
  pub.ingress.identity = policy.identity ∧
  pub.ingress.session = policy.session ∧
  pub.ingress.ciphertextRows.length = 4 ∧
  pub.ingress.inputRows = ciphertextInputs pub.ingress.ciphertextRows ∧
  pub.transferable.identity = pub.ingress.identity ∧
  pub.transferable.ciphertextRows = pub.ingress.ciphertextRows ∧
  pub.transferable.privateStatement.session = pub.ingress.session ∧
  pub.transferable.privateStatement.rule = policy.rule ∧
  pub.clearingClaim.orderRoot =
    pub.transferable.privateStatement.orderRoot ∧
  pub.clearingClaim.output = pub.transferable.privateStatement.output ∧
  pub.clearingClaim.bfvIdentity = codec.encode policy.identity ∧
  pub.clearingClaim.orderedInputs =
    pub.ingress.inputRows ++
      [.commitment pub.transferable.privateStatement.orderRoot] ++
      pub.auxiliaryInputs ∧
  ∀ input ∈ pub.auxiliaryInputs, IsCommitmentInput input

/-- One independently authenticated receipt carrying both certificates. -/
structure CutoverReceipt {S : PrivateBookSemantics}
    (ingressBackend : IngressBackend S)
    (proofBackend : TransferableBackend S) where
  authenticatedQuorum : Bool
  ingressCertificate : ingressBackend.Certificate
  transferableProof : proofBackend.Proof

/-- Acceptance is conjunctive and statement-directed.  Proof bytes never select
the ingress rows, BFV identity, session, rule, root, output, or claim layout. -/
def CutoverReceipt.Accepts {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    (receipt : CutoverReceipt ingressBackend proofBackend)
    (codec : ClaimIdentityCodec) (policy : Policy)
    (pub : PublicCutover) : Prop :=
  receipt.authenticatedQuorum = true ∧
  ingressBackend.verify pub.ingress receipt.ingressCertificate = true ∧
  proofBackend.verify pub.transferable receipt.transferableProof = true ∧
  pub.ExactWiring codec policy

/-- Acceptance always exposes the exact public wiring, independently of either
backend's cryptographic soundness theorem. -/
theorem acceptance_exposes_exact_wiring
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {receipt : CutoverReceipt ingressBackend proofBackend}
    {codec : ClaimIdentityCodec} {policy : Policy} {pub : PublicCutover}
    (haccept : receipt.Accepts codec policy pub) :
    pub.ExactWiring codec policy :=
  haccept.2.2.2

/-- **The ingress-cutover apex.**  Acceptance extracts an ingress opening and a
transferable-proof opening whose exact encrypted rows are literally the same
ordered four rows, under the same relying-party-pinned identity.  Those exact
typed inputs are the clearing claim's prefix, immediately followed by the exact
private root proved by the transferable statement; all remaining inputs are
commitments. -/
theorem acceptance_welds_exact_ingress_proof_and_claim
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {receipt : CutoverReceipt ingressBackend proofBackend}
    {codec : ClaimIdentityCodec} {policy : Policy} {pub : PublicCutover}
    (haccept : receipt.Accepts codec policy pub) :
    ∃ ingressWitness proofWitness : S.Witness,
      S.encryptRows policy.identity ingressWitness = pub.ingress.ciphertextRows ∧
      S.encryptRows policy.identity proofWitness = pub.ingress.ciphertextRows ∧
      pub.ingress.ciphertextRows.length = 4 ∧
      pub.ingress.inputRows = ciphertextInputs pub.ingress.ciphertextRows ∧
      S.orderRoot proofWitness = pub.clearingClaim.orderRoot ∧
      S.clearingOutput proofWitness = pub.clearingClaim.output ∧
      pub.clearingClaim.orderedInputs =
        pub.ingress.inputRows ++ [.commitment pub.clearingClaim.orderRoot] ++
          pub.auxiliaryInputs ∧
      (∀ input ∈ pub.auxiliaryInputs, IsCommitmentInput input) := by
  rcases haccept with ⟨_, hingressVerify, hproofVerify, hwiring⟩
  rcases hwiring with
    ⟨hingressIdentity, _, hfour, hinputs, hproofIdentity, hproofRows,
      _, _, hclaimRoot, hclaimOutput, _, hclaimInputs, haux⟩
  rcases ingressBackend.sound pub.ingress receipt.ingressCertificate
      hingressVerify with ⟨ingressOpening⟩
  rcases proofBackend.sound pub.transferable receipt.transferableProof
      hproofVerify with ⟨proofOpening⟩
  refine ⟨ingressOpening.witness, proofOpening.witness, ?_, ?_, hfour,
    hinputs, ?_, ?_, ?_, haux⟩
  · simpa [hingressIdentity] using ingressOpening.encryptionExact
  · calc
      S.encryptRows policy.identity proofOpening.witness =
          S.encryptRows pub.transferable.identity proofOpening.witness := by
            rw [hproofIdentity, hingressIdentity]
      _ = pub.transferable.ciphertextRows := proofOpening.encryptionExact
      _ = pub.ingress.ciphertextRows := hproofRows
  · exact proofOpening.rootExact.trans hclaimRoot.symm
  · exact proofOpening.outputExact.trans hclaimOutput.symm
  · simpa [hclaimRoot] using hclaimInputs

/-- With the explicitly named bounded-opening binding reduction, the witness
certified at ingress and the witness extracted from the transferable proof have
the same private root and clearing output.  Thus the clearing claim describes
the ingress source's meaning, not merely another encoding listed beside it. -/
theorem acceptance_yields_ingress_source_private_meaning
    {S : PrivateBookSemantics}
    (binding : CiphertextMeaningBinding S)
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {receipt : CutoverReceipt ingressBackend proofBackend}
    {codec : ClaimIdentityCodec} {policy : Policy} {pub : PublicCutover}
    (haccept : receipt.Accepts codec policy pub) :
    ∃ ingressWitness : S.Witness,
      S.orderRoot ingressWitness = pub.clearingClaim.orderRoot ∧
      S.clearingOutput ingressWitness = pub.clearingClaim.output ∧
      S.encryptRows policy.identity ingressWitness = pub.ingress.ciphertextRows := by
  rcases acceptance_welds_exact_ingress_proof_and_claim haccept with
    ⟨ingressWitness, proofWitness, hingressRows, hproofRows, _, _,
      hproofRoot, hproofOutput, _, _⟩
  have hmeaning := binding.sameMeaning policy.identity ingressWitness proofWitness
    (hingressRows.trans hproofRows.symm)
  exact ⟨ingressWitness, hmeaning.1.trans hproofRoot,
    hmeaning.2.trans hproofOutput, hingressRows⟩

/-! ## 3. Refusal teeth. -/

/-- A transferable proof statement naming any different ordered row vector is
refused, even if both vectors occur somewhere in the wider claim. -/
theorem substituted_transferable_rows_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    (receipt : CutoverReceipt ingressBackend proofBackend)
    (codec : ClaimIdentityCodec) (policy : Policy) (pub : PublicCutover)
    (hrows : pub.transferable.ciphertextRows ≠ pub.ingress.ciphertextRows) :
    ¬ receipt.Accepts codec policy pub := by
  intro haccept
  exact hrows (acceptance_exposes_exact_wiring haccept).2.2.2.2.2.1

/-- Reordering is substitution because row order is part of the statement. -/
theorem reordered_transferable_rows_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    (receipt : CutoverReceipt ingressBackend proofBackend)
    (codec : ClaimIdentityCodec) (policy : Policy) (pub : PublicCutover)
    (hreversed : pub.transferable.ciphertextRows =
      pub.ingress.ciphertextRows.reverse)
    (hnonpalindrome : pub.ingress.ciphertextRows.reverse ≠
      pub.ingress.ciphertextRows) :
    ¬ receipt.Accepts codec policy pub := by
  intro haccept
  have heq := (acceptance_exposes_exact_wiring haccept).2.2.2.2.2.1
  exact hnonpalindrome (hreversed.symm.trans heq)

/-- A second ciphertext encoding cannot be hidden in the auxiliary suffix. -/
theorem auxiliary_ciphertext_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    (receipt : CutoverReceipt ingressBackend proofBackend)
    (codec : ClaimIdentityCodec) (policy : Policy) (pub : PublicCutover)
    (row : Nat) (hrow : CompositePrivateInput.ciphertext row ∈ pub.auxiliaryInputs) :
    ¬ receipt.Accepts codec policy pub := by
  intro haccept
  have haux := (acceptance_exposes_exact_wiring haccept).2.2.2.2.2.2.2.2.2.2.2.2
  exact haux (.ciphertext row) hrow

/-- A claim cannot replace the private root while keeping the same proof. -/
theorem substituted_clearing_root_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    (receipt : CutoverReceipt ingressBackend proofBackend)
    (codec : ClaimIdentityCodec) (policy : Policy) (pub : PublicCutover)
    (hroot : pub.clearingClaim.orderRoot ≠
      pub.transferable.privateStatement.orderRoot) :
    ¬ receipt.Accepts codec policy pub := by
  intro haccept
  exact hroot (acceptance_exposes_exact_wiring haccept).2.2.2.2.2.2.2.2.1

/-- The relying-party session cannot be selected by ingress or proof bytes. -/
theorem substituted_ingress_session_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    (receipt : CutoverReceipt ingressBackend proofBackend)
    (codec : ClaimIdentityCodec) (policy : Policy) (pub : PublicCutover)
    (hsession : pub.ingress.session ≠ policy.session) :
    ¬ receipt.Accepts codec policy pub := by
  intro haccept
  exact hsession (acceptance_exposes_exact_wiring haccept).2.1

/-- Valid component proofs without the authenticated quorum are insufficient. -/
theorem proof_without_authenticated_quorum_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    (receipt : CutoverReceipt ingressBackend proofBackend)
    (codec : ClaimIdentityCodec) (policy : Policy) (pub : PublicCutover)
    (hquorum : receipt.authenticatedQuorum = false) :
    ¬ receipt.Accepts codec policy pub := by
  intro haccept
  simp_all [CutoverReceipt.Accepts]

/-! ## 4. RED: dual-encoding co-membership is not a cutover. -/

/-- Weak rule used only to expose the old logical error: every row from both
encodings occurs somewhere in one claim.  It says nothing about equality of the
two ordered vectors. -/
def WeakDualEncodingCoMembership (ingressRows proofRows : List Nat)
    (claim : CompositePrivateClaim) : Prop :=
  ingressRows.length = 4 ∧
  proofRows.length = 4 ∧
  (∀ row ∈ ingressRows, CompositePrivateInput.ciphertext row ∈ claim.orderedInputs) ∧
  (∀ row ∈ proofRows, CompositePrivateInput.ciphertext row ∈ claim.orderedInputs) ∧
  CompositePrivateInput.commitment claim.orderRoot ∈ claim.orderedInputs

def weakIngressRows : List Nat := [101, 102, 103, 104]
def weakProofRows : List Nat := [201, 202, 203, 204]

def weakDualClaim : CompositePrivateClaim :=
  { orderRoot := 41
    output := ⟨1, 8⟩
    bfvIdentity := 17
    orderedInputs :=
      ciphertextInputs weakIngressRows ++ ciphertextInputs weakProofRows ++
        [.commitment 41] }

/-- Concrete collision: two different ordered encodings satisfy the weak
co-membership rule in one authenticated-looking claim. -/
theorem weak_dual_encoding_comembership_collision :
    weakIngressRows ≠ weakProofRows ∧
    WeakDualEncodingCoMembership weakIngressRows weakProofRows weakDualClaim := by
  constructor
  · decide
  · simp [WeakDualEncodingCoMembership, weakIngressRows, weakProofRows,
      weakDualClaim, ciphertextInputs]

/-- **RED theorem.**  No theorem can recover row equality from dual-encoding
co-membership alone.  The exact cutover law above uses ordered equality at every
edge and forbids ciphertexts in the auxiliary suffix. -/
theorem dual_encoding_comembership_does_not_bind_rows :
    ¬ ∀ ingressRows proofRows claim,
      WeakDualEncodingCoMembership ingressRows proofRows claim →
      ingressRows = proofRows := by
  intro hbind
  exact weak_dual_encoding_comembership_collision.1
    (hbind weakIngressRows weakProofRows weakDualClaim
      weak_dual_encoding_comembership_collision.2)

#guard weakIngressRows.length == 4
#guard weakProofRows.length == 4

#assert_all_clean [
  Market.DarkBazaarPrivateIngressCutover.acceptance_exposes_exact_wiring,
  Market.DarkBazaarPrivateIngressCutover.acceptance_welds_exact_ingress_proof_and_claim,
  Market.DarkBazaarPrivateIngressCutover.acceptance_yields_ingress_source_private_meaning,
  Market.DarkBazaarPrivateIngressCutover.substituted_transferable_rows_refused,
  Market.DarkBazaarPrivateIngressCutover.reordered_transferable_rows_refused,
  Market.DarkBazaarPrivateIngressCutover.auxiliary_ciphertext_refused,
  Market.DarkBazaarPrivateIngressCutover.substituted_clearing_root_refused,
  Market.DarkBazaarPrivateIngressCutover.substituted_ingress_session_refused,
  Market.DarkBazaarPrivateIngressCutover.proof_without_authenticated_quorum_refused,
  Market.DarkBazaarPrivateIngressCutover.weak_dual_encoding_comembership_collision,
  Market.DarkBazaarPrivateIngressCutover.dual_encoding_comembership_does_not_bind_rows]

end Market.DarkBazaarPrivateIngressCutover
