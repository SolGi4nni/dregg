/-
# Market.DarkBazaarLiveApexHost — live PartyMPC and hosted-verifier apex laws

The private-book proof now has an exact live-ingress cutover, but two independent
composition obligations remain visible at the playable Dark Bazaar boundary:

1. the reveal transcript must come from a live PartyMPC computation over the
   exact canonical BFV rows certified at source ingress—not from a shape-correct
   simulated transcript or an unrelated ciphertext vector; and
2. after a shared-host restart, the receipt-specific composite verifier must be
   reconstructed from the complete durable public configuration.  Reinstalling
   only a quorum verifier, accepting by verifier-id equality, or verifying only a
   detached claim digest does not reconstruct that verifier.

This module states both laws without manufacturing their cryptographic premises.
`LiveMpcBackend.sound` is the explicit computation-integrity/malicious-arithmetic
boundary.  Authenticated PartyMPC transport alone does not discharge it (the
existing executable RED theorem is re-exported below).  `HostedBackend` likewise
names exact reconstruction and full-claim verification as backend obligations.

The source references mirror the source-bound Rust verifier: each signed message
names a distinct index in the four proof rows and repeats that exact ciphertext
identity.  The packed homomorphic fold is deterministically derived from those
same rows.  There is one ciphertext encoding even though its exact typed digest
may occur once in the proof prefix and once beside its source message.

Pure.  These are target acceptance contracts.  In particular, they do not claim
that the current apex demo's shape-correct simulated reveal transcript or legacy
host registry already realizes the laws.
-/
import Market.DarkBazaarPrivateIngressCutover
import Market.PartyMpcTransportBoundary
import Dregg2.Tactics

namespace Market.DarkBazaarLiveApexHost

open Market.DarkBazaarAttestation
open Market.DarkBazaarPrivateIngressCutover
open Market.MpcClearingSecurity (CrossingLeakage)
open Market.PrivateBookEncryptionBinding

set_option autoImplicit false

/-! ## 1. Exact signed-source references into the canonical proof rows. -/

/-- One authenticated source message names an index in the canonical proof-row
vector and repeats that row's exact ciphertext identity. -/
structure SourceReference where
  messageDigest : Nat
  proofRowIndex : Nat
  ciphertextRow : Nat
  deriving DecidableEq, Repr

/-- Typed claim suffix for one source reference, matching the deployed
`[commitment(message), ciphertext(exact proof row)]` pair. -/
def SourceReference.claimInputs (source : SourceReference) :
    List CompositePrivateInput :=
  [.commitment source.messageDigest, .ciphertext source.ciphertextRow]

def sourceClaimInputs (sources : List SourceReference) :
    List CompositePrivateInput :=
  sources.flatMap SourceReference.claimInputs

/-- Exact source binding.  Both actor messages and selected proof-row indices
are unique, and every named ciphertext is the row at that exact index. -/
def ExactSourceReferences (proofRows : List Nat)
    (sources : List SourceReference) : Prop :=
  sources ≠ [] ∧
  sources.length ≤ proofRows.length ∧
  (sources.map SourceReference.proofRowIndex).Nodup ∧
  (sources.map SourceReference.messageDigest).Nodup ∧
  ∀ source ∈ sources,
    proofRows[source.proofRowIndex]? = some source.ciphertextRow

/-- Deterministic packed-fold implementation selected by the relying party.
Its algebraic denotation is a separate refinement theorem; this law needs the
more elementary but load-bearing fact that the host derives it from the exact
pinned identity and ordered proof rows. -/
structure PackedFold where
  derive : BfvIdentity → List Nat → Nat

/-! ## 2. A live PartyMPC statement over those exact rows. -/

/-- Public reveal-only transcript retained by the frontend-neutral settlement
bundle.  Masked openings remain public; only their digest is abstracted here. -/
structure LiveTranscript where
  session : Nat
  rosterDigest : Nat
  maskedOpeningsDigest : Nat
  output : CrossingLeakage
  deriving DecidableEq, Repr

/-- Complete statement passed to the live-computation verifier.  It includes the
exact source references and packed fold, rather than only `(p*, V*)`. -/
structure LiveMpcStatement where
  identity : BfvIdentity
  ciphertextRows : List Nat
  sourceReferences : List SourceReference
  packedFold : Nat
  transcript : LiveTranscript
  deriving DecidableEq, Repr

/-- Semantic extraction required of live PartyMPC computation integrity.  One
private witness opens the exact statement ciphertext rows and its clearing
meaning is exactly the reconstructed public transcript output. -/
structure ExactLiveComputation (S : PrivateBookSemantics)
    (statement : LiveMpcStatement) where
  witness : S.Witness
  fourRows : statement.ciphertextRows.length = 4
  sourcesExact : ExactSourceReferences statement.ciphertextRows
    statement.sourceReferences
  encryptionExact :
    S.encryptRows statement.identity witness = statement.ciphertextRows
  outputExact :
    S.clearingOutput witness = statement.transcript.output

/-- Explicit live-computation backend.  `sound` is not transport authenticity:
it must cover input/share formation, preprocessing, gate arithmetic, exact
ciphertext/source ingestion, and authenticated transcript reconstruction. -/
structure LiveMpcBackend (S : PrivateBookSemantics) where
  Evidence : Type
  verify : LiveMpcStatement → Evidence → Bool
  sound : ∀ statement evidence, verify statement evidence = true →
    Nonempty (ExactLiveComputation S statement)

/-- Complete relying-party policy for one live private clear. -/
structure ApexPolicy where
  identity : BfvIdentity
  session : Nat
  rule : Nat
  rosterDigest : Nat
  deriving DecidableEq, Repr

/-- Public apex carrier shared by the receipt and restarted host. -/
structure LiveApexPublic where
  ingress : IngressPublic
  transferable : PublicInput
  clearingClaim : CompositePrivateClaim
  live : LiveMpcStatement
  boardCommitment : Nat
  deriving DecidableEq, Repr

/-- Every public edge required by the source-bound live layout.  This permits a
source pair to repeat an exact proof-row ciphertext, but never a separately
encrypted row: `ExactSourceReferences` indexes directly into the proof vector. -/
def LiveApexPublic.ExactWiring (codec : ClaimIdentityCodec)
    (fold : PackedFold) (policy : ApexPolicy) (pub : LiveApexPublic) : Prop :=
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
  pub.live.identity = pub.ingress.identity ∧
  pub.live.ciphertextRows = pub.ingress.ciphertextRows ∧
  ExactSourceReferences pub.live.ciphertextRows pub.live.sourceReferences ∧
  pub.live.packedFold = fold.derive pub.live.identity pub.live.ciphertextRows ∧
  pub.live.transcript.session = pub.ingress.session ∧
  pub.live.transcript.rosterDigest = policy.rosterDigest ∧
  pub.live.transcript.output = pub.transferable.privateStatement.output ∧
  pub.clearingClaim.orderedInputs =
    pub.ingress.inputRows ++
      [.commitment pub.transferable.privateStatement.orderRoot] ++
      sourceClaimInputs pub.live.sourceReferences ++
      [.ciphertext pub.live.packedFold, .commitment pub.boardCommitment]

/-- One receipt carries all three independently necessary evidence objects. -/
structure LiveApexReceipt {S : PrivateBookSemantics}
    (ingressBackend : IngressBackend S)
    (proofBackend : TransferableBackend S)
    (mpcBackend : LiveMpcBackend S) where
  authenticatedQuorum : Bool
  ingressCertificate : ingressBackend.Certificate
  transferableProof : proofBackend.Proof
  liveMpcEvidence : mpcBackend.Evidence

def LiveApexReceipt.Accepts {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {mpcBackend : LiveMpcBackend S}
    (receipt : LiveApexReceipt ingressBackend proofBackend mpcBackend)
    (codec : ClaimIdentityCodec) (fold : PackedFold)
    (policy : ApexPolicy) (pub : LiveApexPublic) : Prop :=
  receipt.authenticatedQuorum = true ∧
  ingressBackend.verify pub.ingress receipt.ingressCertificate = true ∧
  proofBackend.verify pub.transferable receipt.transferableProof = true ∧
  mpcBackend.verify pub.live receipt.liveMpcEvidence = true ∧
  pub.ExactWiring codec fold policy

theorem live_acceptance_exposes_exact_wiring
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {mpcBackend : LiveMpcBackend S}
    {receipt : LiveApexReceipt ingressBackend proofBackend mpcBackend}
    {codec : ClaimIdentityCodec} {fold : PackedFold}
    {policy : ApexPolicy} {pub : LiveApexPublic}
    (haccept : receipt.Accepts codec fold policy pub) :
    pub.ExactWiring codec fold policy :=
  haccept.2.2.2.2

/-- **Live private-apex composition law.**  Acceptance extracts three witnesses
(source ingress, transferable BFV/private-root proof, and live PartyMPC) over
the same exact ordered rows and complete BFV identity.  It also exposes exact
source indices, transcript output, packed fold, and clearing-claim layout. -/
theorem live_acceptance_welds_ingress_proof_mpc_and_claim
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {mpcBackend : LiveMpcBackend S}
    {receipt : LiveApexReceipt ingressBackend proofBackend mpcBackend}
    {codec : ClaimIdentityCodec} {fold : PackedFold}
    {policy : ApexPolicy} {pub : LiveApexPublic}
    (haccept : receipt.Accepts codec fold policy pub) :
    ∃ ingressWitness proofWitness liveWitness : S.Witness,
      S.encryptRows policy.identity ingressWitness = pub.ingress.ciphertextRows ∧
      S.encryptRows policy.identity proofWitness = pub.ingress.ciphertextRows ∧
      S.encryptRows policy.identity liveWitness = pub.ingress.ciphertextRows ∧
      S.orderRoot proofWitness = pub.clearingClaim.orderRoot ∧
      S.clearingOutput proofWitness = pub.clearingClaim.output ∧
      S.clearingOutput liveWitness = pub.live.transcript.output ∧
      ExactSourceReferences pub.ingress.ciphertextRows pub.live.sourceReferences ∧
      pub.live.packedFold =
        fold.derive policy.identity pub.ingress.ciphertextRows ∧
      pub.live.transcript.output = pub.clearingClaim.output ∧
      pub.clearingClaim.orderedInputs =
        pub.ingress.inputRows ++ [.commitment pub.clearingClaim.orderRoot] ++
          sourceClaimInputs pub.live.sourceReferences ++
          [.ciphertext pub.live.packedFold, .commitment pub.boardCommitment] := by
  rcases haccept with
    ⟨_, hingressVerify, hproofVerify, hmpcVerify, hwiring⟩
  rcases hwiring with
    ⟨hingressIdentity, _, _, _, hproofIdentity, hproofRows, _, _,
      hclaimRoot, hclaimOutput, _, hliveIdentity, hliveRows, hsources,
      hfold, _, _, htranscriptOutput, hclaimInputs⟩
  rcases ingressBackend.sound pub.ingress receipt.ingressCertificate
      hingressVerify with ⟨ingressOpening⟩
  rcases proofBackend.sound pub.transferable receipt.transferableProof
      hproofVerify with ⟨proofOpening⟩
  rcases mpcBackend.sound pub.live receipt.liveMpcEvidence hmpcVerify with
    ⟨liveOpening⟩
  refine ⟨ingressOpening.witness, proofOpening.witness, liveOpening.witness,
    ?_, ?_, ?_, proofOpening.rootExact.trans hclaimRoot.symm,
    proofOpening.outputExact.trans hclaimOutput.symm, liveOpening.outputExact,
    ?_, ?_, htranscriptOutput.trans hclaimOutput.symm, ?_⟩
  · simpa [hingressIdentity] using ingressOpening.encryptionExact
  · calc
      S.encryptRows policy.identity proofOpening.witness =
          S.encryptRows pub.transferable.identity proofOpening.witness := by
            rw [hproofIdentity, hingressIdentity]
      _ = pub.transferable.ciphertextRows := proofOpening.encryptionExact
      _ = pub.ingress.ciphertextRows := hproofRows
  · calc
      S.encryptRows policy.identity liveOpening.witness =
          S.encryptRows pub.live.identity liveOpening.witness := by
            rw [hliveIdentity, hingressIdentity]
      _ = pub.live.ciphertextRows := liveOpening.encryptionExact
      _ = pub.ingress.ciphertextRows := hliveRows
  · simpa [hliveRows] using hsources
  · simpa [hliveIdentity, hingressIdentity, hliveRows] using hfold
  · simpa [hclaimRoot] using hclaimInputs

/-- Under the explicitly named bounded-opening binding reduction, the live MPC
output is the private meaning certified at ingress and proved by the
transferable proof—not merely a transcript with the right public shape. -/
theorem live_acceptance_yields_one_private_meaning
    {S : PrivateBookSemantics}
    (binding : CiphertextMeaningBinding S)
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {mpcBackend : LiveMpcBackend S}
    {receipt : LiveApexReceipt ingressBackend proofBackend mpcBackend}
    {codec : ClaimIdentityCodec} {fold : PackedFold}
    {policy : ApexPolicy} {pub : LiveApexPublic}
    (haccept : receipt.Accepts codec fold policy pub) :
    ∃ witness : S.Witness,
      S.orderRoot witness = pub.clearingClaim.orderRoot ∧
      S.clearingOutput witness = pub.clearingClaim.output ∧
      pub.live.transcript.output = pub.clearingClaim.output ∧
      S.encryptRows policy.identity witness = pub.ingress.ciphertextRows := by
  rcases live_acceptance_welds_ingress_proof_mpc_and_claim haccept with
    ⟨ingressWitness, proofWitness, liveWitness, hingressRows, hproofRows,
      hliveRows, hproofRoot, hproofOutput, hliveOutput, _, _, htranscript, _⟩
  have hip := binding.sameMeaning policy.identity ingressWitness proofWitness
    (hingressRows.trans hproofRows.symm)
  have hil := binding.sameMeaning policy.identity ingressWitness liveWitness
    (hingressRows.trans hliveRows.symm)
  have _liveChecksClaim : S.clearingOutput ingressWitness =
      pub.clearingClaim.output :=
    hil.2.trans (hliveOutput.trans htranscript)
  exact ⟨ingressWitness, hip.1.trans hproofRoot,
    hip.2.trans hproofOutput, htranscript, hingressRows⟩

/-! ## 3. Live-composition refusal teeth and transport RED. -/

theorem substituted_live_rows_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {mpcBackend : LiveMpcBackend S}
    (receipt : LiveApexReceipt ingressBackend proofBackend mpcBackend)
    (codec : ClaimIdentityCodec) (fold : PackedFold)
    (policy : ApexPolicy) (pub : LiveApexPublic)
    (hrows : pub.live.ciphertextRows ≠ pub.ingress.ciphertextRows) :
    ¬ receipt.Accepts codec fold policy pub := by
  intro haccept
  exact hrows (live_acceptance_exposes_exact_wiring haccept).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem detached_source_reference_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {mpcBackend : LiveMpcBackend S}
    (receipt : LiveApexReceipt ingressBackend proofBackend mpcBackend)
    (codec : ClaimIdentityCodec) (fold : PackedFold)
    (policy : ApexPolicy) (pub : LiveApexPublic)
    (hsource : ¬ ExactSourceReferences pub.live.ciphertextRows
      pub.live.sourceReferences) :
    ¬ receipt.Accepts codec fold policy pub := by
  intro haccept
  exact hsource
    (live_acceptance_exposes_exact_wiring haccept).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem substituted_transcript_session_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {mpcBackend : LiveMpcBackend S}
    (receipt : LiveApexReceipt ingressBackend proofBackend mpcBackend)
    (codec : ClaimIdentityCodec) (fold : PackedFold)
    (policy : ApexPolicy) (pub : LiveApexPublic)
    (hsession : pub.live.transcript.session ≠ pub.ingress.session) :
    ¬ receipt.Accepts codec fold policy pub := by
  intro haccept
  exact hsession
    (live_acceptance_exposes_exact_wiring haccept).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem substituted_transcript_output_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {mpcBackend : LiveMpcBackend S}
    (receipt : LiveApexReceipt ingressBackend proofBackend mpcBackend)
    (codec : ClaimIdentityCodec) (fold : PackedFold)
    (policy : ApexPolicy) (pub : LiveApexPublic)
    (houtput : pub.live.transcript.output ≠
      pub.transferable.privateStatement.output) :
    ¬ receipt.Accepts codec fold policy pub := by
  intro haccept
  exact houtput
    (live_acceptance_exposes_exact_wiring haccept).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem substituted_packed_fold_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {mpcBackend : LiveMpcBackend S}
    (receipt : LiveApexReceipt ingressBackend proofBackend mpcBackend)
    (codec : ClaimIdentityCodec) (fold : PackedFold)
    (policy : ApexPolicy) (pub : LiveApexPublic)
    (hfold : pub.live.packedFold ≠
      fold.derive pub.live.identity pub.live.ciphertextRows) :
    ¬ receipt.Accepts codec fold policy pub := by
  intro haccept
  exact hfold
    (live_acceptance_exposes_exact_wiring haccept).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem failed_live_mpc_evidence_refused
    {S : PrivateBookSemantics}
    {ingressBackend : IngressBackend S}
    {proofBackend : TransferableBackend S}
    {mpcBackend : LiveMpcBackend S}
    (receipt : LiveApexReceipt ingressBackend proofBackend mpcBackend)
    (codec : ClaimIdentityCodec) (fold : PackedFold)
    (policy : ApexPolicy) (pub : LiveApexPublic)
    (hverify : mpcBackend.verify pub.live receipt.liveMpcEvidence = false) :
    ¬ receipt.Accepts codec fold policy pub := by
  intro haccept
  simp_all [LiveApexReceipt.Accepts]

/-- RED, inherited from the concrete transport model: authenticated and
replay-safe frames do not imply honest input shares, Beaver rows, or gate
messages.  This is why `LiveMpcBackend.sound` is a separate apex premise. -/
theorem authenticated_transport_does_not_discharge_live_mpc_soundness :
    ∃ execution,
      PartyMpcTransportBoundary.TransportAccepted execution ∧
      ¬ PartyMpcTransportBoundary.ArithmeticHonest execution :=
  PartyMpcTransportBoundary.transport_acceptance_does_not_imply_arithmetic_honesty

/-! ## 4. Hosted reconstruction from complete durable public state. -/

/-- Domain/version inputs which are easy to omit from an ad-hoc restart path but
are part of the real receipt-specific verifier identity. -/
structure HostedPins where
  protocolVersion : Nat
  proofCodecDigest : Nat
  quorumVerifierId : Nat
  descriptorDigest : Nat
  evidenceLimitsDigest : Nat
  deriving DecidableEq, Repr

/-- Full public configuration needed to reconstruct the composite verifier.
The complete claim and transcript are pinned, not only their detached digest. -/
structure HostedVerifierConfig where
  pins : HostedPins
  policy : ApexPolicy
  privateStatement : PrivateStatement
  proofRows : List Nat
  sourceReferences : List SourceReference
  packedFold : Nat
  boardCommitment : Nat
  transcript : LiveTranscript
  clearingClaim : CompositePrivateClaim
  deriving DecidableEq, Repr

def expectedHostedConfig (pins : HostedPins) (policy : ApexPolicy)
    (pub : LiveApexPublic) : HostedVerifierConfig :=
  { pins
    policy
    privateStatement := pub.transferable.privateStatement
    proofRows := pub.transferable.ciphertextRows
    sourceReferences := pub.live.sourceReferences
    packedFold := pub.live.packedFold
    boardCommitment := pub.boardCommitment
    transcript := pub.live.transcript
    clearingClaim := pub.clearingClaim }

/-- Domain-separated verifier-id derivation.  No injectivity is assumed: full
configuration equality below is load-bearing. -/
structure HostedVerifierIdCodec where
  derive : HostedVerifierConfig → Nat

/-- Hosted implementation boundary.  Reconstruction exactness and full-claim
verification soundness are named fields rather than conclusions drawn from an
identifier match. -/
structure HostedBackend where
  Verifier : Type
  Evidence : Type
  reconstruct : HostedVerifierConfig → Option Verifier
  configuration : Verifier → HostedVerifierConfig
  verifierId : Verifier → Nat
  verifyClaim : Verifier → LiveApexPublic → Evidence → Bool
  Meaning : HostedVerifierConfig → LiveApexPublic → Evidence → Prop
  reconstructExact : ∀ config verifier,
    reconstruct config = some verifier → configuration verifier = config
  verifySound : ∀ verifier pub evidence,
    verifyClaim verifier pub evidence = true →
    Meaning (configuration verifier) pub evidence

structure HostedSubmission (backend : HostedBackend) where
  durableConfig : HostedVerifierConfig
  receiptVerifierId : Nat
  evidence : backend.Evidence

/-- A restarted host accepts only by reconstructing from the exact expected
configuration, matching both derived and receipt verifier ids, and invoking the
full-claim verifier over the reconstructed public apex. -/
def HostedSubmission.Accepts (backend : HostedBackend)
    (idCodec : HostedVerifierIdCodec) (pins : HostedPins)
    (policy : ApexPolicy) (pub : LiveApexPublic)
    (submission : HostedSubmission backend) : Prop :=
  submission.durableConfig = expectedHostedConfig pins policy pub ∧
  ∃ verifier,
    backend.reconstruct submission.durableConfig = some verifier ∧
    backend.verifierId verifier = idCodec.derive submission.durableConfig ∧
    submission.receiptVerifierId = backend.verifierId verifier ∧
    backend.verifyClaim verifier pub submission.evidence = true

/-- **Hosted reconstruction/pinning law.**  Acceptance yields a verifier whose
actual configuration is exactly the independently expected receipt-specific
configuration, whose identifier matches the receipt, and whose full-claim
verification has the backend's declared meaning. -/
theorem hosted_acceptance_reconstructs_exact_pinned_verifier
    (backend : HostedBackend) (idCodec : HostedVerifierIdCodec)
    (pins : HostedPins) (policy : ApexPolicy) (pub : LiveApexPublic)
    (submission : HostedSubmission backend)
    (haccept : submission.Accepts backend idCodec pins policy pub) :
    ∃ verifier,
      backend.configuration verifier = expectedHostedConfig pins policy pub ∧
      submission.receiptVerifierId =
        idCodec.derive (expectedHostedConfig pins policy pub) ∧
      backend.Meaning (expectedHostedConfig pins policy pub)
        pub submission.evidence := by
  rcases haccept with
    ⟨hconfig, verifier, hreconstruct, hid, hreceiptId, hverify⟩
  have hvconfig := backend.reconstructExact submission.durableConfig verifier
    hreconstruct
  have hmeaning := backend.verifySound verifier pub submission.evidence hverify
  refine ⟨verifier, hvconfig.trans hconfig, ?_, ?_⟩
  · calc
      submission.receiptVerifierId = backend.verifierId verifier := hreceiptId
      _ = idCodec.derive submission.durableConfig := hid
      _ = idCodec.derive (expectedHostedConfig pins policy pub) := by rw [hconfig]
  · simpa [hvconfig, hconfig] using hmeaning

/-! ## 5. Hosted refusal teeth and identifier-only RED. -/

theorem stale_hosted_configuration_refused
    (backend : HostedBackend) (idCodec : HostedVerifierIdCodec)
    (pins : HostedPins) (policy : ApexPolicy) (pub : LiveApexPublic)
    (submission : HostedSubmission backend)
    (hstale : submission.durableConfig ≠ expectedHostedConfig pins policy pub) :
    ¬ submission.Accepts backend idCodec pins policy pub := by
  intro haccept
  exact hstale haccept.1

theorem missing_hosted_reconstruction_refused
    (backend : HostedBackend) (idCodec : HostedVerifierIdCodec)
    (pins : HostedPins) (policy : ApexPolicy) (pub : LiveApexPublic)
    (submission : HostedSubmission backend)
    (hmissing : backend.reconstruct submission.durableConfig = none) :
    ¬ submission.Accepts backend idCodec pins policy pub := by
  intro haccept
  rcases haccept.2 with ⟨verifier, hreconstruct, _⟩
  rw [hmissing] at hreconstruct
  contradiction

theorem mismatched_receipt_verifier_id_refused
    (backend : HostedBackend) (idCodec : HostedVerifierIdCodec)
    (pins : HostedPins) (policy : ApexPolicy) (pub : LiveApexPublic)
    (submission : HostedSubmission backend)
    (hmismatch : submission.receiptVerifierId ≠
      idCodec.derive (expectedHostedConfig pins policy pub)) :
    ¬ submission.Accepts backend idCodec pins policy pub := by
  intro haccept
  rcases haccept with ⟨hconfig, verifier, _, hid, hreceiptId, _⟩
  apply hmismatch
  calc
    submission.receiptVerifierId = backend.verifierId verifier := hreceiptId
    _ = idCodec.derive submission.durableConfig := hid
    _ = idCodec.derive (expectedHostedConfig pins policy pub) := by rw [hconfig]

theorem failed_full_claim_verification_refused
    (backend : HostedBackend) (idCodec : HostedVerifierIdCodec)
    (pins : HostedPins) (policy : ApexPolicy) (pub : LiveApexPublic)
    (submission : HostedSubmission backend)
    (hfailed : ∀ verifier,
      backend.reconstruct submission.durableConfig = some verifier →
      backend.verifyClaim verifier pub submission.evidence = false) :
    ¬ submission.Accepts backend idCodec pins policy pub := by
  intro haccept
  rcases haccept.2 with ⟨verifier, hreconstruct, _, _, hverify⟩
  have := hfailed verifier hreconstruct
  simp_all

def exampleHostedPins : HostedPins :=
  { protocolVersion := 1
    proofCodecDigest := 11
    quorumVerifierId := 12
    descriptorDigest := 13
    evidenceLimitsDigest := 14 }

def exampleApexPolicy : ApexPolicy :=
  { identity := Market.PrivateBookEncryptionBinding.exampleIdentity
    session := 31
    rule := 1
    rosterDigest := 71 }

def exampleTranscript : LiveTranscript :=
  { session := 31
    rosterDigest := 71
    maskedOpeningsDigest := 81
    output := ⟨1, 8⟩ }

def exampleHostedConfigA : HostedVerifierConfig :=
  { pins := exampleHostedPins
    policy := exampleApexPolicy
    privateStatement := Market.PrivateBookEncryptionBinding.exampleStatement
    proofRows := [101, 102, 103, 104]
    sourceReferences :=
      [{ messageDigest := 51, proofRowIndex := 0, ciphertextRow := 101 }]
    packedFold := 91
    boardCommitment := 92
    transcript := exampleTranscript
    clearingClaim := Market.DarkBazaarAttestation.compositeClaimA }

def exampleHostedConfigB : HostedVerifierConfig :=
  { exampleHostedConfigA with
    pins := { exampleHostedPins with protocolVersion := 2 } }

def constantHostedId : HostedVerifierIdCodec := ⟨fun _ => 7⟩

/-- Concrete RED theorem: equality of verifier ids alone cannot reconstruct or
pin the hosted verifier configuration.  The exact configuration equality in
`HostedSubmission.Accepts` is therefore not redundant. -/
theorem verifier_id_equality_alone_does_not_pin_configuration :
    exampleHostedConfigA ≠ exampleHostedConfigB ∧
    constantHostedId.derive exampleHostedConfigA =
      constantHostedId.derive exampleHostedConfigB := by
  constructor
  · decide
  · rfl

#guard (sourceClaimInputs
  [{ messageDigest := 51, proofRowIndex := 0, ciphertextRow := 101 }]).length == 2
#guard constantHostedId.derive exampleHostedConfigA == 7
#guard constantHostedId.derive exampleHostedConfigB == 7

#assert_all_clean [
  Market.DarkBazaarLiveApexHost.live_acceptance_exposes_exact_wiring,
  Market.DarkBazaarLiveApexHost.live_acceptance_welds_ingress_proof_mpc_and_claim,
  Market.DarkBazaarLiveApexHost.live_acceptance_yields_one_private_meaning,
  Market.DarkBazaarLiveApexHost.substituted_live_rows_refused,
  Market.DarkBazaarLiveApexHost.detached_source_reference_refused,
  Market.DarkBazaarLiveApexHost.substituted_transcript_session_refused,
  Market.DarkBazaarLiveApexHost.substituted_transcript_output_refused,
  Market.DarkBazaarLiveApexHost.substituted_packed_fold_refused,
  Market.DarkBazaarLiveApexHost.failed_live_mpc_evidence_refused,
  Market.DarkBazaarLiveApexHost.authenticated_transport_does_not_discharge_live_mpc_soundness,
  Market.DarkBazaarLiveApexHost.hosted_acceptance_reconstructs_exact_pinned_verifier,
  Market.DarkBazaarLiveApexHost.stale_hosted_configuration_refused,
  Market.DarkBazaarLiveApexHost.missing_hosted_reconstruction_refused,
  Market.DarkBazaarLiveApexHost.mismatched_receipt_verifier_id_refused,
  Market.DarkBazaarLiveApexHost.failed_full_claim_verification_refused,
  Market.DarkBazaarLiveApexHost.verifier_id_equality_alone_does_not_pin_configuration]

end Market.DarkBazaarLiveApexHost
