/-
# Market.DistributedPrivateProverBoundary — canonical public worker contributions

`fhegg-fhe/private_book_distributed_prover.rs` is the process boundary between
secret-shared private-book custody and a future production distributed proof
backend.  Each isolated worker consumes one private share and releases one
fixed-size, roster-authenticated public transcript digest.  The coordinator
accepts no private-share type.

This module proves the protocol-facing envelope law:

* every canonical contribution binds the exact session, relation, input
  certificate, backend protocol, complete roster, and roster slot;
* a slot cannot be accepted twice and a collector with a missing slot cannot
  finish;
* context, worker, and ordered-slot substitution are refused;
* a finished envelope has exactly one canonical contribution per roster slot;
* the coordinator view consists only of the public context, ordered transcript
  digests, and bundle digest, and is independent of worker-private values.

Signature soundness and digest construction are explicit backend fields.  The
semantic model uses complete values rather than pretending digest equality is
injectivity.  A production BLAKE3/Ed25519 refinement must discharge that wire
step.  Most importantly, the final theorem retains the unavoidable residual:
all workers together reconstruct an n-of-n additive witness.  This envelope is
therefore a no-coordinator-view boundary, not an all-workers-collude theorem and
not by itself a proof that a distributed R1CS backend is sound or zero knowledge.
-/
import Market.DarkBazaarPrivateIngressCutover
import Dregg2.Tactics

namespace Market.DistributedPrivateProverBoundary

open scoped BigOperators

set_option autoImplicit false

abbrev Digest := Nat
abbrev WorkerId := Nat

/-! ## 1. Exact public context and one worker contribution. -/

/-- Lossless semantic context hashed by `WorkerProofContext` on the wire. -/
structure ProverContext (n : Nat) where
  session : Digest
  relation : Digest
  inputCertificate : Digest
  jointInputCommitment : Digest
  protocol : Digest
  roster : Fin n → WorkerId

/-- Fixed public output of one isolated worker process.  No witness-share field
is representable in this coordinator-facing carrier. -/
structure WorkerContribution (n : Nat) where
  session : Digest
  relation : Digest
  inputCertificate : Digest
  jointInputCommitment : Digest
  protocol : Digest
  roster : Fin n → WorkerId
  slot : Fin n
  worker : WorkerId
  backendTranscript : Digest
  contributionDigest : Digest

/-- Explicit Ed25519/digest refinement boundary.  `signatureSound` is the
roster-authentication guarantee consumed by the semantic theorem. -/
structure ContributionBackend (n : Nat) where
  digestOf : ProverContext n → Fin n → Digest → Digest
  bundleOf : ProverContext n → (Fin n → Digest) → Digest
  verifySignature : WorkerContribution n → Bool
  signatureSound : ∀ contribution, verifySignature contribution = true →
    contribution.worker = contribution.roster contribution.slot

/-- Exact canonical contribution accepted at the coordinator boundary. -/
def CanonicalContribution {n : Nat} (backend : ContributionBackend n)
    (context : ProverContext n) (contribution : WorkerContribution n) : Prop :=
  contribution.session = context.session ∧
  contribution.relation = context.relation ∧
  contribution.inputCertificate = context.inputCertificate ∧
  contribution.jointInputCommitment = context.jointInputCommitment ∧
  contribution.protocol = context.protocol ∧
  contribution.roster = context.roster ∧
  contribution.backendTranscript ≠ 0 ∧
  contribution.contributionDigest =
    backend.digestOf context contribution.slot contribution.backendTranscript ∧
  backend.verifySignature contribution = true

/-- Canonicality exposes every public binding and derives the authenticated
worker identity at the claimed exact roster slot. -/
theorem canonical_contribution_binds_complete_context_and_slot
    {n : Nat} {backend : ContributionBackend n}
    {context : ProverContext n} {contribution : WorkerContribution n}
    (hcanonical : CanonicalContribution backend context contribution) :
    contribution.session = context.session ∧
    contribution.relation = context.relation ∧
    contribution.inputCertificate = context.inputCertificate ∧
    contribution.jointInputCommitment = context.jointInputCommitment ∧
    contribution.protocol = context.protocol ∧
    contribution.roster = context.roster ∧
    contribution.worker = context.roster contribution.slot ∧
    contribution.backendTranscript ≠ 0 ∧
    contribution.contributionDigest =
      backend.digestOf context contribution.slot contribution.backendTranscript := by
  rcases hcanonical with
    ⟨hsession, hrelation, hcertificate, hjoint, hprotocol, hroster,
      htranscript, hdigest, hsignature⟩
  have hworker := backend.signatureSound contribution hsignature
  refine ⟨hsession, hrelation, hcertificate, hjoint, hprotocol, hroster,
    hworker.trans ?_, htranscript, hdigest⟩
  exact congrFun hroster contribution.slot

/-! ## 2. Slot collector: duplicate and missing contributions fail closed. -/

/-- Public coordinator occupancy.  Actual contribution data is retained in the
canonical envelope below; this state isolates the one-contribution-per-slot law. -/
structure CollectorState (n : Nat) where
  received : Fin n → Bool

def recordSlot {n : Nat} (state : CollectorState n) (slot : Fin n) :
    CollectorState n :=
  { received := fun candidate => if candidate = slot then true else state.received candidate }

theorem record_slot_marks_exact_slot {n : Nat}
    (state : CollectorState n) (slot : Fin n) :
    (recordSlot state slot).received slot = true := by
  simp [recordSlot]

theorem record_slot_preserves_other {n : Nat}
    (state : CollectorState n) (slot other : Fin n)
    (hne : other ≠ slot) :
    (recordSlot state slot).received other = state.received other := by
  simp [recordSlot, hne]

/-- One successful coordinator acceptance. -/
def AcceptsContribution {n : Nat} (backend : ContributionBackend n)
    (context : ProverContext n) (before : CollectorState n)
    (contribution : WorkerContribution n) (after : CollectorState n) : Prop :=
  CanonicalContribution backend context contribution ∧
  before.received contribution.slot = false ∧
  after = recordSlot before contribution.slot

/-- The second contribution for an already accepted slot is refused before any
replacement, even when its public bytes are otherwise canonical. -/
theorem duplicate_slot_contribution_refused
    {n : Nat} {backend : ContributionBackend n}
    {context : ProverContext n}
    {before after final : CollectorState n}
    {first second : WorkerContribution n}
    (hfirst : AcceptsContribution backend context before first after)
    (hsame : second.slot = first.slot) :
    ¬ AcceptsContribution backend context after second final := by
  rcases hfirst with ⟨_, _, rfl⟩
  intro hsecond
  have halready : (recordSlot before first.slot).received second.slot = true := by
    rw [hsame]
    exact record_slot_marks_exact_slot before first.slot
  rcases hsecond with ⟨_, hfresh, _⟩
  rw [halready] at hfresh
  exact Bool.noConfusion hfresh

/-- Every roster slot must be occupied before finish. -/
def CollectorComplete {n : Nat} (state : CollectorState n) : Prop :=
  ∀ slot, state.received slot = true

theorem missing_slot_refuses_finish {n : Nat} (state : CollectorState n)
    (slot : Fin n) (hmissing : state.received slot = false) :
    ¬ CollectorComplete state := by
  intro hcomplete
  rw [hcomplete slot] at hmissing
  exact Bool.noConfusion hmissing

/-! ## 3. Substitution refusal. -/

/-- Any substitution in session, relation, certificate, joint commitment,
protocol, or complete roster breaks canonicality. -/
theorem substituted_public_context_refused
    {n : Nat} {backend : ContributionBackend n}
    (context : ProverContext n) (contribution : WorkerContribution n)
    (hwrong :
      contribution.session ≠ context.session ∨
      contribution.relation ≠ context.relation ∨
      contribution.inputCertificate ≠ context.inputCertificate ∨
      contribution.jointInputCommitment ≠ context.jointInputCommitment ∨
      contribution.protocol ≠ context.protocol ∨
      contribution.roster ≠ context.roster) :
    ¬ CanonicalContribution backend context contribution := by
  intro hcanonical
  rcases hcanonical with
    ⟨hsession, hrelation, hcertificate, hjoint, hprotocol, hroster, _⟩
  rcases hwrong with hwrong | hwrong | hwrong | hwrong | hwrong | hwrong
  · exact hwrong hsession
  · exact hwrong hrelation
  · exact hwrong hcertificate
  · exact hwrong hjoint
  · exact hwrong hprotocol
  · exact hwrong hroster

/-- A valid signature from another roster member cannot be relabelled as this
slot's worker contribution. -/
theorem substituted_worker_for_slot_refused
    {n : Nat} {backend : ContributionBackend n}
    (context : ProverContext n) (contribution : WorkerContribution n)
    (hwrong : contribution.worker ≠ context.roster contribution.slot) :
    ¬ CanonicalContribution backend context contribution := by
  intro hcanonical
  exact hwrong
    (canonical_contribution_binds_complete_context_and_slot hcanonical).2.2.2.2.2.2.1

/-! ## 4. Canonical ordered envelope and coordinator public view. -/

/-- Complete ordered envelope: its function index is the coordinator slot, and
the repeated contribution slot must equal that index. -/
structure CanonicalEnvelope {n : Nat} (backend : ContributionBackend n)
    (context : ProverContext n) where
  contributions : Fin n → WorkerContribution n
  exactSlot : ∀ slot, (contributions slot).slot = slot
  canonical : ∀ slot, CanonicalContribution backend context (contributions slot)
  bundleDigest : Digest
  bundleBound : bundleDigest =
    backend.bundleOf context (fun slot => (contributions slot).contributionDigest)

/-- The indexed envelope cannot contain one contribution in two roster slots. -/
theorem canonical_envelope_contributions_are_slot_injective
    {n : Nat} {backend : ContributionBackend n}
    {context : ProverContext n}
    (envelope : CanonicalEnvelope backend context) :
    Function.Injective envelope.contributions := by
  intro left right heq
  have hslot := congrArg WorkerContribution.slot heq
  rw [envelope.exactSlot left, envelope.exactSlot right] at hslot
  exact hslot

/-- Public coordinator observation.  There is intentionally no witness-share,
opening, scalar, or blinding field. -/
structure CoordinatorView (n : Nat) where
  context : ProverContext n
  transcriptDigests : Fin n → Digest
  bundleDigest : Digest

def coordinatorView {n : Nat} {backend : ContributionBackend n}
    {context : ProverContext n}
    (envelope : CanonicalEnvelope backend context) : CoordinatorView n :=
  { context
    transcriptDigests := fun slot => (envelope.contributions slot).backendTranscript
    bundleDigest := envelope.bundleDigest }

/-- Exact public-view theorem: the coordinator sees the configured public
context and one ordered nonzero backend transcript digest per exact slot. -/
theorem coordinator_view_is_exact_public_context_and_ordered_digests
    {n : Nat} {backend : ContributionBackend n}
    {context : ProverContext n}
    (envelope : CanonicalEnvelope backend context) :
    (coordinatorView envelope).context = context ∧
    (∀ slot,
      (coordinatorView envelope).transcriptDigests slot =
        (envelope.contributions slot).backendTranscript ∧
      (envelope.contributions slot).backendTranscript ≠ 0 ∧
      (envelope.contributions slot).slot = slot) ∧
    (coordinatorView envelope).bundleDigest =
      backend.bundleOf context
        (fun slot => (envelope.contributions slot).contributionDigest) := by
  refine ⟨rfl, ?_, envelope.bundleBound⟩
  intro slot
  refine ⟨rfl, ?_, envelope.exactSlot slot⟩
  exact (envelope.canonical slot).2.2.2.2.2.2.1

/-- Model of the API exclusion property: supplying different worker-private
process values cannot alter the coordinator observation when the same public
envelope is released. -/
def observeWithPrivateStates {n : Nat} {backend : ContributionBackend n}
    {context : ProverContext n} {Secret : Type}
    (envelope : CanonicalEnvelope backend context)
    (_privateStates : Fin n → Secret) : CoordinatorView n :=
  coordinatorView envelope

theorem coordinator_view_ignores_worker_private_states
    {n : Nat} {backend : ContributionBackend n}
    {context : ProverContext n} {Secret : Type}
    (envelope : CanonicalEnvelope backend context)
    (privateA privateB : Fin n → Secret) :
    observeWithPrivateStates envelope privateA =
      observeWithPrivateStates envelope privateB :=
  rfl

/-! ## 5. Explicit all-workers-collude residual. -/

/-- n-of-n additive custody.  `reconstructs` is exactly the sharing invariant,
not a privacy theorem. -/
structure AdditiveCustody (n : Nat) (A : Type) [AddCommMonoid A] where
  shares : Fin n → A
  privateWitness : A
  reconstructs : ∑ slot, shares slot = privateWitness

def reconstructAllWorkers {n : Nat} {A : Type} [AddCommMonoid A]
    (custody : AdditiveCustody n A) : A :=
  ∑ slot, custody.shares slot

/-- **Named privacy floor.**  If every worker colludes, their complete additive
view reconstructs the private witness.  The public-only coordinator theorem
above makes no claim against this coalition. -/
theorem all_workers_collude_reconstruct_private_witness
    {n : Nat} {A : Type} [AddCommMonoid A]
    (custody : AdditiveCustody n A) :
    reconstructAllWorkers custody = custody.privateWitness :=
  custody.reconstructs

/-! The public observation is structurally independent of the private custody
and all-collude reconstruction layer. -/
#assert_not_depends_on Market.DistributedPrivateProverBoundary.coordinatorView [
  Market.DistributedPrivateProverBoundary.AdditiveCustody,
  Market.DistributedPrivateProverBoundary.reconstructAllWorkers]

#assert_all_clean [
  Market.DistributedPrivateProverBoundary.canonical_contribution_binds_complete_context_and_slot,
  Market.DistributedPrivateProverBoundary.record_slot_marks_exact_slot,
  Market.DistributedPrivateProverBoundary.record_slot_preserves_other,
  Market.DistributedPrivateProverBoundary.duplicate_slot_contribution_refused,
  Market.DistributedPrivateProverBoundary.missing_slot_refuses_finish,
  Market.DistributedPrivateProverBoundary.substituted_public_context_refused,
  Market.DistributedPrivateProverBoundary.substituted_worker_for_slot_refused,
  Market.DistributedPrivateProverBoundary.canonical_envelope_contributions_are_slot_injective,
  Market.DistributedPrivateProverBoundary.coordinator_view_is_exact_public_context_and_ordered_digests,
  Market.DistributedPrivateProverBoundary.coordinator_view_ignores_worker_private_states,
  Market.DistributedPrivateProverBoundary.all_workers_collude_reconstruct_private_witness]

end Market.DistributedPrivateProverBoundary
