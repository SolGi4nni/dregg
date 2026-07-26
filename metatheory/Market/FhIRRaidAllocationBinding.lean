/-
# Market.FhIRRaidAllocationBinding — exact optimizer certificate → raid assignment

`QpExternalProgramBinding` already proves the hard optimizer fact: an exact
SDD-plus-KKT `FHQPB001` bundle is globally optimal for an independently compiled
fhIR problem once every public problem field `(P,q,A,l,u)` is identical.  The
game-facing raid mechanic has one additional boundary.  Its witnessed predicate
must bind that optimizer statement to:

* the exact ordered raid roster;
* the exact one-copy assignment and selected seat;
* the roster actor written into the post-state slot; and
* the exact objective recomputed from the authorized problem and assignment.

This module states that smallest composition law.  `Backend.sound` is the
explicit wire/checker/refinement assumption: an accepted proof extracts an exact
bundle for an embedded decoded problem and complete problem identity with the
public raid statement.  Lean does not infer this from bytes, a digest, or a
solver report.

The resulting theorem says the assignment actually consumed by the game is
one-copy feasible and globally optimal for the authorized fhIR policy.  The
refusal theorems show that the same proof object cannot be spent under a changed
roster or changed quadratic/linear objective, even if a host tries to reuse it.

Pure.  This is the semantic law behind
`circuit-prove/tests/fhir_verified_raid_allocation.rs`; canonical wire parsing,
fixed-point lifting, program-digest collision resistance, and the Rust-to-Lean
checker refinement remain the named backend premise.
-/
import Market.QpExternalProgramBinding
import Dregg2.Tactics

namespace Market.FhIRRaidAllocationBinding

open scoped BigOperators

set_option autoImplicit false

/-! ## 1. The complete game-facing public statement. -/

/-- An independently authored raid policy: exact fhIR QP plus ordered roster. -/
structure RaidPolicy (n mc : Nat) where
  problem : Market.RustQpProblem n mc
  roster : Fin n → Nat

/-- The public statement checked by the witnessed predicate.  `assignment` is
the exact vector whose selected actor is written into the game cell. -/
structure RaidStatement (n mc : Nat) where
  program : Market.RustQpProblem n mc
  roster : Fin n → Nat
  assignment : Fin n → ℚ
  selectedSeat : Fin n
  selectedActor : Nat
  objective : ℚ

/-- The mechanic is indivisible even though the underlying QP is continuous:
every coordinate is zero or one and exactly one coordinate is selected. -/
def OneCopyAllocation {n : Nat} (assignment : Fin n → ℚ) : Prop :=
  (∀ i, assignment i = 0 ∨ assignment i = 1) ∧
  ∑ i, assignment i = 1

/-- Exact public-policy weld.  Complete QP identity pins all five optimizer
fields; the remaining equalities pin the game interpretation. -/
def RaidStatement.MatchesPolicy {n mc : Nat}
    (statement : RaidStatement n mc) (policy : RaidPolicy n mc) : Prop :=
  Market.QpExternalProgramBinding.CompleteProblemIdentity
    statement.program policy.problem ∧
  statement.roster = policy.roster ∧
  OneCopyAllocation statement.assignment ∧
  statement.assignment statement.selectedSeat = 1 ∧
  statement.selectedActor = statement.roster statement.selectedSeat ∧
  statement.objective =
    Market.rustQpObjective statement.program statement.assignment

/-- Feasibility visible to the game: the selected vector is feasible for the
authorized fhIR policy and is a one-copy allocation naming the selected actor. -/
def GameFacingFeasible {n mc : Nat} (policy : RaidPolicy n mc)
    (statement : RaidStatement n mc) : Prop :=
  Market.RustQpFeasible policy.problem statement.assignment ∧
  OneCopyAllocation statement.assignment ∧
  statement.assignment statement.selectedSeat = 1 ∧
  statement.selectedActor = policy.roster statement.selectedSeat

/-- Global optimality of the exact assignment consumed by the game. -/
def GameFacingOptimal {n mc : Nat} (policy : RaidPolicy n mc)
    (statement : RaidStatement n mc) : Prop :=
  ∀ candidate : Fin n → ℚ,
    Market.RustQpFeasible policy.problem candidate →
    Market.rustQpObjective policy.problem statement.assignment ≤
      Market.rustQpObjective policy.problem candidate

/-! ## 2. Explicit optimizer backend meaning. -/

/-- Semantic extraction from accepted optimizer bytes.  The bundle may embed a
decoded problem distinct as a Lean object; `programBound` is the exact external
fhIR binding step which proves it is the statement's program. -/
structure ExactOptimizerMeaning {n mc : Nat}
    (statement : RaidStatement n mc) : Type where
  embedded : Market.RustQpProblem n mc
  admittedP : Matrix (Fin n) (Fin n) ℚ
  dual : Fin mc → ℚ
  bundle : Market.QpCertificateBundle.ExactQpCertificateBundle
    embedded admittedP statement.assignment dual
  programBound : Market.QpExternalProgramBinding.CompleteProblemIdentity
    embedded statement.program

/-- Cryptographic/codec/checker backend.  Verification is statement-directed:
the proof does not select its roster, assignment, actor, or objective. -/
structure Backend (n mc : Nat) where
  Proof : Type
  verify : RaidStatement n mc → Proof → Bool
  sound : ∀ statement proof, verify statement proof = true →
    Nonempty (ExactOptimizerMeaning statement)

structure Receipt {n mc : Nat} (backend : Backend n mc) where
  proof : backend.Proof

/-- Acceptance is conjunctive: exact policy/game binding plus backend proof
verification over that complete statement. -/
def Receipt.Accepts {n mc : Nat} {backend : Backend n mc}
    (receipt : Receipt backend) (policy : RaidPolicy n mc)
    (statement : RaidStatement n mc) : Prop :=
  statement.MatchesPolicy policy ∧
  backend.verify statement receipt.proof = true

theorem acceptance_exposes_policy_binding
    {n mc : Nat} {backend : Backend n mc}
    {receipt : Receipt backend} {policy : RaidPolicy n mc}
    {statement : RaidStatement n mc}
    (haccept : receipt.Accepts policy statement) :
    statement.MatchesPolicy policy :=
  haccept.1

/-! ## 3. The optimizer → game keystone. -/

/-- **Raid allocation composition.**  Backend acceptance plus complete public
statement binding proves the exact game assignment is QP-feasible, one-copy,
names the roster-selected actor, and is globally optimal for every feasible
alternative.  The claimed objective is also the exact authorized objective. -/
theorem accepted_allocation_is_game_feasible_and_globally_optimal
    {n mc : Nat} {backend : Backend n mc}
    {receipt : Receipt backend} {policy : RaidPolicy n mc}
    {statement : RaidStatement n mc}
    (haccept : receipt.Accepts policy statement) :
    GameFacingFeasible policy statement ∧
    GameFacingOptimal policy statement ∧
    statement.objective =
      Market.rustQpObjective policy.problem statement.assignment := by
  rcases haccept with
    ⟨⟨hstatementProgram, hroster, honeCopy, hselected, hactor,
      hobjective⟩, hverify⟩
  rcases backend.sound statement receipt.proof hverify with ⟨meaning⟩
  have hembedded : meaning.embedded = statement.program :=
    Market.QpExternalProgramBinding.complete_problem_identity_eq
      meaning.programBound
  have hauthorized : statement.program = policy.problem :=
    Market.QpExternalProgramBinding.complete_problem_identity_eq
      hstatementProgram
  have hall : meaning.embedded = policy.problem :=
    hembedded.trans hauthorized
  have hfeasible : Market.RustQpFeasible policy.problem statement.assignment := by
    simpa [hall] using meaning.bundle.kkt.feasible
  have hoptimal : GameFacingOptimal policy statement := by
    intro candidate hcandidate
    have hcandidate' : Market.RustQpFeasible meaning.embedded candidate := by
      simpa [hall] using hcandidate
    have h := Market.QpCertificateBundle.exact_bundle_global_optimal
      meaning.bundle hcandidate'
    simpa [hall] using h
  refine ⟨⟨hfeasible, honeCopy, hselected, ?_⟩, hoptimal, ?_⟩
  · exact hactor.trans (congrFun hroster statement.selectedSeat)
  · exact hobjective.trans <| by rw [hauthorized]

/-! ## 4. Certificate-reuse refusal laws. -/

/-- The same proof/statement accepted for one roster cannot be spent against a
policy with a different ordered roster. -/
theorem accepted_certificate_not_reusable_after_roster_change
    {n mc : Nat} {backend : Backend n mc}
    (receipt : Receipt backend) (statement : RaidStatement n mc)
    (original changed : RaidPolicy n mc)
    (haccept : receipt.Accepts original statement)
    (hroster : changed.roster ≠ original.roster) :
    ¬ receipt.Accepts changed statement := by
  intro hchanged
  have horiginal := (acceptance_exposes_policy_binding haccept).2.1
  have hnew := (acceptance_exposes_policy_binding hchanged).2.1
  exact hroster (hnew.symm.trans horiginal)

/-- Reusing the proof after changing the quadratic objective matrix is refused
by complete fhIR program identity, before optimality is transported. -/
theorem accepted_certificate_not_reusable_after_quadratic_objective_change
    {n mc : Nat} {backend : Backend n mc}
    (receipt : Receipt backend) (statement : RaidStatement n mc)
    (original changed : RaidPolicy n mc)
    (haccept : receipt.Accepts original statement)
    (hobjective : changed.problem.p ≠ original.problem.p) :
    ¬ receipt.Accepts changed statement := by
  intro hchanged
  have horiginal := Market.QpExternalProgramBinding.complete_problem_identity_eq
    (acceptance_exposes_policy_binding haccept).1
  have hnew := Market.QpExternalProgramBinding.complete_problem_identity_eq
    (acceptance_exposes_policy_binding hchanged).1
  exact hobjective (congrArg Market.RustQpProblem.p (hnew.symm.trans horiginal))

/-- The dangerous same-`P`, different-`q` reuse is independently refused. -/
theorem accepted_certificate_not_reusable_after_linear_objective_change
    {n mc : Nat} {backend : Backend n mc}
    (receipt : Receipt backend) (statement : RaidStatement n mc)
    (original changed : RaidPolicy n mc)
    (haccept : receipt.Accepts original statement)
    (hobjective : changed.problem.q ≠ original.problem.q) :
    ¬ receipt.Accepts changed statement := by
  intro hchanged
  have horiginal := Market.QpExternalProgramBinding.complete_problem_identity_eq
    (acceptance_exposes_policy_binding haccept).1
  have hnew := Market.QpExternalProgramBinding.complete_problem_identity_eq
    (acceptance_exposes_policy_binding hchanged).1
  exact hobjective (congrArg Market.RustQpProblem.q (hnew.symm.trans horiginal))

/-- Even with a valid optimizer proof, a host cannot substitute a reported
objective scalar inconsistent with the exact authorized problem and selected
assignment. -/
theorem substituted_game_objective_refused
    {n mc : Nat} {backend : Backend n mc}
    (receipt : Receipt backend) (policy : RaidPolicy n mc)
    (statement : RaidStatement n mc)
    (hobjective : statement.objective ≠
      Market.rustQpObjective statement.program statement.assignment) :
    ¬ receipt.Accepts policy statement := by
  intro haccept
  exact hobjective (acceptance_exposes_policy_binding haccept).2.2.2.2.2

/-- A host-selected loser cannot replace the certificate-selected seat while
retaining the rest of the statement. -/
theorem substituted_selected_actor_refused
    {n mc : Nat} {backend : Backend n mc}
    (receipt : Receipt backend) (policy : RaidPolicy n mc)
    (statement : RaidStatement n mc)
    (hactor : statement.selectedActor ≠
      statement.roster statement.selectedSeat) :
    ¬ receipt.Accepts policy statement := by
  intro haccept
  exact hactor (acceptance_exposes_policy_binding haccept).2.2.2.2.1

/-! The public binding layer stays structural: it may not acquire optimizer
soundness merely by being placed next to the backend. -/
-- POSITIVE CONTROL for the rejector below: both are reached only through the acceptance proof.
#assert_depends_on Market.FhIRRaidAllocationBinding.acceptance_exposes_policy_binding
  [Market.FhIRRaidAllocationBinding.Backend.verify, Market.FhIRRaidAllocationBinding.Receipt.proof]

#assert_not_depends_on Market.FhIRRaidAllocationBinding.RaidStatement.MatchesPolicy [
  Market.QpCertificateBundle.ExactKktAccepted,
  Market.QpCertificateBundle.exact_bundle_global_optimal,
  Market.rustExactKkt_optimal]

#assert_all_clean [
  Market.FhIRRaidAllocationBinding.acceptance_exposes_policy_binding,
  Market.FhIRRaidAllocationBinding.accepted_allocation_is_game_feasible_and_globally_optimal,
  Market.FhIRRaidAllocationBinding.accepted_certificate_not_reusable_after_roster_change,
  Market.FhIRRaidAllocationBinding.accepted_certificate_not_reusable_after_quadratic_objective_change,
  Market.FhIRRaidAllocationBinding.accepted_certificate_not_reusable_after_linear_objective_change,
  Market.FhIRRaidAllocationBinding.substituted_game_objective_refused,
  Market.FhIRRaidAllocationBinding.substituted_selected_actor_refused]

end Market.FhIRRaidAllocationBinding
