/-
# Dregg2.Protocol.WorkflowGuard — the workflow's gates re-expressed as `Spec.Guard` instances.

`Protocol/Workflow.lean` is the executable "DocuSign-for-workflows" demonstrator: author→reviewer→CI,
every step capability-gated, phase-ordered, and attested via `CryptoKernel.verify`. It already
proves its guarantees (`exec_authorized` / `exec_in_order` / `exec_attested` / `merge_requires_approved`)
directly over `exec`.

This module re-founds those guarantees on the abstract `Spec.Guard` law: each gate is expressed as a
`Spec.Guard` term and proved to coincide exactly with the corresponding `Guard.admits`. The three gates:

  1. **authorization** — "only the authorized signer" — a `firstParty` Guard on the actor/role field.
  2. **phase-ordering** — "release only after review" — a `firstParty` Guard on the phase field.
  3. **attestation** — "the step carries a verifying proof" — a `witnessed` Guard at the §8 verify
     seam (`CryptoKernel.verify`, ZK-capable). This is the honest §8 seam, not a gap.

`workflow_step_admits_iff_guards` ties the whole step to the conjunction (`Guard.all`) of the three
gates: the step commits exactly when the abstract Guard web admits it.

Faithful `↔`s with real content.
-/
import Dregg2.Protocol.Workflow
import Dregg2.Spec.Guard

namespace Dregg2.Protocol.WorkflowGuard

open Dregg2.Protocol.Workflow
open Dregg2.Spec
open Dregg2.Crypto
open Dregg2.Laws

/-! ## §1 — The `Request`: the facts a workflow gate reads.

The gate reads the three fields `exec`'s `if`-guard inspects: step kind, actor, and current
phase. The attestation is supplied separately through the verify seam's witness map (§4),
exactly as `Spec.Guard.admits` splits demand from supply. -/

/-- **`WFRequest`** — the facts a workflow gate reads: the step, the actor taking it, and
the phase the workflow is in. This IS the trio `Workflow.exec` decides against. -/
structure WFRequest where
  step  : StepKind
  actor : Party
  phase : Phase
  deriving Repr

/-! ## §2 — The three gates as `Spec.Guard` terms. -/

variable {Digest Proof : Type} [AddCommGroup Digest]

/-- **The authorization gate (`firstParty`).** Admits iff `req.actor = authorizedParty req.step`.
The role/cap check is decidable, so it is a `firstParty` Guard. -/
def authGuard {Statement : Type} : Guard WFRequest Statement :=
  Guard.firstParty (fun req => decide (req.actor = authorizedParty req.step))

/-- **The phase-ordering gate (`firstParty`).** Admits iff `req.phase = precond req.step` —
the choreography precondition. Decidable ⇒ `firstParty`. -/
def orderGuard {Statement : Type} : Guard WFRequest Statement :=
  Guard.firstParty (fun req => decide (req.phase = precond req.step))

/-- **The attestation gate (`witnessed`).** A `witnessed` Guard at the §8 verify seam over
`stmt`. `admits` routes through `Verifiable.Verify stmt (w stmt)`, i.e. `CryptoKernel.verify
stmt att` under the natural witness supply. ZK-capable, fail-closed. -/
def attestGuard (stmt : Digest) : Guard WFRequest Digest :=
  Guard.witnessed stmt

/-- **The whole-step gate** — the conjunction (`Guard.all`, the meet ∧) of the three gates.
This is the abstract Guard web for one workflow step: authorized AND in-order AND attested. -/
def stepGuard (stmt : Digest) : Guard WFRequest Digest :=
  Guard.all [authGuard, orderGuard, attestGuard stmt]

/-! ## §3 — The natural witness supply.

`Guard.admits` takes a witness map `w : Statement → Witness` supplied at evaluation time. The
workflow's attestation `att : Proof` is the witness for the step's statement; the natural
supply is the constant map `fun _ => att`. (For the `firstParty` gates the supply is
irrelevant — they never touch the seam.) -/

/-- The witness supply that hands the workflow's attestation `att` to the verify seam. -/
def wsupply (att : Proof) : Digest → Proof := fun _ => att

/-! ## §4 — The refinement equivalences.

Each concrete gate check coincides exactly with the corresponding `Guard.admits`. The verify
oracle is the `Verifiable Digest Proof` instance induced by `CryptoKernel`, so the witnessed
branch's `Verify` is `CryptoKernel.verify`. -/

section Refinement

variable [CryptoKernel Digest Proof]

/-- **`workflow_authz_is_guard`.** The concrete authorization check (`actor = authorizedParty s`)
holds iff the abstract `authGuard` admits the request. -/
theorem workflow_authz_is_guard (s : StepKind) (actor : Party) (phase : Phase)
    (att : Proof) :
    Guard.admits (authGuard (Statement := Digest)) ⟨s, actor, phase⟩ (wsupply att) = true
      ↔ actor = authorizedParty s := by
  unfold authGuard
  rw [Guard.admits_firstParty]
  exact decide_eq_true_iff

/-- **`workflow_order_is_guard`.** The concrete choreography check (`phase = precond s`)
holds iff the abstract `orderGuard` admits the request. -/
theorem workflow_order_is_guard (s : StepKind) (actor : Party) (phase : Phase)
    (att : Proof) :
    Guard.admits (orderGuard (Statement := Digest)) ⟨s, actor, phase⟩ (wsupply att) = true
      ↔ phase = precond s := by
  unfold orderGuard
  rw [Guard.admits_firstParty]
  exact decide_eq_true_iff

/-- **`workflow_attest_is_guard`.** The concrete attestation check
(`CryptoKernel.verify stmt att = true`) holds iff `attestGuard stmt` admits under the natural
supply. The §8 verify seam is stated — not a hidden gap. -/
theorem workflow_attest_is_guard (stmt : Digest) (s : StepKind) (actor : Party) (phase : Phase)
    (att : Proof) :
    Guard.admits (attestGuard stmt) ⟨s, actor, phase⟩ (wsupply att) = true
      ↔ CryptoKernel.verify stmt att = true := by
  unfold attestGuard wsupply
  rw [Guard.admits_witnessed]
  rfl

/-! ## §5 — The whole-step refinement. -/

/-- **`workflow_step_admits_iff_guards`.** `stepGuard stmt` admits `⟨s, actor, phase⟩` under
the natural supply iff all three concrete `Workflow.exec` checks hold. The workflow step is
admissible precisely when the abstract Guard web admits it, with no remainder. -/
theorem workflow_step_admits_iff_guards (stmt : Digest)
    (s : StepKind) (actor : Party) (phase : Phase) (att : Proof) :
    Guard.admits (stepGuard stmt) ⟨s, actor, phase⟩ (wsupply att) = true
      ↔ (actor = authorizedParty s ∧ phase = precond s
          ∧ CryptoKernel.verify stmt att = true) := by
  unfold stepGuard
  rw [Guard.admits_all]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact (workflow_authz_is_guard s actor phase att).mp
        (h authGuard (by simp))
    · exact (workflow_order_is_guard s actor phase att).mp
        (h orderGuard (by simp))
    · exact (workflow_attest_is_guard stmt s actor phase att).mp
        (h (attestGuard stmt) (by simp))
  · rintro ⟨ha, ho, hv⟩ g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact (workflow_authz_is_guard s actor phase att).mpr ha
    · exact (workflow_order_is_guard s actor phase att).mpr ho
    · exact (workflow_attest_is_guard stmt s actor phase att).mpr hv

/-- **`exec_admits_step_guard`.** Whenever `Workflow.exec` commits (returns `some`), the abstract
`stepGuard` admits the request. Every step the running workflow takes is sanctioned by the
`Spec.Guard` law. -/
theorem exec_admits_step_guard (stmt : Digest)
    {k k' : WState Proof} {s : StepKind} {actor : Party} {att : Proof}
    (h : Workflow.exec stmt k s actor att = some k') :
    Guard.admits (stepGuard stmt) ⟨s, actor, k.phase⟩ (wsupply att) = true :=
  (workflow_step_admits_iff_guards stmt s actor k.phase att).mpr
    ⟨Workflow.exec_authorized h, Workflow.exec_in_order h, Workflow.exec_attested h⟩

end Refinement

/-! ## §6 — Discriminating smoke checks (`example`/`#eval`).

On the reference kernel, the Guard web admits an authorized in-order attested step and rejects
any step that is out-of-order, unauthorized, or unattested. The refinement is non-vacuous. -/

section Smoke

open Dregg2.Crypto.Reference

/-- The good attestation under the reference kernel (echoes statement `7`). -/
private def gAtt : Reference.P := 7
/-- A bad attestation (`9 ≠ 7` ⇒ `verify` rejects). -/
private def bAtt : Reference.P := 9

/-- ADMITS: author (0) submits from `init` with a valid attestation — all three gates pass. -/
example :
    Guard.admits (stepGuard (Digest := Reference.D) 7)
      ⟨.submit, 0, .init⟩ (wsupply gAtt) = true := by
  rw [workflow_step_admits_iff_guards]
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- REJECTS (out of order): merge from `init` — the order gate fails (precond is `approved`). -/
example :
    Guard.admits (stepGuard (Digest := Reference.D) 7)
      ⟨.merge, 2, .init⟩ (wsupply gAtt) = false := by
  rw [Bool.eq_false_iff, ne_eq, workflow_step_admits_iff_guards]
  decide

/-- REJECTS (unauthorized): reviewer (1) tries to submit — the auth gate fails. -/
example :
    Guard.admits (stepGuard (Digest := Reference.D) 7)
      ⟨.submit, 1, .init⟩ (wsupply gAtt) = false := by
  rw [Bool.eq_false_iff, ne_eq, workflow_step_admits_iff_guards]
  decide

/-- REJECTS (unattested): author submits in-order but with a bad attestation (`9 ≠ 7`) — the
attestation gate (the §8 verify seam) fails. Fail-closed. -/
example :
    Guard.admits (stepGuard (Digest := Reference.D) 7)
      ⟨.submit, 0, .init⟩ (wsupply bAtt) = false := by
  rw [Bool.eq_false_iff, ne_eq, workflow_step_admits_iff_guards]
  decide

-- The same, executable, as `#guard` (the discriminating admit/reject vector):
#guard (Guard.admits (stepGuard (Digest := Reference.D) 7)
  ⟨.submit, 0, .init⟩ (wsupply gAtt))   -- true   (authorized, in-order, attested)
#guard (Guard.admits (stepGuard (Digest := Reference.D) 7)
  ⟨.merge, 2, .init⟩ (wsupply gAtt) == false)    -- false  (out of order: can't merge from init)
#guard (Guard.admits (stepGuard (Digest := Reference.D) 7)
  ⟨.submit, 1, .init⟩ (wsupply gAtt) == false)   -- false  (unauthorized: reviewer can't submit)
#guard (Guard.admits (stepGuard (Digest := Reference.D) 7)
  ⟨.submit, 0, .init⟩ (wsupply bAtt) == false)   -- false  (unattested: bad proof 9 ≠ 7)

end Smoke

/-! ## §7 — Axiom-hygiene tripwires.

Each keystone depends only on `{propext, Classical.choice, Quot.sound}` (no `sorryAx`). -/

#assert_axioms workflow_authz_is_guard
#assert_axioms workflow_order_is_guard
#assert_axioms workflow_attest_is_guard
#assert_axioms workflow_step_admits_iff_guards
#assert_axioms exec_admits_step_guard

end Dregg2.Protocol.WorkflowGuard
