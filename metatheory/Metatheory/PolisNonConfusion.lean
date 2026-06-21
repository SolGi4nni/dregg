/-
# Metatheory.PolisNonConfusion — the constitution's NON-CONFUSION FLOOR, bound to the
# DEPLOYED dregg non-amplification theorems.

gpt5.5's "shadow ≠ resource" sanity floor — "the substrate refuses to let symbolic
appearance become operative power merely by being repeated." This is the structural floor
that governs the politician's would-be amplification frauds. Rather than restate it, this
file re-pins the ALREADY-DEPLOYED, kernel-clean dregg theorems as constitutional
invariants: a regression in any of them fails THIS build too, so the non-confusion floor is
CI-enforced as part of the polis subtree (`lake build Metatheory.*`).

Three of the five non-confusion legs are deployed (pinned below); the schema is
"linear event · persistent trace · authorized re-entry" (`Metatheory.Polis`). The two OPEN
legs — `certificate ↛ capability` (the dereliction guard) and `observation ↛ resolution`
(the one-shot promise resolver) — remain the named frontier; red is honest.
-/
import Dregg2.Tactics
import Dregg2.Deos.Transclusion
import Dregg2.Exec.FullForestAuth
import Dregg2.AssuranceCase
import Metatheory.Dynamics.Production
import Dregg2.Await
import Dregg2.Exec.AuthModes
import Dregg2.Apps.PreRotation
import Metatheory.ResharingChain

namespace Metatheory.PolisNonConfusion

/-! ## The authority floor as the REAL substance discipline (the deployed `Auth` camera).

The polis authority floor (`held ⊆ bound`, `DreggPolis §2`) is the deployed `granted ⊆ held`
shadow; its substance-camera form is the Iris frame-preserving update on `Auth M`:
authorized production is an `Fpu` (no third-party holding invalidated), and UNAUTHORIZED
amplification is provably NOT a production step. Re-pinned here as the constitution's
authority floor. -/

#assert_axioms Metatheory.Dynamics.production_step_fpu
#assert_axioms Metatheory.Dynamics.unauthorized_amplification_not_production

/-! ## The foundational defensive floor: deployed light-client unfoolability (anti-Mythos).

The polis's whole premise — "a stranger can check your OS can't exceed what it holds, nor be
shown a forged history" — IS the deployed `unfoolability_guarantee` (whole-history
attestation conjoined with conservation). Re-pinned here as the constitution's foundational
floor: the multi-agent constitution rides on top of this single-system guarantee. -/

#assert_axioms Dregg2.AssuranceCase.unfoolability_guarantee

/-! ## The deployed non-confusion family (re-pinned as the constitutional sanity floor).

  * `transclusion_no_amplify` — copying a transclusion does NOT copy edit authority: a quote
    of a peer cell confers no amplified authority over the source (the document-layer `!`,
    copy-by-reference, is not the linear edit handle).
  * `execFullForestG_no_amplify` — a gated turn confers ≤ what the actor holds (Miller, "only
    connectivity begets connectivity"): no effect grants more authority than was held — the
    deployed authority floor the polis spine abstracts.
  * `noteSpendFresh_rejects_double` (the double-spend leg) lives in the sidecar
    `Metatheory.PolisNonConfusionCircuit` — it pulls the circuit-emit tree, which is currently
    mid-edit by concurrent work; isolated so the rest of the floor stays green.
-/

#assert_axioms Dregg2.Deos.Transclusion.transclusion_no_amplify
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_no_amplify

/-! ## The two previously-OPEN non-confusion legs — DEPLOYED after all (census wihlga2r4).

  * `certificate ↛ capability` (the dereliction guard): a transclusion is the docuverse
    certificate — a provenanced citation of a peer's finalized field.
    `transclusion_is_observed_finalized_read` — it IS an observed read, not an exercisable
    handle; `transclusion_grants_no_unheld_authority` — the sharp negative tooth: an authority
    NOT held is conferred by NO projection of the citation (copying the certificate cannot copy
    the capability; naming the authority does not conjure it).
  * `observation ↛ resolution` (many observers, one resolver): the await observation (its four
    faces unify — `four_faces_unify` — freely-copyable syntax) is distinct from the RESOLUTION
    authority, the captured one-shot continuation. `one_shot_is_static` — any use-plan is
    statically `uses ≤ 1`; `commit_resumes_once` — commit resumes EXACTLY once;
    `rollback_discards_continuation` — abort drops it; `runtime_guard_is_double_spend` — the
    runtime-flag alternative leaves the double-spend window the static discipline removes by
    inexpressibility.
-/

#assert_axioms Dregg2.Deos.Transclusion.transclusion_is_observed_finalized_read
#assert_axioms Dregg2.Deos.Transclusion.transclusion_grants_no_unheld_authority
#assert_axioms Dregg2.Await.one_shot_is_static
#assert_axioms Dregg2.Await.commit_resumes_once
#assert_axioms Dregg2.Await.rollback_discards_continuation
#assert_axioms Dregg2.Await.runtime_guard_is_double_spend
#assert_axioms Dregg2.Await.four_faces_unify

/-! ## The executor-coupled authority gate + the real KERI human floor — DEPLOYED, pinned.

  * `captp_granted_le_held` — the deployed admission-mode law that a CapTP handoff's granted
    cap is ≤ what the actor held (the real `gateOK`/`capAuthorityG` `granted ⊆ held` the Polis
    authority floor abstracts; `execFullForestG_no_amplify`, the whole-turn lift, pinned above).
  * `rotChain_pinned_by_commitments` — the deployed HUMAN floor: KERI pre-rotation, "compromise
    of the current key cannot rewrite the past" — you cannot lose your identity. The resharing
    chain duals carry the same forward-secure floor to the committee-secret side. (These refine
    the `dist ≤ B` recovery shadow of `DreggPolis §2`.)
-/

#assert_axioms Dregg2.Exec.AuthModes.captp_granted_le_held
#assert_axioms Dregg2.Apps.PreRotation.rotChain_pinned_by_commitments
#assert_axioms Metatheory.ResharingChain.ReshareLink.reshare_forward_jump
#assert_axioms Metatheory.ResharingChain.ReshareLink.secret_value_survives

end Metatheory.PolisNonConfusion
