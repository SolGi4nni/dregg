/-
# ActivityOutcome — a small shared result vocabulary for Path of Angels activities

`Core.Contribution` remains the one vocabulary for bounded world-meter and relic
effects.  This module adds only the other thing an exploratory activity needs to
return: a bounded set of predeclared beta-canon *candidates*.

There is deliberately no import of `Canon`.  Producing an `ActivityOutcome` is a
claim that the named material was encountered under an authored policy; it is not
authority to promote, supersede, or otherwise edit canon.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ActivityOutcome

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

/-- One activity can surface at most this many beta-canon candidates. -/
abbrev BETA_CANDIDATE_LIMIT : Nat := 16

/-- A signed activity definition may predeclare a larger candidate catalogue than
one run is allowed to return. -/
abbrev BETA_CATALOGUE_LIMIT : Nat := 4096

/-- The exact mission policy and beta-candidate allowlist fixed before play. -/
structure Policy where
  mission : MissionSpec
  allowedBeta : Finset ArtifactRef
  resultLimit : Fin (BETA_CANDIDATE_LIMIT + 1)
  catalogue_bounded : allowedBeta.card ≤ BETA_CATALOGUE_LIMIT
deriving DecidableEq

/-- Wire-shaped result.  It is never settled directly. -/
structure Raw where
  contribution : RawContribution
  betaCandidates : List ArtifactRef
deriving DecidableEq

/-- Checked result shared by expeditions and future minigames.  The proof fields
make the two authorities explicit: the mission bounds the contribution, while the
activity policy bounds and predeclares beta candidates. -/
structure Checked (policy : Policy) where
  contribution : Contribution
  betaCandidates : Finset ArtifactRef
  contribution_accepted : policy.mission.acceptsContribution contribution = true
  beta_candidates_declared : betaCandidates ⊆ policy.allowedBeta
  beta_candidates_bounded : betaCandidates.card ≤ policy.resultLimit.val
deriving DecidableEq

/-- Fail-closed validation.  Duplicate candidates refuse instead of being silently
deduplicated, so the accepted set is an exact projection of the submitted list. -/
def validate (policy : Policy) (raw : Raw) : Option (Checked policy) := do
  let contribution ← validateContribution raw.contribution
  if hc : policy.mission.acceptsContribution contribution = true then
    if _hn : raw.betaCandidates.Nodup then
      let candidates := raw.betaCandidates.toFinset
      if hd : candidates ⊆ policy.allowedBeta then
        if hb : candidates.card ≤ policy.resultLimit.val then
          some {
            contribution
            betaCandidates := candidates
            contribution_accepted := hc
            beta_candidates_declared := hd
            beta_candidates_bounded := hb
          }
        else none
      else none
    else none
  else none

theorem validate_some_contribution_accepted (policy : Policy) (raw : Raw)
    (checked : Checked policy) (_h : validate policy raw = some checked) :
    policy.mission.acceptsContribution checked.contribution = true :=
  checked.contribution_accepted

theorem validate_some_candidates_declared (policy : Policy) (raw : Raw)
    (checked : Checked policy) (_h : validate policy raw = some checked) :
    checked.betaCandidates ⊆ policy.allowedBeta :=
  checked.beta_candidates_declared

theorem validate_some_candidates_exact (policy : Policy) (raw : Raw)
    (checked : Checked policy) (h : validate policy raw = some checked) :
    checked.betaCandidates = raw.betaCandidates.toFinset := by
  unfold validate at h
  cases hc : validateContribution raw.contribution with
  | none => simp [hc] at h
  | some contribution =>
      simp only [hc] at h
      split at h
      · split at h
        · split at h
          · dsimp at h
            split at h
            · injection h with heq
              rw [← heq]
            · contradiction
          · simp at h
        · simp at h
      · simp at h

theorem validate_some_candidates_bounded (policy : Policy) (raw : Raw)
    (checked : Checked policy) (_h : validate policy raw = some checked) :
    checked.betaCandidates.card ≤ BETA_CANDIDATE_LIMIT :=
  le_trans checked.beta_candidates_bounded (Nat.lt_succ_iff.mp policy.resultLimit.isLt)

theorem duplicate_candidates_refused (policy : Policy) (raw : Raw)
    (hdup : ¬ raw.betaCandidates.Nodup) : validate policy raw = none := by
  simp [validate, hdup]

theorem contribution_overflow_refused (policy : Policy) (raw : Raw)
    (hover : METRIC_LIMIT < raw.contribution.intel) : validate policy raw = none := by
  simp [validate, validateContribution, Nat.not_le.mpr hover]

theorem zero_candidate_policy_returns_no_candidates (policy : Policy)
    (hzero : policy.resultLimit.val = 0) (raw : Raw) (checked : Checked policy)
    (_h : validate policy raw = some checked) : checked.betaCandidates = ∅ := by
  have hcard : checked.betaCandidates.card = 0 :=
    Nat.eq_zero_of_le_zero (hzero ▸ checked.beta_candidates_bounded)
  exact Finset.card_eq_zero.mp hcard

#assert_axioms validate_some_contribution_accepted
#assert_axioms validate_some_candidates_declared
#assert_axioms validate_some_candidates_exact
#assert_axioms validate_some_candidates_bounded
#assert_axioms duplicate_candidates_refused
#assert_axioms contribution_overflow_refused
#assert_axioms zero_candidate_policy_returns_no_candidates

end Dregg2.Games.PathOfAngels.ActivityOutcome
