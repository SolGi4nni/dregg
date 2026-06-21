/-
# Metatheory.PolisAuthGrand — the grounded synthesis: no adversary captures the authority state.

One statement tying the grounded polis together. The polis floor over `Caps` is the conjunction of
the two grounded floors:

  * `PasRefined pol` — the SUBSTANCE DISCIPLINE (authority ⊆ policy): stops **laundering**
    (authority growth). Deployed (`Dregg2.Authority.confinement_preserved`).
  * `AllReach target agents` — every agent can still REACH/derive the authority it needs: stops
    **foreclosure** (domination-by-revocation). The polis's genuine addition (`PolisAuthReach`).

`grand_no_capture`: from any legitimate-and-viable start, NO controller (no adversary) can break this
combined floor — at every tick authority stays policy-bounded AND every agent's goal stays reachable.
A move that breaks EITHER axis is refused by the grounded governor (`combine_monotone`). This is the
theory of knowledge/authority coordination, as one guarantee, over dregg's real nouns.
-/
import Metatheory.PolisAuthGame
import Metatheory.PolisAuthReach
import Dregg2.Authority.Positional

namespace Metatheory.PolisAuthGrand

open Dregg2.Authority Metatheory.PolisGovernorTheory Metatheory.PolisAuthReach

/-- A turn proposes the next cap-state (as in `authGame`). -/
def capsStep : Caps → Caps → Caps := fun _ caps' => caps'

/-- **The grounded polis floor**: the substance discipline AND everyone reaches their goal. -/
def groundedFloor (pol : Policy) (target : Auth) (agents : List Label) : Caps → Prop :=
  combineFloor (PasRefined pol) (AllReach target agents)

open Classical in
noncomputable instance (pol : Policy) (target : Auth) (agents : List Label) :
    DecidablePred (groundedFloor pol target agents) := fun _ => Classical.propDecidable _

open Classical in
/-- The grounded governor: admit the proposed cap-state iff it keeps the substance discipline AND
keeps everyone viable, else shield. -/
noncomputable def groundedGov (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) : Caps :=
  genGovStep (groundedFloor pol target agents) capsStep caps caps'

/-- **`grand_no_capture` — THE grounded synthesis.** From any legitimate-and-viable start, NO
controller (no adversary) can break the grounded floor: at every tick the substance discipline holds
(no laundering) AND every agent still reaches its goal (no foreclosure). `genGov_safe` over
`PasRefined ∧ AllReach`, quantified over every opaque controller. -/
theorem grand_no_capture (pol : Policy) (target : Auth) (agents : List Label)
    (caps0 : Caps) (h : groundedFloor pol target agents caps0) (ctrl : Caps → Caps) (n : Nat) :
    groundedFloor pol target agents
      (genGovTraj (groundedFloor pol target agents) capsStep ctrl caps0 n) :=
  genGov_safe (groundedFloor pol target agents) capsStep ctrl caps0 h n

/-- **Laundering is refused** — a move that grows authority beyond policy breaks `PasRefined`, so the
combined floor fails and the grounded governor shields (`combine_monotone`, the `PasRefined` axis). -/
theorem grounded_refuses_laundering (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (hbad : ¬ PasRefined pol caps') :
    groundedGov pol target agents caps caps' = caps := by
  unfold groundedGov genGovStep
  rw [if_neg (fun hf => hbad hf.1)]

/-- **Foreclosure is refused** — a move that cuts an agent's last path to its goal breaks `AllReach`,
so the combined floor fails and the grounded governor shields (the `AllReach` axis). -/
theorem grounded_refuses_foreclosure (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (hbad : ¬ AllReach target agents caps') :
    groundedGov pol target agents caps caps' = caps := by
  unfold groundedGov genGovStep
  rw [if_neg (fun hf => hbad hf.2)]

/-! ## Concrete non-vacuity, on dregg's authorities. -/

/-- A read-only policy. -/
def polG : Policy := [⟨A, Auth.read, A⟩, ⟨B, Auth.read, B⟩]

/-- A legitimate-and-viable start: A and B each hold their own `read` endpoint. -/
def capsStart : Caps := fun s =>
  if s = A then [.endpoint A [Auth.read]]
  else if s = B then [capRead] else []

theorem capsStart_refined : PasRefined polG capsStart := by
  intro s t c a hc hceq ha
  unfold capsStart at hc
  by_cases hs : s = A
  · subst hs
    simp only [↓reduceIte, List.mem_singleton] at hc
    obtain rfl := hc
    simp only [capAuthConferred, List.mem_singleton] at ha; subst ha
    have ht : t = A := by injection hceq with h1 _; exact h1.symm
    subst ht; unfold polG authorizedEdge; decide
  · by_cases hs' : s = B
    · subst hs'
      simp only [B, A, Nat.reduceEqDiff, ↓reduceIte, List.mem_singleton] at hc
      obtain rfl := hc
      simp only [capRead, capAuthConferred, List.mem_singleton] at ha; subst ha
      have ht : t = B := by simp only [capRead] at hceq; injection hceq with h1 _; exact h1.symm
      subst ht; unfold polG authorizedEdge; decide
    · simp only [if_neg hs, if_neg hs'] at hc; exact absurd hc List.not_mem_nil

/-- The start satisfies the FULL grounded floor (legitimate AND everyone viable). -/
theorem capsStart_grounded : groundedFloor polG tgt agents0 capsStart := by
  refine ⟨capsStart_refined, ?_⟩
  decide

/-- A laundering state: B holds a `write` cap the policy never granted — `PasRefined` fails. -/
def capsLaunder : Caps := fun s =>
  if s = B then [.endpoint B [Auth.write]] else []

theorem capsLaunder_not_refined : ¬ PasRefined polG capsLaunder := by
  intro h
  have hedge := h B B (.endpoint B [Auth.write]) Auth.write
    (by unfold capsLaunder; simp only [↓reduceIte]; exact List.mem_singleton.mpr rfl)
    rfl
    (by simp only [capAuthConferred]; exact List.mem_singleton.mpr rfl)
  exact absurd hedge (by unfold polG authorizedEdge; decide)

/-- **Laundering refused, concretely.** -/
theorem launder_refused : groundedGov polG tgt agents0 capsStart capsLaunder = capsStart :=
  grounded_refuses_laundering polG tgt agents0 capsStart capsLaunder capsLaunder_not_refined

/-- **Foreclosure refused, concretely** (reusing `PolisAuthReach.capsDropAll`, where B can no longer
reach `read`). -/
theorem foreclosure_refused :
    groundedGov polG tgt agents0 capsStart capsDropAll = capsStart :=
  grounded_refuses_foreclosure polG tgt agents0 capsStart capsDropAll
    (fun h => foreclosure_cuts_all_paths (h B (by decide)))

end Metatheory.PolisAuthGrand
