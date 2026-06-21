/-
# Metatheory.PolisAuthGrandDatalog — the GRAND no-capture theorem rides the REAL Datalog viability.

`PolisAuthGameN.groundedFloorN` packaged the grounded polis floor as
`combineFloor (PasRefined pol) (AllReach target agents)` — but its reach half `AllReach` was the
ONE-STEP heuristic of `PolisAuthReach`: `b` reaches `target` iff some held authority `a` satisfies a
single membership check `a = target ∨ a = grant ∨ a = control`, never a chain. That is the toy.

`PolisAuthReachDatalog` already replaced the heuristic with the genuine forward-chaining Datalog
consequence closure: `ReachesD target b caps := Derivable (grantRules b) (factsOf caps b)
(atomOf b target) K` — viability is membership in the bounded multi-step derivation closure of `b`'s
delegation rules, the SAME derivation object as the cross-vat discharge gate (`PolisAuthDatalog`),
where `read ← call ← grant` is a genuine 2-round chain (`one_step_insufficient` certifies it).

This file RETIRES the one-step `AllReach` at the synthesis: it lifts `ReachesD` over a roster
(`AllReachD`), packages the grounded floor with it (`groundedFloorD`), and re-proves the grand
no-capture synthesis (`grand_no_capture_D`) plus the two refusal lanes
(`grounded_refuses_laundering_D` / `grounded_refuses_foreclosure_D`) — so "no adversary captures the
polis" now holds with viability = the genuine multi-step capability-derivation closure, not a
disguised single hop.

PROVED (no `sorry`, no load-bearing `True`):
  * `grand_no_capture_D` — from ANY legitimate-and-viable start (`groundedFloorD`), for ANY policy /
    target / roster / opaque controller, the grounded floor holds at EVERY tick (`genGov_safe` over
    `PasRefined ∧ AllReachD`).
  * `grounded_refuses_laundering_D` — a move that grows authority beyond policy breaks `PasRefined`,
    so the grounded governor shields (`combine_monotone_left`).
  * `grounded_refuses_foreclosure_D` — a move that cuts SOME agent's ALL derivation paths to its goal
    breaks `AllReachD`, so the grounded governor shields (`combine_monotone_right`).
  * Concrete non-vacuity, `decide`-checked, reusing `PolisAuthReachDatalog`'s
    `capsBoth`/`capsDropRead`/`capsDropAll`: `capsDropRead` is ADMITTED (`B` still `ReachesD read` via
    the `read ← call ← grant` chain), `capsDropAll` is REFUSED (`¬ ReachesD read`).
-/
import Metatheory.PolisGovernorTheory
import Metatheory.PolisAuthReachDatalog
import Metatheory.PolisAuthViability
import Dregg2.Authority.Positional

namespace Metatheory.PolisAuthGrandDatalog

open Dregg2.Authority Metatheory.PolisGovernorTheory
open Metatheory.PolisAuthReachDatalog (ReachesD)

/-! ## §1. Multi-step reachability lifted over a roster, and the grounded floor on it. -/

/-- **Everyone reaches its goal — via the REAL multi-step derivation closure.** `AllReachD` is the
roster lift of `PolisAuthReachDatalog.ReachesD`: every agent `b` in the roster can DERIVE `target`
through the bounded forward-chaining closure of its delegation rules (not a single membership check).
This is the genuine viability the one-step `AllReach` only faked. Decidable, since `ReachesD` is. -/
def AllReachD (target : Auth) (agents : List Label) (caps : Caps) : Prop :=
  ∀ b ∈ agents, ReachesD target b caps

instance instDecAllReachD (target : Auth) (agents : List Label) (caps : Caps) :
    Decidable (AllReachD target agents caps) :=
  inferInstanceAs (Decidable (∀ b ∈ agents, ReachesD target b caps))

/-- **The grounded polis floor on REAL viability.** The substance discipline `PasRefined` AND every
agent in the roster can still DERIVE its goal authority through the multi-step closure. A
`combineFloor` of the deployed `PasRefined` and the multi-step `AllReachD` — so the whole
`genGov_*`/`combine_*` governor theory applies for free, with viability = the genuine derivation
object. -/
def groundedFloorD (pol : Policy) (target : Auth) (agents : List Label) : Caps → Prop :=
  combineFloor (PasRefined pol) (AllReachD target agents)

/-- The grounded floor projects to its substance-discipline half. -/
theorem groundedFloorD_refined {pol : Policy} {target : Auth} {agents : List Label} {caps : Caps}
    (h : groundedFloorD pol target agents caps) : PasRefined pol caps := h.1

/-- The grounded floor projects to its everyone-derives half (the REAL multi-step viability). -/
theorem groundedFloorD_reach {pol : Policy} {target : Auth} {agents : List Label} {caps : Caps}
    (h : groundedFloorD pol target agents caps) : AllReachD target agents caps := h.2

open Classical in
noncomputable instance instDecGroundedFloorD (pol : Policy) (target : Auth) (agents : List Label) :
    DecidablePred (groundedFloorD pol target agents) := fun _ => Classical.propDecidable _

/-! ## §2. The step + governor on `Caps`, for an arbitrary roster. -/

/-- A turn PROPOSES the next cap-state (identical to the other grounded files). -/
def capsStep : Caps → Caps → Caps := fun _ caps' => caps'

open Classical in
/-- **The grounded governor over REAL viability** = `genGovStep` over `groundedFloorD`: admit the
proposed cap-state iff it keeps the substance discipline AND keeps everyone DERIVING its goal through
the multi-step closure, else SHIELD. Parametric in policy/target/roster. -/
noncomputable def groundedGovD (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) : Caps :=
  genGovStep (groundedFloorD pol target agents) capsStep caps caps'

/-! ## §3. THE DELIVERABLE — `grand_no_capture_D` over the genuine derivation closure. -/

/-- **`grand_no_capture_D` — the grounded synthesis on the REAL multi-step viability.**

From ANY legitimate-and-viable start `caps0` (it satisfies `groundedFloorD`), for ANY policy, ANY
target authority, ANY roster `agents : List Label`, and ANY opaque controller `ctrl : Caps → Caps`
(the adversary, never inspected): at EVERY tick `n`, the grounded governor keeps the grounded floor
— the substance discipline holds (no laundering) AND every agent still DERIVES its goal through the
genuine forward-chaining closure (no foreclosure). This is `genGov_safe` over
`PasRefined ∧ AllReachD`, with NOTHING fixed and viability = the genuine multi-step derivation. The
toy one-step `AllReach` is retired here. -/
theorem grand_no_capture_D (pol : Policy) (target : Auth) (agents : List Label)
    (caps0 : Caps) (h0 : groundedFloorD pol target agents caps0)
    (ctrl : Caps → Caps) (n : Nat) :
    groundedFloorD pol target agents
      (genGovTraj (groundedFloorD pol target agents) capsStep ctrl caps0 n) :=
  genGov_safe (groundedFloorD pol target agents) capsStep ctrl caps0 h0 n

/-- **Both axes, every tick** (the `combine_safe` projection): the substance discipline at every tick
AND everyone-DERIVES (multi-step) at every tick, for any roster/policy/target/controller. -/
theorem grand_no_capture_D_both (pol : Policy) (target : Auth) (agents : List Label)
    (caps0 : Caps) (h0 : groundedFloorD pol target agents caps0)
    (ctrl : Caps → Caps) :
    (∀ n, PasRefined pol
        (genGovTraj (groundedFloorD pol target agents) capsStep ctrl caps0 n))
      ∧ (∀ n, AllReachD target agents
        (genGovTraj (groundedFloorD pol target agents) capsStep ctrl caps0 n)) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · exact (grand_no_capture_D pol target agents caps0 h0 ctrl n).1
  · exact (grand_no_capture_D pol target agents caps0 h0 ctrl n).2

/-! ## §4. The two refusal lanes, on the genuine derivation closure. -/

/-- **Laundering is refused (multi-step viability)** — a proposed move that grows authority beyond the
policy breaks `PasRefined`, so the combined floor fails and the grounded governor shields. Any
roster. (Direct, matching `PolisAuthGameN.grounded_refuses_laundering_N`.) -/
theorem grounded_refuses_laundering_D (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (hbad : ¬ PasRefined pol caps') :
    groundedGovD pol target agents caps caps' = caps := by
  unfold groundedGovD genGovStep capsStep
  rw [if_neg (fun hf => hbad hf.1)]

/-- **Foreclosure is refused (multi-step viability)** — a proposed move that cuts SOME agent's ALL
derivation paths to its goal breaks `AllReachD` (the genuine closure no longer derives the goal-atom),
so the combined floor fails and the grounded governor shields. This is the strictly sharper refusal:
a move is shielded only when it forecloses EVERY multi-step derivation path, not merely a direct cap.
Any roster. -/
theorem grounded_refuses_foreclosure_D (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (hbad : ¬ AllReachD target agents caps') :
    groundedGovD pol target agents caps caps' = caps := by
  unfold groundedGovD genGovStep capsStep
  rw [if_neg (fun hf => hbad hf.2)]

/-- **Honest, derivation-preserving attenuation is ADMITTED (multi-step viability)** — a move that
only drops/narrows caps (`noGrow`) from a legitimate state stays `PasRefined` by the DEPLOYED
`confinement_preserved`, and if it ALSO keeps everyone DERIVING its goal through the closure, the
governor passes it through unchanged. (Dropping a redundant cap whose derivation path survives is
admitted — least-privilege the right way.) -/
theorem grounded_admits_attenuation_D (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (h : PasRefined pol caps) (noGrow : ∀ s, caps' s ⊆ caps s)
    (hreach : AllReachD target agents caps') :
    groundedGovD pol target agents caps caps' = caps' := by
  have hgood : groundedFloorD pol target agents caps' :=
    ⟨confinement_preserved pol caps caps' h noGrow, hreach⟩
  unfold groundedGovD genGovStep capsStep
  rw [if_pos hgood]

/-! ## §5. Refusals via `combine_monotone` — adding the multi-step axis only GROWS refusals.

The keystone composition lemma: whatever the single-axis governor refuses, the combined grounded
governor refuses too. So laundering refused by the `PasRefined`-only governor stays refused, and
foreclosure refused by the `AllReachD`-only governor stays refused — adding the other axis never
weakens governance. (The genuine derivation closure is the floor here, so foreclosure means cutting
ALL multi-step paths.) -/

open Classical in
/-- The `PasRefined`-only governor over `Caps` (no viability axis). -/
noncomputable def refinedGov (pol : Policy) (caps caps' : Caps) : Caps :=
  genGovStep (PasRefined pol) capsStep caps caps'

open Classical in
/-- The `AllReachD`-only governor over `Caps` (no substance axis). -/
noncomputable def reachGovD (target : Auth) (agents : List Label) (caps caps' : Caps) : Caps :=
  genGovStep (AllReachD target agents) capsStep caps caps'

open Classical in
/-- **Laundering refusal is preserved by adding the viability axis** (`combine_monotone_left`). If the
substance-only governor shields a fresh laundering move, the combined grounded governor shields it
too. -/
theorem grounded_refuses_laundering_monotone (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (hf : refinedGov pol caps caps' = caps) (hfresh : capsStep caps caps' ≠ caps) :
    groundedGovD pol target agents caps caps' = caps := by
  -- The substance-only governor shielded a fresh move, so the move breaks `PasRefined`; therefore it
  -- breaks `PasRefined ∧ AllReachD`, so the grounded governor shields too.
  have hbreak : ¬ PasRefined pol (capsStep caps caps') :=
    genGov_shield_is_genuine (PasRefined pol) capsStep caps caps' hf hfresh
  exact grounded_refuses_laundering_D pol target agents caps caps' hbreak

open Classical in
/-- **Foreclosure refusal is preserved by adding the substance axis** (`combine_monotone_right`). If
the multi-step-viability-only governor shields a fresh foreclosing move (one that cuts all derivation
paths for some agent), the combined grounded governor shields it too. -/
theorem grounded_refuses_foreclosure_monotone (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (hg : reachGovD target agents caps caps' = caps)
    (hfresh : capsStep caps caps' ≠ caps) :
    groundedGovD pol target agents caps caps' = caps := by
  -- The viability-only governor shielded a fresh move, so the move cuts some agent's ALL derivation
  -- paths (breaks `AllReachD`); therefore it breaks the combined floor, so the grounded governor
  -- shields too.
  have hbreak : ¬ AllReachD target agents (capsStep caps caps') :=
    genGov_shield_is_genuine (AllReachD target agents) capsStep caps caps' hg hfresh
  exact grounded_refuses_foreclosure_D pol target agents caps caps' hbreak

/-! ## §6. The substance half stays general — via the deployed `confinement_preserved`. -/

/-- **`attenuation_keeps_substance_D`** — the substance-discipline half of the grounded floor is
preserved by ANY `noGrow` turn, for any policy/caps. The deployed `confinement_preserved`, never
re-proved per witness. -/
theorem attenuation_keeps_substance_D (pol : Policy) (caps caps' : Caps)
    (h : PasRefined pol caps) (noGrow : ∀ s, caps' s ⊆ caps s) :
    PasRefined pol caps' :=
  confinement_preserved pol caps caps' h noGrow

/-- The governor PRESERVES the whole grounded floor for every proposed turn from any legitimate-and-
viable state — `genGov_preserves` over the conjunction, any roster, any opaque proposer. -/
theorem grounded_governor_preserves_D (pol : Policy) (target : Auth) (agents : List Label)
    (caps caps' : Caps) (h : groundedFloorD pol target agents caps) :
    groundedFloorD pol target agents (groundedGovD pol target agents caps caps') :=
  genGov_preserves (groundedFloorD pol target agents) capsStep caps caps' h

/-! ## §7. Concrete non-vacuity — reusing `PolisAuthReachDatalog`'s grant-chain model.

We reuse the EXACT capability states from `PolisAuthReachDatalog` (`capsBoth`/`capsDropRead`/
`capsDropAll` on the single agent `B := 1`), so the multi-step `read ← call ← grant` chain is the
SAME derivation object proven there. The roster is `[B]`, the target is `read`. A policy authorizing
`⟨B, read, B⟩` and `⟨B, grant, B⟩` makes the start legitimate (`capsBoth`/`capsDropRead` both stay
`PasRefined`). All load-bearing facts are `decide`-checked; the `PasRefined` halves ride on the
deployed `confinement_preserved`, never a per-state reproof. -/

open Metatheory.PolisAuthReachDatalog (B tgt capsBoth capsDropRead capsDropAll)

/-- The single-agent roster (`B := 1`). -/
def rosterD : List Label := [B]

/-- A policy authorizing `B`'s `read` on itself AND `B`'s `grant` on itself — so both the direct
`read` cap and the `grant` chain root are policy-legitimate. -/
def polD : Policy := [⟨B, Auth.read, B⟩, ⟨B, Auth.grant, B⟩]

/-! ### §7.1 The multi-step viability facts, decided on the reused grant-chain model. -/

-- `B` reaches `read` at the start (direct fact AND the `read ← call ← grant` chain).
#guard decide (AllReachD tgt rosterD capsBoth)
-- After dropping the DIRECT read cap, `B` STILL reaches `read` via the multi-step `grant` chain: ADMIT.
#guard decide (AllReachD tgt rosterD capsDropRead)
-- After cutting ALL of `B`'s caps, no derivation path remains: the reach-half FAILS.
#guard decide (! decide (AllReachD tgt rosterD capsDropAll))

/-- The start is everyone-derives (the multi-step reach half of the grounded floor). -/
theorem capsBoth_allReachD : AllReachD tgt rosterD capsBoth := by decide

/-- **The redundant revocation keeps everyone DERIVING** — `B` still reaches `read` via the genuine
`read ← call ← grant` chain after its direct cap is dropped. This is exactly where the multi-step
closure does work the one-step heuristic could only fake. -/
theorem capsDropRead_allReachD : AllReachD tgt rosterD capsDropRead := by decide

/-- **The foreclosing revocation BREAKS everyone-deriving** — cutting all of `B`'s caps leaves no
derivation path, so the multi-step closure never derives `read`. -/
theorem capsDropAll_breaks_reachD : ¬ AllReachD tgt rosterD capsDropAll := by decide

/-! ### §7.2 The substance-discipline facts — start refined; attenuation rides `confinement_preserved`;
laundering breaks it. -/

set_option maxRecDepth 1024 in
/-- The start `capsBoth` satisfies the deployed substance discipline `PasRefined`. `B` holds an
endpoint to itself carrying `[read]` and one carrying `[grant]`; `polD` authorizes both edges. -/
theorem capsBoth_refined : PasRefined polD capsBoth := by
  intro s t c a hc hceq ha
  by_cases hs : s = B
  · subst hs
    simp only [capsBoth, ↓reduceIte] at hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · -- the direct `read` cap (endpoint B [read]).
      simp only [capAuthConferred, List.mem_singleton] at ha; subst ha
      have ht : t = B := by simp only [Cap.endpoint.injEq] at hceq; exact hceq.1.symm
      subst ht; unfold polD Metatheory.PolisAuthReachDatalog.B authorizedEdge; decide
    · -- the `grant` cap (endpoint B [grant]); polD authorizes ⟨B, grant, B⟩.
      rw [List.mem_singleton] at hc'; obtain rfl := hc'
      simp only [capAuthConferred, List.mem_singleton] at ha; subst ha
      have ht : t = B := by simp only [Cap.endpoint.injEq] at hceq; exact hceq.1.symm
      subst ht; unfold polD Metatheory.PolisAuthReachDatalog.B authorizedEdge; decide
  · simp only [capsBoth, if_neg hs] at hc
    exact absurd hc List.not_mem_nil

/-- The redundant revocation is `noGrow` from the start (it only drops `B`'s direct `read` cap, keeps
the `grant` cap). -/
theorem capsDropRead_noGrow : ∀ s, capsDropRead s ⊆ capsBoth s := by
  intro s c hc
  by_cases hs : s = B
  · subst hs
    simp only [capsDropRead, ↓reduceIte, List.mem_singleton] at hc
    obtain rfl := hc
    simp only [capsBoth, ↓reduceIte]
    exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  · simp only [capsDropRead, if_neg hs] at hc; exact absurd hc List.not_mem_nil

/-- The redundant revocation stays `PasRefined` — via the DEPLOYED `confinement_preserved` (the
substance half is NEVER re-proved per witness), reusing `capsBoth_refined` and `noGrow`. -/
theorem capsDropRead_refined : PasRefined polD capsDropRead :=
  attenuation_keeps_substance_D polD capsBoth capsDropRead capsBoth_refined capsDropRead_noGrow

/-- The start satisfies the FULL grounded floor on the REAL multi-step viability. -/
theorem capsBoth_grounded : groundedFloorD polD tgt rosterD capsBoth :=
  ⟨capsBoth_refined, capsBoth_allReachD⟩

/-- **ADMIT, decided on the grant-chain model.** The redundant revocation keeps the WHOLE grounded
floor (substance via `confinement_preserved`; multi-step reach decided), so the grounded governor
passes it through unchanged — `B` still DERIVES `read` via `read ← call ← grant`. -/
theorem capsDropRead_admitted :
    groundedGovD polD tgt rosterD capsBoth capsDropRead = capsDropRead :=
  grounded_admits_attenuation_D polD tgt rosterD capsBoth capsDropRead
    capsBoth_refined capsDropRead_noGrow capsDropRead_allReachD

/-- **REFUSE-FORECLOSURE, decided on the grant-chain model.** Cutting all of `B`'s caps breaks the
multi-step reach (no derivation path to `read`), so the grounded governor shields — the sharper
refusal: only cutting EVERY derivation path forecloses. -/
theorem capsDropAll_refused_foreclosure :
    groundedGovD polD tgt rosterD capsBoth capsDropAll = capsBoth :=
  grounded_refuses_foreclosure_D polD tgt rosterD capsBoth capsDropAll capsDropAll_breaks_reachD

/-- **`grand_no_capture_D` INSTANTIATED on the grant-chain model** — from `capsBoth`, NO controller
breaks the grounded floor at any tick, with viability = the genuine multi-step derivation closure. -/
theorem capsBoth_grand_no_capture (ctrl : Caps → Caps) (n : Nat) :
    groundedFloorD polD tgt rosterD
      (genGovTraj (groundedFloorD polD tgt rosterD) capsStep ctrl capsBoth n) :=
  grand_no_capture_D polD tgt rosterD capsBoth capsBoth_grounded ctrl n

/-! ## §8. Axiom hygiene. -/

-- The general deliverables are kernel-clean up to the classical decidability of the ∀-floor (the
-- floor is a ∀ over labels/caps, so its `DecidablePred` instance is `Classical.propDecidable`,
-- exactly as in `PolisAuthGameN`/`PolisAuthGrand`). The concrete witnesses are `decide`-checked.
#print axioms grand_no_capture_D
#print axioms grand_no_capture_D_both
#print axioms grounded_refuses_laundering_D
#print axioms grounded_refuses_foreclosure_D
#print axioms grounded_admits_attenuation_D
#print axioms grounded_refuses_laundering_monotone
#print axioms grounded_refuses_foreclosure_monotone
#print axioms attenuation_keeps_substance_D
#print axioms capsBoth_grand_no_capture
#print axioms capsDropRead_admitted
#print axioms capsDropAll_refused_foreclosure
#print axioms capsDropRead_allReachD

/-!
The grand polis over REAL Datalog viability, in one breath:

  1. `AllReachD target agents` — the roster lift of `PolisAuthReachDatalog.ReachesD`, the genuine
     forward-chaining multi-step derivation closure (`read ← call ← grant`), NOT a one-step check.
  2. `groundedFloorD pol target agents := combineFloor (PasRefined pol) (AllReachD target agents)` —
     the grounded floor with viability = the genuine derivation object.
  3. `grand_no_capture_D` — from any legitimate-and-viable start, NO opaque controller breaks the
     floor at any tick, for EVERY roster/policy/target. The toy one-step `AllReach` is retired here.
  4. `grounded_refuses_{laundering,foreclosure}_D` + monotone forms + `grounded_admits_attenuation_D`
     — the refusal/admission lanes; the substance half rides the DEPLOYED `confinement_preserved`.
  5. The grant-chain witness (reusing `capsBoth`/`capsDropRead`/`capsDropAll`) certifies genuine
     ADMIT (`capsDropRead`: `B` still derives `read` via the 2-round chain) and genuine REFUSE
     (`capsDropAll`: every derivation path cut), `decide`-checked.
-/

end Metatheory.PolisAuthGrandDatalog
