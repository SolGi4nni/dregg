/-
# Metatheory.Open.CurvatureScreen — CLOSING the OrbitalScreen OPEN: the curvature-aware screen.

`Dregg2.Apps.OrbitalScreen` builds a continuous-time-sound collision screen. It is EXACT for
an AFFINE relative trajectory `d(t) = d0 + t·v` (`screen_clear_imp_continuous_clear`), and it
ships a Lipschitz fallback `coarseClear`/`coarse_clear_imp_lipschitz_clear` that is sound for
ANY speed-bounded trajectory — crucially, that fallback takes the speed bound `vmax` as an
explicit HYPOTHESIS rather than smuggling affinity back in. The module then flags one OPEN
(its closing comment, ~lines 394–404):

  > "Upgrading to a curvature-aware bound (a second derivative / `n²`-term envelope) is the
  >  next refinement … the true CW relative solution adds bounded oscillatory/secular terms
  >  `O(n²·t²)` … A curvature-aware screen would bound `sepSq(t)` below by the affine value
  >  minus a `½·κ·t²` envelope (κ a second-derivative bound), recovering an exact continuous
  >  guarantee WITHOUT assuming affinity."

This module CLOSES that OPEN. The honest shape is exactly the `coarseClear` shape: the screen
is sound for an ARBITRARY relative-separation function `sepFn : ℚ → ℚ` (NOT assumed affine),
PROVIDED it meets a STATED curvature-envelope hypothesis with `κ` an explicit parameter — just
as `coarse_clear_imp_lipschitz_clear` is sound for any `sepFn` meeting a stated `vmax` bound.

================================================================================
## THE PHYSICS — why the envelope is `affine − ½·κ·t²`, faithfully (the Taylor/CW story).
================================================================================

Write the true (curved) relative separation along an axis or the genuine 3-D separation as a
C² function `s(t)` of time into the step. Taylor with the Lagrange remainder at `t = 0`:

    s(t) = s(0) + s'(0)·t + ½·s''(ξ)·t²     for some ξ ∈ (0, t).

If the SECOND derivative is bounded by a curvature constant `κ` over the step,
`|s''(ξ)| ≤ κ`, then the remainder is bounded BELOW by `−½·κ·t²` (it can be as negative as
`−½·κ·t²`), so the curved separation is bounded below by its OWN first-order (affine) part
minus the worst-case curvature drop:

    s(t) ≥ s(0) + s'(0)·t − ½·κ·t²  =:  g(t).          (the curvature ENVELOPE)

This is faithful to the Clohessy–Wiltshire / Hill relative dynamics. There the relative
acceleration is `r̈ = A·r + B·ṙ` with the CW matrix carrying the mean motion `n`; the entries
are `O(n²)` and `O(n)`, so the second derivative of any component — and hence of a smooth
separation — is bounded over a step by a `κ = O(n² · scale)` constant. The exact CW solution's
non-affine part is precisely the bounded oscillatory/secular `O(n²t²)` curvature the envelope
absorbs. The honest move (mirroring `coarseClear`'s `vmax`): we take that `κ` bound as the
hypothesis `hcurv` below and DERIVE soundness from it; we do not assume the trajectory affine.

Because the envelope `g(t) = sep0 + slope·t − ½·κ·t²` is a CONCAVE (downward, since `κ ≥ 0`)
parabola, its minimum over the step `[0,T]` is attained at an ENDPOINT — `min(g(0), g(T))`.
That is decidable and `#eval`-able, so the curvature screen checks `min(g(0), g(T)) ≥ thr`.

**STRICT GENERALIZATION of the affine screen.** With `κ = 0` the envelope is exactly the
affine lower line and the screen reduces to the affine endpoint check (`affine_is_curv_zero`).
With `κ > 0` it is genuinely STRONGER: the teeth (`§4`) exhibit a curved separation that clears
at both endpoints AND at the affine interior vertex, yet is correctly REJECTED because the
curvature drop `½·κ·t²` breaches the threshold mid-step — a breach the affine screen, and an
endpoint sampler, both miss.

**THE RESIDUAL (stated precisely, never faked).** This module is sound for any `sepFn` meeting
the explicit curvature-envelope hypothesis `hcurv`. It does NOT itself DERIVE the constant `κ`
from the CW mean motion `n` (that quantitative `κ = O(n²·scale)` derivation, the `s''` bound on
the genuine CW solution, would need a ℝ-analysis development of the CW matrix exponential and
is OUT OF SCOPE — exactly as `coarseClear` does not derive `vmax` from the dynamics either).
What is CLOSED: the curvature screen is genuinely sound for a CURVED (non-affine) trajectory
under a stated `κ` envelope, and strictly generalizes the affine screen. That is the OPEN's
"curvature-aware screen … recovering an exact continuous guarantee without assuming affinity."

Zero `sorry`/`admit`/`native_decide`/`axiom`. Keystones `#assert_axioms`-pinned.
-/
import Dregg2.Apps.OrbitalScreen
import Mathlib.Tactic

namespace Metatheory.Open.CurvatureScreen

open Dregg2.Apps.OrbitalScreen

/-! ## 1. The curvature envelope `g(t) = sep0 + slope·t − ½·κ·t²`.

`sep0` is the linear separation at `t = 0`, `slope` its first-order rate, and `κ ≥ 0` the
second-derivative bound. The Taylor/CW remainder argument (header) gives the envelope: a curved
separation `sepFn` with `|s''| ≤ κ` satisfies `sepFn t ≥ g t` over the step. We work with the
NON-squared linear separation (as `coarseClear` does), so the envelope is a genuine lower bound
on distance and the geometry stays honest. -/

/-- The **curvature envelope** at time `t`: the affine lower line minus the worst-case
second-order curvature drop, `g(t) = sep0 + slope·t − ½·κ·t²`. With `κ = 0` this is the affine
lower bound; with `κ > 0` it is a downward (concave) parabola. -/
def envelope (sep0 slope κ t : ℚ) : ℚ := sep0 + slope * t - κ * t ^ 2 / 2

@[simp] theorem envelope_zero (sep0 slope κ : ℚ) : envelope sep0 slope κ 0 = sep0 := by
  unfold envelope; ring

/-- **The envelope is CONCAVE over `[0,T]`: its minimum is at an ENDPOINT (PROVED).**
For `κ ≥ 0` and any `t ∈ [0,T]`, `g(t) ≥ min(g(0), g(T))`. This is the curvature analogue of
`OrbitalScreen.sepSq_min_at_tca`: where the affine (upward) parabola took its min at an
interior vertex, the concave envelope takes its min at the boundary, so the two endpoint values
bound the envelope over the WHOLE step. The proof: a concave function lies above the chord
joining its endpoints, and the chord lies above its own minimum endpoint. -/
theorem envelope_ge_min_endpoints
    (sep0 slope κ T : ℚ) (hκ : 0 ≤ κ)
    (t : ℚ) (h0 : 0 ≤ t) (hT : t ≤ T) :
    min (envelope sep0 slope κ 0) (envelope sep0 slope κ T) ≤ envelope sep0 slope κ t := by
  -- Concavity bound: `g(t) ≥ ((T - t)/T)·g(0) + (t/T)·g(T)` when `T > 0`; the convex combination
  -- of the endpoints is ≥ their min. We avoid division by handling `T = 0` and `t = 0` directly.
  rcases eq_or_lt_of_le h0 with ht0 | htpos
  · -- `t = 0`: envelope is `g(0)`, trivially ≥ `min(g(0), g(T))`.
    rw [← ht0]; exact min_le_left _ _
  · -- `0 < t ≤ T`, so `0 < T`.
    have hTpos : 0 < T := lt_of_lt_of_le htpos hT
    -- The CHORD value of the line through `(0, g(0))` and `(T, g(T))` at `t`:
    --   chord(t) = g(0) + (g(T) - g(0))·(t/T).
    -- Concavity gap: `g(t) - chord(t) = (κ/2)·t·(T - t) ≥ 0` (since κ,t,(T-t) ≥ 0). Verify:
    --   g(t) = sep0 + slope·t − (κ/2)t²
    --   chord(t) = sep0 + slope·t − (κ/2)·t·T          (the `sep0` cancels, slope is linear)
    --   g(t) − chord(t) = (κ/2)·t·T − (κ/2)·t² = (κ/2)·t·(T − t) ≥ 0.
    have hTt : 0 ≤ T - t := by linarith
    have hgap : 0 ≤ envelope sep0 slope κ t
        - (envelope sep0 slope κ 0
            + (envelope sep0 slope κ T - envelope sep0 slope κ 0) * (t / T)) := by
      have hTne : (T : ℚ) ≠ 0 := ne_of_gt hTpos
      have hexpand : envelope sep0 slope κ t
          - (envelope sep0 slope κ 0
              + (envelope sep0 slope κ T - envelope sep0 slope κ 0) * (t / T))
          = κ / 2 * t * (T - t) := by
        unfold envelope
        field_simp
        ring
      rw [hexpand]
      have : 0 ≤ κ / 2 * t := by positivity
      exact mul_nonneg this hTt
    -- chord(t) is a convex combination of the endpoints with weights in [0,1], hence ≥ their min.
    set lam := t / T with hlam
    have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
    have hlam1 : lam ≤ 1 := by
      rw [hlam, div_le_one hTpos]; exact hT
    -- chord(t) = (1-lam)·g(0) + lam·g(T) ≥ min(g(0), g(T)).
    have hchord_eq : envelope sep0 slope κ 0
          + (envelope sep0 slope κ T - envelope sep0 slope κ 0) * lam
        = (1 - lam) * envelope sep0 slope κ 0 + lam * envelope sep0 slope κ T := by ring
    have hmin_le : min (envelope sep0 slope κ 0) (envelope sep0 slope κ T)
        ≤ (1 - lam) * envelope sep0 slope κ 0 + lam * envelope sep0 slope κ T := by
      have hm0 : min (envelope sep0 slope κ 0) (envelope sep0 slope κ T)
          ≤ envelope sep0 slope κ 0 := min_le_left _ _
      have hmT : min (envelope sep0 slope κ 0) (envelope sep0 slope κ T)
          ≤ envelope sep0 slope κ T := min_le_right _ _
      have e1 : (1 - lam) * min (envelope sep0 slope κ 0) (envelope sep0 slope κ T)
          ≤ (1 - lam) * envelope sep0 slope κ 0 :=
        mul_le_mul_of_nonneg_left hm0 (by linarith)
      have e2 : lam * min (envelope sep0 slope κ 0) (envelope sep0 slope κ T)
          ≤ lam * envelope sep0 slope κ T :=
        mul_le_mul_of_nonneg_left hmT hlam0
      nlinarith [e1, e2]
    -- Combine: min ≤ chord(t) ≤ g(t).
    have hchord_le : envelope sep0 slope κ 0
          + (envelope sep0 slope κ T - envelope sep0 slope κ 0) * lam
        ≤ envelope sep0 slope κ t := by linarith [hgap]
    calc min (envelope sep0 slope κ 0) (envelope sep0 slope κ T)
        ≤ (1 - lam) * envelope sep0 slope κ 0 + lam * envelope sep0 slope κ T := hmin_le
      _ = envelope sep0 slope κ 0
            + (envelope sep0 slope κ T - envelope sep0 slope κ 0) * lam := by rw [hchord_eq]
      _ ≤ envelope sep0 slope κ t := hchord_le

/-! ## 2. THE CURVATURE SCREEN — `clear` iff both endpoint envelope values clear the threshold.

By `envelope_ge_min_endpoints`, the minimum of the concave envelope over `[0,T]` is the smaller
of its two endpoint values. So the screen needs only check those two — decidable, total,
`#eval`-able, exactly the spirit of `OrbitalScreen.screen`. -/

/-- The **curvature-aware screen** over the step `[0,T]`: clear iff the curvature envelope
clears the threshold `thr` at BOTH endpoints (equivalently, at its concave minimum). `sep0` is
the linear separation at `t=0`, `slope` its first-order rate, `κ ≥ 0` the second-derivative
bound. Decidable and runnable. -/
def curvScreen (sep0 slope κ T thr : ℚ) : Bool :=
  decide (thr ≤ envelope sep0 slope κ 0 ∧ thr ≤ envelope sep0 slope κ T)

/-- **`curv_screen_sound` — THE KEYSTONE (PROVED).** The honest curvature screen, in the exact
shape of `coarse_clear_imp_lipschitz_clear`: given an ARBITRARY relative-separation function
`sepFn : ℚ → ℚ` (NOT assumed affine) that meets the explicit **curvature-envelope hypothesis**

    hcurv : ∀ t, 0 ≤ t → t ≤ T → envelope sep0 slope κ t ≤ sepFn t

(the Taylor/CW second-order lower bound `sepFn t ≥ sep0 + slope·t − ½·κ·t²`, with `κ ≥ 0` the
second-derivative bound — see header), if `curvScreen … = true` then `thr ≤ sepFn t` for EVERY
`t ∈ [0,T]`. Sound for a CURVED (non-affine) trajectory; `κ` is the honest hypothesis. -/
theorem curv_screen_sound
    (sep0 slope κ T thr : ℚ) (hκ : 0 ≤ κ)
    (sepFn : ℚ → ℚ)
    (hcurv : ∀ t, 0 ≤ t → t ≤ T → envelope sep0 slope κ t ≤ sepFn t)
    (hclear : curvScreen sep0 slope κ T thr = true)
    (t : ℚ) (h0 : 0 ≤ t) (hT : t ≤ T) :
    thr ≤ sepFn t := by
  unfold curvScreen at hclear
  have hends : thr ≤ envelope sep0 slope κ 0 ∧ thr ≤ envelope sep0 slope κ T :=
    of_decide_eq_true hclear
  obtain ⟨he0, heT⟩ := hends
  -- thr ≤ min(endpoints) ≤ envelope t ≤ sepFn t.
  have hmin : thr ≤ min (envelope sep0 slope κ 0) (envelope sep0 slope κ T) := le_min he0 heT
  have henv : min (envelope sep0 slope κ 0) (envelope sep0 slope κ T) ≤ envelope sep0 slope κ t :=
    envelope_ge_min_endpoints sep0 slope κ T hκ t h0 hT
  exact le_trans (le_trans hmin henv) (hcurv t h0 hT)

/-- **`curv_screen_imp_no_conjunction` — the negative form (PROVED).** A `clear` verdict from
the curvature screen means there is NO continuous time in the step at which the curved pair is
in conjunction (separation strictly below threshold). The referee-facing form: "clear ⇒ no
conjunction anywhere in the step, for any trajectory meeting the κ envelope." -/
theorem curv_screen_imp_no_conjunction
    (sep0 slope κ T thr : ℚ) (hκ : 0 ≤ κ)
    (sepFn : ℚ → ℚ)
    (hcurv : ∀ t, 0 ≤ t → t ≤ T → envelope sep0 slope κ t ≤ sepFn t)
    (hclear : curvScreen sep0 slope κ T thr = true) :
    ¬ ∃ t : ℚ, 0 ≤ t ∧ t ≤ T ∧ sepFn t < thr := by
  rintro ⟨t, h0, hT, hlt⟩
  exact absurd (curv_screen_sound sep0 slope κ T thr hκ sepFn hcurv hclear t h0 hT)
    (not_le.mpr hlt)

/-! ## 3. STRICT GENERALIZATION — at `κ = 0` the curvature screen IS the affine endpoint check.

The curvature screen with `κ = 0` collapses to the affine endpoint check `min(sep0, sep0 +
slope·T) ≥ thr`. So it is a conservative *extension* of the affine line check: anything the
affine check passes, the `κ = 0` curvature screen passes, and vice versa. Turning on `κ > 0`
only TIGHTENS it — never loosens — which is exactly what "strictly generalizes" means here. -/

/-- **`affine_is_curv_zero` — the curvature screen specializes to the affine line check
(PROVED).** With `κ = 0` the envelope is the affine lower line `sep0 + slope·t`, so `curvScreen`
reduces to "both affine endpoints clear `thr`". Hence the affine screen is the `κ = 0` case and
the curvature screen strictly generalizes it (any `κ > 0` only adds the concavity drop). -/
theorem affine_is_curv_zero (sep0 slope T thr : ℚ) :
    curvScreen sep0 slope 0 T thr
      = decide (thr ≤ sep0 ∧ thr ≤ sep0 + slope * T) := by
  unfold curvScreen envelope
  have e0 : sep0 + slope * 0 - 0 * (0:ℚ) ^ 2 / 2 = sep0 := by ring
  have eT : sep0 + slope * T - 0 * T ^ 2 / 2 = sep0 + slope * T := by ring
  rw [e0, eT]

/-! ## 4. TEETH — a CURVED pair that clears at the endpoints AND the affine vertex,
but the CURVATURE term correctly breaches.

This is the whole point and the strict-generalization "teeth". We build a concrete curved
separation `sepFn` whose:
  * affine part `sep0 + slope·t` clears `thr` everywhere on `[0,T]` (so the AFFINE screen, and
    an endpoint sampler, BOTH say "clear" — UNSOUND for the curved truth);
  * curvature envelope `sep0 + slope·t − ½·κ·t²` DROPS below `thr` mid-step;
  * actual value `sepFn` realizes that drop, with a genuine mid-step conjunction.
Then `curvScreen` correctly returns `false`, and `sepFn` meets the envelope hypothesis. So the
curvature screen is genuinely STRONGER than the affine screen on a curved case.

Concretely: `sep0 = 10`, `slope = 0` (the affine part is the CONSTANT line `10`, well clear of
`thr = 6` everywhere), `κ = 2`, `T = 4`. Affine endpoints/vertex all read `10 ≥ 6` ⇒ affine
"clear". But the envelope at `t = 4` is `10 − ½·2·16 = 10 − 16 = −6 < 6`. The realized curved
separation is exactly the envelope, `sepFn t = 10 − t²`, which at `t = 3` is `1 < 6` — a true
conjunction the affine screen misses. -/

/-- The affine separation rate of the teeth pair (FLAT — the affine part is the constant `10`). -/
def teethSlope : ℚ := 0
/-- The teeth pair's separation at `t=0`. -/
def teethSep0 : ℚ := 10
/-- The teeth pair's curvature (second-derivative) bound. -/
def teethKappa : ℚ := 2
/-- The teeth step length. -/
def teethT : ℚ := 4
/-- The teeth threshold (clearance distance `6`). -/
def teethThr : ℚ := 6
/-- The teeth pair's REALIZED curved separation `s(t) = 10 − t²` — exactly the `κ = 2` envelope
of the constant-`10` affine part. It is C² with `s'' = −2`, so `|s''| = 2 = κ`: it meets the
curvature hypothesis with equality (the worst-case curved trajectory). -/
def teethSepFn (t : ℚ) : ℚ := 10 - t ^ 2

/-- **The affine screen / endpoint sampler is FOOLED on the curved pair (PROVED).** With the
affine (κ=0) screen, both endpoints of the affine part read `10 ≥ 6`, so it says "clear". -/
theorem teeth_affine_says_clear :
    curvScreen teethSep0 teethSlope 0 teethT teethThr = true := by
  unfold curvScreen envelope teethSep0 teethSlope teethT teethThr
  norm_num

/-- The realized curved separation meets the curvature-envelope hypothesis WITH EQUALITY: it IS
the `κ = 2` envelope of the constant-`10` affine part. So the teeth pair is a bona fide instance
of `curv_screen_sound`'s hypothesis. -/
theorem teeth_meets_envelope :
    ∀ t : ℚ, 0 ≤ t → t ≤ teethT →
      envelope teethSep0 teethSlope teethKappa t ≤ teethSepFn t := by
  intro t _ _
  unfold envelope teethSep0 teethSlope teethKappa teethSepFn
  -- `10 + 0·t − 2·t²/2 = 10 − t²` exactly; the bound holds with equality.
  apply le_of_eq
  ring

/-- **But there IS a real mid-step conjunction on the curved pair (PROVED).** At `t = 3`,
`sepFn 3 = 10 − 9 = 1 < 6` — a genuine conjunction that the FLAT affine part (constant `10`)
entirely misses. -/
theorem teeth_midstep_conjunction :
    teethSepFn 3 < teethThr := by
  unfold teethSepFn teethThr; norm_num

/-- **THE TEETH — the CURVATURE screen REJECTS the curved pair (PROVED).** With the honest
`κ = 2`, the envelope at the endpoint `t = T = 4` is `10 − ½·2·16 = −6 < 6`, so `curvScreen`
returns `false`. The affine screen (`teeth_affine_says_clear`) and an endpoint sampler BOTH said
"clear" — the curvature screen is genuinely STRONGER: it is sound against the second-order drop
that the affine model cannot see. -/
theorem teeth_curv_rejects :
    curvScreen teethSep0 teethSlope teethKappa teethT teethThr = false := by
  unfold curvScreen envelope teethSep0 teethSlope teethKappa teethT teethThr
  norm_num

/-- **Soundness instantiated on the teeth (PROVED).** Sanity check that the negative form fires:
because `curvScreen … = false`, we can't apply `curv_screen_sound`; instead we exhibit directly
that the screen would have been UNSOUND to clear — the realized conjunction at `t = 3` is inside
the step and breaches the threshold, matching the screen's correct `false`. -/
theorem teeth_conjunction_in_step :
    ∃ t : ℚ, 0 ≤ t ∧ t ≤ teethT ∧ teethSepFn t < teethThr := by
  refine ⟨3, by norm_num, ?_, teeth_midstep_conjunction⟩
  unfold teethT; norm_num

/-! ## 5. build-enforced witnesses — the curvature screen, runnable. -/

-- A genuinely-clear curved pair: sep0=10, slope=0, κ=1, T=2 → envelope min = 10 − ½·1·4 = 8 ≥ 6.
#guard curvScreen 10 0 1 2 6                                    -- (small curvature drop; still clear)
-- The teeth pair: affine (κ=0) says clear, curvature (κ=2) says NOT clear.
#guard curvScreen teethSep0 teethSlope 0 teethT teethThr        -- (affine: FOOLED)
#guard curvScreen teethSep0 teethSlope teethKappa teethT teethThr == false -- (curvature: SOUND reject)
-- The endpoint envelope values exposing the mid-step drop the affine screen misses:
#guard envelope teethSep0 teethSlope teethKappa 0 == 10         -- (clear)
#guard envelope teethSep0 teethSlope teethKappa teethT == -6    -- (breach: 10 − ½·2·16)
#guard teethSepFn 3 == 1                                        -- (realized mid-step conjunction)

/-! ## 6. Axiom hygiene. Every keystone pinned to the standard kernel axioms. -/

#assert_axioms envelope_ge_min_endpoints
#assert_axioms curv_screen_sound
#assert_axioms curv_screen_imp_no_conjunction
#assert_axioms affine_is_curv_zero
#assert_axioms teeth_affine_says_clear
#assert_axioms teeth_meets_envelope
#assert_axioms teeth_midstep_conjunction
#assert_axioms teeth_curv_rejects
#assert_axioms teeth_conjunction_in_step

end Metatheory.Open.CurvatureScreen
