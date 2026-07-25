/-
# `Dregg2.Circuit.ExtChallengeLogUpSite` — the LogUp BUS CHALLENGE at the deployed quartic typing.

## THE SITE, confirmed in the file

`LogUpColumnLayout.logupChallenge` (`:169-170`):

    def logupChallenge (embed : ℤ → F) (d : EffectVmDescriptor2) (t : VmTrace) : F :=
      embed (t.pub (challengeCol d))

— ONE `ℤ` value, read from ONE public trace column (`challengeCol d = d.piCount`), embedded into
the field. The deployed LogUp challenge is a `Challenge`: a quartic-extension element, FOUR ordered
`Val` lanes. `BusModelOk.nonexceptional` (`:314`) is a Fiat–Shamir Schwartz–Zippel event ABOUT that
value, so this is LOAD-BEARING, not decorative: it is the challenge whose non-exceptionality the
whole `busModel_forces_lookup_holds` discharge rides.

⚑ A precision the header must not blur: `LogUpColumnLayout` is field-GENERIC (`{F : Type*}
[Field F]`), so `F` may already be instantiated at the extension. The wound is NOT the type of `F`;
it is the READ — a single-slot `embed (t.pub c)` cannot express a four-lane challenge, and §2 proves
exactly that.

## WHAT IS PROVED HERE (additively; no landed definition edited)

* §1 `logupChallengeExt` — the DEPLOYED four-lane read: `extDeg = 4` consecutive public column
  slots, each embedded as a `Val`, assembled on the deployed lane family. `logupChallengeExt_lift`
  proves the single-slot read is EXACTLY the `lanes 0 = 1`, higher-slots-zero special case, so base
  witnesses lift completely.
* §2 ⚑ THE TRUE RELATION — NO DESCENT, and the base read cannot EXPRESS the deployed challenge.
  Every deployed-embedding single-slot read is confined to `Set.range (algebraMap BabyBear E)`
  (`logupChallenge_deployed_mem_range`), while the four-lane read attains values outside it
  (`logupChallengeExt_beyond_base`, fired at a concrete trace). This is a strict separation of the
  reachable challenge SETS: `p` values against `p^4`.
  §2.1 shows the obstruction is not an artifact of a chosen lane family: for ANY `BabyBear`-basis
  of ANY extension, AT MOST ONE basis vector lies in the base image
  (`atMostOne_basis_mem_range`), so ≥ 3 of the deployed 4 lanes are outside it
  (`bb4Basis_lane_beyond_base`).
* §3 ⚑ THE PAYOFF — the retyping costs the consumer NOTHING. `BusModelOkAt` puts the challenge in
  as a PARAMETER (it is `BusModelOk` at the constant embedding, so every field says exactly what it
  said before, about `α` instead of about a single-slot read). At the four-lane challenge it still
  forces the identical conclusion `Lookup.holdsAt t.tf (envAt t i) l` — a statement about ℤ tuples
  and the committed trace, with no field in it at all. Weaker-but-achievable hypothesis, identical
  conclusion.
* §4 NON-VACUITY: a CONCRETE sound bus at BB4 whose challenge is drawn from
  `BB4 ∖ image(BabyBear)`, on the real range-lookup toy instance, forcing the real membership
  `[3] ∈ rangeRows 2`. Nothing here is true by emptiness — the hypotheses are inhabited exactly in
  the non-base regime the repair is about.

## WHAT THIS DOES NOT CLOSE

* The deployed p3 bus-column LAYOUT correspondence (that the four lanes really sit at
  `challengeCol d … challengeCol d + 3`) is the same Lean-model-to-Rust boundary
  `LogUpColumnLayout` already names per-deployment. `logupChallengeExt` PINS a checkable shape; it
  does not prove the Rust matches it.
* The β-RLC tuple fingerprint `fp : List ℤ → F` is untouched; it is generic and its faithfulness
  event is the separate named `BusModelOk.fpFaithful` residual.
* The ε NUMBER for `BusModelOk.nonexceptional` is not re-derived here; the companion file
  `ExtChallengeOodSites` §4 proves the arithmetic of the denominator move (`p` → `p^4`) in the
  `winProb` frame.

Sorry-free; no `axiom`; no carrier; keystones `#assert_axioms`-checked.
-/
import Dregg2.Circuit.LogUpColumnLayout
import Dregg2.Circuit.FriDeployedExtCode

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.ExtChallengeLogUpSite

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.LogUpSoundness
open Dregg2.Circuit.LogUpColumnLayout
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRange)
open Dregg2.Circuit.FriDeployedExtCode
  (BB4 bb4Basis bb4_finrank exists_not_mem_range_algebraMap)

/-! ## §1 — the DEPLOYED four-lane bus-challenge read, and the single-slot read as its special
case. -/

section Read

variable {E : Type*} [Field E] [Algebra BabyBear E]

/-- **The DEPLOYED bus challenge read.** `extDeg = 4` consecutive public column slots, each embedded
as a `Val` (the deployed `ℤ → BabyBear → Challenge` path), assembled on the lane family `lanes`.
This is the four-lane object `logupChallenge` squeezes to one. The lane family is a parameter
because the deployed presentation is `BinomialExtensionField<BabyBear,4>`'s power basis
`1, X, X², X³` — see `powerLanes`. -/
noncomputable def logupChallengeExt (E : Type*) [Field E] [Algebra BabyBear E]
    (lanes : Fin 4 → E) (d : EffectVmDescriptor2) (t : VmTrace) : E :=
  ∑ i : Fin 4, algebraMap BabyBear E ((t.pub (challengeCol d + (i : ℕ)) : ℤ) : BabyBear) * lanes i

/-- The deployed single-slot embedding `ℤ → Val`. -/
noncomputable def embedVal : ℤ → BabyBear := fun z => (z : BabyBear)

/-- **⚑ THE LIFT — the single-slot read IS the four-lane read restricted.** When the lane family has
`lanes 0 = 1` (the constant term of the deployed power basis) and the three higher slots read `0`,
the four-lane challenge is exactly the embedding of `logupChallenge embedVal d t`. So every
base-typed bus witness transports: the extension-typed demand is strictly WEAKER. -/
theorem logupChallengeExt_lift (lanes : Fin 4 → E) (hl0 : lanes 0 = 1)
    (d : EffectVmDescriptor2) (t : VmTrace)
    (hzero : ∀ i : Fin 4, i ≠ 0 → t.pub (challengeCol d + (i : ℕ)) = 0) :
    logupChallengeExt E lanes d t
      = algebraMap BabyBear E (logupChallenge embedVal d t) := by
  unfold logupChallengeExt
  rw [Finset.sum_eq_single (0 : Fin 4)]
  · rw [hl0, mul_one]
    rfl
  · intro j _ hj
    rw [hzero j hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin 4)) h

/-- A DEPLOYED-SHAPE lane family: `1, θ, θ², θ³` — the power-basis shape of
`BinomialExtensionField<BabyBear, 4> = BabyBear[X]/(X⁴ − 11)`, whose lane 0 is the constant term. -/
noncomputable def powerLanes (θ : E) : Fin 4 → E := ![1, θ, θ ^ 2, θ ^ 3]

@[simp] theorem powerLanes_zero (θ : E) : powerLanes θ 0 = 1 := by simp [powerLanes]
@[simp] theorem powerLanes_one (θ : E) : powerLanes θ 1 = θ := by simp [powerLanes]

end Read

/-! ## §2 — ⚑ THE TRUE RELATION: the base read is CONFINED; the deployed read is NOT.

Investigated, not assumed. The single-slot read, under the deployed embedding, can only ever produce
an element of the base image — a set of `p` values inside a challenge space of `p^4`. The four-lane
read reaches outside it. So the base-typed bus challenge is not a specialization of the deployed
one; it is a different (strictly smaller) object. -/

section NoDescent

variable {E : Type*} [Field E] [Algebra BabyBear E]

/-- **The single-slot read is CONFINED to the base image**, for EVERY descriptor and EVERY trace. -/
theorem logupChallenge_deployed_mem_range (d : EffectVmDescriptor2) (t : VmTrace) :
    algebraMap BabyBear E (logupChallenge embedVal d t)
      ∈ Set.range (algebraMap BabyBear E) :=
  ⟨_, rfl⟩

/-- A trace whose public block carries `1` at the `i₀`-th challenge lane and `0` everywhere else. -/
def laneTrace (d : EffectVmDescriptor2) (i₀ : Fin 4) : VmTrace :=
  { rows := [], pub := fun col => if col = challengeCol d + (i₀ : ℕ) then 1 else 0
  , tf := fun _ => [] }

/-- **⚑ NO DESCENT — the four-lane read attains a value NO single-slot read can express.** If any
deployed lane lies outside the base image (§2.1: at most one of four can be inside), then the
public-column configuration that selects that lane produces a bus challenge outside
`Set.range (algebraMap BabyBear E)` — which, by `logupChallenge_deployed_mem_range`, every
single-slot read is confined to. The base-typed challenge equation is therefore a DIFFERENT
equation over a strictly smaller value space. -/
theorem logupChallengeExt_beyond_base (lanes : Fin 4 → E) (i₀ : Fin 4)
    (hi : lanes i₀ ∉ Set.range (algebraMap BabyBear E)) (d : EffectVmDescriptor2) :
    logupChallengeExt E lanes d (laneTrace d i₀) ∉ Set.range (algebraMap BabyBear E) := by
  have hpub : ∀ j : Fin 4, (laneTrace d i₀).pub (challengeCol d + (j : ℕ))
      = if j = i₀ then (1 : ℤ) else 0 := by
    intro j
    show (if challengeCol d + (j : ℕ) = challengeCol d + (i₀ : ℕ) then (1 : ℤ) else 0) = _
    by_cases h : j = i₀
    · subst h; simp
    · rw [if_neg (fun hh => h (Fin.val_injective (Nat.add_left_cancel hh))), if_neg h]
  have hval : logupChallengeExt E lanes d (laneTrace d i₀) = lanes i₀ := by
    unfold logupChallengeExt
    rw [Finset.sum_eq_single i₀]
    · rw [hpub i₀, if_pos rfl]; simp
    · intro j _ hj
      rw [hpub j, if_neg hj]; simp
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  rw [hval]
  exact hi

/-- **The same fact as a SEPARATION**: that four-lane challenge value is attained by NO single-slot
read, at any descriptor and any trace. -/
theorem logupChallengeExt_not_single_slot (lanes : Fin 4 → E) (i₀ : Fin 4)
    (hi : lanes i₀ ∉ Set.range (algebraMap BabyBear E)) (d : EffectVmDescriptor2)
    (d' : EffectVmDescriptor2) (t' : VmTrace) :
    logupChallengeExt E lanes d (laneTrace d i₀)
      ≠ algebraMap BabyBear E (logupChallenge embedVal d' t') := by
  intro heq
  exact logupChallengeExt_beyond_base lanes i₀ hi d
    (heq ▸ logupChallenge_deployed_mem_range (E := E) d' t')

/-! ### §2.1 — the obstruction is basis-INDEPENDENT: at most one lane can be a base value. -/

/-- **AT MOST ONE BASIS VECTOR LIES IN THE BASE IMAGE.** For ANY `BabyBear`-basis of ANY extension,
two distinct basis vectors cannot both be images of base elements — they would be base-scalar
multiples of one another, contradicting independence. So a lane decomposition of a nontrivial
extension ALWAYS has lanes outside the base field: the four-lane read is never a disguised
single-slot read. -/
theorem atMostOne_basis_mem_range {r : Type*} (b : Module.Basis r BabyBear E) {i j : r}
    (hij : i ≠ j)
    (hi : b i ∈ Set.range (algebraMap BabyBear E))
    (hj : b j ∈ Set.range (algebraMap BabyBear E)) : False := by
  obtain ⟨a, ha⟩ := hi
  obtain ⟨a', ha'⟩ := hj
  have hbi : b i ≠ 0 := b.ne_zero i
  have ha0 : a ≠ 0 := fun h => hbi (by rw [← ha, h, map_zero])
  have hane : algebraMap BabyBear E a ≠ 0 :=
    fun h => ha0 ((algebraMap BabyBear E).injective (by rw [h, map_zero]))
  have hbj : b j = (a' / a) • b i := by
    rw [← ha, ← ha', Algebra.smul_def, map_div₀]
    field_simp
  have h1 : (b.repr (b j)) j = 1 := by simp
  have h2 : (b.repr (b j)) j = 0 := by
    rw [hbj]
    simp [hij]
  rw [h1] at h2
  exact one_ne_zero h2

end NoDescent

/-- **⚑ THE DEPLOYED QUARTIC LANES REACH OUTSIDE THE BASE FIELD.** At `BB4` — the canonical
deployed quartic extension — some lane of the four-lane basis is not a `Val`. -/
theorem bb4Basis_lane_beyond_base :
    ∃ i : Fin 4, bb4Basis i ∉ Set.range (algebraMap BabyBear BB4) := by
  by_contra hcon
  have h0 : bb4Basis 0 ∈ Set.range (algebraMap BabyBear BB4) := by
    by_contra h; exact hcon ⟨0, h⟩
  have h1 : bb4Basis 1 ∈ Set.range (algebraMap BabyBear BB4) := by
    by_contra h; exact hcon ⟨1, h⟩
  exact atMostOne_basis_mem_range bb4Basis (i := 0) (j := 1) (by decide) h0 h1

/-! ## §3 — ⚑ THE PAYOFF: the bus model AT AN ARBITRARY CHALLENGE still forces the identical
conclusion.

`BusModelOk fp embed d t tid mult` computes its challenge as `logupChallenge embed d t`. Taking
`embed` to be the CONSTANT map at `α` makes that read equal to `α` definitionally, so
`BusModelOkAt fp α …` is `BusModelOk` with every field saying exactly what it said before — about a
free challenge `α` rather than about a single-slot read. The landed discharge then applies verbatim
at the four-lane challenge, and the conclusion `Lookup.holdsAt t.tf (envAt t i) l` is unchanged: it
is a statement about ℤ tuples and the committed trace, containing no field element at all. -/

section Payoff

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The bus model AT a given challenge** — `BusModelOk` with the challenge as a PARAMETER. -/
abbrev BusModelOkAt (fp : List ℤ → F) (α : F) (d : EffectVmDescriptor2) (t : VmTrace)
    (tid : TableId) (mult : List ℕ) : Prop :=
  BusModelOk fp (fun _ => α) d t tid mult

/-- The parameterization is exact: the constant embedding's single-slot read IS `α`. -/
theorem logupChallenge_const (α : F) (d : EffectVmDescriptor2) (t : VmTrace) :
    logupChallenge (fun _ => α) d t = α := rfl

/-- **The discharge at an arbitrary challenge.** A sound bus at ANY challenge `α` forces every
declared `.lookup` into `tid` to hold on every row. -/
theorem busModelAt_forces_lookup_holds (fp : List ℤ → F) (α : F)
    (d : EffectVmDescriptor2) (t : VmTrace) (tid : TableId) (mult : List ℕ)
    (hok : BusModelOkAt fp α d t tid mult) :
    ∀ i < t.rows.length, ∀ l ∈ lookupsInto d tid, Lookup.holdsAt t.tf (envAt t i) l :=
  busModel_forces_lookup_holds fp (fun _ => α) d t tid mult hok

end Payoff

section PayoffExt

variable {E : Type*} [Field E] [Algebra BabyBear E] [DecidableEq E]

/-- **⚑ THE PAYOFF — the FOUR-LANE bus challenge forces the SAME conclusion.** With the LogUp
challenge read as the deployed four-lane `Challenge` rather than as one public-column scalar, a
sound bus still forces every declared lookup's membership `Lookup.holdsAt` — the exact `hbus`
lookup arm, unchanged. Weaker-but-achievable hypothesis (the deployed challenge IS an extension
element, §2), identical conclusion. -/
theorem busModelExt_forces_lookup_holds (fp : List ℤ → E) (lanes : Fin 4 → E)
    (d : EffectVmDescriptor2) (t : VmTrace) (tid : TableId) (mult : List ℕ)
    (hok : BusModelOkAt fp (logupChallengeExt E lanes d t) d t tid mult) :
    ∀ i < t.rows.length, ∀ l ∈ lookupsInto d tid, Lookup.holdsAt t.tf (envAt t i) l :=
  busModelAt_forces_lookup_holds fp (logupChallengeExt E lanes d t) d t tid mult hok

/-- **The whole `hbus` arm at the four-lane challenge**, for any graduated-shape descriptor. -/
theorem hbus_of_busModelsExt (hash : List ℤ → ℤ) (fp : List ℤ → E) (lanes : Fin 4 → E)
    (d : EffectVmDescriptor2) (t : VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ Dregg2.Circuit.AirChecksSatisfied.isArith c →
      ∃ l : Lookup, c = .lookup l)
    (hok : ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
        ∃ mult : List ℕ, BusModelOkAt fp (logupChallengeExt E lanes d t) d t l.table mult) :
    ∀ i < t.rows.length, ∀ c ∈ d.constraints,
      ¬ Dregg2.Circuit.AirChecksSatisfied.isArith c →
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  hbus_of_busModels hash fp (fun _ => logupChallengeExt E lanes d t) d t hshape hok

end PayoffExt

/-! ## §4 — NON-VACUITY: a CONCRETE sound bus at a genuinely NON-BASE challenge, on the real
range-lookup instance, forcing a real membership.

The toy instance is `LogUpColumnLayout`'s own (`toyD`/`toyT`/`toyMult`: one range lookup at
`bits = 2`, the value `3`, a 4-row structural table — heap-safe). The only thing changed is the
field (`BB4`) and the challenge, which is drawn from `BB4 ∖ image(BabyBear)`. -/

section Fire

/-- The toy tuple fingerprint at the deployed challenge field: a singleton tuple rides as its
`Val`, embedded into `Challenge`. -/
noncomputable def fpExt : List ℤ → BB4 :=
  fun tup => algebraMap BabyBear BB4 ((tup.headD 0 : ℤ) : BabyBear)

/-- The single honest bus value `fpExt [3]`. -/
noncomputable def val3 : BB4 := fpExt [3]

theorem toy_logupA_ext : logupA fpExt toyD toyT .range = [val3] := rfl

theorem toy_logupB_ext : logupB fpExt toyT .range toyMult = [val3] := rfl

/-- `val3` is a base value (the fingerprint side is base data — it is the CHALLENGE that is not). -/
theorem val3_mem_range : val3 ∈ Set.range (algebraMap BabyBear BB4) := ⟨_, rfl⟩

/-- A challenge outside the base image cannot be the additive inverse of a base value, so the LogUp
poles are automatically avoided in the non-base regime. -/
theorem nonbase_pole_ne_zero {α v : BB4} (hα : α ∉ Set.range (algebraMap BabyBear BB4))
    (hv : v ∈ Set.range (algebraMap BabyBear BB4)) : α + v ≠ 0 := by
  intro h
  obtain ⟨b, hb⟩ := hv
  exact hα ⟨-b, by rw [map_neg, hb]; linear_combination -h⟩

/-- **⚑ THE HYPOTHESES ARE INHABITED AT A NON-BASE CHALLENGE.** For EVERY challenge outside the base
image, the honest toy bus is a sound bus model — the balance holds for any challenge, the poles are
automatically avoided (`nonbase_pole_ne_zero`), the exceptional set of a self-balanced bus is empty,
and the fingerprint is faithful on the 4-row structural table. -/
theorem toy_busModelOk_ext {α : BB4} (hα : α ∉ Set.range (algebraMap BabyBear BB4)) :
    BusModelOkAt fpExt α toyD toyT .range toyMult where
  polesA := by
    rw [toy_logupA_ext]
    intro a ha
    rw [List.mem_singleton] at ha
    subst ha
    exact nonbase_pole_ne_zero hα val3_mem_range
  polesB := by
    rw [toy_logupB_ext]
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact nonbase_pole_ne_zero hα val3_mem_range
  balanced := by
    unfold busBalance
    refine logup_complete _ ?_
    rw [toy_logupA_ext, show expand (logupBM fpExt toyT .range toyMult) = [val3] from
      toy_logupB_ext]
  nonexceptional := by
    rw [toy_logupA_ext, toy_logupB_ext, exceptionalSet, busNum_self, Polynomial.roots_zero,
      Multiset.toFinset_zero]
    exact Finset.notMem_empty _
  nodupA := by rw [toy_logupA_ext]; exact List.nodup_singleton _
  fpFaithful := by
    rw [toy_lookedTuples, toy_tf_range, toy_rangeRows2]
    intro x hx y hy hfp
    rw [List.mem_singleton] at hx
    subst hx
    have hfp' : (((3 : ℤ)) : BabyBear) = ((y.headD 0 : ℤ) : BabyBear) := by
      have hcast := hfp
      unfold fpExt at hcast
      exact (algebraMap BabyBear BB4).injective hcast
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | (exfalso
         rw [ZMod.intCast_eq_intCast_iff'] at hfp'
         revert hfp'; decide)

/-- **⚑ FIRE — the hypothesis bundle is INHABITED at a genuinely non-base challenge, and the
discharge RUNS.** The statement carries the WHOLE `BusModelOkAt` bundle, not just the conclusion, so
it cannot be satisfied vacuously: there is a `BB4` challenge outside `image(BabyBear)` — the regime
§2 shows no single-slot read can reach — at which the toy bus IS sound, and at which the general
discharge forces the real lookup `[3] ∈ rangeRows 2` to hold. Same base-field-free conclusion the
base-typed model delivered. -/
theorem fire_busModelExt_nonbase :
    ∃ α : BB4, α ∉ Set.range (algebraMap BabyBear BB4) ∧
      BusModelOkAt fpExt α toyD toyT .range toyMult ∧
      Lookup.holdsAt toyT.tf (envAt toyT 0) toyLookup := by
  obtain ⟨ξ, hξ⟩ := exists_not_mem_range_algebraMap (F := BabyBear) (E := BB4)
    (by rw [bb4_finrank]; norm_num)
  refine ⟨ξ, hξ, toy_busModelOk_ext hξ, ?_⟩
  exact busModelAt_forces_lookup_holds fpExt ξ toyD toyT .range toyMult
    (toy_busModelOk_ext hξ) 0 (by decide) toyLookup
    (mem_lookupsInto.mpr ⟨List.mem_cons_self .., rfl⟩)

/-- …and the forced membership IS the range meaning: wire 0 lies in `[0, 2²)`. The base-field
conclusion survives the retyping of the challenge, exactly. -/
theorem fire_range_denotation_ext : VmRange.holds (envAt toyT 0) ⟨0, 2⟩ := by
  obtain ⟨_, _, _, hmem⟩ := fire_busModelExt_nonbase
  exact lookup_replaces_range 2 toyT.tf rfl (envAt toyT 0) 0 hmem

/-- **⚑ FIRE — the deployed-shape four-lane read at a genuinely non-base lane.** The power-basis
lane family `1, θ, θ², θ³` at a non-base `θ` produces, on the lane-selecting public configuration, a
bus challenge outside the base image — so the deployed challenge is NOT expressible as any
single-slot read. -/
theorem fire_logupChallengeExt_beyond_base (d : EffectVmDescriptor2) :
    ∃ θ : BB4, θ ∉ Set.range (algebraMap BabyBear BB4) ∧
      logupChallengeExt BB4 (powerLanes θ) d (laneTrace d 1)
        ∉ Set.range (algebraMap BabyBear BB4) := by
  obtain ⟨θ, hθ⟩ := exists_not_mem_range_algebraMap (F := BabyBear) (E := BB4)
    (by rw [bb4_finrank]; norm_num)
  refine ⟨θ, hθ, logupChallengeExt_beyond_base (powerLanes θ) 1 ?_ d⟩
  rw [powerLanes_one]
  exact hθ

end Fire

/-! ## §5 — Axiom hygiene. -/

#assert_all_clean [
  logupChallengeExt_lift,
  logupChallenge_deployed_mem_range,
  logupChallengeExt_beyond_base,
  logupChallengeExt_not_single_slot,
  atMostOne_basis_mem_range,
  bb4Basis_lane_beyond_base
]

#assert_all_clean [
  logupChallenge_const,
  busModelAt_forces_lookup_holds,
  busModelExt_forces_lookup_holds,
  hbus_of_busModelsExt
]

#assert_all_clean [
  toy_logupA_ext,
  toy_logupB_ext,
  nonbase_pole_ne_zero,
  toy_busModelOk_ext,
  fire_busModelExt_nonbase,
  fire_range_denotation_ext,
  fire_logupChallengeExt_beyond_base
]

end Dregg2.Circuit.ExtChallengeLogUpSite
