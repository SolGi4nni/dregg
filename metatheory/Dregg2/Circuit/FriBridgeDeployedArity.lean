/-
# `Dregg2.Circuit.FriBridgeDeployedArity` — DEBT-A composition: the PROVED bridge threaded
through the DEPLOYED 8-to-1 arity setup.

## Honest scope (first sentence)

The deployed-**arity** through-line to `CircuitSound` IS PROVED here
(`deployedArity_circuit_sound`), under three EXPLICIT hypotheses — an accepting arity-8 FRI
transcript (`haccept`: 8 DISTINCT challenges, each fold landing in the low-degree folded code),
the Merkle plumbing (`hplumb`: the opened trace IS the committed oracle's decoded trace), and the
codeword-side AIR obligation (`hcode_sat`: every low-degree codeword decodes to a
transition-satisfying trace) — with the FRI proximity discharged by the PROVED arity-8 keystone
`fold_close_of_arity_challenges` at `n = 8` over BabyBear, NOT re-assumed.

## The TYPE VERDICT: `FriSetup` vs `FriSetupK` — DIFFERENT types.

`FriProximityBridge.friProximity_bridge` takes `S : Commitment → FriSoundness.FriSetup F ι κ`,
whose `geom : FriSoundness.FriGeom` HARD-WIRES the arity-2 squaring quotient (fields `σ`, `two_ne`,
`p_σ_rep`, the two-representative `q_fiber`). The deployed-arity setup `friSetupK8` has type
`FriFoldArity.FriSetupK BabyBear (Fin 16) (Fin 2) 8`, whose `geom : FriGeomK … 8` is the power-`8`
quotient with `8` fiber reps and the `p_reps_inj` distinctness field. These are NOT the same type,
and `FriSetupK … 8` is NOT `FriSetup` (the geometry is a different structure with a different
arity). So `friProximity_bridge` CANNOT be instantiated at `friSetupK8` — coercing an arity-8
geometry into an arity-2 `FriSetup` would be a fake.

The obstruction is confined to the CODE/GEOMETRY layer. The bridge's *proof* touches the geometry
NOWHERE: it uses only `air_binds_of_proximity` (a one-liner over the domain submodule `S.C`),
`closeN`, and `disagree_eq_empty_iff`. So the smallest honest generalization is a faithful mirror
of the proved bridge over `FriSetupK` — `friProximity_bridgeK` below — whose proof is
line-for-line the arity-2 bridge's, over `S.C : Submodule F (ι → F)` (arity-agnostic).

## What is DISCHARGED vs what remains HYPOTHETICAL

DISCHARGED (proved, applied — no re-assumed hypothesis):
  * `friProximityK8_discharge` — the arity-8 FRI proximity, the PROVED
    `fold_close_of_arity_challenges` APPLIED at `friSetupK8` (`n = 8`), giving the honest distance
    constant `n²·d = 64·d`; at `d = 0` this is `0` (`friProximityK8_discharge0`).

HYPOTHETICAL (explicit, visible premises — the SAME residuals as the arity-2 bridge):
  * `hplumb` — the opened trace IS the committed oracle's decoded trace (Merkle binding, an appeal
    to `HashCR`/`Poseidon2SpongeCR`);
  * `hcode_sat` — every codeword `g ∈ friSetupK8.C` decodes to a transition-satisfying trace (the
    codeword-side `AirChecksSatisfied` arithmetic content). LOAD-BEARING: `g` occurs in the
    conclusion `satisfiesTransition … (traceOf g) …`, not a bare `openTr`-only statement.

## The distance cost: 64·d vs 4·d — NOT translated to a soundness-error bound here.

The arity-8 keystone yields `64·d`-closeness (`n² · d` at `n = 8`) where the arity-2 keystone
yields `4·d` (`n² · d` at `n = 2`). At the honest distance `d = 0` BOTH collapse to `0`, so this
file's proximity/soundness through-line — which runs at `d = 0`, "the accepted oracle IS a genuine
low-degree codeword" — is UNAFFECTED by the constant. The `64·d` vs `4·d` gap only matters in the
list-decoding regime `d > 0`, where it inflates the recoverable radius per round; translating that
into a concrete soundness-error bound at the deployed `num_queries = 38`, `log_blowup = 3` (the
`(1 - δ)^{38}` query-soundness term composed over the fold rounds) is a QUANTITATIVE step NOT taken
here. This file claims the `d = 0` proximity-to-`CircuitSound` composition at the deployed field +
rate + ARITY; it does NOT claim a numeric soundness-error figure.

## Teeth (both polarities, load-bearing)

  * FIRES: the honest degree-`< 8` codeword `fHon8`, folded by `8` distinct challenges, discharges
    proximity `0`-close and drives the bridge to `AirSoundness.FriProximity` and thence
    `CircuitSound` (`honest_deployedArity_circuit_sound`, fully closed — no open premises).
  * BITES (arity-specific): the frequency-`8` far word `f0` admits NO accepting arity-8 transcript
    — feeding `friProximityK8_discharge0` its (nonexistent) 8 distinct good challenges would force
    `f0 ∈ friSetupK8.C`, contradicting `f0_not_mem` (`f0_no_honest_discharge`).
  * BITES (codeword side): the lying decoder `⟨0,1,5⟩` (`5 ≠ 0+1`) falsifies `hcode_sat` at the
    codeword `0 ∈ friSetupK8.C` (`hcode_sat_load_bearing`) — so `hcode_sat` is a real obligation.

Sibling `Dregg2/Crypto/MlDsaSignReal.lean` is modified in the working tree — another lane's file;
FLAGGED, not owned or touched here.
-/
import Dregg2.Circuit.FriFoldArity
import Dregg2.Circuit.FriProximityBridge
import Dregg2.Circuit.AirSoundness

namespace Dregg2.Circuit.FriBridgeDeployedArity

open Dregg2.Circuit.FriSoundness (closeN closeN_zero_iff_mem disagree disagree_eq_empty_iff)
open Dregg2.Circuit.FriFoldArity
open Dregg2.Circuit.AirSoundness (Step satisfiesTransition airChecks circuit_sound_via_fri)
open Dregg2.Crypto.TurnSoundness (CircuitSound)
open Dregg2.Circuit.BabyBearFriField (BabyBear)

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {n : ℕ}
variable {State Effect Proof Commitment : Type*}

/-! ## §1 — The arity-`n` geometric proximity Prop and the arity-8 discharge. -/

/-- **`FriProximityK`** — the arity-`n` mirror of `FriSoundness.FriProximity`: the oracle `f` is
`d`-close to the low-degree code `S.C` of an arity-`n` FRI setup. Definitionally `closeN S.C d f`,
so it feeds `air_binds_of_proximityK` unchanged. -/
def FriProximityK (S : FriSetupK F ι κ n) (d : ℕ) (f : ι → F) : Prop := closeN S.C d f

/-- **`friProximityK8_discharge` — the arity-8 proximity, the PROVED keystone APPLIED (no
re-assumed hypothesis).** From `8` DISTINCT challenges `α` (injective) each folding `f` `d`-close
to the folded code `friSetupK8.C'` — an accepting arity-8 FRI transcript — the PROVED
`fold_close_of_arity_challenges` at `n = 8` yields `f` is `8²·d = 64·d`-close to `friSetupK8.C`.
This is the general lemma instantiated at `friSetupK8`, NOT a fresh assumption. -/
theorem friProximityK8_discharge {f : Fin 16 → BabyBear} {α : Fin 8 → BabyBear}
    (hα : Function.Injective α) {d : ℕ}
    (haccept : ∀ i, closeN friSetupK8.C' d (Fold friSetupK8.geom (α i) f)) :
    FriProximityK friSetupK8 (8 ^ 2 * d) f :=
  fold_close_of_arity_challenges friSetupK8 hα haccept

/-- **The `d = 0` specialization** — an accepting arity-8 transcript (each fold IN the folded code,
`8` distinct challenges) discharges proximity `0`-close: the oracle IS a genuine low-degree
codeword. (`8² · 0 = 0` — the distance constant vanishes at the honest distance.) -/
theorem friProximityK8_discharge0 {f : Fin 16 → BabyBear} {α : Fin 8 → BabyBear}
    (hα : Function.Injective α)
    (haccept : ∀ i, Fold friSetupK8.geom (α i) f ∈ friSetupK8.C') :
    FriProximityK friSetupK8 0 f := by
  show FriProximityK friSetupK8 (8 ^ 2 * 0) f
  exact friProximityK8_discharge hα (fun i => closeN_zero_iff_mem.mpr (haccept i))

/-! ## §2 — The arity-generalized bridge (the smallest honest generalization).

The proved `FriProximityBridge.friProximity_bridge` is stated over `FriSoundness.FriSetup` (arity 2).
Its proof uses ONLY the submodule/`closeN`/`disagree` layer, never the geometry — so it mirrors
verbatim over `FriSetupK` (arity `n`). `air_binds_of_proximityK` and `friProximity_bridgeK` below
are that mirror, line-for-line. -/

/-- **`air_binds_of_proximityK`** — arity-`n` mirror of `air_binds_of_proximity`: transport a
property holding on EVERY codeword onto a codeword `g` the oracle matches within `d`. Proof is the
arity-2 one; it touches no geometry, only `S.C`. -/
theorem air_binds_of_proximityK {S : FriSetupK F ι κ n} {f : ι → F} {d : ℕ}
    (hp : FriProximityK S d f) (constraint : (ι → F) → Prop)
    (hconstr : ∀ g ∈ S.C, constraint g) :
    ∃ g ∈ S.C, (disagree f g).card ≤ d ∧ constraint g := by
  obtain ⟨g, hg, hc⟩ := hp
  exact ⟨g, hg, hc, hconstr g hg⟩

/-- **`friProximity_bridgeK` — the DEBT-A bridge over the arity-`n` `FriSetupK`, PROVED.** A faithful
mirror of `FriProximityBridge.friProximity_bridge`, verbatim over `FriSetupK`: the geometric arity-`n`
proximity (`hFRI`, `0`-close) plus the Merkle plumbing (`hplumb`) plus the LOAD-BEARING codeword-side
obligation (`hcode_sat`, whose bound `g` appears in the conclusion) yield the operational
`AirSoundness.FriProximity`. `hFRI` is genuinely used — it identifies the oracle with a codeword. -/
theorem friProximity_bridgeK
    (applyEff : Effect → State → State)
    (verifyLD : Proof → Commitment → Prop)
    (openTr : Commitment → Step State Effect × List (Step State Effect))
    (S : Commitment → FriSetupK F ι κ n)
    (oracle : Commitment → (ι → F))
    (traceOf : (ι → F) → Step State Effect × List (Step State Effect))
    (hFRI : ∀ π com, verifyLD π com → FriProximityK (S com) 0 (oracle com))
    (hplumb : ∀ com, openTr com = traceOf (oracle com))
    (hcode_sat : ∀ com, ∀ g ∈ (S com).C,
        satisfiesTransition applyEff (traceOf g).1 (traceOf g).2) :
    AirSoundness.FriProximity applyEff verifyLD openTr := by
  intro π com hv
  obtain ⟨g, _hg, hdis, hsat⟩ :=
    air_binds_of_proximityK (hFRI π com hv)
      (fun f => satisfiesTransition applyEff (traceOf f).1 (traceOf f).2)
      (hcode_sat com)
  have hog : oracle com = g :=
    disagree_eq_empty_iff.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hdis))
  rw [hplumb com, hog]
  exact hsat

/-! ## §3 — The DEPLOYED-ARITY composition to `CircuitSound`.

`friProximity_bridgeK` at `S := fun _ => friSetupK8`, with `hFRI` DISCHARGED by
`friProximityK8_discharge0` (the proved arity-8 keystone applied), composed through
`circuit_sound_via_fri`. Deployed FIELD (BabyBear) + RATE (`1/8`, `|L| = 16`) + ARITY (8-to-1). -/

/-- **`deployedArity_circuit_sound` — `CircuitSound` with the FRI half PROVED at the deployed field +
rate + ARITY.** Under an accepting arity-8 transcript (`hchal`: 8 distinct challenges; `haccept`:
each fold lands in the folded code) the oracle is `0`-close to `friSetupK8.C` (discharged, not
assumed); with Merkle plumbing (`hplumb`) and the codeword-side AIR obligation (`hcode_sat`) the
AIR-realized checker satisfies `CircuitSound`. Remaining hypothetical: `hplumb` (HashCR) and
`hcode_sat` (AIR arithmetic). -/
theorem deployedArity_circuit_sound
    (applyEff : Effect → State → State)
    (verifyLD : Proof → Commitment → Prop)
    (openTr : Commitment → Step State Effect × List (Step State Effect))
    (oracle : Commitment → (Fin 16 → BabyBear))
    (traceOf : (Fin 16 → BabyBear) → Step State Effect × List (Step State Effect))
    (chal : Commitment → Fin 8 → BabyBear)
    (hchal : ∀ com, Function.Injective (chal com))
    (haccept : ∀ π com, verifyLD π com →
        ∀ i, Fold friSetupK8.geom (chal com i) (oracle com) ∈ friSetupK8.C')
    (hplumb : ∀ com, openTr com = traceOf (oracle com))
    (hcode_sat : ∀ (_com : Commitment), ∀ g ∈ friSetupK8.C,
        satisfiesTransition applyEff (traceOf g).1 (traceOf g).2) :
    CircuitSound applyEff (airChecks verifyLD openTr) :=
  circuit_sound_via_fri applyEff verifyLD openTr
    (friProximity_bridgeK applyEff verifyLD openTr
      (fun _ => friSetupK8) oracle traceOf
      (fun π com hv => friProximityK8_discharge0 (hchal com) (haccept π com hv))
      hplumb hcode_sat)

#assert_axioms friProximityK8_discharge
#assert_axioms friProximityK8_discharge0
#assert_axioms air_binds_of_proximityK
#assert_axioms friProximity_bridgeK
#assert_axioms deployedArity_circuit_sound

/-! ## §4 — TEETH (both polarities load-bearing). -/

section Teeth

/-- The toy effect-VM: an additive counter (matches `AirSoundness`/`FriProximityBridge`). -/
def toyApply : ℕ → ℕ → ℕ := fun e s => s + e

/-- An honest constant decoder: every codeword ↦ the honest row `⟨0,1,1⟩` (`1 = 0 + 1`). -/
def traceHonest : (Fin 16 → BabyBear) → Step ℕ ℕ × List (Step ℕ ℕ) :=
  fun _ => (⟨0, 1, 1⟩, [])

/-- The honest decoder satisfies `hcode_sat` for EVERY codeword of `friSetupK8.C`. -/
theorem traceHonest_code_sat :
    ∀ g ∈ friSetupK8.C, satisfiesTransition toyApply (traceHonest g).1 (traceHonest g).2 := by
  intro g _
  exact ⟨rfl, trivial⟩

/-- **FIRES (fully closed) — the honest chain drives `CircuitSound` at the deployed arity.** The
honest codeword `fHon8`, folded by the `8` distinct `chal8` challenges (all in `C'` by
completeness, `fHon8_reconstruct`), discharges proximity `0`-close; with the honest decoder and any
verifier/plumbing pointing at it, the bridge FIRES to `AirSoundness.FriProximity` and thence
`CircuitSound` — NO open premises beyond the plumbing pointer. -/
theorem honest_deployedArity_circuit_sound
    (verifyLD : Proof → Unit → Prop)
    (openTr : Unit → Step ℕ ℕ × List (Step ℕ ℕ))
    (hplumb : ∀ com, openTr com = traceHonest fHon8) :
    CircuitSound toyApply (airChecks verifyLD openTr) :=
  circuit_sound_via_fri toyApply verifyLD openTr
    (friProximity_bridgeK toyApply verifyLD openTr
      (fun _ => friSetupK8) (fun _ => fHon8) traceHonest
      (fun _ _ _ => fHon8_reconstruct) hplumb (fun _ => traceHonest_code_sat))

/-- **BITES (arity-specific) — the far word admits NO accepting arity-8 transcript.** The
frequency-`8` far word `f0` (∉ `friSetupK8.C`, `f0_not_mem`) has no `8` distinct challenges all
folding into `C'`: such a transcript would drive `friProximityK8_discharge0` to force `f0 ∈
friSetupK8.C`, a contradiction. So the discharge genuinely BITES — it cannot be fed a far word. -/
theorem f0_no_honest_discharge :
    ¬ ∃ α : Fin 8 → BabyBear, Function.Injective α ∧
        ∀ i, Fold friSetupK8.geom (α i) f0 ∈ friSetupK8.C' := by
  rintro ⟨α, hα, hg⟩
  exact f0_not_mem (closeN_zero_iff_mem.mp (friProximityK8_discharge0 hα hg))

/-- A LYING decoder: every codeword ↦ `⟨0,1,5⟩` (`5 ≠ 0 + 1`), violating the step gate. -/
def traceLying : (Fin 16 → BabyBear) → Step ℕ ℕ × List (Step ℕ ℕ) :=
  fun _ => (⟨0, 1, 5⟩, [])

/-- **BITES (codeword side) — `hcode_sat` is LOAD-BEARING.** The lying decoder fails `hcode_sat`:
at the codeword `0 ∈ friSetupK8.C` it decodes to `⟨0,1,5⟩`, whose step gate `5 = toyApply 1 0 = 1`
is FALSE. So `hcode_sat` is a genuine obligation, not free by unfolding. -/
theorem hcode_sat_load_bearing :
    ¬ (∀ g ∈ friSetupK8.C, satisfiesTransition toyApply (traceLying g).1 (traceLying g).2) := by
  intro h
  obtain ⟨hstep, _⟩ := h 0 (Submodule.zero_mem _)
  have : (5 : ℕ) = toyApply 1 0 := hstep
  simp [toyApply] at this

end Teeth

#assert_axioms traceHonest_code_sat
#assert_axioms honest_deployedArity_circuit_sound
#assert_axioms f0_no_honest_discharge
#assert_axioms hcode_sat_load_bearing

end Dregg2.Circuit.FriBridgeDeployedArity
