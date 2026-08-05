/-
# Dregg2.Circuit.CustomBindingFromFold — the DEPLOYED custom binding, proven from the FOLD.

## Why this file exists (the repair)

`CustomCarrierAttack` proved that the prior custom apex consumed `StarkSoundCustom`, a STAGED-AIR
extraction carrier that is **vacuous as deployed**: the deployed per-row `proofBind` denotation is the
vacuous `| .proofBind _ => True` (`DescriptorIR2.VmConstraint2.holdsAt`, `:570`), so over the deployed
True-gate AIR the staged extraction asserts strictly MORE than the verifier enforces
(`deployed_admits_unbacked`, `starkSoundCustom_unsound_over_deployed`). It also showed `EngineBinding`
is NOT an irreducible axiom — at every pair it is determined OR that pair is a witnessed sponge
collision (`CustomCarrierAttack.vk_determined_or_encColl`, floor-free).

The custom binding is actually enforced at the **FOLD** (decided architecture (a),
`docs/.../CustomApex` §"What is DEPLOYED"): the per-turn aggregate folds the custom sub-proof leaf,
**re-verifies it via the recursion** (the in-circuit child-verifier subcircuit — the SAME machinery
`AggAirSound` opens), and **CONNECTS** the leaf's exposed PI-commitment to the effect-vm leg's
now-published `custom_proof_commitment` PI (IR2 slots 46..49). The light client checks the AGGREGATE.

This module proves the REAL deployed custom guarantee from premises that HOLD for the deployed
aggregate — NOT `StarkSoundCustom`:

  * **`custom_binding_from_fold`** — a verifying AGGREGATE (the per-turn fold including the custom leaf)
    FORCES, for the effect-vm leg's exposed custom-commitment PI `c`: (binding) ∃ a verifying custom
    sub-proof `q` with `E.piCommit q = c`, and (anti-ghost) the attested program VK is DETERMINED by
    `c`. It rests ONLY on `{the FRI floor (via AggAirSound's carrier), the per-instance non-collision (via
    vk_determined_of_noEncColl), the connect}`. `StarkSoundCustom` is GONE.

  * **`custom_companion_grounded`** — the analog of `CustomApex.lightclient_unfoolable_custom_binds`,
    consuming `custom_binding_from_fold` instead of `StarkSoundCustom`: the custom light-client
    guarantee rests on the SAME premises as everything else (FRI + the per-instance `hno`), no custom carrier. The
    exposed PI `c` is BACKED by a verifying sub-proof attesting a UNIQUELY DETERMINED program VK.

## Provenance of the FRI floor (= AggAirSound's carrier)

The custom leaf is one CHILD of the aggregation; `AggAirSound.FriExtract` is exactly the floor that a
SATISFIED in-circuit child-verifier subcircuit (pinned at commitment `c`, claiming an exposed
projection) yields a GENUINELY VERIFYING child proof with that pinned identity.
`customLeafFriFloor_of_aggFriExtract` DERIVES the custom-leaf floor `CustomLeafFriFloor` from
`AggAirSound.FriExtract` (the leaf exposes its custom PI-commitment in the segment's `acc` lane). So
the binding's "the leaf verifies" half rests on AggAirSound's carrier — NOT a new dregg axiom.

## Non-vacuity (BOTH polarities, mirroring the Rust tooth)

`honest_companion_fires` — on an HONEST custom turn (the fold accepts, a backing sub-proof exists) the
grounded companion FIRES, handing back the verifying sub-proof and its determined VK.
`forged_unsat` / `forged_unsat_demo` — a fold whose exposed PI is a forged commitment NO verifying
sub-proof backs CANNOT satisfy (under the FRI floor + connect): the aggregate is UNSAT. This is the
circuit twin of the Rust anti-ghost tooth.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. The floor
carriers (the FRI-extraction obligations, `AggAirSound.FriExtract`) appear ONLY
as Prop HYPOTHESES, never as `axiom`s. NO `StarkSoundCustom`, NO new axiom, NO `sorry`. NEW file; all
imports read-only.
-/
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.CustomCarrierAttack

namespace Dregg2.Circuit.CustomBindingFromFold

open Dregg2.Circuit.DescriptorIR2 (ProofEngine EngineBinding oneLaneDemoEngine)
open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.CustomCarrierAttack
  (EncColl vk_determined_of_noEncColl vk_determined_or_encColl floorEngine
   floorEngine_hvk)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the custom-leaf FRI floor, and its provenance from `AggAirSound.FriExtract`.

The custom sub-proof leaf is one CHILD folded into the per-turn aggregate. The in-circuit
child-verifier subcircuit, when satisfied at the leaf's pinned preprocessed commitment, forces a
GENUINELY VERIFYING custom sub-proof exposing the pinned PI-commitment. We name that localized fact
`CustomLeafFriFloor` and DERIVE it from `AggAirSound.FriExtract` — the leaf exposes its custom
PI-commitment in the segment's `acc` lane. -/

/-- **`CustomLeafFriFloor E CustomLeafSat`** — the localized FRI-extraction floor for the custom leaf: a
SATISFIED in-circuit custom-leaf verifier (pinned VK core `leafVk`, exposing custom PI-commitment
`leafCommit`) yields a GENUINELY VERIFYING custom sub-proof of engine `E` whose `piCommit` IS the
exposed `leafCommit`. This is the custom instance of `AggAirSound.FriExtract` (one child of one node),
NOT a new dregg axiom — see `customLeafFriFloor_of_aggFriExtract`.

⚑ **ONE LANE.** This fold model's leaf commitment is a SCALAR `ℤ`; `E.piCommit` is a lane VECTOR
(2026-08-05), so the model meets the engine as the singleton `[leafCommit]`. The DEPLOYED commitment
is EIGHT lanes — the model did not widen with it, it adapts at the engine boundary. -/
def CustomLeafFriFloor (E : ProofEngine) (CustomLeafSat : ℤ → ℤ → Prop) : Prop :=
  ∀ leafVk leafCommit : ℤ, CustomLeafSat leafVk leafCommit →
    ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = [leafCommit]

/-- The custom leaf's exposed segment projection: the leaf carries its custom PI-commitment `x` in the
ordered-digest lane `acc` (the other lanes are inert for a single-leaf wrap). -/
def segOfCommit (x : ℤ) : Seg := { firstOld := 0, lastNew := 0, count := 0, acc := x }

/-- **`customLeafFriFloor_of_aggFriExtract` — the FRI floor IS AggAirSound's carrier.** Given the
aggregation's per-child `FriExtract` over the custom engine — pinned VK core constant `leafPre`, the
child exposing its custom PI-commitment in `acc` (`segOfCommit ∘ piCommit`) — the custom-leaf floor
`CustomLeafFriFloor` follows. So the binding's "the leaf verifies" half rests on the SAME in-circuit
recursion-verifier soundness carrier `AggAirSound.agg_air_sound` discharges, not on a custom axiom.

⚑ **ONE LANE.** `Seg.acc` is a SCALAR, so the exposure projection names the single lane `lane q` the
model's engine squeezes (`hlane : E.piCommit q = [lane q]`) — the assumption the pre-widening
`piCommit : Proof → ℤ` made silently. The deployed commitment is eight lanes; that width is a
DESCRIPTOR-level fact, not this model's. -/
theorem customLeafFriFloor_of_aggFriExtract
    (E : ProofEngine) (leafPre : ℤ) (ChildVerifierSat : ℤ → Seg → Prop)
    (lane : E.Proof → ℤ) (hlane : ∀ q, E.piCommit q = [lane q])
    (hagg : FriExtract E.Proof E.verify (fun _ => leafPre)
              (fun q => segOfCommit (lane q)) ChildVerifierSat) :
    CustomLeafFriFloor E (fun leafVk leafCommit => ChildVerifierSat leafVk (segOfCommit leafCommit)) := by
  intro leafVk leafCommit hcv
  obtain ⟨q, hq, _hvkc, hexp⟩ := hagg leafVk (segOfCommit leafCommit) hcv
  refine ⟨q, hq, ?_⟩
  have hacc : lane q = leafCommit := by simpa [segOfCommit] using congrArg Seg.acc hexp
  rw [hlane q, hacc]

/-! ## §2 — the per-turn fold node + its satisfaction (the connect). -/

/-- **`CustomFold E`** — the per-turn fold's custom face: the custom-leaf's pinned preprocessed
commitment `leafVk` (its VK core), the custom PI-commitment `leafCommit` the leaf exposes, and the
effect-vm leg's published `custom_proof_commitment` PI `c` (IR2 slots 46..49). -/
structure CustomFold (E : ProofEngine) where
  /-- the custom-leaf recursion-verifier's pinned preprocessed commitment (VK core). -/
  leafVk     : ℤ
  /-- the custom PI-commitment the folded leaf exposes. -/
  leafCommit : ℤ
  /-- the effect-vm leg's published `custom_proof_commitment` public input. -/
  c          : ℤ

/-- **`SatCustomFold E CustomLeafSat f`** — a SATISFYING per-turn fold over its custom face:
  * `leafCV` — the in-circuit custom-leaf verifier subcircuit is satisfied (pinned at `leafVk`,
    exposing `leafCommit`);
  * `connect` — the aggregate's combine constraint TIES the leaf's exposed commitment to the
    effect-vm leg's published `custom_proof_commitment` PI (`leafCommit = c`). Modeled as the equality
    a satisfying aggregate forces, exactly as `AggAirSound.SatCombine` models the segment-combine gates.
This is what a verifying aggregate's in-circuit trace IS, restricted to the custom face. -/
structure SatCustomFold (E : ProofEngine) (CustomLeafSat : ℤ → ℤ → Prop) (f : CustomFold E) : Prop where
  leafCV  : CustomLeafSat f.leafVk f.leafCommit
  connect : f.leafCommit = f.c

/-! ## §3 — THE REPAIR: the deployed custom binding, from the FOLD. -/

/-- **`custom_binding_from_fold` (THE DEPLOYED PAYLOAD).** A verifying AGGREGATE — the per-turn fold
including the custom leaf — FORCES, for the effect-vm leg's exposed custom-commitment PI `f.c`:

  (binding) ∃ a verifying custom sub-proof `q` of `E` with `E.piCommit q = f.c`; AND
  (anti-ghost) the attested program VK is DETERMINED by `f.c` — any two verifying sub-proofs exposing
  `f.c` agree on their `vkOf`.

The premise set is EXACTLY `{the FRI floor (`hfri`, = AggAirSound's carrier),
the per-instance non-collision (`hno`), the FRI-extraction factoring of the engine commitment (`hfactor`) + its
structural vk-recovery (`hvk`), the connect (inside `hsat`)}`. The anti-ghost rides `EngineBinding E`,
which is DERIVED here, FLOOR-FREE, via `vk_determined_of_noEncColl` — NOT taken as an axiom.

**`StarkSoundCustom` does not appear.** A forged commitment with no backing sub-proof makes the
aggregate UNSAT: the fold re-verifies the leaf (`hfri`) and the connect ties the commitment, so the
binding cannot be conjured.

⚑ **ONE LANE.** `f.c` is the model's SCALAR published PI, met as the singleton `[f.c]` against the
engine's lane vector; the deployed `custom_proof_commitment` is EIGHT lanes. -/
theorem custom_binding_from_fold
    (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (CustomLeafSat : ℤ → ℤ → Prop)
    (hfri : CustomLeafFriFloor E CustomLeafSat)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = [hash (enc p)])
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : CustomFold E)
    (hno : ∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = [f.c] → E.piCommit q = [f.c] → ¬ EncColl hash enc p q)
    (hsat : SatCustomFold E CustomLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = [f.c]) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = [f.c] → E.piCommit q = [f.c] → E.vkOf p = E.vkOf q) := by
  -- the fold re-verifies the leaf (AggAirSound's FRI floor) and the connect ties its commitment to `c`.
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  -- the anti-ghost: the determined VK (EngineBinding off the floor).
  intro p q' hp hq' hpc hq'c
  exact vk_determined_of_noEncColl hash E enc hfactor hvk hp hq' (by rw [hpc, hq'c])
    (hno p q' hp hq' hpc hq'c)

/-- **`custom_binding_from_fold_or_collides` — the same payload with NO side condition at all.**
The anti-ghost half reads "the attested VK is determined, OR THIS pair of verifying sub-proofs is a
witnessed collision of the deployed sponge at the two public-input lists it absorbs". Unlike the
deleted `Poseidon2SpongeCR` premise — PROVED FALSE at deployed BabyBear parameters — this statement
survives instantiation at the sponge the system actually runs. -/
theorem custom_binding_from_fold_or_collides
    (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (CustomLeafSat : ℤ → ℤ → Prop)
    (hfri : CustomLeafFriFloor E CustomLeafSat)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = [hash (enc p)])
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : CustomFold E) (hsat : SatCustomFold E CustomLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = [f.c]) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = [f.c] → E.piCommit q = [f.c] →
        E.vkOf p = E.vkOf q ∨ EncColl hash enc p q) := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  intro p q' hp hq' hpc hq'c
  exact vk_determined_or_encColl hash E enc hfactor hvk p q' hp hq' (by rw [hpc, hq'c])

/-- **`custom_companion_grounded` — the grounded Custom light-client guarantee (no custom carrier).**
The analog of `CustomApex.lightclient_unfoolable_custom_binds`, but consuming `custom_binding_from_fold`
rather than `StarkSoundCustom`: a verifying aggregate forces that the effect-vm leg's published
`custom_proof_commitment` PI `f.c` is BACKED — `E.boundTo f.c v` for a UNIQUELY DETERMINED program VK
`v` (every verifying sub-proof exposing `f.c` attests exactly `v`, the anti-ghost / forged-commitment
rejection). The custom guarantee rests on the SAME floor as everything else (`FRI` via AggAirSound +
the per-instance `hno`), not on a custom STARK carrier.

⚑ **ONE LANE on the COMMITMENT side only.** `f.c` is the model's SCALAR published PI, met as `[f.c]`
(the deployed one is EIGHT lanes). The determined program VK `v` is the ENGINE's own object and is a
lane vector — nothing in this model constrains its width, so it stays `List ℤ`. -/
theorem custom_companion_grounded
    (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (CustomLeafSat : ℤ → ℤ → Prop)
    (hfri : CustomLeafFriFloor E CustomLeafSat)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = [hash (enc p)])
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : CustomFold E)
    (hno : ∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = [f.c] → E.piCommit q = [f.c] → ¬ EncColl hash enc p q)
    (hsat : SatCustomFold E CustomLeafSat f) :
    ∃ v : List ℤ, E.boundTo [f.c] v ∧
      (∀ q : E.Proof, E.verify q = true → E.piCommit q = [f.c] → E.vkOf q = v) := by
  obtain ⟨⟨q, hq, hqc⟩, hdet⟩ :=
    custom_binding_from_fold E hash enc CustomLeafSat hfri hfactor hvk f hno hsat
  refine ⟨E.vkOf q, ⟨q, hq, hqc, rfl⟩, ?_⟩
  intro q' hq' hq'c
  exact hdet q' q hq' hq hq'c hqc

/-! ## §4 — NON-VACUITY: the companion FIRES on an honest fold; a forged commitment is REJECTED. -/

section Honest

/-- The honest custom face over `floorEngine` (`piCommit p = hash [p.1, p.2]`, `vkOf p = p.1`,
`verify ≡ true`): the folded leaf exposes the commitment of the honest sub-proof `(7, 7)`, and the
connect publishes that same commitment as `c`. -/
def honestFold (hash : List ℤ → ℤ) : CustomFold (floorEngine hash) :=
  { leafVk := 100, leafCommit := hash [7, 7], c := hash [7, 7] }

/-- The honest custom-leaf verifier predicate: it is satisfied exactly when a backing verifying
sub-proof exposes the exposed commitment (the in-circuit verifier's soundness-and-completeness). -/
def honestCLS (hash : List ℤ → ℤ) : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit => ∃ q : ℤ × ℤ,
    (floorEngine hash).verify q = true ∧ (floorEngine hash).piCommit q = [leafCommit]

/-- The honest custom-leaf FRI floor holds by identity (the predicate already names a backing proof). -/
theorem honestFloor (hash : List ℤ → ℤ) : CustomLeafFriFloor (floorEngine hash) (honestCLS hash) :=
  fun _leafVk _leafCommit h => h

/-- The engine's FRI factoring is definitional on `floorEngine` (`piCommit p = [hash [p.1, p.2]]` —
the toy engine squeezes ONE lane). -/
theorem honestFactor (hash : List ℤ → ℤ) :
    ∀ p, (floorEngine hash).verify p = true → (floorEngine hash).piCommit p = [hash [p.1, p.2]] :=
  fun _p _ => rfl

/-- The structural vk-recovery: a vk-headed encoding makes it cons-injectivity (the toy engine's
`vkOf p = [p.1]`, so the recovered scalar is re-wrapped). -/
theorem honestHvk (hash : List ℤ → ℤ) :
    ∀ p q, (floorEngine hash).verify p = true → (floorEngine hash).verify q = true →
      [p.1, p.2] = [q.1, q.2] → (floorEngine hash).vkOf p = (floorEngine hash).vkOf q :=
  floorEngine_hvk hash

/-- The honest fold satisfies: the leaf is backed by `(7, 7)` and the connect is `rfl`. -/
theorem honestSat (hash : List ℤ → ℤ) :
    SatCustomFold (floorEngine hash) (honestCLS hash) (honestFold hash) where
  leafCV  := ⟨(7, 7), rfl, rfl⟩
  connect := rfl

/-- **`honest_companion_fires` (POSITIVE non-vacuity).** On the honest custom turn, the grounded
companion FIRES: the published `custom_proof_commitment` PI `hash [7, 7]` is BACKED by a verifying
sub-proof attesting a uniquely determined program VK — a real, non-vacuous firing, UNCONDITIONAL,
at `Poseidon2Binding.Reference.refSponge` whose CR is PROVED (the FRI legs discharge definitionally
on `floorEngine`).

⚑ ONE LANE: `(honestFold refSponge).c` is the model's scalar leaf commitment, met as `[·]`. -/
theorem honest_companion_fires :
    ∃ v : List ℤ, (floorEngine refSponge).boundTo [(honestFold refSponge).c] v ∧
      (∀ q : ℤ × ℤ, (floorEngine refSponge).verify q = true →
        (floorEngine refSponge).piCommit q = [(honestFold refSponge).c] →
        (floorEngine refSponge).vkOf q = v) :=
  custom_companion_grounded (floorEngine refSponge) refSponge (fun p => [p.1, p.2]) (honestCLS refSponge)
    (honestFloor refSponge) (honestFactor refSponge) (honestHvk refSponge) (honestFold refSponge)
    (fun _p _q _ _ _ _ hcol => hcol.1 (refSponge_CR _ _ hcol.2))
    (honestSat refSponge)

end Honest

section Forged

/-- **`forged_unsat` (THE ANTI-GHOST TOOTH — forged commitment ⟹ UNSAT).** A per-turn fold whose
published `custom_proof_commitment` PI `f.c` is backed by NO verifying sub-proof CANNOT satisfy: the
fold re-verifies the leaf (`hfri`) and the connect ties its commitment to `f.c`, so a satisfying fold
would PRODUCE a backing sub-proof — contradiction. The aggregate is UNSAT. This is the circuit twin of
the Rust anti-ghost tooth: a forged commitment with no backing leaf is rejected by the fold itself. -/
theorem forged_unsat {E : ProofEngine} {CustomLeafSat : ℤ → ℤ → Prop}
    (hfri : CustomLeafFriFloor E CustomLeafSat) {f : CustomFold E}
    (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = [f.c]) :
    ¬ SatCustomFold E CustomLeafSat f := by
  intro hsat
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  exact hforge ⟨q, hq, hqc⟩

/-- The forged custom-leaf predicate over `oneLaneDemoEngine` (the only verifying sub-proof commits
to `123`).

⚑ **WHY THE ONE-LANE ENGINE AND NOT `demoEngine`.** This fold model's leaf commitment is ONE `ℤ`,
while `demoEngine` squeezes the deployed EIGHT lanes — so a scalar claim can never equal its
commitment, and a forged-VALUE pole stated there would be true BY ARITY, saying nothing about the
forged value at all (`demoEngine_is_eight_lanes_oneLane_is_one` pins the two widths). Over
`oneLaneDemoEngine` the refusal is about the value again.

⚠ A one-lane ENGINE MODEL is not a one-lane DESCRIPTOR seam: a scalar-commitment fold is fairly
modelled at one lane, but `PROOF_BIND_MIN_LANES` refuses a one-lane seam at every admission door.
`demoCLS_sat` is the companion that keeps this predicate from being false everywhere. -/
def demoCLS : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit =>
    ∃ q : Bool, oneLaneDemoEngine.verify q = true ∧ oneLaneDemoEngine.piCommit q = [leafCommit]

theorem demoFloor : CustomLeafFriFloor oneLaneDemoEngine demoCLS :=
  fun _leafVk _leafCommit h => h

/-- **`demoCLS_sat` — THE PREDICATE IS SATISFIED AT THE HONEST VALUE, so the pole below refuses a
VALUE rather than everything.** Without it `forged_unsat_demo` is equally consistent with a leaf
predicate that is FALSE EVERYWHERE — which is precisely what the eight-lane `demoEngine` silently
became. The negative pole's meaning depends on this lemma, so it is named. -/
theorem demoCLS_sat : demoCLS 0 123 := ⟨true, rfl, rfl⟩

/-- A FORGED fold over `oneLaneDemoEngine`: the published `custom_proof_commitment` PI is `999`, a
commitment NO verifying sub-proof exposes (the only verifying proof commits to `123`). -/
def forgedFold : CustomFold oneLaneDemoEngine := { leafVk := 0, leafCommit := 999, c := 999 }

/-- **`forged_unsat_demo` (NEGATIVE non-vacuity).** The forged fold (exposed PI `999`, unbacked) does
NOT satisfy — the rejection is non-vacuous: `999` is genuinely beyond the engine's reach, so no
satisfying fold exists. -/
theorem forged_unsat_demo : ¬ SatCustomFold oneLaneDemoEngine demoCLS forgedFold := by
  refine forged_unsat demoFloor (f := forgedFold) ?_
  rintro ⟨q, _hq, hc⟩
  have hc' : [(123 : ℤ)] = [(999 : ℤ)] := hc
  exact absurd hc' (by decide)

end Forged

/-! ## §5 — Axiom hygiene (every load-bearing arm). -/

#assert_axioms customLeafFriFloor_of_aggFriExtract
#assert_axioms custom_binding_from_fold
#assert_axioms custom_binding_from_fold_or_collides
#assert_axioms custom_companion_grounded
#assert_axioms honest_companion_fires
#assert_axioms forged_unsat
#assert_axioms demoCLS_sat
#assert_axioms forged_unsat_demo

end Dregg2.Circuit.CustomBindingFromFold
