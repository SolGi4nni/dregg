/-
# Dregg2.Circuit.FactoryBindingFromFold — the DEPLOYED factory binding, proven from the FOLD.

## Why this file exists (the flip)

`FactoryBackingAttack` proved the deployed `EFFECT_CREATE_CELL` leg VACUOUS as a pure light client
sees it: the deployed AIR gates only the birth transition, never the child-VK derivation / caps /
budget (`deployed_admits_forged_child_vk`, `deployed_intent_does_not_force_backing`). The repair it
NAMED — the backing must come from the per-turn FOLD over a re-proved FACTORY leaf connected to the
published `child_vk` teeth — is now DEPLOYED:

  * STEP 2/2.5 committed the carrier material: the AFTER-block `child_vk8` octet (limbs 88..=95)
    is a committed pre-limb absorbed into `state_commit`, filled from the executor's REAL
    installed `effective_vk` (`rotation_witness.rs::produce`).
  * STEP 3 pinned it: the deployed `factoryVmDescriptor2R24` is `factoryV3Carriers` —
    `withAfterOctetPins` publishes the committed octet at member PIs 47..54
    (`EffectVmEmitRotationV3.factoryV3Carriers`, apex-keyed at `Rfix 18`).
  * The FOLD arm landed (`ivc_turn_chain::prove_chain_core_rotated`, Factory arm): the per-turn
    aggregate folds the re-proven factory-backing leaf
    (`factory_leaf_adapter::prove_factory_leaf`), RE-VERIFIES it via the recursion (the same
    in-circuit child-verifier subcircuit `AggAirSound` opens), and CONNECTS the leaf's exposed
    child-VK commitment to the leg's published `child_vk8` claim PIs
    (`prove_factory_binding_node_segmented`). The deployed-path tooth
    (`factory_binding_deployed_tooth.rs`) exercises BOTH poles on the committed registry row.

This module proves the REAL deployed factory guarantee from premises that HOLD for the deployed
aggregate — the EXACT mirror of `CustomBindingFromFold` (custom was the first carrier over this
universal sub-proof-folding primitive; factory rides the same machinery):

  * **`factory_binding_from_fold`** — a verifying AGGREGATE (the per-turn fold including the factory
    leaf) FORCES, for the leg's published child-VK claim `f.cv`: (binding) ∃ a verifying factory
    sub-proof `q` with `E.piCommit q = f.cv`, and (anti-ghost) the attested VK is DETERMINED by
    `f.cv`. Premises = {the FRI floor (= `AggAirSound`'s carrier), the per-instance non-collision `hno`, the
    engine-commitment factoring + structural vk-recovery, the connect}. No staged-AIR carrier.

  * **`authorized_from_fold`** — the GROUNDING onto `FactoryBackingAttack.Authorized`: when the
    folded leaf's semantics is the re-proved `validate_and_record` (a verifying factory sub-proof
    exposing the leg's published `child_vk` IS a validating creation backing it — the
    `factory_leaf_adapter` obligation, carried as the named premise `hbacks`), a satisfying fold
    DISCHARGES the exact backing predicate `FactoryBackingAttack` proved the deployed AIR omits.
    The §B hole (`deployed_intent_does_not_force_backing`) is thereby CLOSED at the aggregate:
    deployed-intent PLUS the fold forces the backing the deployed AIR alone never could.

## Non-vacuity (BOTH polarities, mirroring the Rust tooth)

`honest_companion_fires` — on an honest factory turn the grounded binding FIRES.
`forged_unsat` / `forged_childvk_unsat_demo` — a fold whose published child-VK claim is the
`FactoryBackingAttack` forgery (`999`, backed by NO verifying sub-proof) CANNOT satisfy: the
aggregate is UNSAT — the circuit twin of `deployed_factory_turn_forged_child_vk_rejected`.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. The floor
carriers appear ONLY as Prop hypotheses. NO new axiom, NO `sorry`. NEW file; imports read-only.
-/
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.CustomCarrierAttack
import Dregg2.Circuit.FactoryBackingAttack

namespace Dregg2.Circuit.FactoryBindingFromFold

open Dregg2.Circuit.DescriptorIR2 (ProofEngine EngineBinding demoEngine)
open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.CustomCarrierAttack
  (EncColl vk_determined_of_noEncColl vk_determined_or_encColl floorEngine
   floorEngine_hvk)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.FactoryBackingAttack (FactoryEngine Authorized childVkOf DeployedFactoryIntent)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the factory-leaf FRI floor, and its provenance from `AggAirSound.FriExtract`.

The re-proved factory-backing leaf is one CHILD folded into the per-turn aggregate. The in-circuit
child-verifier subcircuit, when satisfied at the leaf's pinned preprocessed commitment, forces a
GENUINELY VERIFYING factory sub-proof exposing the pinned child-VK commitment. -/

/-- **`FactoryLeafFriFloor E FactoryLeafSat`** — the localized FRI-extraction floor for the factory
leaf: a SATISFIED in-circuit factory-leaf verifier (pinned VK core `leafVk`, exposing child-VK
commitment `leafCommit`) yields a GENUINELY VERIFYING factory sub-proof of engine `E` whose
`piCommit` IS the exposed `leafCommit`. The factory instance of `AggAirSound.FriExtract` (one child
of one node), NOT a new dregg axiom — see `factoryLeafFriFloor_of_aggFriExtract`. -/
def FactoryLeafFriFloor (E : ProofEngine) (FactoryLeafSat : ℤ → ℤ → Prop) : Prop :=
  ∀ leafVk leafCommit : ℤ, FactoryLeafSat leafVk leafCommit →
    ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = leafCommit

/-- The factory leaf's exposed segment projection: the leaf carries its child-VK commitment `x` in
the ordered-digest lane `acc` (the other lanes are inert for a single-leaf wrap). -/
def segOfCommit (x : ℤ) : Seg := { firstOld := 0, lastNew := 0, count := 0, acc := x }

/-- **`factoryLeafFriFloor_of_aggFriExtract` — the FRI floor IS AggAirSound's carrier.** Given the
aggregation's per-child `FriExtract` over the factory engine — pinned VK core constant `leafPre`,
the child exposing its child-VK commitment in `acc` — the factory-leaf floor follows. The binding's
"the leaf verifies" half rests on the SAME in-circuit recursion-verifier soundness carrier
`AggAirSound.agg_air_sound` discharges. -/
theorem factoryLeafFriFloor_of_aggFriExtract
    (E : ProofEngine) (leafPre : ℤ) (ChildVerifierSat : ℤ → Seg → Prop)
    (hagg : FriExtract E.Proof E.verify (fun _ => leafPre)
              (fun q => segOfCommit (E.piCommit q)) ChildVerifierSat) :
    FactoryLeafFriFloor E (fun leafVk leafCommit => ChildVerifierSat leafVk (segOfCommit leafCommit)) := by
  intro leafVk leafCommit hcv
  obtain ⟨q, hq, _hvkc, hexp⟩ := hagg leafVk (segOfCommit leafCommit) hcv
  refine ⟨q, hq, ?_⟩
  simpa [segOfCommit] using congrArg Seg.acc hexp

/-! ## §2 — the per-turn fold node + its satisfaction (the connect). -/

/-- **`FactoryFold E`** — the per-turn fold's factory face: the factory-leaf's pinned preprocessed
commitment `leafVk` (its VK core), the child-VK commitment `leafCommit` the leaf exposes, and the
effect-vm leg's published `child_vk8` claim `cv` (the committed-octet pins, member PIs 47..54 on
`factoryV3Carriers`). -/
structure FactoryFold (E : ProofEngine) where
  /-- the factory-leaf recursion-verifier's pinned preprocessed commitment (VK core). -/
  leafVk     : ℤ
  /-- the child-VK commitment the folded factory leaf exposes. -/
  leafCommit : ℤ
  /-- the effect-vm leg's published `child_vk8` claim (the committed-octet PI carrier). -/
  cv         : ℤ

/-- **`SatFactoryFold E FactoryLeafSat f`** — a SATISFYING per-turn fold over its factory face:
  * `leafCV` — the in-circuit factory-leaf verifier subcircuit is satisfied (pinned at `leafVk`,
    exposing `leafCommit`);
  * `connect` — the aggregate's combine constraint TIES the leaf's exposed commitment to the leg's
    published `child_vk8` claim (`leafCommit = cv`) — `prove_factory_binding_node_segmented`'s
    in-circuit connect, modeled as the equality a satisfying aggregate forces (exactly as
    `AggAirSound.SatCombine` models the segment-combine gates). -/
structure SatFactoryFold (E : ProofEngine) (FactoryLeafSat : ℤ → ℤ → Prop)
    (f : FactoryFold E) : Prop where
  leafCV  : FactoryLeafSat f.leafVk f.leafCommit
  connect : f.leafCommit = f.cv

/-! ## §3 — THE REPAIR: the deployed factory binding, from the FOLD. -/

/-- **`factory_binding_from_fold` (THE DEPLOYED PAYLOAD).** A verifying AGGREGATE — the per-turn
fold including the factory leaf — FORCES, for the leg's published `child_vk8` claim `f.cv`:

  (binding) ∃ a verifying factory sub-proof `q` of `E` with `E.piCommit q = f.cv`; AND
  (anti-ghost) the attested VK is DETERMINED by `f.cv` — any two verifying sub-proofs exposing
  `f.cv` agree on their `vkOf`.

The premise set is EXACTLY `{the FRI floor (= AggAirSound's carrier), the per-instance `hno`, the
FRI-extraction factoring of the engine commitment + its structural vk-recovery, the connect (inside
`hsat`)}` — the SAME set `custom_binding_from_fold` rests on; no staged-AIR carrier, no factory
axiom. A forged claim with no backing sub-proof makes the aggregate UNSAT. -/
theorem factory_binding_from_fold
    (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (FactoryLeafSat : ℤ → ℤ → Prop)
    (hfri : FactoryLeafFriFloor E FactoryLeafSat)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : FactoryFold E)
    (hno : ∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = f.cv → E.piCommit q = f.cv → ¬ EncColl hash enc p q)
    (hsat : SatFactoryFold E FactoryLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.cv) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = f.cv → E.piCommit q = f.cv → E.vkOf p = E.vkOf q) := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  intro p q' hp hq' hpc hq'c
  exact vk_determined_of_noEncColl hash E enc hfactor hvk hp hq' (by rw [hpc, hq'c])
    (hno p q' hp hq' hpc hq'c)

/-- **`factory_binding_from_fold_or_collides` — the same payload with NO side condition at all.**
The anti-ghost half reads "the attested VK is determined, OR THIS pair of verifying sub-proofs is a
witnessed collision of the deployed sponge at the two public-input lists it absorbs". Unlike the
deleted `Poseidon2SpongeCR` premise — PROVED FALSE at deployed BabyBear parameters — this statement
survives instantiation at the sponge the system actually runs. -/
theorem factory_binding_from_fold_or_collides
    (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (FactoryLeafSat : ℤ → ℤ → Prop)
    (hfri : FactoryLeafFriFloor E FactoryLeafSat)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : FactoryFold E) (hsat : SatFactoryFold E FactoryLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.cv) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = f.cv → E.piCommit q = f.cv →
        E.vkOf p = E.vkOf q ∨ EncColl hash enc p q) := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  intro p q' hp hq' hpc hq'c
  exact vk_determined_or_encColl hash E enc hfactor hvk p q' hp hq' (by rw [hpc, hq'c])

/-- **`authorized_from_fold` — the GROUNDING onto `FactoryBackingAttack.Authorized` (the §B close).**
`FactoryBackingAttack.deployed_intent_does_not_force_backing` proved the deployed AIR ALONE never
forces the factory backing. THIS is the third edge: when the folded leaf's semantics is the
re-proved `validate_and_record` — a verifying factory sub-proof exposing the leg's published
`child_vk` IS a validating creation backing that leg (`hbacks`, the `factory_leaf_adapter`
obligation) — a satisfying fold connected to the leg (`hcv`) DISCHARGES the exact staged backing
predicate the attack file showed the deployed AIR omits. Deployed-intent PLUS the fold forces what
deployed-intent alone provably cannot. -/
theorem authorized_from_fold
    (F : FactoryEngine) (exhausted : ℤ → Prop) (env : VmRowEnv)
    (E : ProofEngine) (FactoryLeafSat : ℤ → ℤ → Prop)
    (hfri : FactoryLeafFriFloor E FactoryLeafSat)
    (hbacks : ∀ q : E.Proof, E.verify q = true → E.piCommit q = childVkOf env →
        Authorized F exhausted env)
    (f : FactoryFold E) (hsat : SatFactoryFold E FactoryLeafSat f)
    (hcv : f.cv = childVkOf env) :
    Authorized F exhausted env := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect, hcv] at hqc
  exact hbacks q hq hqc

/-! ## §4 — NON-VACUITY: the binding FIRES on an honest fold; the §A forgery is REJECTED. -/

section Honest

/-- The honest factory face over `floorEngine` (`piCommit p = hash [p.1, p.2]`, `vkOf p = p.1`,
`verify ≡ true`): the folded leaf exposes the commitment of the honest sub-proof `(7, 7)`, and the
connect publishes that same commitment as the leg's `child_vk8` claim. -/
def honestFold (hash : List ℤ → ℤ) : FactoryFold (floorEngine hash) :=
  { leafVk := 100, leafCommit := hash [7, 7], cv := hash [7, 7] }

/-- The honest factory-leaf verifier predicate: satisfied exactly when a backing verifying
sub-proof exposes the exposed commitment. -/
def honestFLS (hash : List ℤ → ℤ) : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit => ∃ q : ℤ × ℤ,
    (floorEngine hash).verify q = true ∧ (floorEngine hash).piCommit q = leafCommit

theorem honestFloor (hash : List ℤ → ℤ) : FactoryLeafFriFloor (floorEngine hash) (honestFLS hash) :=
  fun _leafVk _leafCommit h => h

theorem honestSat (hash : List ℤ → ℤ) :
    SatFactoryFold (floorEngine hash) (honestFLS hash) (honestFold hash) where
  leafCV  := ⟨(7, 7), rfl, rfl⟩
  connect := rfl

/-- **`honest_companion_fires` (POSITIVE non-vacuity).** On the honest factory turn the binding
FIRES: the published `child_vk8` claim is BACKED by a verifying factory sub-proof attesting a
uniquely determined VK — unconditionally, at `Poseidon2Binding.Reference.refSponge`
whose CR is PROVED (the FRI legs discharge definitionally on `floorEngine`). -/
theorem honest_companion_fires :
    (∃ q : ℤ × ℤ, (floorEngine refSponge).verify q = true ∧
        (floorEngine refSponge).piCommit q = (honestFold refSponge).cv) ∧
    (∀ p q : ℤ × ℤ, (floorEngine refSponge).verify p = true → (floorEngine refSponge).verify q = true →
        (floorEngine refSponge).piCommit p = (honestFold refSponge).cv →
        (floorEngine refSponge).piCommit q = (honestFold refSponge).cv →
        (floorEngine refSponge).vkOf p = (floorEngine refSponge).vkOf q) :=
  factory_binding_from_fold (floorEngine refSponge) refSponge (fun p => [p.1, p.2]) (honestFLS refSponge)
    (honestFloor refSponge) (fun _p _ => rfl)
    (by intro p q _ _ henc; injection henc)
    (honestFold refSponge)
    (fun _p _q _ _ _ _ hcol => hcol.1 (refSponge_CR _ _ hcol.2))
    (honestSat refSponge)

end Honest

section Forged

/-- **`forged_unsat` (THE ANTI-GHOST TOOTH — forged child-VK claim ⟹ UNSAT).** A per-turn fold
whose published `child_vk8` claim `f.cv` is backed by NO verifying factory sub-proof CANNOT
satisfy: the fold re-verifies the leaf (`hfri`) and the connect ties its commitment to `f.cv`, so
a satisfying fold would PRODUCE a backing sub-proof — contradiction. The aggregate is UNSAT. The
circuit twin of `deployed_factory_turn_forged_child_vk_rejected`. -/
theorem forged_unsat {E : ProofEngine} {FactoryLeafSat : ℤ → ℤ → Prop}
    (hfri : FactoryLeafFriFloor E FactoryLeafSat) {f : FactoryFold E}
    (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.cv) :
    ¬ SatFactoryFold E FactoryLeafSat f := by
  intro hsat
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  exact hforge ⟨q, hq, hqc⟩

/-- The forged factory-leaf predicate over `demoEngine` (the only verifying sub-proof commits
to `123`). -/
def demoFLS : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit => ∃ q : Bool, demoEngine.verify q = true ∧ demoEngine.piCommit q = leafCommit

theorem demoFloor : FactoryLeafFriFloor demoEngine demoFLS :=
  fun _leafVk _leafCommit h => h

/-- The `FactoryBackingAttack` §A forgery lifted onto the fold: the published `child_vk8` claim is
`999` (`forgedChildVkEnv`'s `child_vk`) — a commitment NO verifying sub-proof of `demoEngine`
exposes. -/
def forgedFold : FactoryFold demoEngine := { leafVk := 0, leafCommit := 999, cv := 999 }

/-- **`forged_childvk_unsat_demo` (NEGATIVE non-vacuity — the §A attack, INVERTED onto the fold).**
The forged fold (published claim `999`, exactly `FactoryBackingAttack.childVk_forgedEnv`'s value,
unbacked) does NOT satisfy: what the deployed AIR alone admitted
(`deployed_admits_forged_child_vk`), the aggregate REFUSES. -/
theorem forged_childvk_unsat_demo : ¬ SatFactoryFold demoEngine demoFLS forgedFold := by
  refine forged_unsat demoFloor (f := forgedFold) ?_
  rintro ⟨q, _hq, hc⟩
  have hc' : (123 : ℤ) = 999 := hc
  exact absurd hc' (by decide)

end Forged

/-! ## §5 — Axiom hygiene (every load-bearing arm). -/

#assert_axioms factoryLeafFriFloor_of_aggFriExtract
#assert_axioms factory_binding_from_fold
#assert_axioms factory_binding_from_fold_or_collides
#assert_axioms authorized_from_fold
#assert_axioms honest_companion_fires
#assert_axioms forged_unsat
#assert_axioms forged_childvk_unsat_demo

end Dregg2.Circuit.FactoryBindingFromFold
