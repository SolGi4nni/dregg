/-
# Dregg2.Circuit.HatcheryBindingFromFold — the DEPLOYED hatchery-contract binding, from the FOLD.

## Why this file exists (the flip)

`HatcheryBackingAttack` proved the deployed hatchery-mint leg VACUOUS as a pure light client sees
it: the stored `contract_hash` / `invariant_digest` teeth are read by NO constraint
(`deployed_admits_unbacked_hatchery`, `deployed_admits_wrong_contract`,
`deployed_intent_does_not_force_backing`). The repair it named — the attestation must come from the
per-turn FOLD over a re-proved CONTRACT-ATTESTATION leaf connected to the published teeth — is now
DEPLOYED:

  * STEP 2/2.5 committed the carrier material: the AFTER-block `contract_hash8` octet
    (limbs 96..=103) is a committed pre-limb absorbed into `state_commit`, filled from the
    hatchery-mint `HpresProof::Attested` content hash (ZERO on a plain factory turn).
  * STEP 3 pinned it: the deployed `factoryVmDescriptor2R24` (`factoryV3Carriers` — the hatchery
    carrier RIDES factory's `CreateCellFromFactory` leg) publishes the committed octet at member
    PIs 55..62, the SECOND octet cohort after `child_vk8`. The hatchery-INVARIANT carrier rides
    the FIRST octet (`invariant_digest === child_vk`) and consumes the same pins.
  * The FOLD arm landed (`ivc_turn_chain::prove_chain_core_rotated`, Hatchery arm): the aggregate
    folds the re-proven contract-attestation leaf, RE-VERIFIES it via the recursion, and CONNECTS
    the leaf's exposed attestation commitment to the leg's published `contract_hash8` claim PIs.
    The deployed-path tooth (`hatchery_binding_deployed_tooth.rs`) exercises BOTH poles on the
    committed registry row.

The EXACT mirror of `CustomBindingFromFold` / `FactoryBindingFromFold` over the universal
sub-proof-folding primitive:

  * **`hatchery_binding_from_fold`** — a verifying aggregate FORCES, for the leg's published
    `contract_hash8` claim `f.ch`: (binding) ∃ a verifying contract sub-proof exposing it, and
    (anti-ghost) the attested identity is DETERMINED by `f.ch`.
  * **`backed_from_fold`** — the GROUNDING onto `HatcheryBackingAttack.Backed`: when the folded
    leaf's semantics is the re-proved contract attestation (a verifying sub-proof exposing the
    leg's published `contract_hash` IS a verifying `CellContract` attestation of it — the adapter
    obligation, the named premise `hbacks`), a satisfying fold DISCHARGES the exact backing
    predicate the attack file proved the deployed AIR omits. The §B hole is CLOSED at the
    aggregate.

## Non-vacuity (BOTH polarities, mirroring the Rust tooth)

`honest_companion_fires` — the binding FIRES on an honest hatchery mint.
`forged_unsat` / `forged_contract_unsat_demo` — a fold whose published claim is unbacked CANNOT
satisfy — the circuit twin of `deployed_hatchery_turn_forged_contract_hash_rejected`.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. NO new
axiom, NO `sorry`. NEW file; imports read-only.
-/
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.CustomCarrierAttack
import Dregg2.Circuit.HatcheryBackingAttack

namespace Dregg2.Circuit.HatcheryBindingFromFold

open Dregg2.Circuit.DescriptorIR2 (ProofEngine EngineBinding demoEngine)
open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.CustomCarrierAttack (engineBinding_of_floor floorEngine)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.HatcheryBackingAttack (ContractEngine Backed contractHashOf)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the contract-leaf FRI floor, and its provenance from `AggAirSound.FriExtract`. -/

/-- **`ContractLeafFriFloor E ContractLeafSat`** — the localized FRI-extraction floor for the
contract-attestation leaf: a SATISFIED in-circuit contract-leaf verifier (pinned VK core `leafVk`,
exposing attestation commitment `leafCommit`) yields a GENUINELY VERIFYING contract sub-proof of
engine `E` whose `piCommit` IS the exposed `leafCommit`. The hatchery instance of
`AggAirSound.FriExtract`, NOT a new dregg axiom. -/
def ContractLeafFriFloor (E : ProofEngine) (ContractLeafSat : ℤ → ℤ → Prop) : Prop :=
  ∀ leafVk leafCommit : ℤ, ContractLeafSat leafVk leafCommit →
    ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = leafCommit

/-- The contract leaf's exposed segment projection (`acc` carries the attestation commitment). -/
def segOfCommit (x : ℤ) : Seg := { firstOld := 0, lastNew := 0, count := 0, acc := x }

/-- **`contractLeafFriFloor_of_aggFriExtract` — the FRI floor IS AggAirSound's carrier.** -/
theorem contractLeafFriFloor_of_aggFriExtract
    (E : ProofEngine) (leafPre : ℤ) (ChildVerifierSat : ℤ → Seg → Prop)
    (hagg : FriExtract E.Proof E.verify (fun _ => leafPre)
              (fun q => segOfCommit (E.piCommit q)) ChildVerifierSat) :
    ContractLeafFriFloor E
      (fun leafVk leafCommit => ChildVerifierSat leafVk (segOfCommit leafCommit)) := by
  intro leafVk leafCommit hcv
  obtain ⟨q, hq, _hvkc, hexp⟩ := hagg leafVk (segOfCommit leafCommit) hcv
  refine ⟨q, hq, ?_⟩
  simpa [segOfCommit] using congrArg Seg.acc hexp

/-! ## §2 — the per-turn fold node + its satisfaction (the connect). -/

/-- **`HatcheryFold E`** — the per-turn fold's hatchery face: the contract-leaf's pinned
preprocessed commitment `leafVk`, the attestation commitment `leafCommit` the leaf exposes, and
the effect-vm leg's published `contract_hash8` claim `ch` (the committed-octet pins, member PIs
55..62 on `factoryV3Carriers`). -/
structure HatcheryFold (E : ProofEngine) where
  /-- the contract-leaf recursion-verifier's pinned preprocessed commitment (VK core). -/
  leafVk     : ℤ
  /-- the attestation commitment the folded contract leaf exposes. -/
  leafCommit : ℤ
  /-- the effect-vm leg's published `contract_hash8` claim (the committed-octet PI carrier). -/
  ch         : ℤ

/-- **`SatHatcheryFold E ContractLeafSat f`** — a SATISFYING per-turn fold over its hatchery face:
`leafCV` (the in-circuit contract-leaf verifier satisfied) + `connect` (the combine constraint
ties the leaf's exposed commitment to the leg's published claim). -/
structure SatHatcheryFold (E : ProofEngine) (ContractLeafSat : ℤ → ℤ → Prop)
    (f : HatcheryFold E) : Prop where
  leafCV  : ContractLeafSat f.leafVk f.leafCommit
  connect : f.leafCommit = f.ch

/-! ## §3 — THE REPAIR: the deployed hatchery binding, from the FOLD. -/

/-- **`hatchery_binding_from_fold` (THE DEPLOYED PAYLOAD).** A verifying AGGREGATE — the per-turn
fold including the contract-attestation leaf — FORCES, for the leg's published `contract_hash8`
claim `f.ch`: (binding) ∃ a verifying contract sub-proof `q` with `E.piCommit q = f.ch`; AND
(anti-ghost) the attested identity is DETERMINED by `f.ch`. Same premise set as
`custom_binding_from_fold`; no staged-AIR carrier, no hatchery axiom. -/
theorem hatchery_binding_from_fold
    (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (ContractLeafSat : ℤ → ℤ → Prop)
    (hfri : ContractLeafFriFloor E ContractLeafSat)
    (hCR : Poseidon2SpongeCR hash)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : HatcheryFold E) (hsat : SatHatcheryFold E ContractLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.ch) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = f.ch → E.piCommit q = f.ch → E.vkOf p = E.vkOf q) := by
  have hE : EngineBinding E := engineBinding_of_floor hash E enc hCR hfactor hvk
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  intro p q' hp hq' hpc hq'c
  exact hE.commit_determines_vk p q' hp hq' (by rw [hpc, hq'c])

/-- **`backed_from_fold` — the GROUNDING onto `HatcheryBackingAttack.Backed` (the §B close).**
When the folded leaf's semantics is the re-proved contract attestation — a verifying contract
sub-proof exposing the leg's published `contract_hash` IS a verifying `CellContract` attestation
backing that leg (`hbacks`, the adapter obligation) — a satisfying fold connected to the leg
(`hch`) DISCHARGES the exact staged backing predicate `HatcheryBackingAttack` proved the deployed
AIR omits. -/
theorem backed_from_fold
    (C : ContractEngine) (env : VmRowEnv)
    (E : ProofEngine) (ContractLeafSat : ℤ → ℤ → Prop)
    (hfri : ContractLeafFriFloor E ContractLeafSat)
    (hbacks : ∀ q : E.Proof, E.verify q = true → E.piCommit q = contractHashOf env →
        Backed C env)
    (f : HatcheryFold E) (hsat : SatHatcheryFold E ContractLeafSat f)
    (hch : f.ch = contractHashOf env) :
    Backed C env := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect, hch] at hqc
  exact hbacks q hq hqc

/-! ## §4 — NON-VACUITY: the binding FIRES on an honest fold; a forged claim is REJECTED. -/

section Honest

/-- The honest hatchery face over `floorEngine`: the folded leaf exposes the commitment of the
honest attestation sub-proof `(7, 7)`, connected to the leg's published claim. -/
def honestFold (hash : List ℤ → ℤ) : HatcheryFold (floorEngine hash) :=
  { leafVk := 100, leafCommit := hash [7, 7], ch := hash [7, 7] }

/-- The honest contract-leaf verifier predicate. -/
def honestHLS (hash : List ℤ → ℤ) : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit => ∃ q : ℤ × ℤ,
    (floorEngine hash).verify q = true ∧ (floorEngine hash).piCommit q = leafCommit

theorem honestFloor (hash : List ℤ → ℤ) :
    ContractLeafFriFloor (floorEngine hash) (honestHLS hash) :=
  fun _leafVk _leafCommit h => h

theorem honestSat (hash : List ℤ → ℤ) :
    SatHatcheryFold (floorEngine hash) (honestHLS hash) (honestFold hash) where
  leafCV  := ⟨(7, 7), rfl, rfl⟩
  connect := rfl

/-- **`honest_companion_fires` (POSITIVE non-vacuity).** On the honest hatchery mint the binding
FIRES: the published `contract_hash8` claim is BACKED by a verifying attestation sub-proof with a
uniquely determined identity. -/
theorem honest_companion_fires (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    (∃ q : ℤ × ℤ, (floorEngine hash).verify q = true ∧
        (floorEngine hash).piCommit q = (honestFold hash).ch) ∧
    (∀ p q : ℤ × ℤ, (floorEngine hash).verify p = true → (floorEngine hash).verify q = true →
        (floorEngine hash).piCommit p = (honestFold hash).ch →
        (floorEngine hash).piCommit q = (honestFold hash).ch →
        (floorEngine hash).vkOf p = (floorEngine hash).vkOf q) :=
  hatchery_binding_from_fold (floorEngine hash) hash (fun p => [p.1, p.2]) (honestHLS hash)
    (honestFloor hash) hCR (fun _p _ => rfl)
    (by intro p q _ _ henc; injection henc)
    (honestFold hash) (honestSat hash)

end Honest

section Forged

/-- **`forged_unsat` (THE ANTI-GHOST TOOTH — forged contract-hash claim ⟹ UNSAT).** A per-turn
fold whose published `contract_hash8` claim `f.ch` is backed by NO verifying contract sub-proof
CANNOT satisfy — the circuit twin of `deployed_hatchery_turn_forged_contract_hash_rejected`. -/
theorem forged_unsat {E : ProofEngine} {ContractLeafSat : ℤ → ℤ → Prop}
    (hfri : ContractLeafFriFloor E ContractLeafSat) {f : HatcheryFold E}
    (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.ch) :
    ¬ SatHatcheryFold E ContractLeafSat f := by
  intro hsat
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  exact hforge ⟨q, hq, hqc⟩

/-- The forged contract-leaf predicate over `demoEngine` (the only verifying sub-proof commits
to `123`). -/
def demoHLS : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit => ∃ q : Bool, demoEngine.verify q = true ∧ demoEngine.piCommit q = leafCommit

theorem demoFloor : ContractLeafFriFloor demoEngine demoHLS :=
  fun _leafVk _leafCommit h => h

/-- A FORGED fold over `demoEngine`: the published `contract_hash8` claim is `999`, a commitment
NO verifying contract sub-proof exposes. -/
def forgedFold : HatcheryFold demoEngine := { leafVk := 0, leafCommit := 999, ch := 999 }

/-- **`forged_contract_unsat_demo` (NEGATIVE non-vacuity).** What the deployed AIR alone admitted
(`deployed_admits_unbacked_hatchery` / `deployed_admits_wrong_contract`), the aggregate REFUSES:
the forged fold does not satisfy. -/
theorem forged_contract_unsat_demo : ¬ SatHatcheryFold demoEngine demoHLS forgedFold := by
  refine forged_unsat demoFloor (f := forgedFold) ?_
  rintro ⟨q, _hq, hc⟩
  have hc' : (123 : ℤ) = 999 := hc
  exact absurd hc' (by decide)

end Forged

/-! ## §5 — Axiom hygiene (every load-bearing arm). -/

#assert_axioms contractLeafFriFloor_of_aggFriExtract
#assert_axioms hatchery_binding_from_fold
#assert_axioms backed_from_fold
#assert_axioms honest_companion_fires
#assert_axioms forged_unsat
#assert_axioms forged_contract_unsat_demo

end Dregg2.Circuit.HatcheryBindingFromFold
