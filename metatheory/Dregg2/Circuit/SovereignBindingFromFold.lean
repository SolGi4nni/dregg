/-
# Dregg2.Circuit.SovereignBindingFromFold — the DEPLOYED sovereign binding, proven from the FOLD.

## Why this file exists (the flip)

`SovereignBackingAttack` proved the deployed `MakeSovereign` leg VACUOUS as a pure light client
sees it: the deployed AIR gates only the mode transition, never the owner-signature authority /
sequence / anchor (`deployed_admits_unbacked_sovereign`, `deployed_intent_does_not_force_authority`).
The repair it NAMED — the backing must come from the per-turn FOLD over a re-proved AUTHORITY leaf
connected to the published `key_commit` teeth — is now DEPLOYED:

  * STEP 2 committed the carrier material: the BEFORE-block `pubkey8` octet (limbs 104..=111) is a
    committed pre-limb absorbed into `state_commit`, filled UNCONDITIONALLY as
    `canonical_32_to_felts_8(cell.public_key())`.
  * THE BIG-BANG REGEN pinned AND welded it: the committed wide registry row is
    `CarrierComposed.makeSovereignV3DeployedWide` — the 4 KEY_COMMIT teeth columns (113..=116)
    row-0-pinned at claim PIs 58..61 (`SOVEREIGN_KEY_COMMIT_PI_LO`) PLUS the in-AIR KEY_COMMIT
    chip-compress gate (the THIRD EDGE: teeth == `canonical_32_to_felts_4` of the committed octet
    — `makeSovereignV3DeployedWide_publishes_key_commit`, `#assert_axioms`-clean). The apex rides
    the narrow member at `Rfix 38` (`Rfix_makeSovereign`).
  * The FOLD arm is live (`ivc_turn_chain::prove_chain_core_rotated`, Sovereign arm): the per-turn
    aggregate folds the re-proven owner-authority leaf
    (`sovereign_leaf_adapter::prove_sovereign_leaf_with_key_claim`), RE-VERIFIES it via the
    recursion (the same in-circuit child-verifier subcircuit `AggAirSound` opens), and CONNECTS
    the leaf's exposed key-commit claim to the leg's published teeth PIs
    (`prove_sovereign_binding_node_segmented`). The deployed-path tooth
    (`sovereign_binding_deployed_tooth.rs`) exercises BOTH poles on the NATIVE committed registry
    row.

This module proves the REAL deployed sovereign guarantee from premises that HOLD for the deployed
aggregate — the EXACT mirror of `FactoryBindingFromFold` / `CustomBindingFromFold` (the universal
sub-proof-folding primitive; sovereign rides the same machinery):

  * **`sovereign_binding_from_fold`** — a verifying AGGREGATE (the per-turn fold including the
    authority leaf) FORCES, for the leg's published `key_commit` claim `f.kc`: (binding) ∃ a
    verifying authority sub-proof `q` with `E.piCommit q = f.kc`, and (anti-ghost) the attested
    authority is DETERMINED by `f.kc`. Premises = {the FRI floor (= `AggAirSound`'s carrier),
    `Poseidon2SpongeCR`, the engine-commitment factoring + structural vk-recovery, the connect}.
    No staged-AIR carrier.

  * **`authorized_from_fold`** — the GROUNDING onto `SovereignBackingAttack.Authorized`: when the
    folded leaf's semantics is the re-proved owner-signature verification (a verifying authority
    sub-proof exposing the leg's published `key_commit` IS an owner-sig attestation of the leg's
    `(key_commit, sequence, anchor)` tuple, un-replayed — the `sovereign_leaf_adapter` obligation,
    carried as the named premise `hbacks`), a satisfying fold DISCHARGES the exact authority
    predicate `SovereignBackingAttack` proved the deployed AIR omits. The §C hole
    (`deployed_intent_does_not_force_authority`) is thereby CLOSED at the aggregate.

BEYOND the factory mirror, sovereign carries the IN-AIR third edge too: the committed row's
KEY_COMMIT chip gate independently welds the published teeth to the COMMITTED pubkey octet
(`CarrierComposed.makeSovereignV3Deployed_publishes_key_commit`), so the fold's connect target is
itself commitment-bound — the claim slot is not a free column.

## Non-vacuity (BOTH polarities, mirroring the Rust tooth)

`honest_companion_fires` — on an honest sovereign promotion the grounded binding FIRES.
`forged_unsat` / `forged_keycommit_unsat_demo` — a fold whose published key-commit claim is the
`SovereignBackingAttack` §A forgery (`0`, backed by NO verifying sub-proof) CANNOT satisfy: the
aggregate is UNSAT — the circuit twin of `deployed_sovereign_turn_forged_key_commit_rejected`.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. The floor
carriers appear ONLY as Prop hypotheses. NO new axiom, NO `sorry`. NEW file; imports read-only.
-/
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.CustomCarrierAttack
import Dregg2.Circuit.SovereignBackingAttack

namespace Dregg2.Circuit.SovereignBindingFromFold

open Dregg2.Circuit.DescriptorIR2 (ProofEngine EngineBinding demoEngine)
open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.CustomCarrierAttack (engineBinding_of_floor floorEngine)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.SovereignBackingAttack (SovAuthorityEngine Authorized keyCommitOf)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the authority-leaf FRI floor, and its provenance from `AggAirSound.FriExtract`. -/

/-- **`SovereignLeafFriFloor E SovereignLeafSat`** — the localized FRI-extraction floor for the
authority leaf: a SATISFIED in-circuit authority-leaf verifier (pinned VK core `leafVk`, exposing
key-commit claim `leafCommit`) yields a GENUINELY VERIFYING authority sub-proof of engine `E`
whose `piCommit` IS the exposed `leafCommit`. The sovereign instance of `AggAirSound.FriExtract`
(one child of one node), NOT a new dregg axiom — see `sovereignLeafFriFloor_of_aggFriExtract`. -/
def SovereignLeafFriFloor (E : ProofEngine) (SovereignLeafSat : ℤ → ℤ → Prop) : Prop :=
  ∀ leafVk leafCommit : ℤ, SovereignLeafSat leafVk leafCommit →
    ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = leafCommit

/-- The authority leaf's exposed segment projection: the leaf carries its key-commit claim `x` in
the ordered-digest lane `acc` (the other lanes are inert for a single-leaf wrap). -/
def segOfCommit (x : ℤ) : Seg := { firstOld := 0, lastNew := 0, count := 0, acc := x }

/-- **`sovereignLeafFriFloor_of_aggFriExtract` — the FRI floor IS AggAirSound's carrier.** Given
the aggregation's per-child `FriExtract` over the authority engine — pinned VK core constant
`leafPre`, the child exposing its key-commit claim in `acc` — the sovereign-leaf floor follows. -/
theorem sovereignLeafFriFloor_of_aggFriExtract
    (E : ProofEngine) (leafPre : ℤ) (ChildVerifierSat : ℤ → Seg → Prop)
    (hagg : FriExtract E.Proof E.verify (fun _ => leafPre)
              (fun q => segOfCommit (E.piCommit q)) ChildVerifierSat) :
    SovereignLeafFriFloor E
      (fun leafVk leafCommit => ChildVerifierSat leafVk (segOfCommit leafCommit)) := by
  intro leafVk leafCommit hcv
  obtain ⟨q, hq, _hvkc, hexp⟩ := hagg leafVk (segOfCommit leafCommit) hcv
  refine ⟨q, hq, ?_⟩
  simpa [segOfCommit] using congrArg Seg.acc hexp

/-! ## §2 — the per-turn fold node + its satisfaction (the connect). -/

/-- **`SovereignFold E`** — the per-turn fold's sovereign face: the authority-leaf's pinned
preprocessed commitment `leafVk` (its VK core), the key-commit claim `leafCommit` the leaf
exposes, and the effect-vm leg's published KEY_COMMIT claim `kc` (the teeth PIs 58..61 on the
NATIVE `makeSovereignV3DeployedWide` row, modeled as one ℤ exactly as `FactoryFold.cv` models the
8-limb octet claim). -/
structure SovereignFold (E : ProofEngine) where
  /-- the authority-leaf recursion-verifier's pinned preprocessed commitment (VK core). -/
  leafVk     : ℤ
  /-- the key-commit claim the folded authority leaf exposes. -/
  leafCommit : ℤ
  /-- the effect-vm leg's published KEY_COMMIT claim (the teeth PI carrier). -/
  kc         : ℤ

/-- **`SatSovereignFold E SovereignLeafSat f`** — a SATISFYING per-turn fold over its sovereign
face: `leafCV` (the in-circuit authority-leaf verifier subcircuit is satisfied) + `connect` (the
aggregate's combine constraint TIES the leaf's exposed claim to the leg's published teeth —
`prove_sovereign_binding_node_segmented`'s in-circuit connect). -/
structure SatSovereignFold (E : ProofEngine) (SovereignLeafSat : ℤ → ℤ → Prop)
    (f : SovereignFold E) : Prop where
  leafCV  : SovereignLeafSat f.leafVk f.leafCommit
  connect : f.leafCommit = f.kc

/-! ## §3 — THE REPAIR: the deployed sovereign binding, from the FOLD. -/

/-- **`sovereign_binding_from_fold` (THE DEPLOYED PAYLOAD).** A verifying AGGREGATE — the per-turn
fold including the authority leaf — FORCES, for the leg's published KEY_COMMIT claim `f.kc`:

  (binding) ∃ a verifying authority sub-proof `q` of `E` with `E.piCommit q = f.kc`; AND
  (anti-ghost) the attested authority is DETERMINED by `f.kc` — any two verifying sub-proofs
  exposing `f.kc` agree on their `vkOf`.

The premise set is EXACTLY the `custom_binding_from_fold` / `factory_binding_from_fold` set; no
staged-AIR carrier, no sovereign axiom. A forged claim with no backing sub-proof makes the
aggregate UNSAT. -/
theorem sovereign_binding_from_fold
    (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (SovereignLeafSat : ℤ → ℤ → Prop)
    (hfri : SovereignLeafFriFloor E SovereignLeafSat)
    (hCR : Poseidon2SpongeCR hash)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : SovereignFold E) (hsat : SatSovereignFold E SovereignLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.kc) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = f.kc → E.piCommit q = f.kc → E.vkOf p = E.vkOf q) := by
  have hE : EngineBinding E := engineBinding_of_floor hash E enc hCR hfactor hvk
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  intro p q' hp hq' hpc hq'c
  exact hE.commit_determines_vk p q' hp hq' (by rw [hpc, hq'c])

/-- **`authorized_from_fold` — the GROUNDING onto `SovereignBackingAttack.Authorized` (the §C
close).** `deployed_intent_does_not_force_authority` proved the deployed AIR ALONE never forces
the owner authority. THIS is the fold edge: when the folded leaf's semantics is the re-proved
owner-signature verification — a verifying authority sub-proof exposing the leg's published
`key_commit` IS an owner-sig attestation of the leg's tuple, un-replayed (`hbacks`, the
`sovereign_leaf_adapter` obligation) — a satisfying fold connected to the leg (`hkc`) DISCHARGES
the exact authority predicate the attack file showed the deployed AIR omits. -/
theorem authorized_from_fold
    (S : SovAuthorityEngine) (replayed : ℤ → Prop) (env : VmRowEnv)
    (E : ProofEngine) (SovereignLeafSat : ℤ → ℤ → Prop)
    (hfri : SovereignLeafFriFloor E SovereignLeafSat)
    (hbacks : ∀ q : E.Proof, E.verify q = true → E.piCommit q = keyCommitOf env →
        Authorized S replayed env)
    (f : SovereignFold E) (hsat : SatSovereignFold E SovereignLeafSat f)
    (hkc : f.kc = keyCommitOf env) :
    Authorized S replayed env := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect, hkc] at hqc
  exact hbacks q hq hqc

/-! ## §4 — NON-VACUITY: the binding FIRES on an honest fold; the §A forgery is REJECTED. -/

section Honest

/-- The honest sovereign face over `floorEngine`: the folded leaf exposes the commitment of the
honest sub-proof `(7, 7)`, and the connect publishes that same commitment as the leg's KEY_COMMIT
claim. -/
def honestFold (hash : List ℤ → ℤ) : SovereignFold (floorEngine hash) :=
  { leafVk := 100, leafCommit := hash [7, 7], kc := hash [7, 7] }

/-- The honest authority-leaf verifier predicate: satisfied exactly when a backing verifying
sub-proof exposes the exposed claim. -/
def honestSLS (hash : List ℤ → ℤ) : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit => ∃ q : ℤ × ℤ,
    (floorEngine hash).verify q = true ∧ (floorEngine hash).piCommit q = leafCommit

theorem honestFloor (hash : List ℤ → ℤ) :
    SovereignLeafFriFloor (floorEngine hash) (honestSLS hash) :=
  fun _leafVk _leafCommit h => h

theorem honestSat (hash : List ℤ → ℤ) :
    SatSovereignFold (floorEngine hash) (honestSLS hash) (honestFold hash) where
  leafCV  := ⟨(7, 7), rfl, rfl⟩
  connect := rfl

/-- **`honest_companion_fires` (POSITIVE non-vacuity).** On the honest sovereign promotion the
binding FIRES: the published KEY_COMMIT claim is BACKED by a verifying authority sub-proof
attesting a uniquely determined authority — resting on `Poseidon2SpongeCR` alone. -/
theorem honest_companion_fires (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    (∃ q : ℤ × ℤ, (floorEngine hash).verify q = true ∧
        (floorEngine hash).piCommit q = (honestFold hash).kc) ∧
    (∀ p q : ℤ × ℤ, (floorEngine hash).verify p = true → (floorEngine hash).verify q = true →
        (floorEngine hash).piCommit p = (honestFold hash).kc →
        (floorEngine hash).piCommit q = (honestFold hash).kc →
        (floorEngine hash).vkOf p = (floorEngine hash).vkOf q) :=
  sovereign_binding_from_fold (floorEngine hash) hash (fun p => [p.1, p.2]) (honestSLS hash)
    (honestFloor hash) hCR (fun _p _ => rfl)
    (by intro p q _ _ henc; injection henc)
    (honestFold hash) (honestSat hash)

end Honest

section Forged

/-- **`forged_unsat` (THE ANTI-GHOST TOOTH — forged key-commit claim ⟹ UNSAT).** A per-turn fold
whose published KEY_COMMIT claim `f.kc` is backed by NO verifying authority sub-proof CANNOT
satisfy: the fold re-verifies the leaf (`hfri`) and the connect ties its claim to `f.kc`, so a
satisfying fold would PRODUCE a backing sub-proof — contradiction. The circuit twin of
`deployed_sovereign_turn_forged_key_commit_rejected`. -/
theorem forged_unsat {E : ProofEngine} {SovereignLeafSat : ℤ → ℤ → Prop}
    (hfri : SovereignLeafFriFloor E SovereignLeafSat) {f : SovereignFold E}
    (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.kc) :
    ¬ SatSovereignFold E SovereignLeafSat f := by
  intro hsat
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  exact hforge ⟨q, hq, hqc⟩

/-- The authority-leaf predicate over `demoEngine` (the only verifying sub-proof commits to
`123`). -/
def demoSLS : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit =>
    ∃ q : Bool, demoEngine.verify q = true ∧ demoEngine.piCommit q = leafCommit

theorem demoFloor : SovereignLeafFriFloor demoEngine demoSLS :=
  fun _leafVk _leafCommit h => h

/-- The `SovereignBackingAttack` §A forgery lifted onto the fold: the published KEY_COMMIT claim
is `0` (`keyCommit_forgedEnv`'s value) — a claim NO verifying sub-proof of `demoEngine` exposes. -/
def forgedFold : SovereignFold demoEngine := { leafVk := 0, leafCommit := 0, kc := 0 }

/-- **`forged_keycommit_unsat_demo` (NEGATIVE non-vacuity — the §A attack, INVERTED onto the
fold).** The forged fold (published claim `0`, exactly `SovereignBackingAttack.keyCommit_forgedEnv`'s
value, unbacked) does NOT satisfy: what the deployed AIR alone admitted
(`deployed_admits_unbacked_sovereign`), the aggregate REFUSES. -/
theorem forged_keycommit_unsat_demo : ¬ SatSovereignFold demoEngine demoSLS forgedFold := by
  refine forged_unsat demoFloor (f := forgedFold) ?_
  rintro ⟨q, _hq, hc⟩
  have hc' : (123 : ℤ) = 0 := hc
  exact absurd hc' (by decide)

end Forged

/-! ## §5 — Axiom hygiene (every load-bearing arm). -/

#assert_axioms sovereignLeafFriFloor_of_aggFriExtract
#assert_axioms sovereign_binding_from_fold
#assert_axioms authorized_from_fold
#assert_axioms honest_companion_fires
#assert_axioms forged_unsat
#assert_axioms forged_keycommit_unsat_demo

end Dregg2.Circuit.SovereignBindingFromFold
