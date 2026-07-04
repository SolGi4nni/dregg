/-
# Dregg2.Circuit.DslBindingFromFold — the DEPLOYED DSL/Dfa binding, proven from the FOLD.

## Why this file exists (the flip — the 6th carrier)

`DslBackingAttack` proved the deployed `Witnessed{Dfa}` predicate INVISIBLE to a pure light
client: the Dfa caveat is a PRECONDITION with NO op on the deployed effect-vm at all — the
published route-commitment rides free (`deployed_admits_unwitnessed`,
`deployed_does_not_force_witnessed`), and only the off-AIR re-executing
`DslCircuitDfaVerifier` ever inspects it. The repair it NAMED (§C, `dslEngineBinding_of_floor`
— sound on the `Poseidon2SpongeCR` floor, waiting on the descriptor emit) is now DEPLOYED:

  * THE rc-EMIT LANDED cohort-wide: every deployed member is wrapped through
    `EffectVmEmitRotationV3.withDfaRcPins`, publishing the caveat-region 4-felt DFA
    route-commitment carrier (`C_RC_OFF`, filled from `RotatedCaveatManifest::dfa_rc` =
    `dfa_route_commitment(DfaProofWire.public_inputs)` on a Dfa-gated turn, the ZERO
    sentinel otherwise) as member PIs — at FIXED columns but PER-MEMBER PI indices
    (transfer 46..49; the post-exposure members appended their teeth after it), so the fold
    arm DERIVES the slots from the committed registry row
    (`ivc_turn_chain::dsl_rc_claim_pi_lo`).
  * The FOLD arm is live (`ivc_turn_chain::prove_chain_core_rotated`, Dsl arm): the per-turn
    aggregate folds the RE-PROVEN predicate-transition leaf
    (`dsl_leaf_adapter::prove_dsl_leaf_with_commitment` — custom-machinery reuse, term for
    term), RE-VERIFIES it via the recursion (the same in-circuit child-verifier subcircuit
    `AggAirSound` opens), and CONNECTS the leaf's exposed PI-commitment to the leg's
    published rc (`prove_dsl_binding_node_segmented` = `prove_custom_binding_node_segmented`).
    Fail-closed BOTH poles: a pin-less (pre-rc) descriptor is refused, and the ZERO rc
    sentinel is refused host-side (a no-Dfa turn never folds a vacuous claim — it takes the
    re-exec rung with `carrier_witness: None`).
  * The deployed-path tooth (`dsl_binding_deployed_tooth.rs`) exercises the honest / forged /
    zero-sentinel poles on the NATIVE committed transfer row.

This module proves the REAL deployed DSL/Dfa guarantee from premises that HOLD for the
deployed aggregate — the EXACT mirror of `SovereignBindingFromFold` / `CustomBindingFromFold`
(the universal sub-proof-folding primitive; dsl rides custom's machinery):

  * **`dsl_binding_from_fold`** — a verifying AGGREGATE (the per-turn fold including the DSL
    leaf) FORCES, for the leg's published route-commitment `f.rc`: (binding) ∃ a verifying
    DSL sub-proof `q` with `E.piCommit q = f.rc`, and (anti-ghost) the attested predicate
    program is DETERMINED by `f.rc`. Premises = {the FRI floor (= `AggAirSound`'s carrier),
    `Poseidon2SpongeCR`, the route-commitment factoring + structural vk-recovery
    (`DslBackingAttack.dslEngineBinding_of_route_commitment_factoring` — the §C repair,
    consumed here), the connect}. No staged-AIR carrier, no dsl axiom.

  * **`dslWitnessed_from_fold`** — the GROUNDING onto `DslBackingAttack.DslWitnessed`: with
    `Verifying` = the genuine off-AIR acceptance set (every verifying DSL sub-proof's
    exposed commitment is a Verifying value — the `hbacks` obligation, which holds
    definitionally when `Verifying c := ∃ q, verify q ∧ piCommit q = c`), a satisfying fold
    connected to the leg DISCHARGES the exact predicate `DslBackingAttack` proved the
    deployed AIR omits. §B (`deployed_does_not_force_witnessed`) stays TRUE of the bare AIR;
    what flips is the AGGREGATE.

## Non-vacuity (BOTH polarities, mirroring the Rust tooth)

`honest_companion_fires` — on an honest Dfa-gated turn the grounded binding FIRES.
`forged_unsat` / `forged_rc_unsat_demo` — a fold whose published rc is the
`DslBackingAttack` §A forgery (`999`, backed by NO verifying sub-proof) CANNOT satisfy: the
aggregate is UNSAT — the circuit twin of `deployed_dfa_turn_forged_rc_rejected`. (The ZERO
sentinel is refused HOST-SIDE by the arm before any fold — a vacuous claim is never even
offered to the aggregate.)

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. The
floor carriers appear ONLY as Prop hypotheses. NO new axiom, NO `sorry`. NEW file; imports
read-only. `DslBackingAttack` STANDS (the deployed-AIR facts remain true); this file is the
aggregate-level flip beside it.
-/
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.CustomCarrierAttack
import Dregg2.Circuit.DslBackingAttack

namespace Dregg2.Circuit.DslBindingFromFold

open Dregg2.Circuit.DescriptorIR2 (ProofEngine EngineBinding demoEngine)
open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.CustomCarrierAttack (floorEngine)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.DslBackingAttack (DeployedDfaLeg DslWitnessed
  dslEngineBinding_of_route_commitment_factoring)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the DSL-leaf FRI floor, and its provenance from `AggAirSound.FriExtract`. -/

/-- **`DslLeafFriFloor E DslLeafSat`** — the localized FRI-extraction floor for the re-proved
predicate-transition leaf: a SATISFIED in-circuit DSL-leaf verifier (pinned VK core `leafVk`,
exposing PI-commitment claim `leafCommit`) yields a GENUINELY VERIFYING DSL sub-proof of
engine `E` whose `piCommit` IS the exposed `leafCommit`. The dsl instance of
`AggAirSound.FriExtract` (one child of one node), NOT a new dregg axiom — see
`dslLeafFriFloor_of_aggFriExtract`. -/
def DslLeafFriFloor (E : ProofEngine) (DslLeafSat : ℤ → ℤ → Prop) : Prop :=
  ∀ leafVk leafCommit : ℤ, DslLeafSat leafVk leafCommit →
    ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = leafCommit

/-- The DSL leaf's exposed segment projection: the leaf carries its PI-commitment claim `x`
in the ordered-digest lane `acc` (the other lanes are inert for a single-leaf wrap). -/
def segOfCommit (x : ℤ) : Seg := { firstOld := 0, lastNew := 0, count := 0, acc := x }

/-- **`dslLeafFriFloor_of_aggFriExtract` — the FRI floor IS AggAirSound's carrier.** Given the
aggregation's per-child `FriExtract` over the DSL engine — pinned VK core constant `leafPre`,
the child exposing its PI-commitment claim in `acc` — the dsl-leaf floor follows. -/
theorem dslLeafFriFloor_of_aggFriExtract
    (E : ProofEngine) (leafPre : ℤ) (ChildVerifierSat : ℤ → Seg → Prop)
    (hagg : FriExtract E.Proof E.verify (fun _ => leafPre)
              (fun q => segOfCommit (E.piCommit q)) ChildVerifierSat) :
    DslLeafFriFloor E
      (fun leafVk leafCommit => ChildVerifierSat leafVk (segOfCommit leafCommit)) := by
  intro leafVk leafCommit hcv
  obtain ⟨q, hq, _hvkc, hexp⟩ := hagg leafVk (segOfCommit leafCommit) hcv
  refine ⟨q, hq, ?_⟩
  simpa [segOfCommit] using congrArg Seg.acc hexp

/-! ## §2 — the per-turn fold node + its satisfaction (the connect). -/

/-- **`DslFold E`** — the per-turn fold's dsl face: the DSL leaf's pinned preprocessed
commitment `leafVk` (its VK core), the PI-commitment claim `leafCommit` the leaf exposes, and
the effect-vm leg's published route-commitment `rc` (the `withDfaRcPins` rc PIs at the
per-member derived slots — transfer 46..49 — modeled as one ℤ exactly as `SovereignFold.kc`
models the 4-felt teeth claim). -/
structure DslFold (E : ProofEngine) where
  /-- the DSL-leaf recursion-verifier's pinned preprocessed commitment (VK core). -/
  leafVk     : ℤ
  /-- the PI-commitment claim the folded DSL leaf exposes. -/
  leafCommit : ℤ
  /-- the effect-vm leg's published DFA route-commitment (the rc PI carrier). -/
  rc         : ℤ

/-- **`SatDslFold E DslLeafSat f`** — a SATISFYING per-turn fold over its dsl face: `leafCV`
(the in-circuit DSL-leaf verifier subcircuit is satisfied) + `connect` (the aggregate's
combine constraint TIES the leaf's exposed claim to the leg's published rc —
`prove_dsl_binding_node_segmented`'s in-circuit connect). -/
structure SatDslFold (E : ProofEngine) (DslLeafSat : ℤ → ℤ → Prop)
    (f : DslFold E) : Prop where
  leafCV  : DslLeafSat f.leafVk f.leafCommit
  connect : f.leafCommit = f.rc

/-! ## §3 — THE REPAIR: the deployed DSL/Dfa binding, from the FOLD. -/

/-- **`dsl_binding_from_fold` (THE DEPLOYED PAYLOAD).** A verifying AGGREGATE — the per-turn
fold including the re-proved DSL leaf — FORCES, for the leg's published route-commitment
`f.rc`:

  (binding) ∃ a verifying DSL sub-proof `q` of `E` with `E.piCommit q = f.rc`; AND
  (anti-ghost) the attested predicate program is DETERMINED by `f.rc` — any two verifying
  sub-proofs exposing `f.rc` agree on their `vkOf`.

The premise set is EXACTLY the `custom_binding_from_fold` / `sovereign_binding_from_fold`
set; the engine binding is `DslBackingAttack`'s §C repair
(`dslEngineBinding_of_route_commitment_factoring` — the route-commitment IS a Poseidon2
sponge of the DSL PIs, VK recoverable), consumed here rather than restated. A forged rc with
no backing sub-proof makes the aggregate UNSAT. -/
theorem dsl_binding_from_fold
    (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (DslLeafSat : ℤ → ℤ → Prop)
    (hfri : DslLeafFriFloor E DslLeafSat)
    (hCR : Poseidon2SpongeCR hash)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : DslFold E) (hsat : SatDslFold E DslLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.rc) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = f.rc → E.piCommit q = f.rc → E.vkOf p = E.vkOf q) := by
  have hE : EngineBinding E :=
    dslEngineBinding_of_route_commitment_factoring hash E enc hCR hfactor hvk
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  intro p q' hp hq' hpc hq'c
  exact hE.commit_determines_vk p q' hp hq' (by rw [hpc, hq'c])

/-- **`dslWitnessed_from_fold` — the GROUNDING onto `DslBackingAttack.DslWitnessed` (the §B
close, at the aggregate).** `deployed_does_not_force_witnessed` proved the deployed AIR ALONE
never forces the predicate. THIS is the fold edge: when `Verifying` is the genuine off-AIR
acceptance set — every verifying DSL sub-proof's exposed PI-commitment is a `Verifying` value
(`hbacks`, which holds definitionally for `Verifying c := ∃ q, verify q ∧ piCommit q = c`,
the `CellProgram::verify_transition` acceptance set the attack file models) — a satisfying
fold whose published rc is the leg's (`hrc`) DISCHARGES exactly the predicate
`DslBackingAttack` showed the deployed AIR omits: the leg IS `DslWitnessed`. -/
theorem dslWitnessed_from_fold
    (E : ProofEngine) (DslLeafSat : ℤ → ℤ → Prop)
    (hfri : DslLeafFriFloor E DslLeafSat)
    (Verifying : ℤ → Prop)
    (hbacks : ∀ q : E.Proof, E.verify q = true → Verifying (E.piCommit q))
    (f : DslFold E) (hsat : SatDslFold E DslLeafSat f)
    (leg : DeployedDfaLeg) (hrc : f.rc = leg.rc) :
    DslWitnessed Verifying leg := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect, hrc] at hqc
  have hv := hbacks q hq
  rw [hqc] at hv
  exact hv

/-! ## §4 — NON-VACUITY: the binding FIRES on an honest fold; the §A forgery is REJECTED. -/

section Honest

/-- The honest dsl face over `floorEngine`: the folded leaf exposes the commitment of the
honest sub-proof `(7, 7)`, and the connect publishes that same commitment as the leg's rc. -/
def honestFold (hash : List ℤ → ℤ) : DslFold (floorEngine hash) :=
  { leafVk := 100, leafCommit := hash [7, 7], rc := hash [7, 7] }

/-- The honest DSL-leaf verifier predicate: satisfied exactly when a backing verifying
sub-proof exposes the exposed claim. -/
def honestDLS (hash : List ℤ → ℤ) : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit => ∃ q : ℤ × ℤ,
    (floorEngine hash).verify q = true ∧ (floorEngine hash).piCommit q = leafCommit

theorem honestFloor (hash : List ℤ → ℤ) :
    DslLeafFriFloor (floorEngine hash) (honestDLS hash) :=
  fun _leafVk _leafCommit h => h

theorem honestSat (hash : List ℤ → ℤ) :
    SatDslFold (floorEngine hash) (honestDLS hash) (honestFold hash) where
  leafCV  := ⟨(7, 7), rfl, rfl⟩
  connect := rfl

/-- **`honest_companion_fires` (POSITIVE non-vacuity).** On the honest Dfa-gated turn the
binding FIRES: the published route-commitment is BACKED by a verifying DSL sub-proof
attesting a uniquely determined predicate program — resting on `Poseidon2SpongeCR` alone. -/
theorem honest_companion_fires (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    (∃ q : ℤ × ℤ, (floorEngine hash).verify q = true ∧
        (floorEngine hash).piCommit q = (honestFold hash).rc) ∧
    (∀ p q : ℤ × ℤ, (floorEngine hash).verify p = true → (floorEngine hash).verify q = true →
        (floorEngine hash).piCommit p = (honestFold hash).rc →
        (floorEngine hash).piCommit q = (honestFold hash).rc →
        (floorEngine hash).vkOf p = (floorEngine hash).vkOf q) :=
  dsl_binding_from_fold (floorEngine hash) hash (fun p => [p.1, p.2]) (honestDLS hash)
    (honestFloor hash) hCR (fun _p _ => rfl)
    (by intro p q _ _ henc; injection henc)
    (honestFold hash) (honestSat hash)

/-- **The honest fold DISCHARGES `DslWitnessed`** — the grounded §B close is itself
non-vacuous: with `Verifying` = the floor engine's acceptance set, the honest Dfa-gated leg
(published rc = the honest commitment) is `DslWitnessed` FROM the fold. -/
theorem honest_dslWitnessed (hash : List ℤ → ℤ) :
    DslWitnessed
      (fun c => ∃ q : ℤ × ℤ,
        (floorEngine hash).verify q = true ∧ (floorEngine hash).piCommit q = c)
      ⟨(honestFold hash).rc, True⟩ :=
  dslWitnessed_from_fold (floorEngine hash) (honestDLS hash) (honestFloor hash)
    _ (fun q hq => ⟨q, hq, rfl⟩) (honestFold hash) (honestSat hash)
    ⟨(honestFold hash).rc, True⟩ rfl

end Honest

section Forged

/-- **`forged_unsat` (THE ANTI-GHOST TOOTH — forged rc ⟹ UNSAT).** A per-turn fold whose
published route-commitment `f.rc` is backed by NO verifying DSL sub-proof CANNOT satisfy: the
fold re-verifies the leaf (`hfri`) and the connect ties its claim to `f.rc`, so a satisfying
fold would PRODUCE a backing sub-proof — contradiction. The circuit twin of
`deployed_dfa_turn_forged_rc_rejected`. -/
theorem forged_unsat {E : ProofEngine} {DslLeafSat : ℤ → ℤ → Prop}
    (hfri : DslLeafFriFloor E DslLeafSat) {f : DslFold E}
    (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.rc) :
    ¬ SatDslFold E DslLeafSat f := by
  intro hsat
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  exact hforge ⟨q, hq, hqc⟩

/-- The DSL-leaf predicate over `demoEngine` (the only verifying sub-proof commits to
`123`). -/
def demoDLS : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit =>
    ∃ q : Bool, demoEngine.verify q = true ∧ demoEngine.piCommit q = leafCommit

theorem demoFloor : DslLeafFriFloor demoEngine demoDLS :=
  fun _leafVk _leafCommit h => h

/-- The `DslBackingAttack` §A forgery lifted onto the fold: the published route-commitment is
`999` (`deployed_admits_unwitnessed`'s unwitnessed leg value) — a claim NO verifying
sub-proof of `demoEngine` exposes. -/
def forgedFold : DslFold demoEngine := { leafVk := 0, leafCommit := 999, rc := 999 }

/-- **`forged_rc_unsat_demo` (NEGATIVE non-vacuity — the §A attack, INVERTED onto the
fold).** The forged fold (published rc `999`, exactly the `deployed_admits_unwitnessed` leg's
value, unbacked) does NOT satisfy: what the deployed AIR alone admitted, the aggregate
REFUSES. -/
theorem forged_rc_unsat_demo : ¬ SatDslFold demoEngine demoDLS forgedFold := by
  refine forged_unsat demoFloor (f := forgedFold) ?_
  rintro ⟨q, _hq, hc⟩
  have hc' : (123 : ℤ) = 999 := hc
  exact absurd hc' (by decide)

end Forged

/-! ## §5 — Axiom hygiene (every load-bearing arm). -/

#assert_axioms dslLeafFriFloor_of_aggFriExtract
#assert_axioms dsl_binding_from_fold
#assert_axioms dslWitnessed_from_fold
#assert_axioms honest_companion_fires
#assert_axioms honest_dslWitnessed
#assert_axioms forged_unsat
#assert_axioms forged_rc_unsat_demo

end Dregg2.Circuit.DslBindingFromFold
