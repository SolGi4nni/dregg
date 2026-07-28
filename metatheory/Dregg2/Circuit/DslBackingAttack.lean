/-
# Dregg2.Circuit.DslBackingAttack — ADVERSARIAL soundness audit of the DSL/Dfa predicate carrier.

This is the DSL/Dfa analog of `CustomCarrierAttack` / `BridgeBackingAttack` / `SovereignBackingAttack`:
it refutes, IN LEAN, the claim that a pure LIGHT CLIENT (one that folds only the per-turn recursion
tree) witnesses the DSL/Dfa predicate transition gating a turn.

## The deployed object under attack

A `Witnessed { Dfa }` caveat (the relay-routing predicate, `dregg-dfa-routing-v1`, and any deployed
`CellProgram` predicate) is checked OFF-AIR by
`turn::executor::membership_verifier::DslCircuitDfaVerifier::verify`, which resolves the program by
its `vk_hash` and calls `CellProgram::verify_transition → dregg_circuit::stark::verify` (the bespoke
`circuit/src/stark.rs` STARK). This is a RE-EXECUTING-VALIDATOR gate: it runs in the executor's
witnessed-predicate registry, NOT inside the deployed effect-vm AIR.

Crucially, the Dfa predicate is a PRECONDITION CAVEAT, not an `Effect`. So — UNLIKE the custom
carrier, which at least has an in-AIR `proofBind` op whose deployed denotation is the vacuous `True`
(`CustomCarrierAttack.deployed_proofBind_gate_vacuous`) — the deployed effect-vm has NO op at all that
reads the DSL predicate's published route-commitment. The light-client witnessing is not merely
vacuous-gated; it is ABSENT. A validator with vs without `DslCircuitDfaVerifier` registered produces
the SAME `AttestedHistory` for a `Dfa`-gated turn; a pure LC folding the tree cannot tell the
predicate was ever checked.

## What is proved here (self-contained model of the off-AIR registry check)

We model the deployed Dfa-gated turn leg as a record carrying the published DSL PI-commitment column
`rc` (the route-commitment / `custom_proof_pi_commitment` of the predicate's public inputs) and the
effect intent the deployed AIR enforces. The deployed acceptance reads ONLY the intent; `rc` is read
by no constraint (the off-AIR `DslCircuitDfaVerifier` is the only enforcer). The off-AIR registry
check is modeled as the set `Verifying : ℤ → Prop` of route-commitments a GENUINE DFA transition
sub-proof exposes; the LC-witnessed (staged) condition is `rc ∈ Verifying`.

§A `deployed_admits_unwitnessed` — the explicit FORGED leg: a Dfa-gated turn whose deployed effect-vm
   accepts (`DeployedAccepts`) while its published route-commitment is exposed by NO verifying DSL
   sub-proof (`¬ DslWitnessed`). NON-VACUOUS: `deployed_admits_both` exhibits one witnessed AND one
   unwitnessed leg, BOTH deployed-accepted — so the deployed relation genuinely does not see the
   predicate (`rc` is free).

§B `deployed_does_not_force_witnessed` — there is NO uniform bridge `DeployedAccepts ⟹ DslWitnessed`:
   the predicate's light-client witnessing is carried ENTIRELY by the off-AIR registry (or, once
   repaired, the FOLD), NEVER by the deployed circuit. RE-EXEC-ONLY, established as a class.

§C `dslEngineBinding_or_collides` — the REPAIR, floor-free. The fix (this commit's
   `circuit-prove/src/dsl_leaf_adapter.rs`) re-proves the DSL/Dfa `CellProgram` as a recursion leaf
   exposing its PI-commitment in-circuit and `connect`s it to the deployed leg's published `rc` inside
   the tree the LC folds. Its binding (two verifying DSL sub-proofs with the same `rc` agree on their
   program VK) is NOT an irreducible axiom: it REDUCES to `Poseidon2SpongeCR` once the DSL engine's
   commitment FACTORS as the Poseidon2 sponge of its public inputs (the route-commitment chain). We
   instantiate `CustomCarrierAttack.vk_determined_or_encColl` for a DSL engine and prove a concrete DSL
   floor engine's `EngineBinding` resting on `Poseidon2SpongeCR` ALONE.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound} + the named floor
carrier `Poseidon2SpongeCR` AS A HYPOTHESIS (§C only). NO new axiom, NO `sorry`. NEW file; all imports
read-only.
-/
import Dregg2.Circuit.CustomCarrierAttack

namespace Dregg2.Circuit.DslBackingAttack

open Dregg2.Circuit.DescriptorIR2 (ProofEngine EngineBinding)
open Dregg2.Circuit.CustomCarrierAttack
  (EncColl floorEngine floorEngine_hvk refFloorEngine_binding vk_determined_or_encColl
   vk_determined_of_noEncColl)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The model: the deployed Dfa-gated leg vs. the off-AIR DSL predicate. -/

/-- A deployed Dfa-gated turn leg as the deployed effect-vm sees it: the published DSL PI-commitment
column `rc` (the route-commitment / `custom_proof_pi_commitment` of the predicate's public inputs) and
the effect INTENT the deployed AIR algebraically enforces. The deployed AIR reads `intentOk`; it reads
`rc` in NO constraint (the off-AIR `DslCircuitDfaVerifier` is the only thing that ever inspects it). -/
structure DeployedDfaLeg where
  /-- The published route-commitment / DSL PI-commitment column (`Dfa` caveat's exposed value). -/
  rc : ℤ
  /-- The effect intent the deployed effect-vm AIR enforces (everything BUT the DSL predicate). -/
  intentOk : Prop

/-- **The deployed acceptance relation.** A re-executing validator's effect-vm AIR admits the leg iff
its effect intent holds. The DSL predicate's published `rc` is UNCONSTRAINED here — exactly the gap:
`DslCircuitDfaVerifier` runs OFF-AIR, outside this relation. -/
def DeployedAccepts (leg : DeployedDfaLeg) : Prop := leg.intentOk

/-- **The off-AIR registry check, as a light-client-witnessable condition.** `Verifying c` says "a
GENUINE DFA transition sub-proof exposes route-commitment `c`" (the `CellProgram::verify_transition`
acceptance set). The Dfa predicate is honestly satisfied iff the published `rc` is such a value. A
PURE LC folding the deployed tree never checks this; only the off-AIR verifier (or the repaired fold)
does. -/
def DslWitnessed (Verifying : ℤ → Prop) (leg : DeployedDfaLeg) : Prop := Verifying leg.rc

/-! ## §A — the deployed leg admits a Dfa-gated turn whose predicate is unwitnessed. -/

/-- **The deployed relation is INDEPENDENT of the published route-commitment.** Two legs with the same
intent but ANY two route-commitments are both deployed-accepted: `rc` rides free. This is the formal
content of "a validator with vs without `DslCircuitDfaVerifier` produces the same `AttestedHistory`". -/
theorem deployed_independent_of_rc (intent : Prop) (h : intent) (rc rc' : ℤ) :
    DeployedAccepts ⟨rc, intent⟩ ∧ DeployedAccepts ⟨rc', intent⟩ :=
  ⟨h, h⟩

/-- **Non-vacuity of the independence: the deployed leg accepts BOTH a witnessed and an unwitnessed
route-commitment.** With `Verifying = (· = 123)`: the leg `rc = 123` is deployed-accepted AND
DSL-witnessed; the leg `rc = 999` is deployed-accepted AND NOT DSL-witnessed. The deployed relation
genuinely cannot tell them apart. -/
theorem deployed_admits_both :
    let Verifying : ℤ → Prop := (· = 123)
    DeployedAccepts ⟨123, True⟩ ∧ DslWitnessed Verifying ⟨123, True⟩ ∧
    DeployedAccepts ⟨999, True⟩ ∧ ¬ DslWitnessed Verifying ⟨999, True⟩ := by
  refine ⟨trivial, rfl, trivial, ?_⟩
  intro h; exact absurd (show (999 : ℤ) = 123 from h) (by decide)

/-- **§A keystone — `deployed_admits_unwitnessed`.** ∃ an off-AIR DFA-verification set `Verifying` and
a deployed Dfa-gated leg that the deployed effect-vm AIR ACCEPTS while its published route-commitment
is exposed by NO verifying DSL sub-proof. This is the explicit forged Dfa-gated turn: the deployed
circuit (hence a pure light client folding it) cannot detect that the DSL predicate fails — only the
re-executing validator's off-AIR `DslCircuitDfaVerifier` can. RE-EXEC-ONLY, exhibited. -/
theorem deployed_admits_unwitnessed :
    ∃ (Verifying : ℤ → Prop) (leg : DeployedDfaLeg),
      DeployedAccepts leg ∧ ¬ DslWitnessed Verifying leg :=
  ⟨(· = 123), ⟨999, True⟩, trivial, by intro h; exact absurd (show (999 : ℤ) = 123 from h) (by decide)⟩

/-! ## §B — the DSL predicate's witnessing is carried OFF-AIR (or by the fold), never by the deployed
circuit. -/

/-- **§B keystone — `deployed_does_not_force_witnessed`.** There is NO uniform implication
`DeployedAccepts ⟹ DslWitnessed`. Hence any light-client-unfoolability claim that consumes the
deployed Dfa leg (whose acceptance is what a folded recursion tree certifies) asserts strictly MORE
than the deployed circuit enforces: the DSL predicate binding is carried ENTIRELY by the off-AIR
registry, or — after the repair — by the FOLD (`prove_custom_binding_node_segmented` over the re-proved
DSL leaf), but NEVER by the deployed effect-vm. §A is the counterexample. -/
theorem deployed_does_not_force_witnessed :
    ¬ ∀ (Verifying : ℤ → Prop) (leg : DeployedDfaLeg),
        DeployedAccepts leg → DslWitnessed Verifying leg := by
  intro hbridge
  exact (deployed_admits_unwitnessed.choose_spec.choose_spec).2
    (hbridge _ _ (deployed_admits_unwitnessed.choose_spec.choose_spec).1)

/-! ## §C — the FOLD REPAIR is sound on the floor (the binding reduces to Poseidon2-CR).

The fix this commit builds (`circuit-prove/src/dsl_leaf_adapter.rs`) re-proves the DSL/Dfa
`CellProgram` as a recursion-foldable leaf exposing its PI-commitment IN-CIRCUIT (via the reused
`custom_leaf_adapter::prove_custom_leaf_with_commitment`) and `connect`s that commitment to the
deployed leg's published `rc` inside the tree the light client folds
(`prove_custom_binding_node_segmented`). For that bind to be SOUND the DSL proof engine must satisfy
`EngineBinding` (two verifying sub-proofs with equal `piCommit` agree on the program VK). We show this
is NOT a new axiom: it REDUCES to `Poseidon2SpongeCR` exactly as for the custom carrier, because the
DSL `custom_proof_pi_commitment` IS a Poseidon2 sponge of the predicate's public inputs (the
route-commitment chain), with the program VK among them. -/

/-- A concrete DSL/Dfa floor engine: its proofs are `(vk, route_statement)` pairs and its
PI-commitment IS the Poseidon2 sponge of `[vk, route_statement]` (the FRI factoring holds BY
CONSTRUCTION). This is exactly the `dregg-dfa-routing-v1` shape: the published `route_commitment` is a
Poseidon2 chain over the predicate's public inputs, the program `vk_hash` leading. -/
def dslFloorEngine (hash : List ℤ → ℤ) : ProofEngine := floorEngine hash

/-- **§C keystone — `dslEngineBinding_or_collides`.** The DSL/Dfa fold-leaf's commitment binding, at
the pair the extraction actually hands back: two verifying DSL sub-proofs exposing the same
route-commitment either attest the same predicate program, or their two absorbed public-input lists
are a NAMED collision of the deployed sponge. So once the deployed Dfa leg EMITS its route-commitment
at a fixed PI slot (the named big-bang descriptor-emit) and the fold connects it to the re-proved DSL
leaf, a forged route-commitment that no verifying DSL sub-proof backs is UNSAT in the tree the light
client folds.

⛑ CUT OVER 2026-07-27. `dslEngineBinding_of_floor` said this rested on `Poseidon2SpongeCR` ALONE;
that floor is PROVED FALSE at deployed BabyBear parameters
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so the statement said nothing about the
shipping DSL engine — and `EngineBinding (dslFloorEngine hash)` is itself false there (the diagonal
`n ↦ (n, 0)` is an infinite injection into a bounded codomain). WHAT WAS LOST: the unqualified
`EngineBinding (dslFloorEngine hash)` for an arbitrary deployed `hash`. What replaces it is this
dichotomy, which holds AT the deployed hash with no hypothesis, plus `dslFloorEngine_binding` — the
same conclusion, unconditionally, at a sponge whose CR is PROVED. -/
theorem dslEngineBinding_or_collides (hash : List ℤ → ℤ) (p q : ℤ × ℤ)
    (hpc : (dslFloorEngine hash).piCommit p = (dslFloorEngine hash).piCommit q) :
    (dslFloorEngine hash).vkOf p = (dslFloorEngine hash).vkOf q
      ∨ EncColl hash (fun r : ℤ × ℤ => [r.1, r.2]) p q :=
  vk_determined_or_encColl hash (floorEngine hash) (fun r => [r.1, r.2]) (fun _ _ => rfl)
    (floorEngine_hvk hash) p q rfl rfl hpc

/-- The DSL floor engine's binding, UNCONDITIONALLY, at a sponge that really is collision-free
(`Poseidon2Binding.Reference.refSponge`, CR PROVED). The non-vacuity witness that `EngineBinding` is
still DERIVABLE rather than carried. -/
theorem dslFloorEngine_binding :
    EngineBinding (dslFloorEngine Dregg2.Circuit.Poseidon2Binding.Reference.refSponge) :=
  refFloorEngine_binding

/-- A general restatement: ANY DSL engine whose verifying proofs expose a PI-commitment that factors as
the Poseidon2 sponge of an encoding of their public inputs (VK recoverable from the encoding) binds the
program VK at every pair — unless THAT pair is a witnessed sponge collision. This is the
route-commitment-chain factoring the `dregg-dfa-routing-v1` AIR's `SeedHash2to1`/`ChainedHash2to1`
constraints realize, and it carries no floor. -/
theorem dslEngineBinding_of_route_commitment_factoring
    (hash : List ℤ → ℤ) (E : ProofEngine) (enc : E.Proof → List ℤ)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    {p q : E.Proof} (hp : E.verify p = true) (hq : E.verify q = true)
    (hpc : E.piCommit p = E.piCommit q) (hno : ¬ EncColl hash enc p q) :
    E.vkOf p = E.vkOf q :=
  vk_determined_of_noEncColl hash E enc hfactor hvk hp hq hpc hno

/-! ## Axiom audit — every load-bearing arm. -/

#assert_axioms deployed_independent_of_rc
#assert_axioms deployed_admits_both
#assert_axioms deployed_admits_unwitnessed
#assert_axioms deployed_does_not_force_witnessed
#assert_axioms dslEngineBinding_or_collides
#assert_axioms dslFloorEngine_binding
#assert_axioms dslEngineBinding_of_route_commitment_factoring

end Dregg2.Circuit.DslBackingAttack
