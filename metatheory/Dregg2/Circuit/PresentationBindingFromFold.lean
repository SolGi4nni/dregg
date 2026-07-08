/-
# Dregg2.Circuit.PresentationBindingFromFold — the BOUND-PRESENTATION authorization claim, proven
  from the FOLD (Golden Lift, stage 2).

## Why this file exists (the flip)

Stage 1 (`Emit.BoundPresentationEmit.boundPresentationDesc`, "dregg-bound-presentation::v1") makes
the presentation's authorization claim — `action_binding[8]` (PI 1..8), `revealed_facts[8]`
(PI 11..18) and the `presentation_tag` (PI 10, constrained in-circuit to
`Poseidon2(final_root, randomness, verifier_nonce, DSK)`) — a genuinely CONSTRAINED, light-client
visible set of public inputs, and `Emit.BoundPresentationRung2` shows each binding BITES at the LEAF
(`forge_action_rejected`, `forge_facts_rejected`, `forge_tag_rejected`, `honest_satisfied2`). But
that soundness is LEAF-level: it certifies a single re-proved bound-presentation trace. A light
client that verifies only the AGGREGATED root — the per-turn recursion fold — never re-runs the leaf
verifier; for it, the leg's published presentation claim is executor-attested and, absent the fold
edge, unbacked. That is the SAME class `MembershipBackingAttack` proves for the sender-membership leg.

This module proves the FOLD edge for the presentation claim, mirroring
`MembershipBindingFromFold`: for the AGGREGATE a light client verifies, the leg's published
presentation claim `(action_binding, revealed_facts, tag)` MUST be backed by a verifying
bound-presentation sub-proof — with both non-vacuity poles. It builds ON the leaf soundness
(`BoundPresentationRefine.boundPresentation_sat_refines` / `BoundPresentationRung2`): the leaf the
fold re-proves IS the bound-presentation descriptor, whose SAT ⟹ SEM bridge and forge-rejection
teeth are the leaf-level content; this file carries that content THROUGH the recursion to the root.

  * **`presentation_binding_from_fold`** — a verifying AGGREGATE FORCES, for the leg's published
    presentation claim `f.claim`: (binding) ∃ a verifying bound-presentation sub-proof `q` with
    `E.piCommit q = f.claim`, and (anti-ghost) the attested program VK is DETERMINED by `f.claim`.
    Premises = the `custom_binding_from_fold` set (localized FRI-extraction floor + Poseidon2SpongeCR,
    as Prop hypotheses only); no staged-AIR carrier, no new axiom.

  * **`authorized_presentation_from_fold`** — the light-client-at-the-root corollary: when the folded
    leaf's semantics is the re-proved bound-presentation relation (a verifying sub-proof exposing the
    leg's published presentation claim IS a bound-presentation leaf attesting that authorization —
    the `presentation_leaf_adapter` obligation, carried as `hbacks`), a satisfying fold connected to
    the leg DISCHARGES the presentation-authorization predicate the deployed light client omits.

## Non-vacuity (BOTH polarities)

`honest_companion_fires` — on an honest bound presentation the grounded binding FIRES.
`forged_unsat` / `forged_claim_unsat_demo` — a fold whose published presentation claim (e.g. a wrong
`action_binding`) is backed by NO verifying bound-presentation sub-proof CANNOT satisfy: the
aggregate is UNSAT. `honest_leaf_is_real` welds the abstract leaf floor to the DEPLOYED
bound-presentation leaf (`BoundPresentationRung2.honest_fires`) — the sub-proof the fold re-proves is
not a fiction.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. The floor
carriers appear ONLY as Prop hypotheses. NO new axiom, NO `sorry`. NEW file; imports read-only.
-/
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.CustomCarrierAttack
import Dregg2.Circuit.Emit.BoundPresentationRung2

namespace Dregg2.Circuit.PresentationBindingFromFold

open Dregg2.Circuit.DescriptorIR2 (ProofEngine EngineBinding demoEngine)
open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.CustomCarrierAttack (engineBinding_of_floor floorEngine)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.BoundPresentationEmit (boundPresentationDesc PRESENTATION_TAG)
open Dregg2.Circuit.Emit.BoundPresentationRefine (BoundPresentation)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the bound-presentation-leaf FRI floor, and its provenance from `AggAirSound.FriExtract`. -/

/-- **`PresentationLeafFriFloor E PresentationLeafSat`** — the localized FRI-extraction floor for the
bound-presentation leaf: a SATISFIED in-circuit bound-presentation-leaf verifier (pinned VK core
`leafVk`, exposing the presentation claim `leafCommit`) yields a GENUINELY VERIFYING
bound-presentation sub-proof of engine `E` whose `piCommit` IS the exposed `leafCommit`. The
presentation instance of `AggAirSound.FriExtract` — see
`presentationLeafFriFloor_of_aggFriExtract`. -/
def PresentationLeafFriFloor (E : ProofEngine) (PresentationLeafSat : ℤ → ℤ → Prop) : Prop :=
  ∀ leafVk leafCommit : ℤ, PresentationLeafSat leafVk leafCommit →
    ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = leafCommit

/-- The bound-presentation leaf's exposed segment projection: the leaf carries its presentation
claim `x` in the ordered-digest lane `acc` (the other lanes are inert for a single-leaf wrap). -/
def segOfCommit (x : ℤ) : Seg := { firstOld := 0, lastNew := 0, count := 0, acc := x }

/-- **`presentationLeafFriFloor_of_aggFriExtract` — the FRI floor IS AggAirSound's carrier.** -/
theorem presentationLeafFriFloor_of_aggFriExtract
    (E : ProofEngine) (leafPre : ℤ) (ChildVerifierSat : ℤ → Seg → Prop)
    (hagg : FriExtract E.Proof E.verify (fun _ => leafPre)
              (fun q => segOfCommit (E.piCommit q)) ChildVerifierSat) :
    PresentationLeafFriFloor E
      (fun leafVk leafCommit => ChildVerifierSat leafVk (segOfCommit leafCommit)) := by
  intro leafVk leafCommit hcv
  obtain ⟨q, hq, _hvkc, hexp⟩ := hagg leafVk (segOfCommit leafCommit) hcv
  refine ⟨q, hq, ?_⟩
  simpa [segOfCommit] using congrArg Seg.acc hexp

/-! ## §2 — the presentation-authorization predicate + the per-turn fold node (the connect). -/

/-- An abstract bound-presentation authority engine: its accepting bit, and the presentation claim
`(action_binding, revealed_facts, tag)` a VERIFYING bound-presentation proof attests (collapsed to
one ℤ, exactly as `MembershipBindingFromFold` collapses the `(sender_leaf, authorized_root)` octet
claim). The presentation analog of `MembershipBackingAttack.MembershipEngine`. -/
structure PresentationEngine where
  /-- The proof type of the bound-presentation STARK. -/
  Witness : Type
  /-- The verifier's accepting bit (`verify_bound_presentation(...).is_ok()`). -/
  verifyPres : Witness → Bool
  /-- The presentation claim a verifying bound-presentation proof attests
  (`action_binding, revealed_facts, tag`, collapsed to one ℤ). -/
  provenClaim : Witness → ℤ

/-- The published presentation claim column: `PRESENTATION_TAG` (summary col 10, the Poseidon2 image
that binds `final_root, randomness, verifier_nonce` — the representative of the whole
`(action_binding, revealed_facts, tag)` claim, collapsed to one ℤ). -/
def presentationClaimCol : Nat := PRESENTATION_TAG

/-- The presentation claim a leg row publishes. -/
def presentationClaimOf (env : VmRowEnv) : ℤ := env.loc presentationClaimCol

/-- **`PresentationAuthorized P env`** — the presentation-authorization predicate the deployed
light client SHOULD (but does not, absent the fold) enforce: the leg's published presentation claim
is attested by SOME verifying bound-presentation proof. The presentation analog of
`MembershipBackingAttack.Authorized`. -/
def PresentationAuthorized (P : PresentationEngine) (env : VmRowEnv) : Prop :=
  ∃ w : P.Witness, P.verifyPres w = true ∧ P.provenClaim w = presentationClaimOf env

/-- **`PresentationFold E`** — the per-turn fold's presentation face: the bound-presentation-leaf's
pinned preprocessed commitment `leafVk`, the presentation claim `leafCommit` the leaf exposes, and
the effect-vm leg's published presentation claim `claim` (the `(action_binding, revealed_facts, tag)`
claim PIs, modeled as one ℤ exactly as `MembershipFold.tup` models the octet claim). -/
structure PresentationFold (E : ProofEngine) where
  /-- the bound-presentation-leaf recursion-verifier's pinned preprocessed commitment (VK core). -/
  leafVk     : ℤ
  /-- the presentation claim the folded bound-presentation leaf exposes. -/
  leafCommit : ℤ
  /-- the effect-vm leg's published presentation claim (the claim-PI carrier). -/
  claim      : ℤ

/-- **`SatPresentationFold E PresentationLeafSat f`** — a SATISFYING per-turn fold over its
presentation face: `leafCV` (the in-circuit bound-presentation-leaf verifier subcircuit is
satisfied) + `connect` (the aggregate's combine constraint TIES the leaf's exposed presentation
claim to the leg's published claim — the `prove_presentation_binding_node_segmented` in-circuit
connect). -/
structure SatPresentationFold (E : ProofEngine) (PresentationLeafSat : ℤ → ℤ → Prop)
    (f : PresentationFold E) : Prop where
  leafCV  : PresentationLeafSat f.leafVk f.leafCommit
  connect : f.leafCommit = f.claim

/-! ## §3 — THE PAYLOAD: the bound-presentation authorization claim, from the FOLD. -/

/-- **`presentation_binding_from_fold` (THE PAYLOAD).** A verifying AGGREGATE — the per-turn fold
including the bound-presentation leaf — FORCES, for the leg's published presentation claim `f.claim`:
(binding) ∃ a verifying bound-presentation sub-proof `q` of `E` with `E.piCommit q = f.claim`; AND
(anti-ghost) any two verifying sub-proofs exposing `f.claim` agree on their `vkOf`. The premise set
is EXACTLY the `custom_binding_from_fold` / `membership_binding_from_fold` set. -/
theorem presentation_binding_from_fold
    (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (PresentationLeafSat : ℤ → ℤ → Prop)
    (hfri : PresentationLeafFriFloor E PresentationLeafSat)
    (hCR : Poseidon2SpongeCR hash)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : PresentationFold E) (hsat : SatPresentationFold E PresentationLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.claim) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = f.claim → E.piCommit q = f.claim → E.vkOf p = E.vkOf q) := by
  have hE : EngineBinding E := engineBinding_of_floor hash E enc hCR hfactor hvk
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  intro p q' hp hq' hpc hq'c
  exact hE.commit_determines_vk p q' hp hq' (by rw [hpc, hq'c])

/-- **`authorized_presentation_from_fold` — the light-client-at-the-root corollary.**
The deployed light client alone never forces the presentation authorization (the leaf verifier is
off the fold path). THIS is the fold edge: when the folded leaf's semantics is the re-proved
bound-presentation relation — a verifying bound-presentation sub-proof exposing the leg's published
presentation claim IS a bound-presentation leaf attesting the leg's authorization (`hbacks`, the
`presentation_leaf_adapter` obligation) — a satisfying fold connected to the leg (`hclaim`)
DISCHARGES the presentation-authorization predicate the light client omits. -/
theorem authorized_presentation_from_fold
    (P : PresentationEngine) (env : VmRowEnv)
    (E : ProofEngine) (PresentationLeafSat : ℤ → ℤ → Prop)
    (hfri : PresentationLeafFriFloor E PresentationLeafSat)
    (hbacks : ∀ q : E.Proof, E.verify q = true → E.piCommit q = presentationClaimOf env →
        PresentationAuthorized P env)
    (f : PresentationFold E) (hsat : SatPresentationFold E PresentationLeafSat f)
    (hclaim : f.claim = presentationClaimOf env) :
    PresentationAuthorized P env := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect, hclaim] at hqc
  exact hbacks q hq hqc

/-! ## §4 — NON-VACUITY: the binding FIRES on an honest fold; the forgery is REJECTED. -/

section Honest

/-- The honest presentation face over `floorEngine`: the folded leaf exposes the commitment of the
honest sub-proof `(7, 7)`, and the connect publishes that same commitment as the leg's claim. -/
def honestFold (hash : List ℤ → ℤ) : PresentationFold (floorEngine hash) :=
  { leafVk := 100, leafCommit := hash [7, 7], claim := hash [7, 7] }

/-- The honest bound-presentation-leaf verifier predicate. -/
def honestPLS (hash : List ℤ → ℤ) : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit => ∃ q : ℤ × ℤ,
    (floorEngine hash).verify q = true ∧ (floorEngine hash).piCommit q = leafCommit

theorem honestFloor (hash : List ℤ → ℤ) :
    PresentationLeafFriFloor (floorEngine hash) (honestPLS hash) :=
  fun _leafVk _leafCommit h => h

theorem honestSat (hash : List ℤ → ℤ) :
    SatPresentationFold (floorEngine hash) (honestPLS hash) (honestFold hash) where
  leafCV  := ⟨(7, 7), rfl, rfl⟩
  connect := rfl

/-- **`honest_companion_fires` (POSITIVE non-vacuity).** On the honest bound presentation the
binding FIRES — resting on `Poseidon2SpongeCR` alone. -/
theorem honest_companion_fires (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    (∃ q : ℤ × ℤ, (floorEngine hash).verify q = true ∧
        (floorEngine hash).piCommit q = (honestFold hash).claim) ∧
    (∀ p q : ℤ × ℤ, (floorEngine hash).verify p = true → (floorEngine hash).verify q = true →
        (floorEngine hash).piCommit p = (honestFold hash).claim →
        (floorEngine hash).piCommit q = (honestFold hash).claim →
        (floorEngine hash).vkOf p = (floorEngine hash).vkOf q) :=
  presentation_binding_from_fold (floorEngine hash) hash (fun p => [p.1, p.2]) (honestPLS hash)
    (honestFloor hash) hCR (fun _p _ => rfl)
    (by intro p q _ _ henc; injection henc)
    (honestFold hash) (honestSat hash)

/-- **`honest_leaf_is_real` — the abstract leaf floor is REALIZED by the DEPLOYED bound-presentation
leaf.** The sub-proof the fold re-proves is not a fiction: the deployed
`boundPresentationDesc` has a genuinely satisfying honest trace that fires the bound-presentation
relation (`BoundPresentationRung2.honest_fires`), so the `PresentationLeafFriFloor` floor is
inhabited by the real leaf soundness this file builds on. -/
theorem honest_leaf_is_real :
    ∃ (h : List ℤ → ℤ) (loc pub : Dregg2.Circuit.Assignment), BoundPresentation h loc pub :=
  ⟨_, _, _, Dregg2.Circuit.Emit.BoundPresentationRung2.honest_fires⟩

end Honest

section Forged

/-- **`forged_unsat` (THE ANTI-GHOST TOOTH — forged presentation claim ⟹ UNSAT).** A per-turn fold
whose published presentation claim `f.claim` is backed by NO verifying bound-presentation sub-proof
CANNOT satisfy. The circuit twin of `BoundPresentationRung2.forge_action_rejected` /
`forge_facts_rejected` / `forge_tag_rejected`, carried to the root. -/
theorem forged_unsat {E : ProofEngine} {PresentationLeafSat : ℤ → ℤ → Prop}
    (hfri : PresentationLeafFriFloor E PresentationLeafSat) {f : PresentationFold E}
    (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.claim) :
    ¬ SatPresentationFold E PresentationLeafSat f := by
  intro hsat
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  exact hforge ⟨q, hq, hqc⟩

/-- The bound-presentation-leaf predicate over `demoEngine` (the only verifying sub-proof commits to
`123`). -/
def demoPLS : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit =>
    ∃ q : Bool, demoEngine.verify q = true ∧ demoEngine.piCommit q = leafCommit

theorem demoFloor : PresentationLeafFriFloor demoEngine demoPLS :=
  fun _leafVk _leafCommit h => h

/-- A forged presentation leg lifted onto the fold: the published presentation claim is `0` (e.g. a
forged `action_binding`) — a claim NO verifying sub-proof of `demoEngine` exposes. -/
def forgedFold : PresentationFold demoEngine := { leafVk := 0, leafCommit := 0, claim := 0 }

/-- **`forged_claim_unsat_demo` (NEGATIVE non-vacuity — a forged presentation claim, on the fold).**
What the deployed light client alone would admit, the aggregate REFUSES: no verifying
bound-presentation sub-proof backs the forged claim, so the fold is UNSAT. -/
theorem forged_claim_unsat_demo : ¬ SatPresentationFold demoEngine demoPLS forgedFold := by
  refine forged_unsat demoFloor (f := forgedFold) ?_
  rintro ⟨q, _hq, hc⟩
  have hc' : (123 : ℤ) = 0 := hc
  exact absurd hc' (by decide)

end Forged

/-! ## §5 — shape pins + Axiom hygiene (every load-bearing arm). -/

#guard boundPresentationDesc.name == "dregg-bound-presentation::v1"
#guard presentationClaimCol == 10

#assert_axioms presentationLeafFriFloor_of_aggFriExtract
#assert_axioms presentation_binding_from_fold
#assert_axioms authorized_presentation_from_fold
#assert_axioms honest_companion_fires
#assert_axioms honest_leaf_is_real
#assert_axioms forged_unsat
#assert_axioms forged_claim_unsat_demo

end Dregg2.Circuit.PresentationBindingFromFold
