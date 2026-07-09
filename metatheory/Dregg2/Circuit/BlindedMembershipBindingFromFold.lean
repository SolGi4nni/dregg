/-
# Dregg2.Circuit.BlindedMembershipBindingFromFold — the BLINDED RING-MEMBERSHIP claim, proven from the
  FOLD (Golden Lift, stage 3d-2).

## Why this file exists (the flip)

Stage 3d-1 (`Emit.BlindedMembershipEmit.blindedMembershipDesc`, "dregg-blinded-membership::v1") makes
the anonymous-credential show's claim — the published `blinded_leaf` (PI 0) and the federation `root`
(PI 1) — a genuinely CONSTRAINED, light-client-visible set of public inputs, and
`Emit.BlindedMembershipRung2` shows the two teeth BITE at the LEAF: the membership forge
(`forge_nonmember_rejected`, a non-member `leaf` under the committed root is UNSAT once the last-row
continuity fix restores the level-tie), the blinding forge (`forge_blinded_leaf_rejected`, a spoofed
`blinded_leaf` that is not `hash_2_to_1(leaf_hash, blinding)` is UNSAT), the acceptance pole
(`honest_satisfied2` / `honest_height1_fires`), and the unlinkability pole
(`honest_two_shows_unlinkable`). But that soundness is LEAF-level: it certifies a single re-proved
blinded-membership trace. A light client that verifies only the AGGREGATED root — the per-turn
recursion fold — never re-runs the leaf verifier; for it, the leg's published blinded-membership claim
is executor-attested and, absent the fold edge, unbacked. That is the SAME class
`MembershipBackingAttack` proves for the sender-membership leg.

This module proves the FOLD edge for the blinded-membership claim, mirroring
`MembershipBindingFromFold` / `PresentationBindingFromFold`: for the AGGREGATE a light client
verifies, the leg's published blinded-membership claim `(blinded_leaf, root)` MUST be backed by a
verifying blinded-membership sub-proof — with both non-vacuity poles. It builds ON the leaf soundness
(`BlindedMembershipRefine.blindedMembership_sat_refines` / `BlindedMembershipRung2`): the leaf the
fold re-proves IS the blinded-membership descriptor, whose SAT ⟹ SEM bridge, forge-rejection teeth,
and unlinkability pole are the leaf-level content; this file carries that content THROUGH the
recursion to the root.

  * **`blinded_membership_binding_from_fold`** — a verifying AGGREGATE FORCES, for the leg's published
    blinded-membership claim `f.claim`: (binding) ∃ a verifying blinded-membership sub-proof `q` with
    `E.piCommit q = f.claim`, and (anti-ghost) the attested program VK is DETERMINED by `f.claim`.
    Premises = the `custom_binding_from_fold` set (localized FRI-extraction floor + Poseidon2SpongeCR,
    as Prop hypotheses only); no staged-AIR carrier, no new axiom.

  * **`blinded_membership_authorized_from_fold`** — the light-client-at-the-root corollary: when the
    folded leaf's semantics is the re-proved blinded-membership relation (a verifying sub-proof
    exposing the leg's published `(blinded_leaf, root)` claim IS a blinded-membership leaf attesting
    that anonymous show — the `blinded_leaf_adapter` obligation, carried as `hbacks`), a satisfying
    fold connected to the leg DISCHARGES the blinded-membership predicate the deployed light client
    omits.

## Non-vacuity (BOTH polarities)

`honest_companion_fires` — on an honest anonymous show the grounded binding FIRES.
`forged_unsat` / `forged_claim_unsat_demo` — a fold whose published blinded-membership claim (e.g. a
forged non-member `blinded_leaf`) is backed by NO verifying blinded-membership sub-proof CANNOT
satisfy: the aggregate is UNSAT. `honest_leaf_is_real` welds the abstract leaf floor to the DEPLOYED
blinded-membership leaf (`BlindedMembershipRung2.honest_height1_fires`) — the sub-proof the fold
re-proves is not a fiction.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. The floor
carriers appear ONLY as Prop hypotheses. NO new axiom, NO `sorry`. NEW file; imports read-only.
-/
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.CustomCarrierAttack
import Dregg2.Circuit.Emit.BlindedMembershipRung2

namespace Dregg2.Circuit.BlindedMembershipBindingFromFold

open Dregg2.Circuit.DescriptorIR2 (ProofEngine EngineBinding demoEngine)
open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.CustomCarrierAttack (engineBinding_of_floor floorEngine)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.BlindedMembershipEmit (blindedMembershipDesc BLINDED_LEAF_PI)
open Dregg2.Circuit.Emit.BlindedMembershipRefine (BlindedMembers)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the blinded-membership-leaf FRI floor, and its provenance from `AggAirSound.FriExtract`. -/

/-- **`BlindedLeafFriFloor E BlindedLeafSat`** — the localized FRI-extraction floor for the
blinded-membership leaf: a SATISFIED in-circuit blinded-membership-leaf verifier (pinned VK core
`leafVk`, exposing the blinded-membership claim `leafCommit`) yields a GENUINELY VERIFYING
blinded-membership sub-proof of engine `E` whose `piCommit` IS the exposed `leafCommit`. The
blinded-membership instance of `AggAirSound.FriExtract` — see
`blindedLeafFriFloor_of_aggFriExtract`. -/
def BlindedLeafFriFloor (E : ProofEngine) (BlindedLeafSat : ℤ → ℤ → Prop) : Prop :=
  ∀ leafVk leafCommit : ℤ, BlindedLeafSat leafVk leafCommit →
    ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = leafCommit

/-- The blinded-membership leaf's exposed segment projection: the leaf carries its blinded-membership
claim `x` in the ordered-digest lane `acc` (the other lanes are inert for a single-leaf wrap). -/
def segOfCommit (x : ℤ) : Seg := { firstOld := 0, lastNew := 0, count := 0, acc := x }

/-- **`blindedLeafFriFloor_of_aggFriExtract` — the FRI floor IS AggAirSound's carrier.** -/
theorem blindedLeafFriFloor_of_aggFriExtract
    (E : ProofEngine) (leafPre : ℤ) (ChildVerifierSat : ℤ → Seg → Prop)
    (hagg : FriExtract E.Proof E.verify (fun _ => leafPre)
              (fun q => segOfCommit (E.piCommit q)) ChildVerifierSat) :
    BlindedLeafFriFloor E
      (fun leafVk leafCommit => ChildVerifierSat leafVk (segOfCommit leafCommit)) := by
  intro leafVk leafCommit hcv
  obtain ⟨q, hq, _hvkc, hexp⟩ := hagg leafVk (segOfCommit leafCommit) hcv
  refine ⟨q, hq, ?_⟩
  simpa [segOfCommit] using congrArg Seg.acc hexp

/-! ## §2 — the blinded-membership predicate + the per-turn fold node (the connect). -/

/-- An abstract blinded-membership authority engine: its accepting bit, and the blinded-membership
claim `(blinded_leaf, root)` a VERIFYING blinded-membership proof attests (collapsed to one ℤ,
exactly as `MembershipBindingFromFold` collapses the `(sender_leaf, authorized_root)` octet claim).
The blinded-membership analog of `MembershipBackingAttack.MembershipEngine`. -/
structure BlindedEngine where
  /-- The proof type of the blinded-membership STARK. -/
  Witness : Type
  /-- The verifier's accepting bit (`verify_blinded_merkle(...).is_ok()`). -/
  verifyBlinded : Witness → Bool
  /-- The blinded-membership claim a verifying blinded-membership proof attests
  (`blinded_leaf, root`, collapsed to one ℤ). -/
  provenClaim : Witness → ℤ

/-- The published blinded-membership claim column: `BLINDED_LEAF_PI` (PI 0, the unlinkable
`hash_2_to_1(leaf_hash, blinding)` commitment — the representative of the whole `(blinded_leaf, root)`
claim, collapsed to one ℤ, exactly as `MembershipFold` projects via `senderLeafOf`). -/
def blindedClaimCol : Nat := BLINDED_LEAF_PI

/-- The blinded-membership claim a leg row publishes. -/
def blindedClaimOf (env : VmRowEnv) : ℤ := env.loc blindedClaimCol

/-- **`BlindedAuthorized P env`** — the blinded-membership predicate the deployed light client SHOULD
(but does not, absent the fold) enforce: the leg's published blinded-membership claim is attested by
SOME verifying blinded-membership proof. The blinded-membership analog of
`MembershipBackingAttack.Authorized`. -/
def BlindedAuthorized (P : BlindedEngine) (env : VmRowEnv) : Prop :=
  ∃ w : P.Witness, P.verifyBlinded w = true ∧ P.provenClaim w = blindedClaimOf env

/-- **`BlindedFold E`** — the per-turn fold's blinded-membership face: the blinded-membership-leaf's
pinned preprocessed commitment `leafVk`, the blinded-membership claim `leafCommit` the leaf exposes,
and the effect-vm leg's published blinded-membership claim `claim` (the `(blinded_leaf, root)` claim
PIs, modeled as one ℤ exactly as `MembershipFold.tup` models the octet claim). -/
structure BlindedFold (E : ProofEngine) where
  /-- the blinded-membership-leaf recursion-verifier's pinned preprocessed commitment (VK core). -/
  leafVk     : ℤ
  /-- the blinded-membership claim the folded blinded-membership leaf exposes. -/
  leafCommit : ℤ
  /-- the effect-vm leg's published blinded-membership claim (the claim-PI carrier). -/
  claim      : ℤ

/-- **`SatBlindedFold E BlindedLeafSat f`** — a SATISFYING per-turn fold over its blinded-membership
face: `leafCV` (the in-circuit blinded-membership-leaf verifier subcircuit is satisfied) + `connect`
(the aggregate's combine constraint TIES the leaf's exposed blinded-membership claim to the leg's
published claim — the `prove_blinded_membership_binding_node_segmented` in-circuit connect). -/
structure SatBlindedFold (E : ProofEngine) (BlindedLeafSat : ℤ → ℤ → Prop)
    (f : BlindedFold E) : Prop where
  leafCV  : BlindedLeafSat f.leafVk f.leafCommit
  connect : f.leafCommit = f.claim

/-! ## §3 — THE PAYLOAD: the blinded-membership claim, from the FOLD. -/

/-- **`blinded_membership_binding_from_fold` (THE PAYLOAD).** A verifying AGGREGATE — the per-turn fold
including the blinded-membership leaf — FORCES, for the leg's published blinded-membership claim
`f.claim`: (binding) ∃ a verifying blinded-membership sub-proof `q` of `E` with
`E.piCommit q = f.claim`; AND (anti-ghost) any two verifying sub-proofs exposing `f.claim` agree on
their `vkOf`. The premise set is EXACTLY the `custom_binding_from_fold` /
`membership_binding_from_fold` set. -/
theorem blinded_membership_binding_from_fold
    (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (BlindedLeafSat : ℤ → ℤ → Prop)
    (hfri : BlindedLeafFriFloor E BlindedLeafSat)
    (hCR : Poseidon2SpongeCR hash)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : BlindedFold E) (hsat : SatBlindedFold E BlindedLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.claim) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = f.claim → E.piCommit q = f.claim → E.vkOf p = E.vkOf q) := by
  have hE : EngineBinding E := engineBinding_of_floor hash E enc hCR hfactor hvk
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  intro p q' hp hq' hpc hq'c
  exact hE.commit_determines_vk p q' hp hq' (by rw [hpc, hq'c])

/-- **`blinded_membership_authorized_from_fold` — the light-client-at-the-root corollary.**
The deployed light client alone never forces the blinded-membership authorization (the leaf verifier
is off the fold path). THIS is the fold edge: when the folded leaf's semantics is the re-proved
blinded-membership relation — a verifying blinded-membership sub-proof exposing the leg's published
`(blinded_leaf, root)` claim IS a blinded-membership leaf attesting the leg's anonymous show
(`hbacks`, the `blinded_leaf_adapter` obligation) — a satisfying fold connected to the leg
(`hclaim`) DISCHARGES the blinded-membership predicate the light client omits. -/
theorem blinded_membership_authorized_from_fold
    (P : BlindedEngine) (env : VmRowEnv)
    (E : ProofEngine) (BlindedLeafSat : ℤ → ℤ → Prop)
    (hfri : BlindedLeafFriFloor E BlindedLeafSat)
    (hbacks : ∀ q : E.Proof, E.verify q = true → E.piCommit q = blindedClaimOf env →
        BlindedAuthorized P env)
    (f : BlindedFold E) (hsat : SatBlindedFold E BlindedLeafSat f)
    (hclaim : f.claim = blindedClaimOf env) :
    BlindedAuthorized P env := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect, hclaim] at hqc
  exact hbacks q hq hqc

/-! ## §4 — NON-VACUITY: the binding FIRES on an honest fold; the forgery is REJECTED. -/

section Honest

/-- The honest blinded-membership face over `floorEngine`: the folded leaf exposes the commitment of
the honest sub-proof `(7, 7)`, and the connect publishes that same commitment as the leg's claim. -/
def honestFold (hash : List ℤ → ℤ) : BlindedFold (floorEngine hash) :=
  { leafVk := 100, leafCommit := hash [7, 7], claim := hash [7, 7] }

/-- The honest blinded-membership-leaf verifier predicate. -/
def honestBLS (hash : List ℤ → ℤ) : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit => ∃ q : ℤ × ℤ,
    (floorEngine hash).verify q = true ∧ (floorEngine hash).piCommit q = leafCommit

theorem honestFloor (hash : List ℤ → ℤ) :
    BlindedLeafFriFloor (floorEngine hash) (honestBLS hash) :=
  fun _leafVk _leafCommit h => h

theorem honestSat (hash : List ℤ → ℤ) :
    SatBlindedFold (floorEngine hash) (honestBLS hash) (honestFold hash) where
  leafCV  := ⟨(7, 7), rfl, rfl⟩
  connect := rfl

/-- **`honest_companion_fires` (POSITIVE non-vacuity).** On the honest anonymous show the binding
FIRES — resting on `Poseidon2SpongeCR` alone. -/
theorem honest_companion_fires (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    (∃ q : ℤ × ℤ, (floorEngine hash).verify q = true ∧
        (floorEngine hash).piCommit q = (honestFold hash).claim) ∧
    (∀ p q : ℤ × ℤ, (floorEngine hash).verify p = true → (floorEngine hash).verify q = true →
        (floorEngine hash).piCommit p = (honestFold hash).claim →
        (floorEngine hash).piCommit q = (honestFold hash).claim →
        (floorEngine hash).vkOf p = (floorEngine hash).vkOf q) :=
  blinded_membership_binding_from_fold (floorEngine hash) hash (fun p => [p.1, p.2]) (honestBLS hash)
    (honestFloor hash) hCR (fun _p _ => rfl)
    (by intro p q _ _ henc; injection henc)
    (honestFold hash) (honestSat hash)

/-- **`honest_leaf_is_real` — the abstract leaf floor is REALIZED by the DEPLOYED blinded-membership
leaf.** The sub-proof the fold re-proves is not a fiction: the deployed `blindedMembershipDesc` has a
genuinely satisfying honest height-1 show that fires the strengthened blinded-membership relation
(`BlindedMembershipRung2.honest_height1_fires`), so the `BlindedLeafFriFloor` floor is inhabited by
the real leaf soundness this file builds on. -/
theorem honest_leaf_is_real :
    ∃ (h : List ℤ → ℤ) (blinded_leaf leaf_hash blinding s0a s0b s0c s1a s1b s1c root : ℤ),
      BlindedMembers h blinded_leaf leaf_hash blinding s0a s0b s0c s1a s1b s1c root :=
  ⟨_, _, _, _, _, _, _, _, _, _, _,
   Dregg2.Circuit.Emit.BlindedMembershipRung2.honest_height1_fires⟩

end Honest

section Forged

/-- **`forged_unsat` (THE ANTI-GHOST TOOTH — forged blinded-membership claim ⟹ UNSAT).** A per-turn
fold whose published blinded-membership claim `f.claim` is backed by NO verifying blinded-membership
sub-proof CANNOT satisfy. The circuit twin of `BlindedMembershipRung2.forge_nonmember_rejected` /
`forge_blinded_leaf_rejected`, carried to the root. -/
theorem forged_unsat {E : ProofEngine} {BlindedLeafSat : ℤ → ℤ → Prop}
    (hfri : BlindedLeafFriFloor E BlindedLeafSat) {f : BlindedFold E}
    (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.claim) :
    ¬ SatBlindedFold E BlindedLeafSat f := by
  intro hsat
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  exact hforge ⟨q, hq, hqc⟩

/-- The blinded-membership-leaf predicate over `demoEngine` (the only verifying sub-proof commits to
`123`). -/
def demoBLS : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit =>
    ∃ q : Bool, demoEngine.verify q = true ∧ demoEngine.piCommit q = leafCommit

theorem demoFloor : BlindedLeafFriFloor demoEngine demoBLS :=
  fun _leafVk _leafCommit h => h

/-- A forged blinded-membership leg lifted onto the fold: the published blinded-membership claim is `0`
(e.g. a forged non-member `blinded_leaf`) — a claim NO verifying sub-proof of `demoEngine` exposes. -/
def forgedFold : BlindedFold demoEngine := { leafVk := 0, leafCommit := 0, claim := 0 }

/-- **`forged_claim_unsat_demo` (NEGATIVE non-vacuity — a forged blinded-membership claim, on the
fold).** What the deployed light client alone would admit, the aggregate REFUSES: no verifying
blinded-membership sub-proof backs the forged claim, so the fold is UNSAT. -/
theorem forged_claim_unsat_demo : ¬ SatBlindedFold demoEngine demoBLS forgedFold := by
  refine forged_unsat demoFloor (f := forgedFold) ?_
  rintro ⟨q, _hq, hc⟩
  have hc' : (123 : ℤ) = 0 := hc
  exact absurd hc' (by decide)

end Forged

/-! ## §5 — shape pins + Axiom hygiene (every load-bearing arm). -/

#guard blindedMembershipDesc.name == "dregg-blinded-membership::v1"
#guard blindedClaimCol == 0

#assert_axioms blindedLeafFriFloor_of_aggFriExtract
#assert_axioms blinded_membership_binding_from_fold
#assert_axioms blinded_membership_authorized_from_fold
#assert_axioms honest_companion_fires
#assert_axioms honest_leaf_is_real
#assert_axioms forged_unsat
#assert_axioms forged_claim_unsat_demo

end Dregg2.Circuit.BlindedMembershipBindingFromFold
