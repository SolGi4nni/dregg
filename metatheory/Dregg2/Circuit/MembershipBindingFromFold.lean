/-
# Dregg2.Circuit.MembershipBindingFromFold — the DEPLOYED membership binding, proven from the FOLD.

## Why this file exists (the flip)

`MembershipBackingAttack` proved the deployed `SenderAuthorized` leg VACUOUS as a pure light
client sees it: the deployed AIR gates only the transfer transition, never the sender-membership
Merkle path (`deployed_admits_unbacked_membership`, `deployed_admits_injected_root`,
`deployed_intent_does_not_force_membership`). The repair it NAMED — the backing must come from the
per-turn FOLD over a re-proved MEMBERSHIP leaf connected to the published
`(sender_leaf, authorized_root)` teeth — is now DEPLOYED:

  * THE BIG-BANG REGEN pinned the exposure: the committed wide registry row is
    `CarrierComposed.transferV3MembershipWide` — the two teeth columns (past the wide carriers,
    1771..1772) row-0-pinned at claim PIs 50..51 (`MEMBERSHIP_CLAIM_PI_LO` —
    `transferV3MembershipWide_publishes_teeth`, `#assert_axioms`-clean). The apex rides the narrow
    member at `Rfix 0` (`Rfix_transfer`).
  * The FOLD arm is live (`ivc_turn_chain::prove_chain_core_rotated`, Membership arm): the
    per-turn aggregate folds the re-proven membership leaf
    (`membership_leaf_adapter::prove_membership_leaf_with_claim` — the REAL `dsl::membership`
    Merkle STARK, sender-compress executor-ALIGNED since `687601953`), RE-VERIFIES it via the
    recursion, and CONNECTS the leaf's exposed tuple to the leg's published claim PIs
    (`prove_membership_binding_node_segmented`). The deployed-path tooth
    (`membership_binding_deployed_tooth.rs`) exercises BOTH poles on the NATIVE committed row.

## ⚑ HONEST SCOPE (the fail-open law — what this flip does and does NOT claim)

The deployed-AIR leg is the PI EXPOSURE only (`CarrierComposed` §5): the in-AIR sender-compress /
fields-root read welds stay the named `MembershipAuthRootEdge` seams, so
`MembershipBackingAttack` §A/§A′ STAND as deployed-AIR facts. What THIS module proves is the FOLD
edge — for the AGGREGATE a light client verifies, a published tuple claim must be backed by a
verifying membership sub-proof (the exact predicate the attack file staged), with both
non-vacuity poles. The mirror of `FactoryBindingFromFold` over the universal sub-proof-folding
primitive.

  * **`membership_binding_from_fold`** — a verifying AGGREGATE FORCES, for the leg's published
    tuple claim `f.tup`: (binding) ∃ a verifying membership sub-proof `q` with
    `E.piCommit q = f.tup`, and (anti-ghost) the attested path is DETERMINED by `f.tup`.
    Premises = the `custom_binding_from_fold` set; no staged-AIR carrier.

  * **`authorized_from_fold`** — the GROUNDING onto `MembershipBackingAttack.Authorized`: when
    the folded leaf's semantics is the re-proved `verify_membership_dsl` (a verifying membership
    sub-proof exposing the leg's published tuple IS a verifying Merkle path attesting it — the
    `membership_leaf_adapter` obligation, carried as `hbacks`), a satisfying fold DISCHARGES the
    exact membership predicate the attack file showed the deployed AIR omits.

## Non-vacuity (BOTH polarities, mirroring the Rust tooth)

`honest_companion_fires` — on an honest sender-authorized transfer the grounded binding FIRES.
`forged_unsat` / `forged_tuple_unsat_demo` — a fold whose published tuple claim is the
`MembershipBackingAttack` §A forgery (`sender_leaf = 0`, backed by NO verifying path) CANNOT
satisfy: the aggregate is UNSAT — the circuit twin of
`deployed_membership_turn_forged_tuple_rejected`.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. The floor
carriers appear ONLY as Prop hypotheses. NO new axiom, NO `sorry`. NEW file; imports read-only.
-/
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.CustomCarrierAttack
import Dregg2.Circuit.MembershipBackingAttack

namespace Dregg2.Circuit.MembershipBindingFromFold

open Dregg2.Circuit.DescriptorIR2 (ProofEngine EngineBinding demoEngine)
open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.CustomCarrierAttack (engineBinding_of_floor floorEngine)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.MembershipBackingAttack (MembershipEngine Authorized senderLeafOf)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the membership-leaf FRI floor, and its provenance from `AggAirSound.FriExtract`. -/

/-- **`MembershipLeafFriFloor E MembershipLeafSat`** — the localized FRI-extraction floor for the
membership leaf: a SATISFIED in-circuit membership-leaf verifier (pinned VK core `leafVk`,
exposing tuple claim `leafCommit`) yields a GENUINELY VERIFYING membership sub-proof of engine `E`
whose `piCommit` IS the exposed `leafCommit`. The membership instance of `AggAirSound.FriExtract`
— see `membershipLeafFriFloor_of_aggFriExtract`. -/
def MembershipLeafFriFloor (E : ProofEngine) (MembershipLeafSat : ℤ → ℤ → Prop) : Prop :=
  ∀ leafVk leafCommit : ℤ, MembershipLeafSat leafVk leafCommit →
    ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = leafCommit

/-- The membership leaf's exposed segment projection: the leaf carries its tuple claim `x` in the
ordered-digest lane `acc` (the other lanes are inert for a single-leaf wrap). -/
def segOfCommit (x : ℤ) : Seg := { firstOld := 0, lastNew := 0, count := 0, acc := x }

/-- **`membershipLeafFriFloor_of_aggFriExtract` — the FRI floor IS AggAirSound's carrier.** -/
theorem membershipLeafFriFloor_of_aggFriExtract
    (E : ProofEngine) (leafPre : ℤ) (ChildVerifierSat : ℤ → Seg → Prop)
    (hagg : FriExtract E.Proof E.verify (fun _ => leafPre)
              (fun q => segOfCommit (E.piCommit q)) ChildVerifierSat) :
    MembershipLeafFriFloor E
      (fun leafVk leafCommit => ChildVerifierSat leafVk (segOfCommit leafCommit)) := by
  intro leafVk leafCommit hcv
  obtain ⟨q, hq, _hvkc, hexp⟩ := hagg leafVk (segOfCommit leafCommit) hcv
  refine ⟨q, hq, ?_⟩
  simpa [segOfCommit] using congrArg Seg.acc hexp

/-! ## §2 — the per-turn fold node + its satisfaction (the connect). -/

/-- **`MembershipFold E`** — the per-turn fold's membership face: the membership-leaf's pinned
preprocessed commitment `leafVk`, the tuple claim `leafCommit` the leaf exposes, and the effect-vm
leg's published `(sender_leaf, authorized_root)` claim `tup` (the claim PIs 50..51 on the NATIVE
`transferV3MembershipWide` row, modeled as one ℤ exactly as `FactoryFold.cv` models the 8-limb
octet claim). -/
structure MembershipFold (E : ProofEngine) where
  /-- the membership-leaf recursion-verifier's pinned preprocessed commitment (VK core). -/
  leafVk     : ℤ
  /-- the tuple claim the folded membership leaf exposes. -/
  leafCommit : ℤ
  /-- the effect-vm leg's published `(sender_leaf, authorized_root)` claim (the claim-PI carrier). -/
  tup        : ℤ

/-- **`SatMembershipFold E MembershipLeafSat f`** — a SATISFYING per-turn fold over its membership
face: `leafCV` (the in-circuit membership-leaf verifier subcircuit is satisfied) + `connect` (the
aggregate's combine constraint TIES the leaf's exposed tuple to the leg's published claim —
`prove_membership_binding_node_segmented`'s in-circuit connect). -/
structure SatMembershipFold (E : ProofEngine) (MembershipLeafSat : ℤ → ℤ → Prop)
    (f : MembershipFold E) : Prop where
  leafCV  : MembershipLeafSat f.leafVk f.leafCommit
  connect : f.leafCommit = f.tup

/-! ## §3 — THE REPAIR: the deployed membership binding, from the FOLD. -/

/-- **`membership_binding_from_fold` (THE DEPLOYED PAYLOAD).** A verifying AGGREGATE — the
per-turn fold including the membership leaf — FORCES, for the leg's published tuple claim
`f.tup`: (binding) ∃ a verifying membership sub-proof `q` of `E` with `E.piCommit q = f.tup`; AND
(anti-ghost) any two verifying sub-proofs exposing `f.tup` agree on their `vkOf`. The premise set
is EXACTLY the `custom_binding_from_fold` / `factory_binding_from_fold` set. -/
theorem membership_binding_from_fold
    (E : ProofEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (MembershipLeafSat : ℤ → ℤ → Prop)
    (hfri : MembershipLeafFriFloor E MembershipLeafSat)
    (hCR : Poseidon2SpongeCR hash)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q)
    (f : MembershipFold E) (hsat : SatMembershipFold E MembershipLeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.tup) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.piCommit p = f.tup → E.piCommit q = f.tup → E.vkOf p = E.vkOf q) := by
  have hE : EngineBinding E := engineBinding_of_floor hash E enc hCR hfactor hvk
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  intro p q' hp hq' hpc hq'c
  exact hE.commit_determines_vk p q' hp hq' (by rw [hpc, hq'c])

/-- **`authorized_from_fold` — the GROUNDING onto `MembershipBackingAttack.Authorized` (the §C
close at the aggregate).** `deployed_intent_does_not_force_membership` proved the deployed AIR
ALONE never forces the sender membership. THIS is the fold edge: when the folded leaf's semantics
is the re-proved `verify_membership_dsl` — a verifying membership sub-proof exposing the leg's
published `sender_leaf` IS a verifying Merkle path attesting the leg's tuple (`hbacks`, the
`membership_leaf_adapter` obligation) — a satisfying fold connected to the leg (`htup`)
DISCHARGES the exact membership predicate the attack file showed the deployed AIR omits. -/
theorem authorized_from_fold
    (M : MembershipEngine) (env : VmRowEnv)
    (E : ProofEngine) (MembershipLeafSat : ℤ → ℤ → Prop)
    (hfri : MembershipLeafFriFloor E MembershipLeafSat)
    (hbacks : ∀ q : E.Proof, E.verify q = true → E.piCommit q = senderLeafOf env →
        Authorized M env)
    (f : MembershipFold E) (hsat : SatMembershipFold E MembershipLeafSat f)
    (htup : f.tup = senderLeafOf env) :
    Authorized M env := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect, htup] at hqc
  exact hbacks q hq hqc

/-! ## §4 — NON-VACUITY: the binding FIRES on an honest fold; the §A forgery is REJECTED. -/

section Honest

/-- The honest membership face over `floorEngine`: the folded leaf exposes the commitment of the
honest sub-proof `(7, 7)`, and the connect publishes that same commitment as the leg's tuple
claim. -/
def honestFold (hash : List ℤ → ℤ) : MembershipFold (floorEngine hash) :=
  { leafVk := 100, leafCommit := hash [7, 7], tup := hash [7, 7] }

/-- The honest membership-leaf verifier predicate. -/
def honestMLS (hash : List ℤ → ℤ) : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit => ∃ q : ℤ × ℤ,
    (floorEngine hash).verify q = true ∧ (floorEngine hash).piCommit q = leafCommit

theorem honestFloor (hash : List ℤ → ℤ) :
    MembershipLeafFriFloor (floorEngine hash) (honestMLS hash) :=
  fun _leafVk _leafCommit h => h

theorem honestSat (hash : List ℤ → ℤ) :
    SatMembershipFold (floorEngine hash) (honestMLS hash) (honestFold hash) where
  leafCV  := ⟨(7, 7), rfl, rfl⟩
  connect := rfl

/-- **`honest_companion_fires` (POSITIVE non-vacuity).** On the honest sender-authorized transfer
the binding FIRES — resting on `Poseidon2SpongeCR` alone. -/
theorem honest_companion_fires (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    (∃ q : ℤ × ℤ, (floorEngine hash).verify q = true ∧
        (floorEngine hash).piCommit q = (honestFold hash).tup) ∧
    (∀ p q : ℤ × ℤ, (floorEngine hash).verify p = true → (floorEngine hash).verify q = true →
        (floorEngine hash).piCommit p = (honestFold hash).tup →
        (floorEngine hash).piCommit q = (honestFold hash).tup →
        (floorEngine hash).vkOf p = (floorEngine hash).vkOf q) :=
  membership_binding_from_fold (floorEngine hash) hash (fun p => [p.1, p.2]) (honestMLS hash)
    (honestFloor hash) hCR (fun _p _ => rfl)
    (by intro p q _ _ henc; injection henc)
    (honestFold hash) (honestSat hash)

end Honest

section Forged

/-- **`forged_unsat` (THE ANTI-GHOST TOOTH — forged tuple claim ⟹ UNSAT).** A per-turn fold whose
published tuple claim `f.tup` is backed by NO verifying membership sub-proof CANNOT satisfy. The
circuit twin of the tooth's forged-tuple rejection. -/
theorem forged_unsat {E : ProofEngine} {MembershipLeafSat : ℤ → ℤ → Prop}
    (hfri : MembershipLeafFriFloor E MembershipLeafSat) {f : MembershipFold E}
    (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.piCommit q = f.tup) :
    ¬ SatMembershipFold E MembershipLeafSat f := by
  intro hsat
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafCommit hsat.leafCV
  rw [hsat.connect] at hqc
  exact hforge ⟨q, hq, hqc⟩

/-- The membership-leaf predicate over `demoEngine` (the only verifying sub-proof commits to
`123`). -/
def demoMLS : ℤ → ℤ → Prop :=
  fun _leafVk leafCommit =>
    ∃ q : Bool, demoEngine.verify q = true ∧ demoEngine.piCommit q = leafCommit

theorem demoFloor : MembershipLeafFriFloor demoEngine demoMLS :=
  fun _leafVk _leafCommit h => h

/-- The `MembershipBackingAttack` §A forgery lifted onto the fold: the published tuple claim is
`0` (`senderLeaf_forgedEnv`'s value — the NOT-IN-THE-SET sender) — a claim NO verifying sub-proof
of `demoEngine` exposes. -/
def forgedFold : MembershipFold demoEngine := { leafVk := 0, leafCommit := 0, tup := 0 }

/-- **`forged_tuple_unsat_demo` (NEGATIVE non-vacuity — the §A attack, INVERTED onto the fold).**
What the deployed AIR alone admitted (`deployed_admits_unbacked_membership`), the aggregate
REFUSES. -/
theorem forged_tuple_unsat_demo : ¬ SatMembershipFold demoEngine demoMLS forgedFold := by
  refine forged_unsat demoFloor (f := forgedFold) ?_
  rintro ⟨q, _hq, hc⟩
  have hc' : (123 : ℤ) = 0 := hc
  exact absurd hc' (by decide)

end Forged

/-! ## §5 — Axiom hygiene (every load-bearing arm). -/

#assert_axioms membershipLeafFriFloor_of_aggFriExtract
#assert_axioms membership_binding_from_fold
#assert_axioms authorized_from_fold
#assert_axioms honest_companion_fires
#assert_axioms forged_unsat
#assert_axioms forged_tuple_unsat_demo

end Dregg2.Circuit.MembershipBindingFromFold
