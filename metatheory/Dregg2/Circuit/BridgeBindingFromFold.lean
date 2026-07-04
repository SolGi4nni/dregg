/-
# Dregg2.Circuit.BridgeBindingFromFold — the DEPLOYED bridge-mint backing, proven from the FOLD.

## Why this file exists (the flip — the 7th, LAST carrier)

`BridgeBackingAttack` proved the deployed bridge-mint's foreign-spend backing INVISIBLE to a
pure light client: the deployed member gated only credit + freeze + tick, read `mint_hash`
(`prmCol 0`) in NONE of its constraints, and the published digest was the executor's
BYTE-domain blake3 — a fold no circuit could recompute (`deployed_admits_unbacked_bridge`,
`deployed_intent_does_not_force_backing`). The repair it NAMED (§B: "the real backing must
come from the per-turn FOLD over the re-proved note-spend leaf connected to the published
`mint_hash` PI") is now DEPLOYED, via the felt-domain mint_hash thread:

  * THE EXECUTOR RE-ALIGN (STEP 1, the membership-`687601953` precedent): the projector's
    `mint_hash` is now the FELT-domain `note_spend_mint_hash_felt` =
    `hash_fact(hash_fact(nullifier, [root, dest_fed, asset]), [value_lo, value_hi])` over
    EXACTLY the six compressed felts `apply_bridge_mint` enforces the REAL note-spend STARK
    against (`dsl::note_spending::bridge_mint_hash_felt`, the ONE canonical function).
  * THE PIN-EMIT (STEPS 2–4): the deployed `mintVmDescriptor2R24` is `mintV3BridgeHash` =
    `withMintHashPin (withSelectorGate selM.MINT mintV3)` — the mint row's `param0` published
    at PI 46 on the FIRST row (`EffectVmEmitRotationV3.withMintHashPin_publishes`), rc at
    47..50, producer-filled (`trace_rotated.rs` BridgeMint arm), regen landed (drift PASS).
  * THE FOLD ARM (STEP 5, `ivc_turn_chain::prove_chain_core_rotated` Bridge arm): the
    per-turn aggregate folds the RE-PROVEN REAL note-spend STARK
    (`note_spend_leaf_adapter::prove_note_spend_leaf_with_claim` — spending-key knowledge +
    Merkle membership + full-width commitment, with the mint identity recomputed IN-AIR at
    claim lane 6 from the leaf's OWN PI-pinned tuple), RE-VERIFIES it via the recursion
    (the same in-circuit child-verifier subcircuit `AggAirSound` opens), and CONNECTS the
    leaf's exposed identity to the leg's published PI-46 mint identity
    (`prove_note_spend_mint_binding_node_segmented`). Fail-closed: a pin-less /
    wrong-column leg is refused by the admission (`carrier_claim_pins_admitted`, FIRST-row
    `prmCol 0` only). Folding the binding-only `bridge_action_air` was REFUSED as the
    backing (a prover-chosen tuple — the vacuous connect the fail-open law forbids).
  * The deployed-path tooth (`bridge_binding_deployed_tooth.rs`) exercises the honest /
    forged-identity poles on the NATIVE committed mint row + the regen-tie geometry + the
    nullifier-binding linkage.

This module proves the REAL deployed bridge guarantee from premises that HOLD for the
deployed aggregate — the EXACT mirror of `DslBindingFromFold` / `SovereignBindingFromFold`
(the universal sub-proof-folding primitive):

  * **`bridge_binding_from_fold`** — a verifying AGGREGATE (the per-turn fold including the
    note-spend leaf) FORCES, for the leg's published mint identity `f.mintHash`: (binding)
    ∃ a verifying foreign note-spend `q` with `E.spendDigest q = f.mintHash`, and
    (anti-double-mint linkage) the CONSUMED NULLIFIER is DETERMINED by `f.mintHash` — any
    two verifying spends exposing the published identity agree on their nullifier (the
    identity is a Poseidon2 sponge of the spend tuple, CR ⇒ tuple-determined). Premises =
    {the FRI floor (= `AggAirSound`'s carrier), `Poseidon2SpongeCR`, the identity factoring
    (the `hash_fact` chain over the spend tuple — `note_spend_mint_hash_felt`'s shape), the
    connect}. No staged-AIR carrier, no bridge axiom.

  * **`backedAt_from_fold`** — the GROUNDING onto `BridgeBackingAttack.BackedAt`: a
    satisfying fold connected to the leg's published `mint_hash` DISCHARGES the exact
    (staged) backing predicate `BridgeBackingAttack` proved the deployed AIR omits. §B
    (`deployed_intent_does_not_force_backing`) stays TRUE of the bare AIR; what flips is
    the AGGREGATE. ⚑ FRESHNESS STAYS EXECUTOR-SIDE (§C of the attack file, HONEST SCOPE):
    `BackedAt`'s ¬consumed half is discharged from the `hfresh` hypothesis — the
    consume-once guard is the RE-EXEC tooth (`BridgedNullifierSet` /
    `bridge_ledger.rs::bridge_mint_against_lock`), NOT a fold edge. What the fold ADDS for
    freshness is the LINKAGE: the folded identity pins WHICH nullifier was minted against
    (the anti-double-mint half of `bridge_binding_from_fold`), so the executor's
    set-uniqueness ranges over a light-client-visible key.
    `deployed_admits_consumed_nullifier` STANDS as a deployed-AIR fact.

## Non-vacuity (BOTH polarities, mirroring the Rust tooth)

`honest_companion_fires` — on an honest bridge-mint turn the grounded binding FIRES.
`forged_unsat` / `forged_mint_hash_unsat_demo` — a fold whose published identity is the
`BridgeBackingAttack` §A forgery (the `goodBridgeMintRow`'s published `mint_hash = 0`,
backed by NO verifying spend of `demoSpend`) CANNOT satisfy: the aggregate is UNSAT — the
circuit twin of `deployed_bridge_mint_forged_identity_rejected`.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. The
floor carriers appear ONLY as Prop hypotheses. NO new axiom, NO `sorry`. NEW file; imports
read-only. `BridgeBackingAttack` STANDS (the deployed-AIR facts remain true); this file is
the aggregate-level flip beside it.
-/
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.BridgeBackingAttack

namespace Dregg2.Circuit.BridgeBindingFromFold

open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.BridgeBackingAttack (NoteSpendEngine BackedAt mintHashOf demoSpend
  mintHash_goodRow noneConsumed)
open Dregg2.Circuit.Emit.EffectVmEmitBridgeMint (goodBridgeMintRow)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the note-spend-leaf FRI floor, and its provenance from `AggAirSound.FriExtract`. -/

/-- **`NoteSpendLeafFriFloor E LeafSat`** — the localized FRI-extraction floor for the
re-proved foreign note-spend leaf: a SATISFIED in-circuit note-spend-leaf verifier (pinned VK
core `leafVk`, exposing mint-identity claim `leafIdentity` — the leaf's lane 6, the
IN-AIR-recomputed `note_spend_mint_hash_felt` over its own PI-pinned spend tuple) yields a
GENUINELY VERIFYING foreign spend of engine `E` whose `spendDigest` IS the exposed identity.
The bridge instance of `AggAirSound.FriExtract` (one child of one node), NOT a new dregg
axiom — see `noteSpendLeafFriFloor_of_aggFriExtract`. -/
def NoteSpendLeafFriFloor (E : NoteSpendEngine) (LeafSat : ℤ → ℤ → Prop) : Prop :=
  ∀ leafVk leafIdentity : ℤ, LeafSat leafVk leafIdentity →
    ∃ q : E.Proof, E.verify q = true ∧ E.spendDigest q = leafIdentity

/-- The note-spend leaf's exposed segment projection: the leaf carries its mint-identity
claim `x` in the ordered-digest lane `acc` (the other lanes are inert for a single-leaf
wrap). -/
def segOfIdentity (x : ℤ) : Seg := { firstOld := 0, lastNew := 0, count := 0, acc := x }

/-- **`noteSpendLeafFriFloor_of_aggFriExtract` — the FRI floor IS AggAirSound's carrier.**
Given the aggregation's per-child `FriExtract` over the note-spend engine — pinned VK core
constant `leafPre`, the child exposing its mint-identity claim in `acc` — the bridge-leaf
floor follows. -/
theorem noteSpendLeafFriFloor_of_aggFriExtract
    (E : NoteSpendEngine) (leafPre : ℤ) (ChildVerifierSat : ℤ → Seg → Prop)
    (hagg : FriExtract E.Proof E.verify (fun _ => leafPre)
              (fun q => segOfIdentity (E.spendDigest q)) ChildVerifierSat) :
    NoteSpendLeafFriFloor E
      (fun leafVk leafIdentity => ChildVerifierSat leafVk (segOfIdentity leafIdentity)) := by
  intro leafVk leafIdentity hcv
  obtain ⟨q, hq, _hvkc, hexp⟩ := hagg leafVk (segOfIdentity leafIdentity) hcv
  refine ⟨q, hq, ?_⟩
  simpa [segOfIdentity] using congrArg Seg.acc hexp

/-! ## §2 — the per-turn fold node + its satisfaction (the connect). -/

/-- **`BridgeFold E`** — the per-turn fold's bridge face: the note-spend leaf's pinned
preprocessed commitment `leafVk` (its VK core), the mint-identity claim `leafIdentity` the
leaf exposes (lane 6), and the effect-vm leg's published mint identity `mintHash` (the PI-46
`withMintHashPin` slot — the STEP-1 felt-domain `note_spend_mint_hash_felt` the producer
filled at `param0`). -/
structure BridgeFold (E : NoteSpendEngine) where
  /-- the note-spend-leaf recursion-verifier's pinned preprocessed commitment (VK core). -/
  leafVk       : ℤ
  /-- the mint-identity claim the folded note-spend leaf exposes (lane 6). -/
  leafIdentity : ℤ
  /-- the effect-vm leg's published felt mint identity (the PI-46 pin carrier). -/
  mintHash     : ℤ

/-- **`SatBridgeFold E LeafSat f`** — a SATISFYING per-turn fold over its bridge face:
`leafCV` (the in-circuit note-spend-leaf verifier subcircuit is satisfied) + `connect` (the
aggregate's combine constraint TIES the leaf's exposed identity to the leg's published
mint identity — `prove_note_spend_mint_binding_node_segmented`'s in-circuit connect). -/
structure SatBridgeFold (E : NoteSpendEngine) (LeafSat : ℤ → ℤ → Prop)
    (f : BridgeFold E) : Prop where
  leafCV  : LeafSat f.leafVk f.leafIdentity
  connect : f.leafIdentity = f.mintHash

/-! ## §3 — THE REPAIR: the deployed bridge-mint backing, from the FOLD. -/

/-- **`bridge_binding_from_fold` (THE DEPLOYED PAYLOAD).** A verifying AGGREGATE — the
per-turn fold including the re-proved REAL note-spend leaf — FORCES, for the leg's published
mint identity `f.mintHash`:

  (binding) ∃ a verifying foreign note-spend `q` of `E` with `E.spendDigest q = f.mintHash`;
  AND (anti-double-mint linkage) the consumed NULLIFIER is DETERMINED by `f.mintHash` — any
  two verifying spends exposing the published identity agree on their nullifier.

The premise set is EXACTLY the `dsl_binding_from_fold` / `sovereign_binding_from_fold` set:
the FRI floor, `Poseidon2SpongeCR`, and the identity FACTORING — the published digest of a
verifying spend is the sponge of its spend tuple (`note_spend_mint_hash_felt`'s `hash_fact`
chain over `(nullifier, root, dest_fed, asset, value_lo, value_hi)`; `henc` recovers the
nullifier from the tuple encoding). A forged identity with no backing spend makes the
aggregate UNSAT. -/
theorem bridge_binding_from_fold
    (E : NoteSpendEngine) (hash : List ℤ → ℤ) (enc : E.Proof → List ℤ)
    (LeafSat : ℤ → ℤ → Prop)
    (hfri : NoteSpendLeafFriFloor E LeafSat)
    (hCR : Poseidon2SpongeCR hash)
    (hfactor : ∀ p, E.verify p = true → E.spendDigest p = hash (enc p))
    (henc : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q →
        E.nullifier p = E.nullifier q)
    (f : BridgeFold E) (hsat : SatBridgeFold E LeafSat f) :
    (∃ q : E.Proof, E.verify q = true ∧ E.spendDigest q = f.mintHash) ∧
    (∀ p q : E.Proof, E.verify p = true → E.verify q = true →
        E.spendDigest p = f.mintHash → E.spendDigest q = f.mintHash →
        E.nullifier p = E.nullifier q) := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafIdentity hsat.leafCV
  rw [hsat.connect] at hqc
  refine ⟨⟨q, hq, hqc⟩, ?_⟩
  intro p q' hp hq' hpc hq'c
  have hhash : hash (enc p) = hash (enc q') := by
    rw [← hfactor p hp, ← hfactor q' hq', hpc, hq'c]
  exact henc p q' hp hq' (hCR _ _ hhash)

/-- **`backedAt_from_fold` — the GROUNDING onto `BridgeBackingAttack.BackedAt` (the §A/§B
close, at the aggregate).** `deployed_intent_does_not_force_backing` proved the deployed AIR
ALONE never forces the backing. THIS is the fold edge: a satisfying fold whose published
mint identity is the row's (`hpub` — the `withMintHashPin` pin welds PI 46 to the row's
`param0`, `mintHashOf env`) DISCHARGES exactly the (staged) predicate `BridgeBackingAttack`
showed the deployed AIR omits: the row IS `BackedAt`.

⚑ HONEST SCOPE — the ¬consumed half rides `hfresh`: the consume-once guard is the RE-EXEC
tooth (`BridgedNullifierSet`'s atomic contains-then-insert, journaled), supplied HERE as the
hypothesis "every spend the engine still verifies is unconsumed" — the attack file's §C
(`deployed_admits_consumed_nullifier`) STANDS; the fold's own contribution to freshness is
the nullifier LINKAGE (`bridge_binding_from_fold`'s second half). -/
theorem backedAt_from_fold
    (E : NoteSpendEngine) (LeafSat : ℤ → ℤ → Prop)
    (hfri : NoteSpendLeafFriFloor E LeafSat)
    (consumed : ℤ → Prop)
    (hfresh : ∀ q : E.Proof, E.verify q = true → ¬ consumed (E.nullifier q))
    (f : BridgeFold E) (hsat : SatBridgeFold E LeafSat f)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hpub : f.mintHash = mintHashOf env) :
    BackedAt E consumed env := by
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafIdentity hsat.leafCV
  rw [hsat.connect, hpub] at hqc
  exact ⟨q, hq, hqc, hfresh q hq⟩

/-! ## §4 — NON-VACUITY: the binding FIRES on an honest fold; the §A forgery is REJECTED. -/

section Honest

/-- The honest foreign-spend engine over the sponge: a spend is `(nullifier, rest)`, every
proof verifies, its digest is the sponge of the tuple, its nullifier the first lane — the
`floorEngine` shape, at the `NoteSpendEngine` signature. -/
def honestSpend (hash : List ℤ → ℤ) : NoteSpendEngine where
  Proof := ℤ × ℤ
  verify := fun _ => true
  spendDigest := fun p => hash [p.1, p.2]
  nullifier := fun p => p.1

/-- The honest bridge face over `honestSpend`: the folded leaf exposes the identity of the
honest spend `(7, 7)`, and the connect publishes that same identity as the leg's PI-46
mint identity. -/
def honestFold (hash : List ℤ → ℤ) : BridgeFold (honestSpend hash) :=
  { leafVk := 100, leafIdentity := hash [7, 7], mintHash := hash [7, 7] }

/-- The honest note-spend-leaf verifier predicate: satisfied exactly when a backing
verifying spend exposes the exposed identity claim. -/
def honestNLS (hash : List ℤ → ℤ) : ℤ → ℤ → Prop :=
  fun _leafVk leafIdentity => ∃ q : ℤ × ℤ,
    (honestSpend hash).verify q = true ∧ (honestSpend hash).spendDigest q = leafIdentity

theorem honestFloor (hash : List ℤ → ℤ) :
    NoteSpendLeafFriFloor (honestSpend hash) (honestNLS hash) :=
  fun _leafVk _leafIdentity h => h

theorem honestSat (hash : List ℤ → ℤ) :
    SatBridgeFold (honestSpend hash) (honestNLS hash) (honestFold hash) where
  leafCV  := ⟨(7, 7), rfl, rfl⟩
  connect := rfl

/-- **`honest_companion_fires` (POSITIVE non-vacuity).** On the honest bridge-mint turn the
binding FIRES: the published mint identity is BACKED by a verifying foreign spend whose
nullifier is uniquely determined by the identity — resting on `Poseidon2SpongeCR` alone. -/
theorem honest_companion_fires (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    (∃ q : ℤ × ℤ, (honestSpend hash).verify q = true ∧
        (honestSpend hash).spendDigest q = (honestFold hash).mintHash) ∧
    (∀ p q : ℤ × ℤ, (honestSpend hash).verify p = true → (honestSpend hash).verify q = true →
        (honestSpend hash).spendDigest p = (honestFold hash).mintHash →
        (honestSpend hash).spendDigest q = (honestFold hash).mintHash →
        (honestSpend hash).nullifier p = (honestSpend hash).nullifier q) :=
  bridge_binding_from_fold (honestSpend hash) hash (fun p => [p.1, p.2]) (honestNLS hash)
    (honestFloor hash) hCR (fun _p _ => rfl)
    (by
      intro p q _ _ henc
      have h1 : p.1 = q.1 := by injection henc
      exact h1)
    (honestFold hash) (honestSat hash)

/-- **The honest fold DISCHARGES `BackedAt`** — the grounded close is itself non-vacuous:
against the fresh-baseline consumed set (`noneConsumed`), the honest fold backs ANY row
whose published `mint_hash` is the honest identity. -/
theorem honest_backedAt (hash : List ℤ → ℤ)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hpub : (honestFold hash).mintHash = mintHashOf env) :
    BackedAt (honestSpend hash) noneConsumed env :=
  backedAt_from_fold (honestSpend hash) (honestNLS hash) (honestFloor hash)
    _ (fun _q _ h => h) (honestFold hash) (honestSat hash) env hpub

end Honest

section Forged

/-- **`forged_unsat` (THE ANTI-GHOST TOOTH — forged mint identity ⟹ UNSAT).** A per-turn
fold whose published mint identity `f.mintHash` is backed by NO verifying foreign spend
CANNOT satisfy: the fold re-verifies the leaf (`hfri`) and the connect ties its claim to
`f.mintHash`, so a satisfying fold would PRODUCE a backing spend — contradiction. The
circuit twin of `deployed_bridge_mint_forged_identity_rejected`. -/
theorem forged_unsat {E : NoteSpendEngine} {LeafSat : ℤ → ℤ → Prop}
    (hfri : NoteSpendLeafFriFloor E LeafSat) {f : BridgeFold E}
    (hforge : ¬ ∃ q : E.Proof, E.verify q = true ∧ E.spendDigest q = f.mintHash) :
    ¬ SatBridgeFold E LeafSat f := by
  intro hsat
  obtain ⟨q, hq, hqc⟩ := hfri f.leafVk f.leafIdentity hsat.leafCV
  rw [hsat.connect] at hqc
  exact hforge ⟨q, hq, hqc⟩

/-- The note-spend-leaf predicate over `demoSpend` (the only verifying spend exposes digest
`123`). -/
def demoNLS : ℤ → ℤ → Prop :=
  fun _leafVk leafIdentity =>
    ∃ q : Bool, demoSpend.verify q = true ∧ demoSpend.spendDigest q = leafIdentity

theorem demoFloor : NoteSpendLeafFriFloor demoSpend demoNLS :=
  fun _leafVk _leafIdentity h => h

/-- The `BridgeBackingAttack` §A forgery lifted onto the fold: the published mint identity
is `goodBridgeMintRow`'s published `mint_hash` (= 0, `mintHash_goodRow`) — the digest the §A
row published, which NO verifying spend of `demoSpend` exposes. -/
def forgedFold : BridgeFold demoSpend :=
  { leafVk := 0, leafIdentity := mintHashOf goodBridgeMintRow,
    mintHash := mintHashOf goodBridgeMintRow }

/-- **`forged_mint_hash_unsat_demo` (NEGATIVE non-vacuity — the §A attack, INVERTED onto the
fold).** The forged fold (published identity = the `deployed_admits_unbacked_bridge` row's
`mint_hash = 0`, unbacked) does NOT satisfy: what the deployed AIR alone admitted, the
aggregate REFUSES. -/
theorem forged_mint_hash_unsat_demo : ¬ SatBridgeFold demoSpend demoNLS forgedFold := by
  refine forged_unsat demoFloor (f := forgedFold) ?_
  rintro ⟨q, _hq, hc⟩
  rw [show forgedFold.mintHash = 0 from mintHash_goodRow] at hc
  have hc' : (123 : ℤ) = 0 := hc
  exact absurd hc' (by decide)

end Forged

/-! ## §5 — Axiom hygiene (every load-bearing arm). -/

#assert_axioms noteSpendLeafFriFloor_of_aggFriExtract
#assert_axioms bridge_binding_from_fold
#assert_axioms backedAt_from_fold
#assert_axioms honest_companion_fires
#assert_axioms honest_backedAt
#assert_axioms forged_unsat
#assert_axioms forged_mint_hash_unsat_demo

end Dregg2.Circuit.BridgeBindingFromFold
