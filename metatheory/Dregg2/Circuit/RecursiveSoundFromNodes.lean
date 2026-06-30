/-
# Dregg2.Circuit.RecursiveSoundFromNodes — the WHOLE-TREE fold that retires the carried `hrec`.

**What this closes.** `GroundedApex.engineSound_grounded` derives `EngineSound`'s `binding_sound` and
`leaf_sound` legs, but STILL carries the third leg `recursive_sound` as the named hypothesis `hrec`:

  `verify agg.root = true → (∀ p ∈ agg.leafProofs, verify p = true) ∧ verify agg.bindingProof = true`

`AggAirSound` already opened that leg's PER-NODE content: `segsound_node_discharged` proves that a
satisfying aggregation node, under the localized `FriExtract` floor, forces its two children to verify
and the segment-combine to be `CombineOk` — strictly local, one node and its two immediate children.
What remained (the precise residual `Dregg2.lean` names beside the `GroundedApex` import) was the
WHOLE-TREE FOLD: composing that per-node implication, over the entire aggregation tree, into the
root→all-leaves shape `recursive_sound` asserts over the FLAT list `agg.leafProofs`.

This file PROVES that fold. It models the aggregation artifact as a proof-carrying tree `PTree` whose
in-order leaf proofs are exactly the wrapped `agg.leafProofs` (+ the binding leaf), and takes the
per-node carrier in the structural shape `AggAirSound.segsound_node_discharged` delivers — a verifying
node forces ITS OWN two child subtrees' root proofs to verify, plus `CombineOk`. By a clean induction
on the tree (`all_leaves_verify`), a verifying root forces EVERY wrapped leaf proof to verify; reading
that against the flat list yields exactly the `recursive_sound` shape (`recursive_sound_from_nodes`).
`engineSound_recursive_derived` then assembles a full `EngineSound` whose `recursive_sound` is DERIVED
from the per-node carrier rather than carried — the analog, for the recursion leg, of
`WitnessRealizing.engineSound_of_refinements` for the leaf leg.

**The residual floor (exactly what is left).** The proof-propagation fold rests on NOTHING but the
per-node carrier itself — the function-form reading of `AggAirSound.FriExtract` over the ACTUALLY
WRAPPED child proofs ("the node's verification forces its wrapped children's proofs to verify"). It is
the same per-node in-circuit recursion-verifier soundness `AggAirSound` names; NO new carrier, NO
`Poseidon2SpongeCR` (the digest CR floor is the orthogonal segment-reorder tooth `combine_digest_binds`,
not the proof propagation), NO new axiom, NO `sorry`. The CombineOk arm of the carrier additionally
chains to the genuine fold by `RecursiveAggregation.combineOk_eq` (`node_seg_is_combine`), reusing the
existing segment machinery — exhibited here for completeness, though `recursive_sound`'s shape needs
only the proof arm.

**The one honest nuance (existential vs. function form), named not hidden.** `AggAirSound`'s
`FriExtract`/`segsound_node_discharged` state the per-node fact EXISTENTIALLY (`∃ p, verify p = true ∧
vkCommit p = c ∧ exposedPI p = s`) — a verifying child proof with the pinned commitment and exposed
segment. That suffices for `AggAirSound`'s segment-binding purpose, but to propagate verification to
the SPECIFIC elements of the flat `agg.leafProofs` list (which `recursive_sound`, and its downstream
`leaf_sound` positional pairing, require) the carrier must be read in FUNCTION form: the wrapped child
proof — the one element of `agg.leafProofs` — verifies. That strengthening is sound by construction
(the recursion verifier wraps exactly one proof per child, so the pinned `(commitment, segment)` is
that proof's), not a new crypto assumption; `(commitment, segment)`-uniqueness of proofs is NOT, and
need not be, derived. The `PTree` carrier encodes precisely this function-form per-node floor.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); the per-node carrier is a
Prop/`def`, never an `axiom`. Standalone: `lake build Dregg2.Circuit.RecursiveSoundFromNodes`.
-/
import Dregg2.Circuit.AggAirSound

namespace Dregg2.Circuit.RecursiveSoundFromNodes

open Dregg2.Circuit.RecursiveAggregation
  (Seg combineSeg CombineOk combineOk_eq Aggregate EngineSound)
open Dregg2.Distributed.HistoryAggregation
  (ChainStep ChainBound stateRoot zeroTurn foldedFinalRoot)
open Dregg2.Exec (RecChainedState recCexec)

set_option autoImplicit false

/-! ## 1. The proof-carrying aggregation tree.

`PTree` is the aggregation tree the recursion engine folds, with the recursion PROOF carried at every
node (leaf = a per-turn whole-turn / binding leaf proof; node = one `segment_combine_expose` proof) and
the exposed segment `Seg` alongside it. The host folds the leaf proofs into the single root proof; the
in-order `leavesP` are exactly the wrapped `agg.leafProofs` (plus the binding leaf). -/

/-- The proof-carrying aggregation tree: a leaf carries its proof and exposed segment; a node carries
its own proof, exposed segment, and two child subtrees. -/
inductive PTree (Proof : Type) where
  | leaf : Proof → Seg → PTree Proof
  | node : Proof → Seg → PTree Proof → PTree Proof → PTree Proof

variable {Proof : Type}

/-- The proof a subtree's root carries (the proof the host/parent verifies for this subtree). -/
def rootP : PTree Proof → Proof
  | .leaf p _     => p
  | .node p _ _ _ => p

/-- The segment a subtree exposes (its public segment claim). -/
def segP : PTree Proof → Seg
  | .leaf _ s     => s
  | .node _ s _ _ => s

/-- The wrapped leaf proofs under a subtree, in chain (in-order) order — the flat list the engine
folds, which the host check pins to `agg.leafProofs`. -/
def leavesP : PTree Proof → List Proof
  | .leaf p _     => [p]
  | .node _ _ l r => leavesP l ++ leavesP r

@[simp] theorem rootP_node (p : Proof) (c : Seg) (l r : PTree Proof) :
    rootP (.node p c l r) = p := rfl
@[simp] theorem rootP_leaf (p : Proof) (c : Seg) : rootP (.leaf p c) = p := rfl
@[simp] theorem leavesP_node (p : Proof) (c : Seg) (l r : PTree Proof) :
    leavesP (.node p c l r) = leavesP l ++ leavesP r := rfl
@[simp] theorem leavesP_leaf (p : Proof) (c : Seg) : leavesP (.leaf p c) = [p] := rfl

/-! ## 2. The per-node carrier — `AggAirSound.segsound_node_discharged`'s conclusion, made structural.

`NodeCarrier` is the per-node aggregation-soundness floor, recursive over the tree. Its node clause is
EXACTLY the conclusion `AggAirSound.segsound_node_discharged` delivers — a verifying node forces its two
(here STRUCTURAL, i.e. wrapped) child proofs to verify AND the segment combine to be `CombineOk` — read
in function form over the actually-wrapped proofs (see the file header). A leaf carries no obligation
(its statement soundness is the leaf rung, `EngineSound.leaf_sound`). This is the per-node `FriExtract`
floor; the whole-tree fold below rests on it ALONE. -/
def NodeCarrier (verify : Proof → Bool) (H : ℤ → ℤ → ℤ) : PTree Proof → Prop
  | .leaf _ _   => True
  | .node p c l r =>
      (verify p = true →
        (verify (rootP l) = true ∧ verify (rootP r) = true)
          ∧ CombineOk H (segP l) (segP r) c)
      ∧ NodeCarrier verify H l ∧ NodeCarrier verify H r

theorem nodeCarrier_node (verify : Proof → Bool) (H : ℤ → ℤ → ℤ)
    (p : Proof) (c : Seg) (l r : PTree Proof) :
    NodeCarrier verify H (.node p c l r) =
      ((verify p = true →
        (verify (rootP l) = true ∧ verify (rootP r) = true)
          ∧ CombineOk H (segP l) (segP r) c)
      ∧ NodeCarrier verify H l ∧ NodeCarrier verify H r) := rfl

/-! ## 3. THE WHOLE-TREE FOLD — root verifies ⟹ every wrapped leaf proof verifies. -/

/-- **`all_leaves_verify` (THE FOLD).** A verifying root forces EVERY wrapped leaf proof to verify, by
induction on the aggregation tree off the per-node carrier. BASE = a leaf: the root IS the leaf proof,
already verifying. STEP = a node: the carrier's node arm turns the node's verification into its two
child roots' verification; the IH carries each down to its leaves; the in-order leaf list is the append
of the two child leaf lists. This is the composition `segsound_node_discharged` opened the per-node
content FOR — now run over the whole tree, with the only input the per-node carrier. -/
theorem all_leaves_verify (verify : Proof → Bool) (H : ℤ → ℤ → ℤ) (t : PTree Proof) :
    NodeCarrier verify H t → verify (rootP t) = true → ∀ p ∈ leavesP t, verify p = true := by
  induction t with
  | leaf p c =>
      intro _ hv q hq
      rw [leavesP_leaf, List.mem_singleton] at hq
      subst hq
      exact hv
  | node p c l r ihl ihr =>
      intro hc hv q hq
      rw [nodeCarrier_node] at hc
      obtain ⟨hstep, hcl, hcr⟩ := hc
      obtain ⟨⟨hvl, hvr⟩, _hcomb⟩ := hstep hv
      rw [leavesP_node, List.mem_append] at hq
      rcases hq with h | h
      · exact ihl hcl hvl q h
      · exact ihr hcr hvr q h

/-! ## 4. The CombineOk arm chains to the genuine fold (reusing `combineOk_eq`).

For completeness — `recursive_sound`'s shape needs only the proof arm above — the carrier's `CombineOk`
arm chains through `RecursiveAggregation.combineOk_eq` exactly as `subtree_binding` does: a verifying
node's exposed segment IS the genuine ordered `combineSeg` of its children's segments, with the
seam-continuity. So the per-node carrier composes on BOTH arms (proofs verify ⊕ segments fold). -/
theorem node_seg_is_combine (verify : Proof → Bool) (H : ℤ → ℤ → ℤ)
    (p : Proof) (c : Seg) (l r : PTree Proof)
    (hc : NodeCarrier verify H (.node p c l r)) (hv : verify p = true) :
    c = combineSeg H (segP l) (segP r) ∧ (segP l).lastNew = (segP r).firstOld := by
  rw [nodeCarrier_node] at hc
  exact combineOk_eq H (hc.1 hv).2

/-! ## 5. `recursive_sound_from_nodes` — the carried `hrec` shape, DERIVED. -/

/-- **`recursive_sound_from_nodes` (THE DISCHARGE OF `hrec`).** Exactly `EngineSound.recursive_sound`'s
statement — a verifying root forces every `agg.leafProofs` element AND the `agg.bindingProof` to verify
— produced from the per-node carrier over a tree `t` whose root proof is `agg.root` and whose wrapped
leaves cover `agg.leafProofs` and the binding leaf. The whole-tree fold (`all_leaves_verify`) is the
only content; the carried FRI hypothesis `hrec` is no longer assumed, it is this theorem. -/
theorem recursive_sound_from_nodes (verify : Proof → Bool) (H : ℤ → ℤ → ℤ)
    (agg : Aggregate Proof) (t : PTree Proof)
    (hc : NodeCarrier verify H t)
    (hroot : rootP t = agg.root)
    (hwrap : ∀ p ∈ agg.leafProofs, p ∈ leavesP t)
    (hbind : agg.bindingProof ∈ leavesP t) :
    verify agg.root = true →
      (∀ p ∈ agg.leafProofs, verify p = true) ∧ verify agg.bindingProof = true := by
  intro hv
  have hall : ∀ p ∈ leavesP t, verify p = true :=
    all_leaves_verify verify H t hc (by rw [hroot]; exact hv)
  exact ⟨fun p hp => hall p (hwrap p hp), hall agg.bindingProof hbind⟩

/-! ## 6. `engineSound_recursive_derived` — `EngineSound` with `recursive_sound` DERIVED.

The recursion analog of `WitnessRealizing.engineSound_of_refinements` (which derives `leaf_sound`): the
`recursive_sound` leg is no longer a hypothesis but the DERIVED `recursive_sound_from_nodes`, off the
per-node carrier + the wrapping facts. The other two legs are supplied (they are grounded elsewhere —
`leaf_sound` by `engineSound_of_refinements`, `binding_sound` by `BindingAirSound`). So a full
`EngineSound` is assembled with NONE of its three legs left as the whole-tree FRI hypothesis. -/
theorem engineSound_recursive_derived
    (verify : Proof → Bool) (H : ℤ → ℤ → ℤ)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ) (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (t : PTree Proof)
    (hc : NodeCarrier verify H t)
    (hroot : rootP t = agg.root)
    (hwrap : ∀ p ∈ agg.leafProofs, p ∈ leavesP t)
    (hbind : agg.bindingProof ∈ leavesP t)
    (hleaf : List.Forall₂
      (fun (p : Proof) (s : ChainStep) => verify p = true → recCexec s.pre s.turn = some s.post)
      agg.leafProofs steps)
    (hbindsound : verify agg.bindingProof = true →
      ChainBound CH RH cmb compress compressN steps
        ∧ agg.genesisRoot = (match steps.head? with
            | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
            | some s => ChainStep.oldRoot CH RH cmb compress compressN s)
        ∧ agg.finalRoot = foldedFinalRoot CH RH cmb compress compressN g steps) :
    EngineSound Proof verify CH RH cmb compress compressN agg g steps where
  recursive_sound := recursive_sound_from_nodes verify H agg t hc hroot hwrap hbind
  leaf_sound := hleaf
  binding_sound := hbindsound

/-! ## 7. NON-VACUITY — the fold FIRES on a real honest 2-leaf tree.

The fold would be hollow if no tree satisfied the per-node carrier with a verifying root. We exhibit an
honest 2-leaf combine — `[1→2] ⋆ [2→3]`, the same shape `AggAirSound.honestNode` exhibits — over an
accepting verifier: the per-node carrier holds (both leaves verify; the combine is `CombineOk` with the
genuine `combineSeg` parent and the `2 = 2` seam), and `recursive_sound_from_nodes` concludes a REAL
`recursive_sound` — verifying the root forces both wrapped leaf proofs and the binding leaf to verify. -/

section Vacuity

/-- The accepting verifier and the trivial digest combiner for the witness. -/
def accept : Unit → Bool := fun _ => true
def zH : ℤ → ℤ → ℤ := fun _ _ => 0

/-- Honest left/right segments `1 → 2` and `2 → 3` (count 1 each); the seam `2 = 2` holds. -/
def honL : Seg := { firstOld := 1, lastNew := 2, count := 1, acc := 0 }
def honR : Seg := { firstOld := 2, lastNew := 3, count := 1, acc := 0 }

/-- The honest 2-leaf tree: two accepting leaves, the node exposing their genuine `combineSeg`. -/
def honestTree : PTree Unit :=
  .node () (combineSeg zH honL honR) (.leaf () honL) (.leaf () honR)

/-- **`honest_node_carrier` (the carrier is INHABITED).** The per-node carrier holds on the honest
tree: the node arm gives both leaves verifying (`accept _ = true`) and `CombineOk` (the parent is the
genuine fold; the seam `honL.lastNew = 2 = honR.firstOld` is `rfl`); the leaves carry `True`. -/
theorem honest_node_carrier : NodeCarrier accept zH honestTree := by
  refine ⟨fun _ => ⟨⟨rfl, rfl⟩, ?_⟩, trivial, trivial⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`honest_all_leaves_verify` (the fold FIRES).** A verifying root forces every wrapped leaf proof
to verify — a real, non-vacuous firing of `all_leaves_verify` on the honest 2-leaf tree. -/
theorem honest_all_leaves_verify : ∀ p ∈ leavesP honestTree, accept p = true :=
  all_leaves_verify accept zH honestTree honest_node_carrier rfl

/-- The realizing aggregate: every wrapped proof is the accepting `Unit`; its leaf list / binding leaf
are exactly the honest tree's leaves. -/
def honestAgg : Aggregate Unit where
  root := ()
  leafProofs := [(), ()]
  bindingProof := ()
  genesisRoot := 0
  finalRoot := 0
  chainDigest := 0
  numTurns := 2

/-- **`honest_recursive_sound` (THE DISCHARGED `hrec` FIRES).** `recursive_sound_from_nodes` produces a
genuine `recursive_sound` on the honest tree+aggregate: verifying the root forces both wrapped leaf
proofs and the binding leaf to verify. So the discharge of the carried `hrec` is non-vacuous — it is a
real instance of the exact shape `EngineSound.recursive_sound` demands. -/
theorem honest_recursive_sound :
    accept honestAgg.root = true →
      (∀ p ∈ honestAgg.leafProofs, accept p = true) ∧ accept honestAgg.bindingProof = true :=
  recursive_sound_from_nodes accept zH honestAgg honestTree honest_node_carrier
    rfl
    (fun p _ => by cases p; exact List.mem_cons_self)
    List.mem_cons_self

/-- **`honest_node_seg_is_combine` (the CombineOk arm chains, WITNESSED).** On the honest node, the
exposed segment IS the genuine `combineSeg` of the children's and the seam continues — a real firing of
`node_seg_is_combine` (hence of `combineOk_eq`) on the honest combine. -/
theorem honest_node_seg_is_combine :
    (combineSeg zH honL honR) = combineSeg zH (segP (PTree.leaf () honL)) (segP (PTree.leaf () honR))
      ∧ (segP (PTree.leaf () honL)).lastNew = (segP (PTree.leaf () honR)).firstOld :=
  node_seg_is_combine accept zH () (combineSeg zH honL honR)
    (.leaf () honL) (.leaf () honR) honest_node_carrier rfl

end Vacuity

/-! ## 8. Axiom hygiene — the whole-tree fold + the discharge are `#assert_axioms`-clean. -/

#assert_axioms all_leaves_verify
#assert_axioms node_seg_is_combine
#assert_axioms recursive_sound_from_nodes
#assert_axioms engineSound_recursive_derived
#assert_axioms honest_node_carrier
#assert_axioms honest_all_leaves_verify
#assert_axioms honest_recursive_sound
#assert_axioms honest_node_seg_is_combine

end Dregg2.Circuit.RecursiveSoundFromNodes
