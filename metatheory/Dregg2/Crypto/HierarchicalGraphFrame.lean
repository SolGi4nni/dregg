/-
# Dregg2.Crypto.HierarchicalGraphFrame — ⚑ THE FRAME CONVERSE of the hierarchical graph commitment.

`Crypto.HierarchicalGraphCommitment` builds the depth-two domain-separated tree over the four
deployed graph slots and proves, for every opening it defines, exactly ONE direction:

    (honest opening).check … = true      (`openLeaf_checks`, `openInterface_checks`,
                                          `openRedex2_checks`, `updateLeaf_checks`)

That is COMPLETENESS.  The theorem the hypergraph VM actually needs is the CONVERSE, and it is the
FRAME theorem:

    an ACCEPTED `AncestorUpdate` at index `u` forces the committed graph to change ONLY at `u`
    — and to change there EXACTLY to the authenticated slot.

Without it, `AncestorUpdate.check` is a check that authenticates one path and says nothing about the
other slots, so a step is only sound if the AIR re-hashes the WHOLE graph — which is exactly what
the deployed `privateGraphRewriteDescriptor` does (`GRAPH_SLOTS := 4`, a Θ(|G|) absorb every step,
112 of its 310 columns permutation staging).  The frame problem there is AVOIDED by smallness, not
solved.  This file proves the converse, at two resolutions, and states what it buys.

## §1 — the PURE STRUCTURAL core, and the named hypothesis it needs

`frame_of_absorbInjective`: if the deployed digest is injective on the three absorb SHAPES the tree
feeds it (`TreeAbsorbInjective`), then an accepted update at `u` gives

    g_before.slots u = update.before   ∧   g_after.slots = Function.update g_before.slots u update.after

— the full frame plus exactness, with NO hypothesis about the semantics and NO escape branch.

⚑ WHAT THE TREE NEEDS, PRECISELY, AND WHAT IT ALREADY HAS.  The converse needs a POSITIONAL binding:
a leaf digest must not be re-usable at another position, and a node digest must not be re-usable with
its children swapped.  The tree HAS both, and the proof shows where: the leaf absorb carries the slot
INDEX (`leafInputs index slot`, `leafInputs_injective` at a FIXED index), and the node absorb carries
its two children IN ORDER (`nodeInputs_injective` as a map out of `Digest8 × Digest8`).  Nothing else
is needed — in particular the peel never compares a LEAF absorb with a PAIR absorb or a PAIR with the
ROOT, so the `LEAF_TAG`/`PAIR_TAG`/`ROOT_TAG` domain separation is NOT what makes the frame work
(it is doing other work: keeping the memo/occurrence layers apart).  There is no missing structural
injectivity: the obstruction to the converse is ENTIRELY the hash, not the layout.

⚠ `TreeAbsorbInjective` is an ASSUMPTION, and at the deployed sponge it is FALSE — the node absorb is
17 limbs wide and the digest is 8 bounded lanes, so `not_treeAbsorbInjective_of_boundedLanes` REFUTES
it for every bounded-lane digest (no pigeonhole hand-waving: an infinite family of node absorbs into a
finite lane space).  So §1 is a statement about the LAYOUT, priced at zero, and it is NOT the deployed
statement.  It is also not vacuous: `exists_treeAbsorbInjective` exhibits a hash satisfying it.

## §2 — the DEPLOYED-RESOLUTION converse: a reduction on the SAME keyed-ROM floor

The exported frame converse is `frame_binds_rom`, in the shape `semanticRoot_binds_rom` already uses,
and for the reason its header records: the old `GraphRewriteHistory` / `HierarchicalGraphCommitment`
`_or_collision` disjunctions were DELETED because `∃ collision` is UNCONDITIONALLY TRUE at a
compressing root, so a `binds ∨ ∃ collision` theorem is satisfiable through the escape branch with the
binding never holding.  This file therefore ships NO such disjunction.  Instead:

  * `frameForgery` is a first-class `RomForgery hgcRomFamily`: the adversary outputs an index, a
    before/after slot, a PATH, and the two graph payloads its two roots commit to; it WINS iff both
    reconstructions check at the sampled role-keyed oracle AND the after-graph is NOT the before-graph
    with slot `u` replaced (the EXACTNESS break — strictly stronger than a frame violation, and
    `frame_violation_wins` proves a frame violation is one of these);
  * `frameExtractComp` is the extractor as an ORACLE PROGRAM: run the forger, then re-walk the path
    layer (8 queries) and both trees (12 queries), and `frameSelect` names the shallowest layer that
    equivocates — a `bindComp`, so the budget is ADDITIVE (`Q + 20`), never answer size;
  * `frame_binds_rom` closes from `romCarrier_binds` (hence `keyedRom_hard`, the birthday bound — a
    THEOREM).  NO floor hypothesis, NO escape branch.

The peel is: the ROOT absorb of the path differs from the before-graph's (a root-role equivocation),
or it agrees and the PAIR absorb differs (a pair-role equivocation through the shared root digest),
or both agree — in which case the path IS the before-graph's honest path, so the after-root commits to
`before-graph with slot u replaced` (`romRootFromPath_honest`), and disagreeing with the after-graph
payload is a root equivocation between two DISTINCT graphs, killed by the tree-walk of
`hgcSelect_wins` (the standalone form of `semanticRoot_binds_rom`'s own extractor argument).

⚑ THE MODELLING STEP IS INHERITED, NOT NEW: the sampled `H : Role × Msg → Fin (2 ^ l)` idealises the
fixed deployed eight-lane digest at an asymptotic width (`RomCarrierSites` header).  Nothing is
claimed about the fixed public hash.

## §3 — what the converse BUYS: Θ(|G|) absorbs → depth+1 absorbs, as a proposition

`update_rehashes_only_ancestor_path`: the root of the updated graph is the digest of the LAST of
`updateAbsorbs`, a THREE-block list determined by `(u, new slot, the two path digests)` alone;
`afterRoot_depends_only_on_path`: two graphs with the same path at `u` produce the same updated root,
so the update reads the rest of the graph NOT AT ALL.  Counted against the full recompute:
`(updateAbsorbs …).length = 3` with `2 ^ (3 - 1) = GRAPH_SLOTS` (depth + 1) versus
`(semanticRootAbsorbs …).length = 7 = 2 * GRAPH_SLOTS - 1`.  `single_slot_step_logarithmic_update`
puts the two together on a REAL rewrite step: a `BoundedOneStep` that touches only slot `u` is a
`RewriteStep` whose committed endpoints are joined by ONE accepted `AncestorUpdate` costing three
absorbs instead of seven.

⚠ HONEST SCOPE.  This is `GRAPH_SLOTS = 4`: `3 = log₂ 4 + 1` and `7 = 2·4 − 1` are INSTANCES of the
depth-vs-size counts, not a theorem over `n`.  The general Θ(log n) statement needs a depth-parametric
tree, which this prototype does not have — that generalisation, and the two-slot (redex-2) composition
where the two updates share a pair node, are named residuals, not claims.  Nothing here touches the
deployed AIR: `privateGraphRewriteDescriptor` still absorbs the whole graph core, so the frame converse
is the PREREQUISITE for shrinking it, not a measurement of a shrunken circuit.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`, no `decide`-discharged Props.
-/
import Dregg2.Crypto.HierarchicalGraphCommitment
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.HierarchicalGraphFrame

open Dregg2.Crypto.PrivateGraphRewrite
open Dregg2.Crypto.GraphRewrite
open Dregg2.Crypto.HierarchicalGraphCommitment

set_option autoImplicit false

/-! ## §0 — four-way case analysis on `Fin 4`, without `decide`. -/

/-- The four deployed slot indices, enumerated. -/
theorem fin4_cases (u : Fin 4) : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by
  have hlt : u.val < 4 := u.isLt
  have h : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 ∨ u.val = 3 := by omega
  rcases h with h | h | h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Or.inl (Fin.ext (by simpa using h)))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext (by simpa using h))))

/-! ## §1 — the PURE STRUCTURAL frame converse.

The hypothesis is about the three absorb SHAPES only, and it is stated per FIXED index / per FIXED
tag: that is exactly the positional binding the tree's own encodings provide. -/

/-- **THE LAYOUT HYPOTHESIS THE FRAME CONVERSE NEEDS.** The digest is injective on the leaf absorbs
at a fixed slot index, and on the node absorbs at a fixed tag (jointly in both children).

⚠ This is an ASSUMPTION about the deployed digest, and `not_treeAbsorbInjective_of_boundedLanes`
proves it FALSE for every bounded-lane digest — the deployed statement is §2's reduction.  What it
isolates is the LAYOUT's contribution: given absorb injectivity, the tree frames with no further
structure (no per-position domain separation is missing). -/
structure TreeAbsorbInjective (H : Hash) : Prop where
  /-- A leaf digest at a FIXED index determines its slot (`leafInputs` carries the index). -/
  leaf : ∀ (i : Fin 4) (s t : HostEdgeSlot), leafDigest H i s = leafDigest H i t → s = t
  /-- A node digest at a FIXED tag determines BOTH children, IN ORDER. -/
  node : ∀ (tag : Int) (x y x' y' : Digest8),
    nodeDigest H tag x y = nodeDigest H tag x' y' → x = x' ∧ y = y'

/-- **THE PATH PEEL.** A reconstruction that hits the committed root forces the authenticated leaf to
be the graph's own slot at `u` AND the offered path to be the graph's own path at `u`.  This is the
whole structural content of the converse: two peels (root absorb, then the pair absorb), where the
child ORDER pins which side of the pair `u` sits on and the leaf INDEX pins which leaf it is. -/
theorem path_peel {H : Hash} (hinj : TreeAbsorbInjective H) (u : Fin 4) (s : HostEdgeSlot)
    (p : Path4) (g : BoundedGraph)
    (h : rootFromPath H u (leafDigest H u s) p = semanticRoot H g) :
    s = g.slots u ∧ p = pathFor H g u := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl
  · have h' : nodeDigest H ROOT_TAG
        (nodeDigest H PAIR_TAG (leafDigest H 0 s) p.siblingLeaf) p.siblingPair
        = nodeDigest H ROOT_TAG (leftPair H g) (rightPair H g) := h
    obtain ⟨hnode, hpair⟩ := hinj.node _ _ _ _ _ h'
    have hnode' : nodeDigest H PAIR_TAG (leafDigest H 0 s) p.siblingLeaf
        = nodeDigest H PAIR_TAG (leafDigest H 0 (g.slots 0)) (leafDigest H 1 (g.slots 1)) := hnode
    obtain ⟨hleaf, hsib⟩ := hinj.node _ _ _ _ _ hnode'
    refine ⟨hinj.leaf 0 _ _ hleaf, ?_⟩
    show p = (⟨leafDigest H 1 (g.slots 1), rightPair H g⟩ : Path4)
    calc p = (⟨p.siblingLeaf, p.siblingPair⟩ : Path4) := rfl
      _ = ⟨leafDigest H 1 (g.slots 1), rightPair H g⟩ := by rw [hsib, hpair]
  · have h' : nodeDigest H ROOT_TAG
        (nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H 1 s)) p.siblingPair
        = nodeDigest H ROOT_TAG (leftPair H g) (rightPair H g) := h
    obtain ⟨hnode, hpair⟩ := hinj.node _ _ _ _ _ h'
    have hnode' : nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H 1 s)
        = nodeDigest H PAIR_TAG (leafDigest H 0 (g.slots 0)) (leafDigest H 1 (g.slots 1)) := hnode
    obtain ⟨hsib, hleaf⟩ := hinj.node _ _ _ _ _ hnode'
    refine ⟨hinj.leaf 1 _ _ hleaf, ?_⟩
    show p = (⟨leafDigest H 0 (g.slots 0), rightPair H g⟩ : Path4)
    calc p = (⟨p.siblingLeaf, p.siblingPair⟩ : Path4) := rfl
      _ = ⟨leafDigest H 0 (g.slots 0), rightPair H g⟩ := by rw [hsib, hpair]
  · have h' : nodeDigest H ROOT_TAG p.siblingPair
        (nodeDigest H PAIR_TAG (leafDigest H 2 s) p.siblingLeaf)
        = nodeDigest H ROOT_TAG (leftPair H g) (rightPair H g) := h
    obtain ⟨hpair, hnode⟩ := hinj.node _ _ _ _ _ h'
    have hnode' : nodeDigest H PAIR_TAG (leafDigest H 2 s) p.siblingLeaf
        = nodeDigest H PAIR_TAG (leafDigest H 2 (g.slots 2)) (leafDigest H 3 (g.slots 3)) := hnode
    obtain ⟨hleaf, hsib⟩ := hinj.node _ _ _ _ _ hnode'
    refine ⟨hinj.leaf 2 _ _ hleaf, ?_⟩
    show p = (⟨leafDigest H 3 (g.slots 3), leftPair H g⟩ : Path4)
    calc p = (⟨p.siblingLeaf, p.siblingPair⟩ : Path4) := rfl
      _ = ⟨leafDigest H 3 (g.slots 3), leftPair H g⟩ := by rw [hsib, hpair]
  · have h' : nodeDigest H ROOT_TAG p.siblingPair
        (nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H 3 s))
        = nodeDigest H ROOT_TAG (leftPair H g) (rightPair H g) := h
    obtain ⟨hpair, hnode⟩ := hinj.node _ _ _ _ _ h'
    have hnode' : nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H 3 s)
        = nodeDigest H PAIR_TAG (leafDigest H 2 (g.slots 2)) (leafDigest H 3 (g.slots 3)) := hnode
    obtain ⟨hsib, hleaf⟩ := hinj.node _ _ _ _ _ hnode'
    refine ⟨hinj.leaf 3 _ _ hleaf, ?_⟩
    show p = (⟨leafDigest H 2 (g.slots 2), leftPair H g⟩ : Path4)
    calc p = (⟨p.siblingLeaf, p.siblingPair⟩ : Path4) := rfl
      _ = ⟨leafDigest H 2 (g.slots 2), leftPair H g⟩ := by rw [hsib, hpair]

/-- **OFF-INDEX AGREEMENT.** Two graphs whose paths at `u` coincide agree at every OTHER slot: the
sibling leaf pins the co-leaf of `u`'s pair, and the sibling pair digest pins the other two leaves. -/
theorem slots_agree_off_index {H : Hash} (hinj : TreeAbsorbInjective H) (u : Fin 4)
    (g₁ g₂ : BoundedGraph) (hpp : pathFor H g₁ u = pathFor H g₂ u) :
    ∀ i, i ≠ u → g₁.slots i = g₂.slots i := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl
  · have hsl : leafDigest H 1 (g₁.slots 1) = leafDigest H 1 (g₂.slots 1) :=
      congrArg Path4.siblingLeaf hpp
    have hsp : nodeDigest H PAIR_TAG (leafDigest H 2 (g₁.slots 2)) (leafDigest H 3 (g₁.slots 3))
        = nodeDigest H PAIR_TAG (leafDigest H 2 (g₂.slots 2)) (leafDigest H 3 (g₂.slots 3)) :=
      congrArg Path4.siblingPair hpp
    obtain ⟨h2, h3⟩ := hinj.node _ _ _ _ _ hsp
    intro i hi
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · exact hinj.leaf 1 _ _ hsl
    · exact hinj.leaf 2 _ _ h2
    · exact hinj.leaf 3 _ _ h3
  · have hsl : leafDigest H 0 (g₁.slots 0) = leafDigest H 0 (g₂.slots 0) :=
      congrArg Path4.siblingLeaf hpp
    have hsp : nodeDigest H PAIR_TAG (leafDigest H 2 (g₁.slots 2)) (leafDigest H 3 (g₁.slots 3))
        = nodeDigest H PAIR_TAG (leafDigest H 2 (g₂.slots 2)) (leafDigest H 3 (g₂.slots 3)) :=
      congrArg Path4.siblingPair hpp
    obtain ⟨h2, h3⟩ := hinj.node _ _ _ _ _ hsp
    intro i hi
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact hinj.leaf 0 _ _ hsl
    · exact absurd rfl hi
    · exact hinj.leaf 2 _ _ h2
    · exact hinj.leaf 3 _ _ h3
  · have hsl : leafDigest H 3 (g₁.slots 3) = leafDigest H 3 (g₂.slots 3) :=
      congrArg Path4.siblingLeaf hpp
    have hsp : nodeDigest H PAIR_TAG (leafDigest H 0 (g₁.slots 0)) (leafDigest H 1 (g₁.slots 1))
        = nodeDigest H PAIR_TAG (leafDigest H 0 (g₂.slots 0)) (leafDigest H 1 (g₂.slots 1)) :=
      congrArg Path4.siblingPair hpp
    obtain ⟨h0, h1⟩ := hinj.node _ _ _ _ _ hsp
    intro i hi
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact hinj.leaf 0 _ _ h0
    · exact hinj.leaf 1 _ _ h1
    · exact absurd rfl hi
    · exact hinj.leaf 3 _ _ hsl
  · have hsl : leafDigest H 2 (g₁.slots 2) = leafDigest H 2 (g₂.slots 2) :=
      congrArg Path4.siblingLeaf hpp
    have hsp : nodeDigest H PAIR_TAG (leafDigest H 0 (g₁.slots 0)) (leafDigest H 1 (g₁.slots 1))
        = nodeDigest H PAIR_TAG (leafDigest H 0 (g₂.slots 0)) (leafDigest H 1 (g₂.slots 1)) :=
      congrArg Path4.siblingPair hpp
    obtain ⟨h0, h1⟩ := hinj.node _ _ _ _ _ hsp
    intro i hi
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact hinj.leaf 0 _ _ h0
    · exact hinj.leaf 1 _ _ h1
    · exact hinj.leaf 2 _ _ hsl
    · exact absurd rfl hi

/-- **⚑⚑ THE FRAME CONVERSE, PURE CORE.** An ACCEPTED `AncestorUpdate` at index `u` between two
committed graphs forces the before-graph's slot at `u` to be the authenticated `before`, and the
after-graph to be the before-graph with slot `u` replaced by the authenticated `after` — hence
unchanged at every other slot.  The converse of `updateLeaf_checks`, at zero price under the LAYOUT
hypothesis. -/
theorem frame_of_absorbInjective {H : Hash} (hinj : TreeAbsorbInjective H)
    (g₁ g₂ : BoundedGraph) (upd : AncestorUpdate)
    (hcheck : upd.check H (semanticRoot H g₁) (semanticRoot H g₂) = true) :
    g₁.slots upd.index = upd.before ∧
      g₂.slots = Function.update g₁.slots upd.index upd.after := by
  rw [AncestorUpdate.check, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨_, _⟩, hb⟩, ha⟩ := hcheck
  have h1 : rootFromPath H upd.index (leafDigest H upd.index upd.before) upd.path
      = semanticRoot H g₁ := digestFields_injective (of_decide_eq_true hb)
  have h2 : rootFromPath H upd.index (leafDigest H upd.index upd.after) upd.path
      = semanticRoot H g₂ := digestFields_injective (of_decide_eq_true ha)
  obtain ⟨hs1, hp1⟩ := path_peel hinj upd.index upd.before upd.path g₁ h1
  obtain ⟨hs2, hp2⟩ := path_peel hinj upd.index upd.after upd.path g₂ h2
  have hoff := slots_agree_off_index hinj upd.index g₁ g₂ (hp1.symm.trans hp2)
  refine ⟨hs1.symm, ?_⟩
  funext i
  by_cases hi : i = upd.index
  · subst hi
    simpa using hs2.symm
  · simpa [Function.update, hi] using (hoff i hi).symm

/-- **THE FRAME CONVERSE AT GRAPH GRANULARITY.** Packaged as the very `replaceSlot` the completeness
direction uses: the accepted update's after-graph IS `replaceSlot` of the before-graph.  (`hcanonical`
is derivable from the check's own `canonicalSlotB update.after` tooth; it is an argument only so the
`replaceSlot` term in the statement stays readable.) -/
theorem afterGraph_eq_replaceSlot {H : Hash} (hinj : TreeAbsorbInjective H)
    (g₁ g₂ : BoundedGraph) (upd : AncestorUpdate)
    (hcanonical : upd.after.canonicalPadding)
    (hcheck : upd.check H (semanticRoot H g₁) (semanticRoot H g₂) = true) :
    g₂ = replaceSlot g₁ upd.index upd.after hcanonical := by
  obtain ⟨_, hslots⟩ := frame_of_absorbInjective hinj g₁ g₂ upd hcheck
  cases g₁ with
  | mk s₁ c₁ =>
    cases g₂ with
    | mk s₂ c₂ =>
      simp only at hslots
      subst hslots
      rfl

/-! ### §1 teeth — the layout hypothesis is INHABITED, and FALSE at the deployed digest. -/

/-- A lossless reference digest: absorb the limb list into ONE unbounded lane.  Only a witness that
`TreeAbsorbInjective` is satisfiable — it is not a hash. -/
def injHash (xs : List Int) : List Int := [((Encodable.encode xs : ℕ) : Int)]

theorem injHash_digest8_injective : Function.Injective (digest8 injHash) := by
  intro a b h
  have h0 : digest8 injHash a 0 = digest8 injHash b 0 := congrFun h 0
  have h1 : ((Encodable.encode a : ℕ) : Int) = ((Encodable.encode b : ℕ) : Int) := h0
  exact Encodable.encode_injective (by exact_mod_cast h1)

/-- Absorb injectivity follows from injectivity of the digest, through the tree's OWN encoding
injectivities (`leafInputs_injective` at a fixed index, `nodeInputs_injective` at a fixed tag). -/
theorem treeAbsorbInjective_of_digest8_injective {H : Hash}
    (h : Function.Injective (digest8 H)) : TreeAbsorbInjective H where
  leaf := fun i s t hst => leafInputs_injective i (h hst)
  node := fun tag x y x' y' hxy => by
    have h2 : (fun p : Digest8 × Digest8 => nodeInputs tag p.1 p.2) (x, y)
        = (fun p : Digest8 × Digest8 => nodeInputs tag p.1 p.2) (x', y') := h hxy
    have h3 : ((x, y) : Digest8 × Digest8) = (x', y') := nodeInputs_injective tag h2
    exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

/-- **(TOOTH — §1 is not vacuous.)** Some digest satisfies the layout hypothesis. -/
theorem exists_treeAbsorbInjective : ∃ H : Hash, TreeAbsorbInjective H :=
  ⟨injHash, treeAbsorbInjective_of_digest8_injective injHash_digest8_injective⟩

/-- **(TOOTH — §1's hypothesis is FALSE at the deployed digest, so §1 is NOT the deployed claim.)**
Every digest whose lanes are nonnegative and bounded fails absorb injectivity: the node absorbs
`nodeInputs ROOT_TAG (const n) (const n)` form an INFINITE family, the lane space is FINITE, so two
distinct node absorbs collide and `node` is refuted.  No pigeonhole hand-wave — the counting is
`Finite.exists_ne_map_eq_of_infinite`. -/
theorem not_treeAbsorbInjective_of_boundedLanes (H : Hash) (B : ℕ)
    (hlo : ∀ (xs : List Int) (i : Fin 8), 0 ≤ digest8 H xs i)
    (hhi : ∀ (xs : List Int) (i : Fin 8), digest8 H xs i < (B : Int)) :
    ¬ TreeAbsorbInjective H := by
  intro hinj
  have hB : 0 < B := by
    have h0 := hlo [] 0
    have h1 := hhi [] 0
    omega
  let const : ℕ → Digest8 := fun n => fun _ => (n : Int)
  let φ : ℕ → (Fin 8 → Fin B) := fun n i =>
    ⟨(nodeDigest H ROOT_TAG (const n) (const n) i).toNat, by
      have h1 : nodeDigest H ROOT_TAG (const n) (const n) i < (B : Int) :=
        hhi (nodeInputs ROOT_TAG (const n) (const n)) i
      omega⟩
  obtain ⟨n, m, hnm, hφ⟩ := Finite.exists_ne_map_eq_of_infinite φ
  have hdig : nodeDigest H ROOT_TAG (const n) (const n)
      = nodeDigest H ROOT_TAG (const m) (const m) := by
    funext i
    have hi : ((nodeDigest H ROOT_TAG (const n) (const n) i).toNat : ℕ)
        = ((nodeDigest H ROOT_TAG (const m) (const m) i).toNat : ℕ) :=
      congrArg Fin.val (congrFun hφ i)
    have hn : 0 ≤ nodeDigest H ROOT_TAG (const n) (const n) i :=
      hlo (nodeInputs ROOT_TAG (const n) (const n)) i
    have hm : 0 ≤ nodeDigest H ROOT_TAG (const m) (const m) i :=
      hlo (nodeInputs ROOT_TAG (const m) (const m)) i
    omega
  obtain ⟨hx, _⟩ := hinj.node _ _ _ _ _ hdig
  have : (n : Int) = (m : Int) := congrFun hx 0
  exact hnm (by exact_mod_cast this)

/-! ## §2 — the frame converse at the SAMPLED role-keyed oracle: a REDUCTION on the PROVED floor.

Same family, same carrier, same floor as `semanticRoot_binds_rom`.  Nothing new is assumed; the only
new content is the peel and the extractor. -/

section RomFrame

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomCarrierSites

/-- The ideal digest space. -/
abbrev RomDig (l : ℕ) : Type := Fin (2 ^ l)

/-- One leaf absorb at the sampled oracle — the index is IN the message (positional binding). -/
def romLeaf (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (i : Fin 4) (s : SlotEnc) : RomDig l :=
  H (hgcLeafRole, Sum.inl (i, s))

/-- One pair-node absorb at the sampled oracle, children IN ORDER. -/
def romPairOf (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (q : RomDig l × RomDig l) : RomDig l :=
  H (hgcPairRole, Sum.inr q)

/-- The root absorb at the sampled oracle. -/
def romRootOf (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (q : RomDig l × RomDig l) : RomDig l :=
  H (hgcRootRole, Sum.inr q)

/-- The left pair digest of a payload. -/
def romLeftPair (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : GraphSlots) : RomDig l :=
  romPairOf l H (romLeaf l H 0 (g 0), romLeaf l H 1 (g 1))

/-- The right pair digest of a payload. -/
def romRightPair (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : GraphSlots) : RomDig l :=
  romPairOf l H (romLeaf l H 2 (g 2), romLeaf l H 3 (g 3))

/-- `hgcRomRoot` in the vocabulary of this section — the same absorb schedule, unchanged. -/
theorem hgcRomRoot_eq (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : GraphSlots) :
    hgcRomRoot l H g = romRootOf l H (romLeftPair l H g, romRightPair l H g) := rfl

/-- The ROM face of `Path4`: the sibling leaf digest and the sibling pair digest. -/
abbrev RomPath (l : ℕ) : Type := RomDig l × RomDig l

/-- The ROM face of `pathFor`. -/
def romPathFor (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : GraphSlots) (u : Fin 4) :
    RomPath l :=
  match u.val with
  | 0 => (romLeaf l H 1 (g 1), romRightPair l H g)
  | 1 => (romLeaf l H 0 (g 0), romRightPair l H g)
  | 2 => (romLeaf l H 3 (g 3), romLeftPair l H g)
  | _ => (romLeaf l H 2 (g 2), romLeftPair l H g)

/-- **THE PAIR ABSORB OF A PATH RECONSTRUCTION** — the authenticated leaf and the sibling leaf, in
the order `u`'s parity dictates. -/
def framePairBlock (l : ℕ) (u : Fin 4) (leaf : RomDig l) (p : RomPath l) : RomDig l × RomDig l :=
  if u.val % 2 = 0 then (leaf, p.1) else (p.1, leaf)

/-- **THE ROOT ABSORB OF A PATH RECONSTRUCTION** — the reconstructed pair digest and the sibling pair
digest, in the order `u`'s half dictates. -/
def frameRootBlock (l : ℕ) (u : Fin 4) (pathPair : RomDig l) (p : RomPath l) :
    RomDig l × RomDig l :=
  if u.val < 2 then (pathPair, p.2) else (p.2, pathPair)

/-- **THE COMMITTED PAIR ABSORB `u` SITS UNDER** — the two leaf digests of `u`'s own pair. -/
def frameGraphPairBlock (l : ℕ) (u : Fin 4) (b0 b1 b2 b3 : RomDig l) : RomDig l × RomDig l :=
  if u.val < 2 then (b0, b1) else (b2, b3)

/-- The ROM face of `rootFromPath`: three absorbs — the leaf, `u`'s pair, the root. -/
def romRootFromPath (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (u : Fin 4) (leaf : RomDig l)
    (p : RomPath l) : RomDig l :=
  romRootOf l H (frameRootBlock l u (romPairOf l H (framePairBlock l u leaf p)) p)

/-- The ROM face of `replaceSlot`. -/
def romReplace (g : GraphSlots) (u : Fin 4) (s : SlotEnc) : GraphSlots :=
  Function.update g u s

/-- **THE HONEST PATH RECONSTRUCTS THE UPDATED ROOT** — the ROM face of
`pathFor_replaceSlot ∘ pathFor_reconstructs`: reconstructing along the OLD path with a NEW leaf is
exactly the root of the graph with that ONE slot replaced. -/
theorem romRootFromPath_honest (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (g : GraphSlots)
    (u : Fin 4) (s : SlotEnc) :
    romRootFromPath l H u (romLeaf l H u s) (romPathFor l H g u)
      = hgcRomRoot l H (romReplace g u s) := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl <;>
    simp [romRootFromPath, romPathFor, romReplace, hgcRomRoot, romRootOf, romPairOf, romLeaf,
      romLeftPair, romRightPair, framePairBlock, frameRootBlock]

/-! ### The forgery, the extractor, and the binding. -/

/-- **WHAT A FRAME FORGER OUTPUTS** — an index, the authenticated before/after slots, a PATH of its
own choosing, and the two graph payloads its before/after roots commit to. -/
structure FrameAns (l : ℕ) where
  /-- The authenticated slot index. -/
  index : Fin 4
  /-- The authenticated old slot. -/
  before : SlotEnc
  /-- The authenticated new slot. -/
  after : SlotEnc
  /-- The offered path — adversarial, NOT assumed honest. -/
  path : RomPath l
  /-- The payload the before-root commits to. -/
  beforeGraph : GraphSlots
  /-- The payload the after-root commits to. -/
  afterGraph : GraphSlots

/-- **THE FRAME FORGERY** — the adversary wins iff BOTH reconstructions check at the sampled oracle
and the after-graph is NOT the before-graph with slot `index` replaced by `after`.  The break is IN
the win relation: it is exactly "an accepted ancestor update that did something else". -/
def frameForgery : RomForgery hgcRomFamily where
  Ans := FrameAns
  wins := fun l H a =>
    romRootFromPath l H a.index (romLeaf l H a.index a.before) a.path = hgcRomRoot l H a.beforeGraph
      ∧ romRootFromPath l H a.index (romLeaf l H a.index a.after) a.path
          = hgcRomRoot l H a.afterGraph
      ∧ a.afterGraph ≠ romReplace a.beforeGraph a.index a.after
  winsDec := fun _ _ _ => by infer_instance

/-- The frame break game. -/
abbrev frameBreakGame : Game := frameForgery.game

/-- **A FRAME VIOLATION IS A WIN** — the weaker break (some slot OFF the authenticated index moved)
is dominated by the exactness break the game states, so the binding covers it. -/
theorem frame_violation_wins (l : ℕ) (H : frameBreakGame.Inst l) (a : FrameAns l)
    (hb : romRootFromPath l H a.index (romLeaf l H a.index a.before) a.path
      = hgcRomRoot l H a.beforeGraph)
    (haf : romRootFromPath l H a.index (romLeaf l H a.index a.after) a.path
      = hgcRomRoot l H a.afterGraph)
    (i : Fin 4) (hi : i ≠ a.index) (hne : a.beforeGraph i ≠ a.afterGraph i) :
    frameBreakGame.wins l H a := by
  refine ⟨hb, haf, fun hEq => hne ?_⟩
  have := congrFun hEq i
  simpa [romReplace, Function.update, hi] using this.symm

/-- **THE ROOT-EQUIVOCATION TOOTH, STANDALONE** — the tree walk of `semanticRoot_binds_rom`, stated
as a lemma about `hgcSelect`: two DISTINCT payloads with EQUAL tree roots make the re-walked
selection a win of the tree's single carrier.  (Same argument as
`HierarchicalGraphCommitment.semanticRoot_binds_rom`'s final peel; factored out here because the frame
reduction consumes it at an interior branch.) -/
theorem hgcSelect_wins (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (a : GraphSlots × GraphSlots)
    (hne : a.1 ≠ a.2) (heq : hgcRomRoot l H a.1 = hgcRomRoot l H a.2) :
    (romCarrierGame hgcRomFamily hgcRomCarrier).wins l H
      (hgcSelect l a
        (romLeaf l H 0 (a.1 0)) (romLeaf l H 1 (a.1 1))
        (romLeaf l H 2 (a.1 2)) (romLeaf l H 3 (a.1 3))
        (romLeaf l H 0 (a.2 0)) (romLeaf l H 1 (a.2 1))
        (romLeaf l H 2 (a.2 2)) (romLeaf l H 3 (a.2 3))
        (romLeftPair l H a.1) (romRightPair l H a.1)
        (romLeftPair l H a.2) (romRightPair l H a.2)) := by
  unfold hgcSelect
  split_ifs with hRoot hL hR h0 h1 h2
  · exact ⟨fun hc => hRoot (Sum.inr_injective hc), heq⟩
  · exact ⟨fun hc => hL (Sum.inr_injective hc), congrArg Prod.fst (not_not.mp hRoot)⟩
  · exact ⟨fun hc => hR (Sum.inr_injective hc), congrArg Prod.snd (not_not.mp hRoot)⟩
  · exact ⟨fun hc => h0 (congrArg Prod.snd (Sum.inl_injective hc)),
      congrArg Prod.fst (not_not.mp hL)⟩
  · exact ⟨fun hc => h1 (congrArg Prod.snd (Sum.inl_injective hc)),
      congrArg Prod.snd (not_not.mp hL)⟩
  · exact ⟨fun hc => h2 (congrArg Prod.snd (Sum.inl_injective hc)),
      congrArg Prod.fst (not_not.mp hR)⟩
  · have h3 : a.1 3 ≠ a.2 3 := by
      intro hc
      apply hne
      funext i
      fin_cases i
      · exact not_not.mp h0
      · exact not_not.mp h1
      · exact not_not.mp h2
      · exact hc
    exact ⟨fun hc => h3 (congrArg Prod.snd (Sum.inl_injective hc)),
      congrArg Prod.snd (not_not.mp hR)⟩

/-- **THE FRAME SELECTION** — from the forger's answer and the re-walked digests, name the shallowest
layer that equivocates: the ROOT absorb of the offered path against the committed one, then `u`'s PAIR
absorb, and otherwise (the path IS honest) the root equivocation between the correctly-updated payload
and the offered after-payload.  Pure: every query was already paid by `frameExtractComp`. -/
def frameSelect (l : ℕ) (a : FrameAns l)
    (b0 b1 b2 b3 bL bR Lb pathPair : RomDig l)
    (d0 d1 d2 d3 rL rR c0 c1 c2 c3 cL cR : RomDig l) :
    hgcRomCarrier.Ctx l × hgcRomCarrier.Val l × hgcRomCarrier.Val l :=
  if frameRootBlock l a.index pathPair a.path ≠ (bL, bR) then
    ((hgcRootRole, ()), Sum.inr (frameRootBlock l a.index pathPair a.path), Sum.inr (bL, bR))
  else if framePairBlock l a.index Lb a.path ≠ frameGraphPairBlock l a.index b0 b1 b2 b3 then
    ((hgcPairRole, ()), Sum.inr (framePairBlock l a.index Lb a.path),
      Sum.inr (frameGraphPairBlock l a.index b0 b1 b2 b3))
  else
    hgcSelect l (romReplace a.beforeGraph a.index a.after, a.afterGraph)
      d0 d1 d2 d3 c0 c1 c2 c3 rL rR cL cR

/-- **⚑ WIN-PRESERVATION — the whole mathematical content of the frame converse.** A frame forgery at
the sampled oracle makes the selected triple a genuine equivocation of the tree's carrier. -/
theorem frameSelect_wins (l : ℕ) (H : HgcRole × HgcRomMsg l → RomDig l) (a : FrameAns l)
    (hb : romRootFromPath l H a.index (romLeaf l H a.index a.before) a.path
      = hgcRomRoot l H a.beforeGraph)
    (haf : romRootFromPath l H a.index (romLeaf l H a.index a.after) a.path
      = hgcRomRoot l H a.afterGraph)
    (hbreak : a.afterGraph ≠ romReplace a.beforeGraph a.index a.after) :
    (romCarrierGame hgcRomFamily hgcRomCarrier).wins l H
      (frameSelect l a
        (romLeaf l H 0 (a.beforeGraph 0)) (romLeaf l H 1 (a.beforeGraph 1))
        (romLeaf l H 2 (a.beforeGraph 2)) (romLeaf l H 3 (a.beforeGraph 3))
        (romLeftPair l H a.beforeGraph) (romRightPair l H a.beforeGraph)
        (romLeaf l H a.index a.before)
        (romPairOf l H (framePairBlock l a.index (romLeaf l H a.index a.before) a.path))
        (romLeaf l H 0 (romReplace a.beforeGraph a.index a.after 0))
        (romLeaf l H 1 (romReplace a.beforeGraph a.index a.after 1))
        (romLeaf l H 2 (romReplace a.beforeGraph a.index a.after 2))
        (romLeaf l H 3 (romReplace a.beforeGraph a.index a.after 3))
        (romLeftPair l H (romReplace a.beforeGraph a.index a.after))
        (romRightPair l H (romReplace a.beforeGraph a.index a.after))
        (romLeaf l H 0 (a.afterGraph 0)) (romLeaf l H 1 (a.afterGraph 1))
        (romLeaf l H 2 (a.afterGraph 2)) (romLeaf l H 3 (a.afterGraph 3))
        (romLeftPair l H a.afterGraph) (romRightPair l H a.afterGraph)) := by
  obtain ⟨u, before, after, path, bg, ag⟩ := a
  simp only [frameSelect]
  rcases fin4_cases u with rfl | rfl | rfl | rfl
  · split_ifs with hroot hpair
    · exact ⟨fun hc => hroot (Sum.inr_injective hc), hb⟩
    · have hr : ((romPairOf l H (framePairBlock l 0 (romLeaf l H 0 before) path), path.2)
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      exact ⟨fun hc => hpair (Sum.inr_injective hc), congrArg Prod.fst hr⟩
    · have hr : ((romPairOf l H (framePairBlock l 0 (romLeaf l H 0 before) path), path.2)
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      have hp : ((romLeaf l H 0 before, path.1) : RomDig l × RomDig l)
          = (romLeaf l H 0 (bg 0), romLeaf l H 1 (bg 1)) := not_not.mp hpair
      have hpath : path = romPathFor l H bg 0 := by
        have e1 : path.1 = romLeaf l H 1 (bg 1) := congrArg Prod.snd hp
        have e2 : path.2 = romRightPair l H bg := congrArg Prod.snd hr
        show path = (romLeaf l H 1 (bg 1), romRightPair l H bg)
        rw [← e1, ← e2]
      have heq : hgcRomRoot l H (romReplace bg 0 after) = hgcRomRoot l H ag := by
        rw [← romRootFromPath_honest l H bg 0 after, ← hpath]; exact haf
      exact hgcSelect_wins l H (romReplace bg 0 after, ag) (Ne.symm hbreak) heq
  · split_ifs with hroot hpair
    · exact ⟨fun hc => hroot (Sum.inr_injective hc), hb⟩
    · have hr : ((romPairOf l H (framePairBlock l 1 (romLeaf l H 1 before) path), path.2)
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      exact ⟨fun hc => hpair (Sum.inr_injective hc), congrArg Prod.fst hr⟩
    · have hr : ((romPairOf l H (framePairBlock l 1 (romLeaf l H 1 before) path), path.2)
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      have hp : ((path.1, romLeaf l H 1 before) : RomDig l × RomDig l)
          = (romLeaf l H 0 (bg 0), romLeaf l H 1 (bg 1)) := not_not.mp hpair
      have hpath : path = romPathFor l H bg 1 := by
        have e1 : path.1 = romLeaf l H 0 (bg 0) := congrArg Prod.fst hp
        have e2 : path.2 = romRightPair l H bg := congrArg Prod.snd hr
        show path = (romLeaf l H 0 (bg 0), romRightPair l H bg)
        rw [← e1, ← e2]
      have heq : hgcRomRoot l H (romReplace bg 1 after) = hgcRomRoot l H ag := by
        rw [← romRootFromPath_honest l H bg 1 after, ← hpath]; exact haf
      exact hgcSelect_wins l H (romReplace bg 1 after, ag) (Ne.symm hbreak) heq
  · split_ifs with hroot hpair
    · exact ⟨fun hc => hroot (Sum.inr_injective hc), hb⟩
    · have hr : ((path.2, romPairOf l H (framePairBlock l 2 (romLeaf l H 2 before) path))
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      exact ⟨fun hc => hpair (Sum.inr_injective hc), congrArg Prod.snd hr⟩
    · have hr : ((path.2, romPairOf l H (framePairBlock l 2 (romLeaf l H 2 before) path))
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      have hp : ((romLeaf l H 2 before, path.1) : RomDig l × RomDig l)
          = (romLeaf l H 2 (bg 2), romLeaf l H 3 (bg 3)) := not_not.mp hpair
      have hpath : path = romPathFor l H bg 2 := by
        have e1 : path.1 = romLeaf l H 3 (bg 3) := congrArg Prod.snd hp
        have e2 : path.2 = romLeftPair l H bg := congrArg Prod.fst hr
        show path = (romLeaf l H 3 (bg 3), romLeftPair l H bg)
        rw [← e1, ← e2]
      have heq : hgcRomRoot l H (romReplace bg 2 after) = hgcRomRoot l H ag := by
        rw [← romRootFromPath_honest l H bg 2 after, ← hpath]; exact haf
      exact hgcSelect_wins l H (romReplace bg 2 after, ag) (Ne.symm hbreak) heq
  · split_ifs with hroot hpair
    · exact ⟨fun hc => hroot (Sum.inr_injective hc), hb⟩
    · have hr : ((path.2, romPairOf l H (framePairBlock l 3 (romLeaf l H 3 before) path))
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      exact ⟨fun hc => hpair (Sum.inr_injective hc), congrArg Prod.snd hr⟩
    · have hr : ((path.2, romPairOf l H (framePairBlock l 3 (romLeaf l H 3 before) path))
          : RomDig l × RomDig l) = (romLeftPair l H bg, romRightPair l H bg) := not_not.mp hroot
      have hp : ((path.1, romLeaf l H 3 before) : RomDig l × RomDig l)
          = (romLeaf l H 2 (bg 2), romLeaf l H 3 (bg 3)) := not_not.mp hpair
      have hpath : path = romPathFor l H bg 3 := by
        have e1 : path.1 = romLeaf l H 2 (bg 2) := congrArg Prod.fst hp
        have e2 : path.2 = romLeftPair l H bg := congrArg Prod.fst hr
        show path = (romLeaf l H 2 (bg 2), romLeftPair l H bg)
        rw [← e1, ← e2]
      have heq : hgcRomRoot l H (romReplace bg 3 after) = hgcRomRoot l H ag := by
        rw [← romRootFromPath_honest l H bg 3 after, ← hpath]; exact haf
      exact hgcSelect_wins l H (romReplace bg 3 after, ag) (Ne.symm hbreak) heq

/-- **THE EXTRACTOR, AS AN ORACLE PROGRAM** — run the forger, re-walk the path layer (four committed
leaves, two committed pairs, the authenticated leaf, the path's pair absorb) and both trees (eight
leaves, four pairs), then select the equivocating layer.  `bindComp` keeps the accounting additive: a
`Q`-query forger yields a `Q + 20`-query carrier equivocator. -/
def frameExtractComp
    (M : ∀ l, OracleComp (hgcRomFamily.toRomFamily.D l) (hgcRomFamily.toRomFamily.R l)
      (frameForgery.Ans l)) :
    RomCarrierComp hgcRomFamily hgcRomCarrier :=
  fun l => OracleComp.bindComp (M l) (fun a =>
    OracleComp.query (hgcLeafRole, Sum.inl (0, a.beforeGraph 0)) (fun b0 =>
    OracleComp.query (hgcLeafRole, Sum.inl (1, a.beforeGraph 1)) (fun b1 =>
    OracleComp.query (hgcLeafRole, Sum.inl (2, a.beforeGraph 2)) (fun b2 =>
    OracleComp.query (hgcLeafRole, Sum.inl (3, a.beforeGraph 3)) (fun b3 =>
    OracleComp.query (hgcPairRole, Sum.inr (b0, b1)) (fun bL =>
    OracleComp.query (hgcPairRole, Sum.inr (b2, b3)) (fun bR =>
    OracleComp.query (hgcLeafRole, Sum.inl (a.index, a.before)) (fun Lb =>
    OracleComp.query (hgcPairRole, Sum.inr (framePairBlock l a.index Lb a.path)) (fun pathPair =>
    OracleComp.query (hgcLeafRole, Sum.inl (0, romReplace a.beforeGraph a.index a.after 0))
      (fun d0 =>
    OracleComp.query (hgcLeafRole, Sum.inl (1, romReplace a.beforeGraph a.index a.after 1))
      (fun d1 =>
    OracleComp.query (hgcLeafRole, Sum.inl (2, romReplace a.beforeGraph a.index a.after 2))
      (fun d2 =>
    OracleComp.query (hgcLeafRole, Sum.inl (3, romReplace a.beforeGraph a.index a.after 3))
      (fun d3 =>
    OracleComp.query (hgcPairRole, Sum.inr (d0, d1)) (fun rL =>
    OracleComp.query (hgcPairRole, Sum.inr (d2, d3)) (fun rR =>
    OracleComp.query (hgcLeafRole, Sum.inl (0, a.afterGraph 0)) (fun c0 =>
    OracleComp.query (hgcLeafRole, Sum.inl (1, a.afterGraph 1)) (fun c1 =>
    OracleComp.query (hgcLeafRole, Sum.inl (2, a.afterGraph 2)) (fun c2 =>
    OracleComp.query (hgcLeafRole, Sum.inl (3, a.afterGraph 3)) (fun c3 =>
    OracleComp.query (hgcPairRole, Sum.inr (c0, c1)) (fun cL =>
    OracleComp.query (hgcPairRole, Sum.inr (c2, c3)) (fun cR =>
    OracleComp.pure (frameSelect l a b0 b1 b2 b3 bL bR Lb pathPair
      d0 d1 d2 d3 rL rR c0 c1 c2 c3 cL cR))))))))))))))))))))))

/-- **⚑⚑ THE FRAME CONVERSE, DISCHARGED ON THE PROVED KEYED-ROM FLOOR.**

Every query-bounded forger that produces an ACCEPTED ancestor update whose after-graph is NOT the
before-graph with the authenticated slot replaced has NEGLIGIBLE advantage.  Equivalently: except with
negligible probability, an accepted `AncestorUpdate` at index `u` changes the committed graph ONLY at
`u`, and there exactly to the authenticated slot.  This is the theorem `updateLeaf_checks` was missing,
and it is what lets a step re-hash the ancestor path instead of the whole graph.

NO floor hypothesis, NO escape branch: the peel produces a CONCRETE equivocation of the tree's single
carrier at a NAMED role, and `romCarrier_binds` (hence `keyedRom_hard`, the birthday bound) kills it. -/
theorem frame_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary frameBreakGame)
    (hA : RomForgeryEff hgcRomFamily frameForgery Q A) :
    Negl (gameAdv frameBreakGame A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine negl_of_le (fun l => (gameAdv_mem_unit frameBreakGame A l).1)
    (fun l => ?_)
    (romCarrier_binds hgcRomFamily hgcRomCarrier
      (fun l => Q l + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2)
      (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ (polyBounded_sq_add_two _
        (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ (polyBounded_sq_add_two _
          (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ (polyBounded_sq_add_two _
            (polyBounded_sq_add_two _ hQ))))))))))
      hgcRomFamily_card_R
      (romCarrierAdv _ _ (frameExtractComp M))
      ⟨frameExtractComp M,
        fun l => (OracleComp.bindComp_queryBounded (hM l)
          (fun a => QueryBounded.query 19 _ _ (fun _ => QueryBounded.query 18 _ _
            (fun _ => QueryBounded.query 17 _ _ (fun _ => QueryBounded.query 16 _ _
            (fun _ => QueryBounded.query 15 _ _ (fun _ => QueryBounded.query 14 _ _
            (fun _ => QueryBounded.query 13 _ _ (fun _ => QueryBounded.query 12 _ _
            (fun _ => QueryBounded.query 11 _ _ (fun _ => QueryBounded.query 10 _ _
            (fun _ => QueryBounded.query 9 _ _ (fun _ => QueryBounded.query 8 _ _
            (fun _ => QueryBounded.query 7 _ _ (fun _ => QueryBounded.query 6 _ _
            (fun _ => QueryBounded.query 5 _ _ (fun _ => QueryBounded.query 4 _ _
            (fun _ => QueryBounded.query 3 _ _ (fun _ => QueryBounded.query 2 _ _
            (fun _ => QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _
            (fun _ => QueryBounded.pure 0 _)))))))))))))))))))))).mono
          (by show Q l + 20 ≤ Q l + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2; omega),
        fun _ _ => rfl⟩)
  refine @winProb_le_of_imp _ (frameBreakGame.instFin l) _ _ (fun H hH => ?_)
  rw [Adversary.hit_eq_true] at hH ⊢
  obtain ⟨hb, haf, hbreak⟩ := hH
  have hArun : A.run l H = (M l).eval H := hrun l H
  set a := A.run l H with ha
  have hBrun : (romCarrierAdv _ _ (frameExtractComp M)).run l H
      = frameSelect l a
        (romLeaf l H 0 (a.beforeGraph 0)) (romLeaf l H 1 (a.beforeGraph 1))
        (romLeaf l H 2 (a.beforeGraph 2)) (romLeaf l H 3 (a.beforeGraph 3))
        (romLeftPair l H a.beforeGraph) (romRightPair l H a.beforeGraph)
        (romLeaf l H a.index a.before)
        (romPairOf l H (framePairBlock l a.index (romLeaf l H a.index a.before) a.path))
        (romLeaf l H 0 (romReplace a.beforeGraph a.index a.after 0))
        (romLeaf l H 1 (romReplace a.beforeGraph a.index a.after 1))
        (romLeaf l H 2 (romReplace a.beforeGraph a.index a.after 2))
        (romLeaf l H 3 (romReplace a.beforeGraph a.index a.after 3))
        (romLeftPair l H (romReplace a.beforeGraph a.index a.after))
        (romRightPair l H (romReplace a.beforeGraph a.index a.after))
        (romLeaf l H 0 (a.afterGraph 0)) (romLeaf l H 1 (a.afterGraph 1))
        (romLeaf l H 2 (a.afterGraph 2)) (romLeaf l H 3 (a.afterGraph 3))
        (romLeftPair l H a.afterGraph) (romRightPair l H a.afterGraph) := by
    show (frameExtractComp M l).eval H = _
    unfold frameExtractComp
    rw [OracleComp.bindComp_eval, ← hArun]
    rfl
  rw [hBrun]
  exact frameSelect_wins l H a hb haf hbreak

/-! ### §2 teeth — the game is WINNABLE, the admitted refuter-shape is DEFANGED, and a non-negligible
frame forger is OUTSIDE the class. -/

/-- A padding slot. -/
def slotPad : SlotEnc := (false, 0, 0, 0)

/-- An ACTIVE slot, distinct from the padding slot. -/
def slotLive : SlotEnc := (true, 0, 0, 0)

theorem slotPad_ne_slotLive : slotPad ≠ slotLive := by
  intro h
  exact absurd (congrArg Prod.fst h) (by simp [slotPad, slotLive])

/-- The `0`-query constant frame answer: it re-authenticates the padding slot at index `0` while
claiming an after-graph of live slots — an EXACTNESS break at every oracle that maps everything to one
digest. -/
def constFrameAns (l : ℕ) : FrameAns l where
  index := 0
  before := slotPad
  after := slotPad
  path := (⟨0, by positivity⟩, ⟨0, by positivity⟩)
  beforeGraph := fun _ => slotPad
  afterGraph := fun _ => slotLive

/-- **(TOOTH — the frame game is WINNABLE and the admitted refuter-shape is DEFANGED.)** The `0`-query
constant answerer is IN the class, WINS at the constant oracle (every absorb collapses to one digest,
so both reconstructions "check" while the after-graph is wrong), and its advantage is NEGLIGIBLE by
`frame_binds_rom` — the frame converse prices something genuinely nonzero, and the pigeonhole strategy
that made a `∨ ∃ collision` disjunction a free pass dies at the sampled oracle. -/
theorem frame_constAnswer_defanged (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    (RomForgeryEff hgcRomFamily frameForgery Q ⟨fun l _ => constFrameAns l⟩)
      ∧ (∀ l, 0 < gameAdv frameBreakGame ⟨fun l _ => constFrameAns l⟩ l)
      ∧ Negl (gameAdv frameBreakGame ⟨fun l _ => constFrameAns l⟩) := by
  have hmem : RomForgeryEff hgcRomFamily frameForgery Q ⟨fun l _ => constFrameAns l⟩ :=
    ⟨fun l => OracleComp.pure (constFrameAns l), fun l => QueryBounded.pure (Q l) _,
      fun _ _ => rfl⟩
  refine ⟨hmem, fun l => ?_, frame_binds_rom Q hQ _ hmem⟩
  obtain ⟨r₀⟩ : Nonempty (Fin (2 ^ l)) := ⟨⟨0, by positivity⟩⟩
  refine @winProb_pos_of_witness _ (frameBreakGame.instFin l) _ (fun _ => r₀) ?_
  refine (Adversary.hit_eq_true _ l _).mpr ⟨rfl, rfl, ?_⟩
  intro hEq
  have h1 := congrFun hEq 1
  simp only [constFrameAns, romReplace] at h1
  rw [Function.update_apply] at h1
  simp only [if_neg (show (1 : Fin 4) ≠ 0 from Fin.ne_of_val_ne (by omega))] at h1
  exact slotPad_ne_slotLive h1.symm

/-- **(TOOTH — a non-negligible frame forger is OUTSIDE the class.)** -/
theorem frame_nonNegl_forger_excluded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary frameBreakGame) (hnn : ¬ Negl (gameAdv frameBreakGame A)) :
    ¬ RomForgeryEff hgcRomFamily frameForgery Q A :=
  fun hA => hnn (frame_binds_rom Q hQ A hA)

end RomFrame

/-! ## §3 — WHAT THE CONVERSE BUYS: the update's absorb schedule is the ancestor path.

Counted at the deployed shape, as propositions about the commitment — not benchmarks. -/

/-- The absorb schedule of a FULL root recomputation: four leaves, two pairs, the root. -/
def semanticRootAbsorbs (H : Hash) (g : BoundedGraph) : List (List Int) :=
  [leafInputs 0 (g.slots 0), leafInputs 1 (g.slots 1), leafInputs 2 (g.slots 2),
    leafInputs 3 (g.slots 3),
    nodeInputs PAIR_TAG (leafDigest H 0 (g.slots 0)) (leafDigest H 1 (g.slots 1)),
    nodeInputs PAIR_TAG (leafDigest H 2 (g.slots 2)) (leafDigest H 3 (g.slots 3)),
    nodeInputs ROOT_TAG (leftPair H g) (rightPair H g)]

/-- The absorb schedule of an ANCESTOR UPDATE: the new leaf, `u`'s pair, the root — and nothing else.
Its arguments are the index, the new slot and the two path digests; no other slot can appear. -/
def updateAbsorbs (H : Hash) (u : Fin 4) (s : HostEdgeSlot) (p : Path4) : List (List Int) :=
  match u.val with
  | 0 => [leafInputs u s, nodeInputs PAIR_TAG (leafDigest H u s) p.siblingLeaf,
      nodeInputs ROOT_TAG (nodeDigest H PAIR_TAG (leafDigest H u s) p.siblingLeaf) p.siblingPair]
  | 1 => [leafInputs u s, nodeInputs PAIR_TAG p.siblingLeaf (leafDigest H u s),
      nodeInputs ROOT_TAG (nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H u s)) p.siblingPair]
  | 2 => [leafInputs u s, nodeInputs PAIR_TAG (leafDigest H u s) p.siblingLeaf,
      nodeInputs ROOT_TAG p.siblingPair (nodeDigest H PAIR_TAG (leafDigest H u s) p.siblingLeaf)]
  | _ => [leafInputs u s, nodeInputs PAIR_TAG p.siblingLeaf (leafDigest H u s),
      nodeInputs ROOT_TAG p.siblingPair (nodeDigest H PAIR_TAG p.siblingLeaf (leafDigest H u s))]

theorem updateAbsorbs_length (H : Hash) (u : Fin 4) (s : HostEdgeSlot) (p : Path4) :
    (updateAbsorbs H u s p).length = 3 := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl <;> rfl

theorem semanticRootAbsorbs_length (H : Hash) (g : BoundedGraph) :
    (semanticRootAbsorbs H g).length = 7 := rfl

/-- The reconstructed root IS the digest of the schedule's last absorb. -/
theorem rootFromPath_eq_last_absorb (H : Hash) (u : Fin 4) (s : HostEdgeSlot) (p : Path4) :
    rootFromPath H u (leafDigest H u s) p = digest8 H ((updateAbsorbs H u s p).getD 2 []) := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl <;> rfl

/-- The full root is the digest of the full schedule's last absorb. -/
theorem semanticRoot_eq_last_absorb (H : Hash) (g : BoundedGraph) :
    semanticRoot H g = digest8 H ((semanticRootAbsorbs H g).getD 6 []) := rfl

/-- **⚑⚑ THE Θ(|G|) → depth+1 STATEMENT.** The root of the graph with slot `u` replaced is the digest
of the LAST of THREE absorbs, and those three absorbs are determined by `(u, the new slot, the two
path digests)` — the ancestor path — alone.  The rest of the graph is not read. -/
theorem update_rehashes_only_ancestor_path (H : Hash) (g : BoundedGraph) (u : Fin 4)
    (s : HostEdgeSlot) (hc : s.canonicalPadding) :
    semanticRoot H (replaceSlot g u s hc)
      = digest8 H ((updateAbsorbs H u s (pathFor H g u)).getD 2 []) := by
  have hslot : (replaceSlot g u s hc).slots u = s := by
    simp [replaceSlot]
  have h1 := pathFor_reconstructs H (replaceSlot g u s hc) u
  rw [hslot, pathFor_replaceSlot H g u s hc] at h1
  rw [← h1]
  exact rootFromPath_eq_last_absorb H u s (pathFor H g u)

/-- **THE UPDATE READS THE OLD GRAPH ONLY THROUGH ITS PATH.** Two graphs with the same ancestor path
at `u` have the same updated root — the frame, from the COST side. -/
theorem afterRoot_depends_only_on_path (H : Hash) (g g' : BoundedGraph) (u : Fin 4)
    (s : HostEdgeSlot) (hc : s.canonicalPadding) (h : pathFor H g u = pathFor H g' u) :
    semanticRoot H (replaceSlot g u s hc) = semanticRoot H (replaceSlot g' u s hc) := by
  rw [update_rehashes_only_ancestor_path H g u s hc,
    update_rehashes_only_ancestor_path H g' u s hc, h]

/-- **THE COUNT, AT THE DEPLOYED SHAPE.** Three absorbs is depth + 1 (`2 ^ (3 - 1) = GRAPH_SLOTS`),
seven is the full tree (`2 * GRAPH_SLOTS - 1`).  ⚠ These are INSTANCES at `GRAPH_SLOTS = 4`, not a
theorem over `n`: the general depth-`d` statement needs a depth-parametric tree this prototype does
not have. -/
theorem frame_cost_at_deployed_slots (H : Hash) (g : BoundedGraph) (u : Fin 4) (s : HostEdgeSlot)
    (p : Path4) :
    2 ^ ((updateAbsorbs H u s p).length - 1) = GRAPH_SLOTS
      ∧ (semanticRootAbsorbs H g).length = 2 * GRAPH_SLOTS - 1
      ∧ (updateAbsorbs H u s p).length < (semanticRootAbsorbs H g).length := by
  rw [updateAbsorbs_length, semanticRootAbsorbs_length]
  refine ⟨by norm_num [GRAPH_SLOTS], by norm_num [GRAPH_SLOTS], by norm_num⟩

/-- **⚑⚑ WHAT IT BUYS, ON A REAL REWRITE STEP.** A bounded rewrite step that touches only slot `u`
is a generic `RewriteStep`, its committed endpoints are joined by ONE ACCEPTED `AncestorUpdate`, and
that update's root recomputation is THREE absorbs against the full recompute's SEVEN.  With
`frame_binds_rom`, acceptance is not merely necessary but (except with negligible probability)
sufficient: nothing outside slot `u` can have moved. -/
theorem single_slot_step_logarithmic_update (H : Hash) (rules : List BoundedRule)
    (g : BoundedGraph) (u : Fin 4) (s : HostEdgeSlot) (hc : s.canonicalPadding)
    (rule : BoundedRule) (sigma : Var → Node) (context : BoundedContext)
    (hstep : BoundedOneStep rules g (replaceSlot g u s hc) rule sigma context) :
    RewriteStep (rules.map BoundedRule.toRule) g.toHypergraph (replaceSlot g u s hc).toHypergraph
      ∧ (updateLeaf H g u s).check H (semanticRoot H g)
          (semanticRoot H (replaceSlot g u s hc)) = true
      ∧ semanticRoot H (replaceSlot g u s hc)
          = digest8 H ((updateAbsorbs H u s (pathFor H g u)).getD 2 [])
      ∧ (updateAbsorbs H u s (pathFor H g u)).length = 3
      ∧ (semanticRootAbsorbs H (replaceSlot g u s hc)).length = 7 :=
  ⟨boundedOneStep_to_rewriteStep hstep,
    updateLeaf_checks H g u s hc,
    update_rehashes_only_ancestor_path H g u s hc,
    updateAbsorbs_length H u s (pathFor H g u),
    semanticRootAbsorbs_length H (replaceSlot g u s hc)⟩

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  fin4_cases,
  path_peel,
  slots_agree_off_index,
  frame_of_absorbInjective,
  afterGraph_eq_replaceSlot,
  injHash_digest8_injective,
  treeAbsorbInjective_of_digest8_injective,
  exists_treeAbsorbInjective,
  not_treeAbsorbInjective_of_boundedLanes,
  hgcRomRoot_eq,
  romRootFromPath_honest,
  frame_violation_wins,
  hgcSelect_wins,
  frameSelect_wins,
  frame_binds_rom,
  frame_constAnswer_defanged,
  frame_nonNegl_forger_excluded,
  updateAbsorbs_length,
  semanticRootAbsorbs_length,
  rootFromPath_eq_last_absorb,
  semanticRoot_eq_last_absorb,
  update_rehashes_only_ancestor_path,
  afterRoot_depends_only_on_path,
  frame_cost_at_deployed_slots,
  single_slot_step_logarithmic_update]

end Dregg2.Crypto.HierarchicalGraphFrame
