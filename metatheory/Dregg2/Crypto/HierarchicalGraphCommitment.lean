/-
# Dregg2.Crypto.HierarchicalGraphCommitment

An isolated prototype for locally opening and updating the bounded private
graph commitment.  This module deliberately stops before any ZK/PCD claim:

* four graph-edge slots are committed as a depth-two, domain-separated tree;
* a leaf opening exposes one local edge (including its endpoint interface) and
  the two sibling digests needed to authenticate it;
* an ancestor update reuses the same path for an old and a new leaf, proving
  that only the authenticated leaf position changes;
* the semantic root is stable, while an occurrence wrapper separately binds a
  session, step index, and fresh blinding;
* a fold-use ledger consumes occurrence ids, not semantic proof ids.  The same
  memoized semantic proof can therefore be rebound at distinct occurrences,
  while consuming one occurrence twice fails closed.

Hash binding is stated in the same honest style as `PrivateGraphRewrite`: any
two different accepted preimages for one eight-lane digest produce an explicit
`DigestCollision`.  No mathematical injectivity of a compressing hash is
assumed.
-/
import Dregg2.Crypto.PrivateGraphRewrite
import Dregg2.Tactics
import Mathlib.Tactic.FinCases

namespace Dregg2.Crypto.HierarchicalGraphCommitment

open Dregg2.Crypto.PrivateGraphRewrite

abbrev Hash := List Int → List Int
abbrev NodeId := Digest8

def LEAF_TAG : Int := 7401
def PAIR_TAG : Int := 7402
def ROOT_TAG : Int := 7403
def OCCURRENCE_TAG : Int := 7404
def OCCURRENCE_ID_TAG : Int := 7405

/-! ## Fixed-width encodings -/

def digestFields (d : Digest8) : List Int :=
  [d 0, d 1, d 2, d 3, d 4, d 5, d 6, d 7]

theorem digestFields_injective : Function.Injective digestFields := by
  intro a b h
  funext i
  fin_cases i <;> simp_all [digestFields]

def leafInputs (index : Fin 4) (slot : HostEdgeSlot) : List Int :=
  [LEAF_TAG, index.val, boolInt slot.active, slot.label.val, slot.src.val, slot.dst.val]

theorem boolInt_injective : Function.Injective boolInt := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolInt]

theorem leafInputs_injective (index : Fin 4) : Function.Injective (leafInputs index) := by
  intro a b h
  have hactive : boolInt a.active = boolInt b.active := by
    simpa [leafInputs] using congrArg (fun xs => xs.getD 2 0) h
  have hlabel : a.label.val = b.label.val := by
    simpa [leafInputs] using congrArg (fun xs => xs.getD 3 0) h
  have hsrc : a.src.val = b.src.val := by
    simpa [leafInputs] using congrArg (fun xs => xs.getD 4 0) h
  have hdst : a.dst.val = b.dst.val := by
    simpa [leafInputs] using congrArg (fun xs => xs.getD 5 0) h
  cases a
  cases b
  simp only at hactive hlabel hsrc hdst ⊢
  congr
  · exact boolInt_injective hactive
  · exact Fin.ext hlabel
  · exact Fin.ext hsrc
  · exact Fin.ext hdst

def nodeInputs (tag : Int) (left right : Digest8) : List Int :=
  [tag] ++ digestFields left ++ digestFields right

theorem nodeInputs_injective (tag : Int) :
    Function.Injective (fun p : Digest8 × Digest8 => nodeInputs tag p.1 p.2) := by
  intro a b h
  have hleft : digestFields a.1 = digestFields b.1 := by
    simpa [nodeInputs] using congrArg (fun xs => (xs.drop 1).take 8) h
  have hright : digestFields a.2 = digestFields b.2 := by
    simpa [nodeInputs] using congrArg (fun xs => xs.drop 9) h
  exact Prod.ext (digestFields_injective hleft) (digestFields_injective hright)

def leafDigest (H : Hash) (index : Fin 4) (slot : HostEdgeSlot) : Digest8 :=
  digest8 H (leafInputs index slot)

def nodeDigest (H : Hash) (tag : Int) (left right : Digest8) : Digest8 :=
  digest8 H (nodeInputs tag left right)

def canonicalSlotB (slot : HostEdgeSlot) : Bool :=
  if slot.active then true
  else slot.label == 0 && slot.src == 0 && slot.dst == 0

theorem canonicalSlotB_iff (slot : HostEdgeSlot) :
    canonicalSlotB slot = true ↔ slot.canonicalPadding := by
  cases hactive : slot.active <;>
    simp [canonicalSlotB, HostEdgeSlot.canonicalPadding, hactive, and_assoc]

/-! ## A four-leaf hierarchical semantic commitment -/

def leftPair (H : Hash) (g : BoundedGraph) : Digest8 :=
  nodeDigest H PAIR_TAG (leafDigest H 0 (g.slots 0)) (leafDigest H 1 (g.slots 1))

def rightPair (H : Hash) (g : BoundedGraph) : Digest8 :=
  nodeDigest H PAIR_TAG (leafDigest H 2 (g.slots 2)) (leafDigest H 3 (g.slots 3))

/-- A stable semantic root.  Session, step index, and hiding randomness are
bound separately by `occurrenceRoot`; they do not poison the memo key. -/
def semanticRoot (H : Hash) (g : BoundedGraph) : Digest8 :=
  nodeDigest H ROOT_TAG (leftPair H g) (rightPair H g)

structure Path4 where
  /-- The other leaf in the selected leaf's pair. -/
  siblingLeaf : Digest8
  /-- The complete sibling pair at the root. -/
  siblingPair : Digest8
  deriving DecidableEq

def rootFromPath (H : Hash) (index : Fin 4) (leaf : Digest8) (path : Path4) : Digest8 :=
  match index.val with
  | 0 => nodeDigest H ROOT_TAG
      (nodeDigest H PAIR_TAG leaf path.siblingLeaf) path.siblingPair
  | 1 => nodeDigest H ROOT_TAG
      (nodeDigest H PAIR_TAG path.siblingLeaf leaf) path.siblingPair
  | 2 => nodeDigest H ROOT_TAG path.siblingPair
      (nodeDigest H PAIR_TAG leaf path.siblingLeaf)
  | _ => nodeDigest H ROOT_TAG path.siblingPair
      (nodeDigest H PAIR_TAG path.siblingLeaf leaf)

def pathFor (H : Hash) (g : BoundedGraph) (index : Fin 4) : Path4 :=
  match index.val with
  | 0 => ⟨leafDigest H 1 (g.slots 1), rightPair H g⟩
  | 1 => ⟨leafDigest H 0 (g.slots 0), rightPair H g⟩
  | 2 => ⟨leafDigest H 3 (g.slots 3), leftPair H g⟩
  | _ => ⟨leafDigest H 2 (g.slots 2), leftPair H g⟩

theorem pathFor_reconstructs (H : Hash) (g : BoundedGraph) (index : Fin 4) :
    rootFromPath H index (leafDigest H index (g.slots index)) (pathFor H g index) =
      semanticRoot H g := by
  fin_cases index <;> rfl

structure LeafOpening where
  index : Fin 4
  slot : HostEdgeSlot
  path : Path4
  deriving DecidableEq

def LeafOpening.canonical (opening : LeafOpening) : Prop :=
  opening.slot.canonicalPadding

def LeafOpening.check (H : Hash) (claimedRoot : Digest8) (opening : LeafOpening) : Bool :=
  canonicalSlotB opening.slot && decide
    (digestFields (rootFromPath H opening.index (leafDigest H opening.index opening.slot) opening.path) =
      digestFields claimedRoot)

def openLeaf (H : Hash) (g : BoundedGraph) (index : Fin 4) : LeafOpening :=
  ⟨index, g.slots index, pathFor H g index⟩

theorem openLeaf_checks (H : Hash) (g : BoundedGraph) (index : Fin 4) :
    (openLeaf H g index).check H (semanticRoot H g) = true := by
  rw [LeafOpening.check, Bool.and_eq_true]
  constructor
  · exact (canonicalSlotB_iff _).mpr (g.canonicalPadding index)
  · change decide
      (digestFields
        (rootFromPath H index (leafDigest H index (g.slots index)) (pathFor H g index)) =
          digestFields (semanticRoot H g)) = true
    exact decide_eq_true (congrArg digestFields (pathFor_reconstructs H g index))

/-- The opened active edge exposes its two endpoint nodes as the local rewrite
interface.  No unrelated graph slot is revealed. -/
structure InterfaceOpening where
  leaf : LeafOpening
  src : Node
  dst : Node
  deriving DecidableEq

def InterfaceOpening.check (H : Hash) (claimedRoot : Digest8)
    (opening : InterfaceOpening) : Bool :=
  opening.leaf.check H claimedRoot &&
    decide (opening.leaf.slot.active = true ∧
      opening.src = opening.leaf.slot.src ∧ opening.dst = opening.leaf.slot.dst)

def openInterface (H : Hash) (g : BoundedGraph) (index : Fin 4) : InterfaceOpening :=
  ⟨openLeaf H g index, (g.slots index).src, (g.slots index).dst⟩

theorem openInterface_checks (H : Hash) (g : BoundedGraph) (index : Fin 4)
    (hactive : (g.slots index).active = true) :
    (openInterface H g index).check H (semanticRoot H g) = true := by
  rw [InterfaceOpening.check, Bool.and_eq_true]
  constructor
  · exact openLeaf_checks H g index
  · simp [openInterface, openLeaf, hactive]

/-- A two-edge local redex.  The distinct-index tooth prevents presenting one
authenticated graph leaf twice as a two-edge redex. -/
structure Redex2Opening where
  first : InterfaceOpening
  second : InterfaceOpening
  deriving DecidableEq

def Redex2Opening.check (H : Hash) (claimedRoot : Digest8)
    (opening : Redex2Opening) : Bool :=
  opening.first.check H claimedRoot && opening.second.check H claimedRoot &&
    decide (opening.first.leaf.index ≠ opening.second.leaf.index)

def openRedex2 (H : Hash) (g : BoundedGraph) (first second : Fin 4) : Redex2Opening :=
  ⟨openInterface H g first, openInterface H g second⟩

theorem openRedex2_checks (H : Hash) (g : BoundedGraph) (first second : Fin 4)
    (hfirst : (g.slots first).active = true) (hsecond : (g.slots second).active = true)
    (hdistinct : first ≠ second) :
    (openRedex2 H g first second).check H (semanticRoot H g) = true := by
  rw [Redex2Opening.check]
  simp only [openRedex2]
  rw [openInterface_checks H g first hfirst, openInterface_checks H g second hsecond]
  simpa [openInterface, openLeaf] using hdistinct

/-! ## Same-path authenticated ancestor updates -/

structure AncestorUpdate where
  index : Fin 4
  before : HostEdgeSlot
  after : HostEdgeSlot
  path : Path4
  deriving DecidableEq

def AncestorUpdate.check (H : Hash) (beforeRoot afterRoot : Digest8)
    (update : AncestorUpdate) : Bool :=
  canonicalSlotB update.before && canonicalSlotB update.after &&
    decide (digestFields
      (rootFromPath H update.index (leafDigest H update.index update.before) update.path) =
        digestFields beforeRoot) &&
    decide (digestFields
      (rootFromPath H update.index (leafDigest H update.index update.after) update.path) =
        digestFields afterRoot)

def replaceSlot (g : BoundedGraph) (index : Fin 4) (slot : HostEdgeSlot)
    (hcanonical : slot.canonicalPadding) : BoundedGraph where
  slots := Function.update g.slots index slot
  canonicalPadding := by
    intro i
    by_cases h : i = index
    · subst i
      simpa using hcanonical
    · simpa [Function.update, h] using g.canonicalPadding i

theorem pathFor_replaceSlot (H : Hash) (g : BoundedGraph) (index : Fin 4)
    (slot : HostEdgeSlot) (hcanonical : slot.canonicalPadding) :
    pathFor H (replaceSlot g index slot hcanonical) index = pathFor H g index := by
  fin_cases index <;> simp [pathFor, replaceSlot, leftPair, rightPair, Function.update]

def updateLeaf (H : Hash) (g : BoundedGraph) (index : Fin 4) (after : HostEdgeSlot) :
    AncestorUpdate :=
  ⟨index, g.slots index, after, pathFor H g index⟩

theorem updateLeaf_checks (H : Hash) (g : BoundedGraph) (index : Fin 4)
    (after : HostEdgeSlot) (hcanonical : after.canonicalPadding) :
    (updateLeaf H g index after).check H (semanticRoot H g)
      (semanticRoot H (replaceSlot g index after hcanonical)) = true := by
  have hbeforeCanonical : canonicalSlotB (g.slots index) = true :=
    (canonicalSlotB_iff _).mpr (g.canonicalPadding index)
  have hafterCanonical : canonicalSlotB after = true :=
    (canonicalSlotB_iff _).mpr hcanonical
  have hbeforeRoot := pathFor_reconstructs H g index
  have hafterRoot := pathFor_reconstructs H (replaceSlot g index after hcanonical) index
  have hpath := pathFor_replaceSlot H g index after hcanonical
  have hafterRoot' :
      rootFromPath H index (leafDigest H index after) (pathFor H g index) =
        semanticRoot H (replaceSlot g index after hcanonical) := by
    rw [← hpath]
    simpa [replaceSlot] using hafterRoot
  simp only [AncestorUpdate.check, updateLeaf, hbeforeCanonical, hafterCanonical,
    Bool.true_and]
  rw [Bool.and_eq_true]
  constructor
  · exact decide_eq_true (congrArg digestFields hbeforeRoot)
  · exact decide_eq_true (congrArg digestFields hafterRoot')

/-! ## Collision-explicit faithfulness -/

theorem digest_eq_preimage_or_collision (H : Hash) {left right : List Int}
    (h : digest8 H left = digest8 H right) : left = right ∨ DigestCollision H := by
  by_cases heq : left = right
  · exact Or.inl heq
  · exact Or.inr ⟨left, right, heq, h⟩

def genericLeafRoot (H : Hash) (preimages : Fin 4 → List Int) (index : Fin 4) : Digest8 :=
  digest8 H (preimages index)

def genericLeftPair (H : Hash) (preimages : Fin 4 → List Int) : Digest8 :=
  nodeDigest H PAIR_TAG (genericLeafRoot H preimages 0) (genericLeafRoot H preimages 1)

def genericRightPair (H : Hash) (preimages : Fin 4 → List Int) : Digest8 :=
  nodeDigest H PAIR_TAG (genericLeafRoot H preimages 2) (genericLeafRoot H preimages 3)

def genericRoot (H : Hash) (preimages : Fin 4 → List Int) : Digest8 :=
  nodeDigest H ROOT_TAG (genericLeftPair H preimages) (genericRightPair H preimages)

private theorem pair_preimages_eq_or_collision (H : Hash)
    {a0 a1 b0 b1 : List Int}
    (h : nodeDigest H PAIR_TAG (digest8 H a0) (digest8 H a1) =
      nodeDigest H PAIR_TAG (digest8 H b0) (digest8 H b1)) :
    (a0 = b0 ∧ a1 = b1) ∨ DigestCollision H := by
  rcases digest_eq_preimage_or_collision H h with hnode | hcollision
  · have hpairs : (digest8 H a0, digest8 H a1) = (digest8 H b0, digest8 H b1) := by
      apply nodeInputs_injective PAIR_TAG
      exact hnode
    have h0 := congrArg Prod.fst hpairs
    have h1 := congrArg Prod.snd hpairs
    rcases digest_eq_preimage_or_collision H h0 with hpre0 | hcollision
    · rcases digest_eq_preimage_or_collision H h1 with hpre1 | hcollision
      · exact Or.inl ⟨hpre0, hpre1⟩
      · exact Or.inr hcollision
    · exact Or.inr hcollision
  · exact Or.inr hcollision

/-- Equal four-leaf roots authenticate every leaf preimage, unless they expose
an explicit collision somewhere in the two-level tree. -/
theorem genericRoot_eq_preimages_or_collision (H : Hash)
    {left right : Fin 4 → List Int} (hroot : genericRoot H left = genericRoot H right) :
    (∀ i, left i = right i) ∨ DigestCollision H := by
  rcases digest_eq_preimage_or_collision H hroot with htop | hcollision
  · have hpairs :
        (genericLeftPair H left, genericRightPair H left) =
          (genericLeftPair H right, genericRightPair H right) := by
      apply nodeInputs_injective ROOT_TAG
      exact htop
    have hleft := congrArg Prod.fst hpairs
    have hright := congrArg Prod.snd hpairs
    rcases pair_preimages_eq_or_collision H hleft with hl | hcollision
    · rcases pair_preimages_eq_or_collision H hright with hr | hcollision
      · left
        intro i
        fin_cases i
        · exact hl.1
        · exact hl.2
        · exact hr.1
        · exact hr.2
      · exact Or.inr hcollision
    · exact Or.inr hcollision
  · exact Or.inr hcollision

theorem semanticRoot_eq_graph_or_collision (H : Hash) {left right : BoundedGraph}
    (hroot : semanticRoot H left = semanticRoot H right) :
    left = right ∨ DigestCollision H := by
  have hgeneric :
      genericRoot H (fun i => leafInputs i (left.slots i)) =
        genericRoot H (fun i => leafInputs i (right.slots i)) := by
    simpa [semanticRoot, leftPair, rightPair, genericRoot, genericLeftPair,
      genericRightPair, genericLeafRoot, leafDigest, nodeDigest] using hroot
  rcases genericRoot_eq_preimages_or_collision H hgeneric with hpre | hcollision
  · left
    cases left with
    | mk leftSlots leftCanonical =>
      cases right with
      | mk rightSlots rightCanonical =>
        congr
        funext i
        exact leafInputs_injective i (hpre i)
  · exact Or.inr hcollision

/-! ## Session-bound occurrence wrappers -/

def occurrenceInputs (semantic : Digest8) (blind : Blind4)
    (domain session version index : Int) : List Int :=
  [OCCURRENCE_TAG, domain, session, version, index] ++ digestFields semantic ++ List.ofFn blind

def occurrenceRoot (H : Hash) (semantic : Digest8) (blind : Blind4)
    (domain session version index : Int) : Digest8 :=
  digest8 H (occurrenceInputs semantic blind domain session version index)

structure OccurrenceOpening where
  semantic : Digest8
  blind : Blind4
  domain : Int
  session : Int
  version : Int
  index : Int

def canonicalBlindB (blind : Blind4) : Bool :=
  decide (0 ≤ blind 0 ∧ blind 0 < 2013265921) &&
  decide (0 ≤ blind 1 ∧ blind 1 < 2013265921) &&
  decide (0 ≤ blind 2 ∧ blind 2 < 2013265921) &&
  decide (0 ≤ blind 3 ∧ blind 3 < 2013265921)

theorem canonicalBlindB_iff (blind : Blind4) :
    canonicalBlindB blind = true ↔ CanonicalBlind blind := by
  simp only [canonicalBlindB, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩

def OccurrenceOpening.check (H : Hash) (claimedRoot : Digest8)
    (opening : OccurrenceOpening) : Bool :=
  canonicalBlindB opening.blind && decide
    (digestFields (occurrenceRoot H opening.semantic opening.blind
      opening.domain opening.session opening.version opening.index) = digestFields claimedRoot)

def openOccurrence (semantic : Digest8) (blind : Blind4)
    (domain session version index : Int) : OccurrenceOpening :=
  ⟨semantic, blind, domain, session, version, index⟩

theorem openOccurrence_checks (H : Hash) (semantic : Digest8) (blind : Blind4)
    (domain session version index : Int) (hcanonical : CanonicalBlind blind) :
    (openOccurrence semantic blind domain session version index).check H
      (occurrenceRoot H semantic blind domain session version index) = true := by
  rw [OccurrenceOpening.check, Bool.and_eq_true]
  exact ⟨(canonicalBlindB_iff blind).mpr hcanonical, decide_eq_true rfl⟩

theorem two_occurrence_openings_yield_collision (H : Hash) {claimedRoot : Digest8}
    {left right : OccurrenceOpening}
    (hl : left.check H claimedRoot = true) (hr : right.check H claimedRoot = true)
    (hdiff : occurrenceInputs left.semantic left.blind left.domain left.session left.version left.index ≠
      occurrenceInputs right.semantic right.blind right.domain right.session right.version right.index) :
    DigestCollision H := by
  rw [OccurrenceOpening.check, Bool.and_eq_true] at hl hr
  have hlroot : occurrenceRoot H left.semantic left.blind left.domain left.session left.version left.index =
      claimedRoot := digestFields_injective (of_decide_eq_true hl.2)
  have hrroot : occurrenceRoot H right.semantic right.blind right.domain right.session right.version right.index =
      claimedRoot := digestFields_injective (of_decide_eq_true hr.2)
  exact ⟨_, _, hdiff, hlroot.trans hrroot.symm⟩

/-- The consumed fold identity is occurrence-specific and deliberately does
not depend on the cached semantic proof id.  Otherwise one occurrence could be
consumed twice merely by presenting two semantic proof ids. -/
def occurrenceIdInputs (occurrence : Digest8) : List Int :=
  [OCCURRENCE_ID_TAG] ++ digestFields occurrence

def occurrenceId (H : Hash) (occurrence : Digest8) : NodeId :=
  digest8 H (occurrenceIdInputs occurrence)

structure FoldUse where
  semanticProofId : NodeId
  occurrenceRoot : Digest8
  useId : NodeId
  deriving DecidableEq

def FoldUse.check (H : Hash) (use : FoldUse) : Bool :=
  decide (digestFields use.useId =
    digestFields (occurrenceId H use.occurrenceRoot))

/-- Distinct occurrence roots with the same consumed id expose the exact hash
collision that can otherwise cause an alias/refusal. -/
theorem occurrenceId_alias_yields_collision (H : Hash) {left right : Digest8}
    (hid : occurrenceId H left = occurrenceId H right)
    (hdiff : occurrenceIdInputs left ≠ occurrenceIdInputs right) : DigestCollision H :=
  ⟨occurrenceIdInputs left, occurrenceIdInputs right, hdiff, hid⟩

abbrev UseLedger := List NodeId

/-- Consume an occurrence exactly once.  The semantic proof id is intentionally
not inserted into the ledger, so memoized semantics can be rebound safely. -/
def consume (H : Hash) (ledger : UseLedger) (use : FoldUse) : Option UseLedger :=
  if use.check H then
    if use.useId ∈ ledger then none else some (use.useId :: ledger)
  else none

theorem consume_fresh {H : Hash} {ledger next : UseLedger} {use : FoldUse}
    (hledger : ledger.Nodup) (h : consume H ledger use = some next) :
    next.Nodup ∧ use.useId ∈ next := by
  unfold consume at h
  split at h
  next hcheck =>
    split at h
    next hmem => contradiction
    next hnotmem =>
      simp only [Option.some.injEq] at h
      subst next
      exact ⟨List.nodup_cons.mpr ⟨hnotmem, hledger⟩, List.mem_cons_self⟩
  next => contradiction

theorem consume_duplicate_refused (H : Hash) (ledger : UseLedger) (use : FoldUse)
    (hcheck : use.check H = true) :
    consume H (use.useId :: ledger) use = none := by
  simp [consume, hcheck]

theorem consume_fresh_occurrence_succeeds (H : Hash) (ledger : UseLedger) (use : FoldUse)
    (hcheck : use.check H = true) (hfresh : use.useId ∉ ledger) :
    consume H ledger use = some (use.useId :: ledger) := by
  simp [consume, hcheck, hfresh]

/-! ## Executable non-vacuity and refusal teeth -/

namespace Reference

def toyHash (xs : List Int) : List Int :=
  List.ofFn fun lane : Fin 8 =>
    xs.foldl (fun acc item =>
      (acc * (Int.ofNat lane.val + 19) + item + Int.ofNat lane.val) % 1000003)
      (Int.ofNat lane.val + 17)

def graph : BoundedGraph where
  slots
    | 0 => ⟨true, 1, 1, 2⟩
    | 1 => ⟨true, 2, 2, 3⟩
    | 2 => ⟨true, 3, 3, 4⟩
    | _ => ⟨false, 0, 0, 0⟩
  canonicalPadding := by
    intro i
    fin_cases i <;> simp [HostEdgeSlot.canonicalPadding]

def replacement : HostEdgeSlot := ⟨true, 7, 1, 3⟩

#guard (openLeaf toyHash graph 1).check toyHash (semanticRoot toyHash graph)
#guard (openInterface toyHash graph 1).check toyHash (semanticRoot toyHash graph)
#guard (openRedex2 toyHash graph 0 1).check toyHash (semanticRoot toyHash graph)
#guard (updateLeaf toyHash graph 1 replacement).check toyHash (semanticRoot toyHash graph)
  (semanticRoot toyHash (replaceSlot graph 1 replacement (by
    simp [replacement, HostEdgeSlot.canonicalPadding])))

def badDuplicateRedex : Redex2Opening :=
  let opened := openInterface toyHash graph 1
  ⟨opened, opened⟩

#guard !(badDuplicateRedex.check toyHash (semanticRoot toyHash graph))

def blind : Blind4 := fun i => i.val + 11

def occurrenceA : Digest8 :=
  occurrenceRoot toyHash (semanticRoot toyHash graph) blind 9 100 1 4

def occurrenceB : Digest8 :=
  occurrenceRoot toyHash (semanticRoot toyHash graph) blind 9 100 1 5

def semanticProof : NodeId := digest8 toyHash [991, 992, 993]

def wrapperA : OccurrenceOpening :=
  openOccurrence (semanticRoot toyHash graph) blind 9 100 1 4

def wrapperWrongIndex : OccurrenceOpening :=
  openOccurrence (semanticRoot toyHash graph) blind 9 100 1 5

#guard wrapperA.check toyHash occurrenceA
#guard !(wrapperWrongIndex.check toyHash occurrenceA)

def useA : FoldUse :=
  ⟨semanticProof, occurrenceA, occurrenceId toyHash occurrenceA⟩

def useB : FoldUse :=
  ⟨semanticProof, occurrenceB, occurrenceId toyHash occurrenceB⟩

def alternateSemanticProof : NodeId := digest8 toyHash [881, 882, 883]

def useAAlternateProof : FoldUse :=
  ⟨alternateSemanticProof, occurrenceA, occurrenceId toyHash occurrenceA⟩

#guard (consume toyHash [] useA).isSome
#guard (consume toyHash [useA.useId] useA).isNone
#guard (consume toyHash [useA.useId] useAAlternateProof).isNone
#guard (consume toyHash [useA.useId] useB).isSome

end Reference

#assert_all_clean [
  digestFields_injective,
  leafInputs_injective,
  nodeInputs_injective,
  pathFor_reconstructs,
  openLeaf_checks,
  openInterface_checks,
  openRedex2_checks,
  pathFor_replaceSlot,
  updateLeaf_checks,
  digest_eq_preimage_or_collision,
  genericRoot_eq_preimages_or_collision,
  semanticRoot_eq_graph_or_collision,
  openOccurrence_checks,
  two_occurrence_openings_yield_collision,
  occurrenceId_alias_yields_collision,
  consume_fresh,
  consume_duplicate_refused,
  consume_fresh_occurrence_succeeds]

end Dregg2.Crypto.HierarchicalGraphCommitment
