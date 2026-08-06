/-
# Dregg2.Circuit.Emit.AdjacencyMembershipWideEmit — the WIDE (`node8`) neighbor-adjacency
family: the sorted-set NON-MEMBERSHIP lift at full digest width.

**This is Lean-authored AIR.** This module authors the algebra; Rust parses the emitted IR-v2
bytes and supplies witnesses — it constructs no constraints.

## What this file IS, and the wound it closes

`AdjacencyMembershipEmit.adjacencyDesc` (`dregg-membership-adjacency::poseidon2-v1`) is the
DEPLOYED double-spend gate: `turn/src/executor/membership_verifier.rs`'s
`verify_nullifier_nonmembership` proves a spent nullifier is FRESH by exhibiting two leaves
`lo < nf < hi` that are CONSECUTIVE under the committed nullifier root.

Every node of that tree is ONE BabyBear felt. The per-level chip lookup is
`chipLookupTupleNarrow [left, right] par` — the arity-2 NARROW bus, which binds `out0` alone —
and the chain window is `next.cur = loc.par`, a single column. `hash_2_to_1` in
`circuit/src/poseidon2.rs` is the producer-side twin: a genuine 16-wide permutation whose
`state.state[0]` is kept and whose other fifteen lanes are discarded.

So every node value lives in a codomain of size `p = 15·2^27 + 1`, `log2 p = 30.9069`:

                        retired (1 felt)      this file (node8, 8 felts)
  codomain              30.907 bits           247.255 bits
  COLLISION (binding)   2^15.45               2^123.63
  second-preimage       2^30.91               2^247.26

⚑ The COLLISION figure is the binding one. The attacker chooses BOTH sides: they mint a leaf
pair `(q0, q1)` whose parent collides with a genuine adjacent leaf pair of the committed tree,
present it at the same index, and the fold reaches the honest root. `q0` and `q1` are at
consecutive indices, so the consecutiveness tooth is SATISFIED — and they can be chosen to
bracket a nullifier that IS in the set. That is a double-spend for ~2^15.45 hash evaluations.
`circuit/tests/adjacency_forge_tooth.rs` exhibits it.

## The widened scheme

* Every node of the binary tree is a FULL 8-felt Poseidon2 digest (`Digest8`), never a lane-0
  squeeze. Two 8-felt children are exactly `CHIP_RATE = 16` felts, so ONE arity-16 `node8`
  absorb realizes a level — the same `A16` the heap/cap/fields trees already ride, and simpler
  than the 4-ary family's balanced two-stage fold:

      wideNode2(l, r) = A16(l ‖ r)

* The child-ordering algebra is the deployed family's `leftOrderBody` / `rightOrderBody`
  term-for-term, instantiated at each lane with the SHARED direction bit: an 8-felt running node
  sits left or right of an 8-felt sibling as one decision.
* Chain continuity is 8 window gates per path — `next.cur[k] = this.par[k]` for EVERY lane —
  where the deployed family has one.
* PI layout `[root0..7, leaf_lower0..7, leaf_upper0..7, idx_lower, idx_upper]` (piCount 26). The
  LEAVES widen with the root: pinning an 8-felt root while the bracket keys stay 31-bit would
  buy nothing (the class-D lesson `MerkleMembership4aryWideEmit` states).
* THE CATCH TOOTH is preserved verbatim — `u_idx_out - l_idx_out - 1 == 0` as a `VmRow.last`
  boundary, on columns already `piBinding`-pinned to the index PIs. Consecutiveness is an
  INTEGER property of reconstructed positions; it does not widen and must not be dropped.
* The last-row re-lowerings (`AdjacencyMembershipEmit`'s `adjLastOrderFix` / `adjLastIdxFix`)
  are carried over per lane: transition `.gate`s are vacuous on the last row, so without them
  the TOP Merkle level's ordering and the published index would be free.

## What is proved here

* `wideNodeFold_sound` — under a sound WIDE chip table, a row whose node lookup holds carries
  the genuine `wideNode2` of its two 8-felt ordered children in the 8 parent columns: the full
  8-felt node binding, per row, per path.
* `wCont_all_zero_iff` — the 8 continuity windows hold iff the NEXT row's 8-felt running node IS
  this row's 8-felt parent (the widened chain, stated at `Digest8`).
* `wideOrder_arranged_lane` — the per-lane ordering gates pin `(left, right)` to the direction
  bit's arrangement of `(cur, sib)` at EVERY lane.
* `consecutive_body_zero_iff`, `idx_step_body_zero_iff` — the catch tooth's and the index
  reconstruction's teeth (ported to this layout's columns).
* **The anti-masquerade tooth** `interior_forge_narrow_admits_wide_refuses`, in the
  collision-extraction discipline (`Coll8`; the injectivity-hypothesis style is REFUTED at
  deployed parameters): fix two child PAIRS agreeing on lane 0 but differing at some lane. Then
  (1) the deployed `hash_2_to_1` fold is blind — its parents are literally equal, at zero cost;
  and (2) the wide fold refuses: equal wide parents hand back a specific, named, full-width chip
  collision.

NAMED RESIDUAL: the full multi-row `Satisfied2 ⇒` recomposed-two-path refinement lives in
`AdjacencyMembershipRefine` / `Rung2` for the NARROW layout; porting that walk to this layout is
not done here. The per-row teeth are strictly more than the narrow file's parity.

## Axiom hygiene

Definitional descriptor + byte-pinned `#guard` on its wire string + non-vacuous shape/semantic
lemmas. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.AdjacencyMembershipEmit
import Dregg2.Circuit.DeployedCapTree

namespace Dregg2.Circuit.Emit.AdjacencyMembershipWideEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowExpr WindowConstraint Lookup TableId Table
   chipLookupTupleN ChipTableSoundN chip_lookup_sound_N CHIP_RATE CHIP_OUT_LANES emitVmJson2 ChipArityAdmitted chipArity_le_rate)
open Dregg2.Circuit.Emit.AdjacencyMembershipEmit
  (negE dirBinaryBody leftOrderBody rightOrderBody copyWindow copyWindow_eq)
open Dregg2.Circuit.GateExpr (gEsub gSwapLeft gSwapRight gMux gNeg render toEmitted)
open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 pack8_inj)

set_option autoImplicit false

/-! ## §1 — Trace column layout: every Merkle value is an 8-lane group.

One binary tree level per row (depth = trace height), two parallel authentication paths
(lower ‖ upper) plus the shared power-of-two accumulator — the deployed adjacency shape, with
`cur`/`sib`/`left`/`right`/`par` promoted from single felts to 8-lane groups. The direction bit
and the index accumulators stay per-row scalars (a position is one integer, at any digest
width). -/

/-- The 8 columns of a lane group starting at `base`. -/
def lane (base : Nat) : Fin 8 → Nat := fun k => base + k.val

-- LOWER path.
/-- The 8-felt running node of the lower path (row 0 = `leaf_lower`). -/
def aCUR : Fin 8 → Nat := lane 0
/-- The 8-felt co-path sibling at this level (HIDDEN). -/
def aSIB : Fin 8 → Nat := lane 8
/-- The direction bit (`1` ⇒ the running node is the RIGHT child). -/
def aDIR : Nat := 16
/-- The ordered 8-felt left child. -/
def aLEFT : Fin 8 → Nat := lane 17
/-- The ordered 8-felt right child. -/
def aRIGHT : Fin 8 → Nat := lane 25
/-- The 8-felt parent `A16(left ‖ right)`. -/
def aPAR : Fin 8 → Nat := lane 33
/-- Index accumulated BEFORE this level. -/
def aIDX_IN : Nat := 41
/-- Index accumulated INCLUDING this level. -/
def aIDX_OUT : Nat := 42

-- UPPER path (the mirror, +43).
def bCUR : Fin 8 → Nat := lane 43
def bSIB : Fin 8 → Nat := lane 51
def bDIR : Nat := 59
def bLEFT : Fin 8 → Nat := lane 60
def bRIGHT : Fin 8 → Nat := lane 68
def bPAR : Fin 8 → Nat := lane 76
def bIDX_IN : Nat := 84
def bIDX_OUT : Nat := 85

/-- `2^level` for this row (row 0 = 1). -/
def POW : Nat := 86
/-- `2·pow` (the helper feeding the next row's `pow`). -/
def POW2 : Nat := 87

/-- Total main-trace width: 10 8-lane groups + 2 direction bits + 4 index/pow scalars + 2. -/
def ADJW_WIDTH : Nat := 88

/-! ## §2 — Public inputs.

`[root0..7, leaf_lower0..7, leaf_upper0..7, idx_lower, idx_upper]`. The two leaves widen WITH the
root: the sorted-set bracket `lo < nf < hi` the executor checks is over the leaf domain, so a
1-felt leaf PI would re-narrow the gate at its boundary no matter how wide the interior is. -/
def wPI_ROOT (k : Fin 8) : Nat := k.val
def wPI_LEAF_LOWER (k : Fin 8) : Nat := 8 + k.val
def wPI_LEAF_UPPER (k : Fin 8) : Nat := 16 + k.val
def wPI_IDX_LOWER : Nat := 24
def wPI_IDX_UPPER : Nat := 25
def ADJW_PI_COUNT : Nat := 26

/-! ## §3 — Expression builders.

The child-ordering and direction-binary bodies are `AdjacencyMembershipEmit`'s, term-for-term —
they are already column-parameterized, so instantiating them at each lane with the SHARED
direction column is literally the deployed algebra, applied eight times. The index/pow bodies
are re-stated here only because the narrow module's hard-code `POW = 16`. -/

/-- `idx_out - idx_in - dir*pow` (the same-row index accumulation step), with `pow` a parameter. -/
def wIdxStepBody (dir idxIn idxOut pow : Nat) : EmittedExpr :=
  .add (.var idxOut) (.add (negE (.var idxIn)) (negE (.mul (.var dir) (.var pow))))

/-- `pow2 - 2*pow` (the same-row doubling helper). -/
def wPow2Body : EmittedExpr := .add (.var POW2) (.mul (.const (-2)) (.var POW))

/-- `pow - 1` (the row-0 `Fixed pow = 1` anchor). -/
def wPowAnchorBody : EmittedExpr := .add (.var POW) (.const (-1))

/-- `u_idx_out - l_idx_out - 1` — THE CATCH TOOTH, internalized on the Last row where
`aIDX_OUT`/`bIDX_OUT` are already `piBinding`-pinned to the two index PIs. -/
def wConsecutiveBody : EmittedExpr :=
  .add (.var bIDX_OUT) (.add (negE (.var aIDX_OUT)) (.const (-1)))

/-! ## §4 — The per-path per-row block, at full digest width. -/

/-- The 8 columns of a lane group, in lane order (the wide lookup's `digestCols`). -/
def wCols (g : Fin 8 → Nat) : List Nat := (List.finRange 8).map g

/-- Read a lane group under an assignment as a `Digest8`. -/
def wVal (a : Assignment) (g : Fin 8 → Nat) : Digest8 := fun k => a (g k)

/-- The 8 group columns read under `a` ARE `List.ofFn (wVal a g)` — the bridge between the wide
lever's `digestCols.map a` conclusion and the `Digest8` carrier the fold model consumes. -/
theorem wCols_map (a : Assignment) (g : Fin 8 → Nat) :
    (wCols g).map a = List.ofFn (wVal a g) := by
  unfold wCols wVal
  rw [List.map_map, List.ofFn_eq_map]
  rfl

/-- The 16 input expressions of the node absorb: the two ordered 8-lane children, in lane order.
Exactly `CHIP_RATE`, so ONE arity-16 `node8` row realizes a binary level. -/
def wNodeIns (gL gR : Fin 8 → Nat) : List EmittedExpr :=
  (wCols gL ++ wCols gR).map EmittedExpr.var

/-- The node input list evaluates to exactly `pack8` of the two ordered children — the same
`L8 ‖ R8` block the deployed heap/cap `node8` absorbs. -/
theorem wNodeIns_eval (a : Assignment) (gL gR : Fin 8 → Nat) :
    (wNodeIns gL gR).map (·.eval a) = pack8 (wVal a gL) (wVal a gR) := by
  have hcomp : ∀ g : Fin 8 → Nat,
      ((wCols g).map EmittedExpr.var).map (·.eval a) = (wCols g).map a := by
    intro g
    rw [List.map_map]
    rfl
  simp only [wNodeIns, List.map_append, hcomp, wCols_map]
  rfl

/-- The per-lane ordering bodies for one path: `left[k]` and `right[k]` under the shared bit. -/
def wOrderBodiesAt (cur sib : Fin 8 → Nat) (dir : Nat) (left right : Fin 8 → Nat) (k : Fin 8) :
    List EmittedExpr :=
  [ leftOrderBody (cur k) (sib k) dir (left k)
  , rightOrderBody (cur k) (sib k) dir (right k) ]

/-- The per-row polynomial bodies of ONE path: the direction-binary gate, then the two ordering
gates at each of the 8 lanes, then the index-accumulation step. `1 + 8·2 + 1 = 18` bodies. -/
def wPathBodies (cur sib : Fin 8 → Nat) (dir : Nat) (left right : Fin 8 → Nat)
    (idxIn idxOut : Nat) : List EmittedExpr :=
  (dirBinaryBody dir)
    :: (((List.finRange 8).map (wOrderBodiesAt cur sib dir left right)).flatten
        ++ [wIdxStepBody dir idxIn idxOut POW])

/-- The node lookup of one path: `A16(left8 ‖ right8)` → the 8 parent columns, EVERY lane bound
by the wide bus (`TableId.poseidon2`, tuple width `1 + 16 + 8 = 25`). The deployed narrow
descriptor rides `chipLookupTupleNarrow` and binds `out0` alone — that is the wound. -/
def wNodeLookup (left right par : Fin 8 → Nat) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (wNodeIns left right) (wCols par)⟩

/-- The 8 cross-row continuity windows of one path: `next.cur[k] = this.par[k]` at EVERY lane. -/
def wContinuity (cur par : Fin 8 → Nat) : List VmConstraint2 :=
  (List.finRange 8).map fun k => .windowGate (copyWindow (cur k) (par k))

/-- Lane `k`'s continuity window body. -/
def wContWindow (cur par : Fin 8 → Nat) (k : Fin 8) : WindowExpr :=
  (copyWindow (cur k) (par k)).body

/-- One path's complete per-row block: the 18 transition gates, the wide node lookup, the 8-lane
chain continuity, and the index carry. -/
def wPathBlock (cur sib : Fin 8 → Nat) (dir : Nat) (left right par : Fin 8 → Nat)
    (idxIn idxOut : Nat) : List VmConstraint2 :=
  ((wPathBodies cur sib dir left right idxIn idxOut).map fun b => .base (.gate b))
    ++ [wNodeLookup left right par]
    ++ wContinuity cur par
    ++ [.windowGate (copyWindow idxIn idxOut)]

/-! ## §5 — The constraint list and the descriptor. -/

/-- The LOWER path's per-row bodies. -/
def wBodiesLower : List EmittedExpr :=
  wPathBodies aCUR aSIB aDIR aLEFT aRIGHT aIDX_IN aIDX_OUT
/-- The UPPER path's per-row bodies. -/
def wBodiesUpper : List EmittedExpr :=
  wPathBodies bCUR bSIB bDIR bLEFT bRIGHT bIDX_IN bIDX_OUT

/-- **The last-row re-lowering** — every per-row body of both paths, re-emitted as a `VmRow.last`
boundary. The transition `.gate`s are vacuous on the last row, so without this the TOP Merkle
level's direction bit and child ordering would be unconstrained (the forge
`AdjacencyMembershipEmit.adjLastOrderFix` closed) and the published index would be decoupled from
its in-circuit reconstruction (`adjLastIdxFix`). Both fixes are carried here, per lane. -/
def wLastRowFix : List VmConstraint2 :=
  (wBodiesLower ++ wBodiesUpper).map fun b => .base (.boundary VmRow.last b)

/-- The 16 leaf pins: the row-0 running nodes are the two 8-felt leaf PIs. -/
def wLeafPins : List VmConstraint2 :=
  ((List.finRange 8).map fun k => .base (.piBinding VmRow.first (aCUR k) (wPI_LEAF_LOWER k)))
    ++ ((List.finRange 8).map fun k => .base (.piBinding VmRow.first (bCUR k) (wPI_LEAF_UPPER k)))

/-- The 16 root pins: BOTH paths' last-row parents are the SAME 8-felt root PI block — the
"two paths reach one committed root" condition, at full digest width. -/
def wRootPins : List VmConstraint2 :=
  ((List.finRange 8).map fun k => .base (.piBinding VmRow.last (aPAR k) (wPI_ROOT k)))
    ++ ((List.finRange 8).map fun k => .base (.piBinding VmRow.last (bPAR k) (wPI_ROOT k)))

/-- The shared power-of-two accumulator, the row-0 anchors, the index PI pins, and THE CATCH
TOOTH. -/
def wSharedBlock : List VmConstraint2 :=
  [ .base (.gate wPow2Body)
  , .windowGate (copyWindow POW POW2)
  , .base (.piBinding VmRow.last aIDX_OUT wPI_IDX_LOWER)
  , .base (.piBinding VmRow.last bIDX_OUT wPI_IDX_UPPER)
  , .base (.boundary VmRow.first wPowAnchorBody)
  , .base (.boundary VmRow.first (.var aIDX_IN))
  , .base (.boundary VmRow.first (.var bIDX_IN))
  , .base (.boundary VmRow.last wConsecutiveBody) ]

/-- The full constraint list. -/
def adjacencyWideConstraints : List VmConstraint2 :=
  wPathBlock aCUR aSIB aDIR aLEFT aRIGHT aPAR aIDX_IN aIDX_OUT
    ++ wPathBlock bCUR bSIB bDIR bLEFT bRIGHT bPAR bIDX_IN bIDX_OUT
    ++ wSharedBlock ++ wLeafPins ++ wRootPins ++ wLastRowFix

/-- **`adjacencyWideDesc`** — the WIDE neighbor-adjacency descriptor: 8-felt nodes, one arity-16
`node8` absorb per level per path, an 8-lane chain, 8-felt leaves and root, and the internalized
consecutiveness catch tooth. Tree depth is the trace height; the algebra is uniform for every
supported power-of-two depth, exactly as the narrow descriptor's was. -/
def adjacencyWideDesc : EffectVmDescriptor2 :=
  { name        := "dregg-membership-adjacency-wide::node8-v1"
  , traceWidth  := ADJW_WIDTH
  , piCount     := ADJW_PI_COUNT
  , tables      := []
  , constraints := adjacencyWideConstraints
  , hashSites   := []
  , ranges      := [] }

theorem descriptor_has_complete_shape :
    adjacencyWideDesc.constraints =
      wPathBlock aCUR aSIB aDIR aLEFT aRIGHT aPAR aIDX_IN aIDX_OUT
        ++ wPathBlock bCUR bSIB bDIR bLEFT bRIGHT bPAR bIDX_IN bIDX_OUT
        ++ wSharedBlock ++ wLeafPins ++ wRootPins ++ wLastRowFix := rfl

/-! ## §6 — The node fold: what a satisfied row FORCES, at full width. -/

/-- **`wideNode2`** — the widened binary node function: ONE arity-16 `node8` absorb over the two
ordered 8-felt children. All 16 child felts enter the preimage; all 8 output lanes ARE the node.
The Rust twin is `absorb16` (`circuit/src/membership_descriptor_4ary.rs`). -/
def wideNode2 (absorb : List ℤ → Digest8) (l r : Digest8) : Digest8 := absorb (pack8 l r)

/-- The wide permutation output of an 8-output absorb, as the `List ℤ` block a sound wide chip
table carries. -/
def wPermOut (absorb : List ℤ → Digest8) : List ℤ → List ℤ := fun xs => List.ofFn (absorb xs)

/-- **`wideNodeFold_sound`** — under a SOUND WIDE chip table, a row whose node lookup holds
carries the genuine `wideNode2` of its two ordered 8-felt children in the 8 parent columns. The
wide lever (`chip_lookup_sound_N`) forces every parent column; nothing rides lane 0 alone. -/
theorem wideNodeFold_sound (absorb : List ℤ → Digest8) (tbl : Table)
    (hChip : ChipTableSoundN (wPermOut absorb) tbl) (a : Assignment)
    (left right par : Fin 8 → Nat)
    (hP : (chipLookupTupleN (wNodeIns left right) (wCols par)).map (·.eval a) ∈ tbl) :
    wVal a par = wideNode2 absorb (wVal a left) (wVal a right) := by
  -- 8 + 8 = 16 lanes: the admitted `node8` full-width compression arity. Literal spine.
  have hadm : ChipArityAdmitted (wNodeIns left right).length := of_decide_eq_true (Eq.refl true)
  have h := chip_lookup_sound_N (wPermOut absorb) tbl hChip a _ _ hadm hP
  rw [wCols_map, wNodeIns_eval] at h
  exact List.ofFn_inj.mp h

/-! ## §7 — The 8-lane chain, and the per-lane ordering. -/

/-- Lane `k`'s continuity body vanishes exactly when that lane chains. -/
theorem wCont_zero_iff (cur par : Fin 8 → Nat) (k : Fin 8) (env : VmRowEnv) :
    (wContWindow cur par k).eval env = 0 ↔ env.nxt (cur k) = env.loc (par k) := by
  simp only [wContWindow, copyWindow_eq, WindowExpr.eval]
  constructor <;> intro h <;> omega

/-- **The widened chain, at `Digest8`**: all 8 continuity windows vanish iff the next row's
8-felt running node IS this row's 8-felt parent. The interior of the tree is chained at full
digest width — the property whose absence made the deployed adjacency interior ~31-bit. -/
theorem wCont_all_zero_iff (cur par : Fin 8 → Nat) (env : VmRowEnv) :
    (∀ k : Fin 8, (wContWindow cur par k).eval env = 0)
      ↔ wVal env.nxt cur = wVal env.loc par := by
  constructor
  · intro h
    funext k
    exact (wCont_zero_iff cur par k env).mp (h k)
  · intro h k
    exact (wCont_zero_iff cur par k env).mpr (congrFun h k)

/-- **`wideOrder_arranged_lane`** — at EVERY lane `k`, a row satisfying the direction-binary gate
and lane `k`'s two ordering gates has `(left[k], right[k])` equal to the direction bit's
arrangement of `(cur[k], sib[k])`. The bit is shared, so all 8 lanes arrange together: an 8-felt
child is one child. -/
theorem wideOrder_arranged_lane (a : Assignment) (cur sib : Fin 8 → Nat) (dir : Nat)
    (left right : Fin 8 → Nat) (k : Fin 8)
    (hd : (dirBinaryBody dir).eval a = 0)
    (hl : (leftOrderBody (cur k) (sib k) dir (left k)).eval a = 0)
    (hr : (rightOrderBody (cur k) (sib k) dir (right k)).eval a = 0) :
    (a dir = 0 ∧ a (left k) = a (cur k) ∧ a (right k) = a (sib k))
      ∨ (a dir = 1 ∧ a (left k) = a (sib k) ∧ a (right k) = a (cur k)) := by
  simp only [dirBinaryBody, negE, EmittedExpr.eval] at hd
  simp only [leftOrderBody, rightOrderBody, render, gEsub, gSwapLeft, gSwapRight, gMux, gNeg,
    toEmitted, EmittedExpr.eval] at hl hr
  have hb : a dir = 0 ∨ a dir = 1 := by
    have h : a dir * (a dir - 1) = 0 := by linear_combination hd
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hb with h0 | h1
  · rw [h0] at hl hr
    exact Or.inl ⟨h0, by linarith, by linarith⟩
  · rw [h1] at hl hr
    exact Or.inr ⟨h1, by linarith, by linarith⟩

/-- **The whole 8-felt child, arranged.** Under the direction-binary gate and ALL 16 ordering
gates of a path, the ordered children ARE the two `Digest8` values, swapped by the bit. Stated at
`Digest8` — the deployed narrow gate can only say this of one felt. -/
theorem wideOrder_arranged_digest (a : Assignment) (cur sib : Fin 8 → Nat) (dir : Nat)
    (left right : Fin 8 → Nat)
    (hd : (dirBinaryBody dir).eval a = 0)
    (hall : ∀ k : Fin 8,
      (leftOrderBody (cur k) (sib k) dir (left k)).eval a = 0 ∧
      (rightOrderBody (cur k) (sib k) dir (right k)).eval a = 0) :
    (wVal a left = wVal a cur ∧ wVal a right = wVal a sib)
      ∨ (wVal a left = wVal a sib ∧ wVal a right = wVal a cur) := by
  have hb : a dir = 0 ∨ a dir = 1 := by
    simp only [dirBinaryBody, negE, EmittedExpr.eval] at hd
    have h : a dir * (a dir - 1) = 0 := by linear_combination hd
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hb with h0 | h1
  · refine Or.inl ⟨funext fun k => ?_, funext fun k => ?_⟩ <;>
      · obtain ⟨hl, hr⟩ := hall k
        rcases wideOrder_arranged_lane a cur sib dir left right k hd hl hr with
          ⟨_, hL, hR⟩ | ⟨h1', _, _⟩
        · first | exact hL | exact hR
        · exact absurd (h0 ▸ h1' : (0 : ℤ) = 1) (by decide)
  · refine Or.inr ⟨funext fun k => ?_, funext fun k => ?_⟩ <;>
      · obtain ⟨hl, hr⟩ := hall k
        rcases wideOrder_arranged_lane a cur sib dir left right k hd hl hr with
          ⟨h0', _, _⟩ | ⟨_, hL, hR⟩
        · exact absurd (h1 ▸ h0' : (1 : ℤ) = 0) (by decide)
        · first | exact hL | exact hR

/-! ## §8 — The catch tooth's teeth and the index reconstruction (ported to this layout). -/

/-- THE CATCH TOOTH's teeth: the consecutiveness gate body is zero EXACTLY when the upper index
is one past the lower — TRUE for a genuine adjacent pair, FALSE otherwise. Consecutiveness is an
integer property of reconstructed positions and does NOT widen; this is the narrow module's
lemma at this layout's columns. -/
theorem consecutive_body_zero_iff (a : Assignment) :
    wConsecutiveBody.eval a = 0 ↔ a bIDX_OUT = a aIDX_OUT + 1 := by
  simp only [wConsecutiveBody, negE, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- THE INDEX-RECONSTRUCTION fix's teeth: the index-step body vanishes EXACTLY when the published
`idx_out` equals the genuine in-circuit reconstruction `idx_in + dir*pow`. -/
theorem idx_step_body_zero_iff (a : Assignment) (dir idxIn idxOut pow : Nat) :
    (wIdxStepBody dir idxIn idxOut pow).eval a = 0 ↔ a idxOut = a idxIn + a dir * a pow := by
  simp only [wIdxStepBody, negE, EmittedExpr.eval]
  constructor <;> intro h <;> linarith

/-! ## §9 — The anti-masquerade tooth (collision-extraction discipline).

The injectivity-hypothesis style is REFUTED at deployed parameters (`Compress8CR` is false for
the real chip), so conclusions hand back the SPECIFIC colliding pair a total extractor returns,
never a bare `∃` — which pigeonhole makes unconditionally true and therefore contentless. -/

/-- The DEPLOYED 1-felt binary node, stated of the same 8-felt data: absorb ONLY lane 0 of each
child. This is `hash_2_to_1` / `chipLookupTupleNarrow [left, right] par` — arity 2, `out0` alone.
Lanes 1..7 never enter the preimage. -/
def narrowNode2Lane0 (absorb : List ℤ → Digest8) (l r : Digest8) : Digest8 :=
  absorb [l 0, r 0]

/-- The wide-node collision extractor: the two arity-16 preimage blocks. Total; branches are
decidable. -/
def wideNode2Coll8Find (l r l' r' : Digest8) : List ℤ × List ℤ :=
  (pack8 l r, pack8 l' r')

/-- **`wideNode2_binds_or_collides`** — equal wide parents EITHER force both 8-felt children
equal, OR the extractor's pair is a genuine full-width chip collision, handed back by name. -/
theorem wideNode2_binds_or_collides (absorb : List ℤ → Digest8) (l r l' r' : Digest8)
    (heq : wideNode2 absorb l r = wideNode2 absorb l' r') :
    (l = l' ∧ r = r') ∨ Coll8 absorb (wideNode2Coll8Find l r l' r') := by
  by_cases hpk : pack8 l r = pack8 l' r'
  · exact Or.inl (pack8_inj hpk)
  · exact Or.inr ⟨hpk, heq⟩

/-- **⚑ THE ANTI-MASQUERADE TOOTH.** Fix two child PAIRS that agree on lane 0 (so the deployed
1-felt `hash_2_to_1` fold cannot tell them apart) but differ at lane `j` of the left child — the
interior-forge class. Field-faithfully:

1. the deployed lane-0 fold is BLIND: its outputs are literally equal — the forge is FREE; and
2. the WIDE fold REFUSES: if the wide parents are equal too, the extractor's pair is a genuine
   full-width chip collision. The forge that cost ~2^15.45 hash evaluations against the deployed
   node now costs a real Poseidon2 collision over the full 16-felt preimage domain. -/
theorem interior_forge_narrow_admits_wide_refuses (absorb : List ℤ → Digest8)
    {l r l' r' : Digest8} (j : Fin 8)
    (hlane0 : l 0 = l' 0 ∧ r 0 = r' 0)
    (hdiff : l j ≠ l' j) :
    narrowNode2Lane0 absorb l r = narrowNode2Lane0 absorb l' r'
    ∧ (wideNode2 absorb l r = wideNode2 absorb l' r' →
        Coll8 absorb (wideNode2Coll8Find l r l' r')) := by
  constructor
  · unfold narrowNode2Lane0
    rw [hlane0.1, hlane0.2]
  · intro heq
    rcases wideNode2_binds_or_collides absorb l r l' r' heq with hbind | hcoll
    · exact absurd (congrFun hbind.1 j) hdiff
    · exact hcoll

-- Satisfiability canaries: a lane-0-agreeing, lane-1-differing pair EXISTS, the extractor
-- returns a genuine collision under a toy absorb, and the narrow fold is blind on that pair.
def toyAbsorb : List ℤ → Digest8 := fun _ _ => 0
def laneForged : Digest8 := fun k => if k.val = 1 then 5 else 0
def laneZero : Digest8 := fun _ => 0
#guard decide (laneForged 0 = laneZero 0)
#guard decide (laneForged 1 ≠ laneZero 1)
#guard decide (wideNode2 toyAbsorb laneForged laneZero = wideNode2 toyAbsorb laneZero laneZero)
#guard decide (Coll8 toyAbsorb (wideNode2Coll8Find laneForged laneZero laneZero laneZero))
#guard decide (narrowNode2Lane0 toyAbsorb laneForged laneZero
  = narrowNode2Lane0 toyAbsorb laneZero laneZero)

/-! ## §10 — Shape pins (non-vacuous; every one moves if a layout constant drifts). -/

#guard adjacencyWideDesc.traceWidth == ADJW_WIDTH
#guard adjacencyWideDesc.piCount == ADJW_PI_COUNT
#guard adjacencyWideDesc.tables.length == 0
#guard ADJW_WIDTH == 88
#guard ADJW_PI_COUNT == 26
#guard wBodiesLower.length == 18
#guard wBodiesUpper.length == 18
#guard wLastRowFix.length == 36
#guard wLeafPins.length == 16
#guard wRootPins.length == 16
#guard (wNodeIns aLEFT aRIGHT).length == CHIP_RATE
#guard (chipLookupTupleN (wNodeIns aLEFT aRIGHT) (wCols aPAR)).length == 1 + CHIP_RATE + 8
#guard wCols aCUR == [0, 1, 2, 3, 4, 5, 6, 7]
#guard wCols aPAR == [33, 34, 35, 36, 37, 38, 39, 40]
#guard wCols bPAR == [76, 77, 78, 79, 80, 81, 82, 83]
#guard CHIP_OUT_LANES == 8

-- The staged adjacency to the RETIRED narrow descriptor: distinct names, distinct shapes, so no
-- proof or wire identity can cross between them.
#guard Dregg2.Circuit.Emit.AdjacencyMembershipEmit.adjacencyDesc.traceWidth == 18
#guard Dregg2.Circuit.Emit.AdjacencyMembershipEmit.adjacencyDesc.piCount == 5
#guard Dregg2.Circuit.Emit.AdjacencyMembershipEmit.adjacencyDesc.name != adjacencyWideDesc.name

-- Continuity non-vacuity: lane 0 accepts a chained window and rejects an unchained one; and the
-- interior canary — a next row copying lane 0 but dropping lane 7 satisfies the lane-0 window and
-- FAILS the lane-7 window. That assignment class is exactly what the deployed single-window
-- continuity admitted wholesale.
#guard decide ((wContWindow aCUR aPAR 0).eval
  ⟨fun i => if i = aPAR 0 then 7 else 0, fun i => if i = aCUR 0 then 7 else 0, fun _ => 0, fun _ => 0⟩ = 0)
#guard decide (¬ ((wContWindow aCUR aPAR 0).eval
  ⟨fun _ => 0, fun i => if i = aCUR 0 then 7 else 0, fun _ => 0, fun _ => 0⟩ = 0))
#guard decide ((wContWindow aCUR aPAR 0).eval
  ⟨fun i => if i = aPAR 0 then 7 else if i = aPAR 7 then 9 else 0,
   fun i => if i = aCUR 0 then 7 else 0, fun _ => 0, fun _ => 0⟩ = 0)
#guard decide (¬ ((wContWindow aCUR aPAR 7).eval
  ⟨fun i => if i = aPAR 0 then 7 else if i = aPAR 7 then 9 else 0,
   fun i => if i = aCUR 0 then 7 else 0, fun _ => 0, fun _ => 0⟩ = 0))

-- The catch tooth ACCEPTS an adjacent pair and REJECTS a gap.
#guard decide (wConsecutiveBody.eval
  (fun i => if i = bIDX_OUT then 6 else if i = aIDX_OUT then 5 else 0) = 0)
#guard decide (¬ (wConsecutiveBody.eval
  (fun i => if i = bIDX_OUT then 7 else if i = aIDX_OUT then 5 else 0) = 0))

/-! ## §11 — Axiom hygiene on the keystones. -/

#assert_axioms descriptor_has_complete_shape
#assert_axioms wideNodeFold_sound
#assert_axioms wCont_all_zero_iff
#assert_axioms wideOrder_arranged_lane
#assert_axioms wideOrder_arranged_digest
#assert_axioms consecutive_body_zero_iff
#assert_axioms idx_step_body_zero_iff
#assert_axioms wideNode2_binds_or_collides
#assert_axioms interior_forge_narrow_admits_wide_refuses

/-! ## §12 — The byte-pinned wire golden.

THE EQUALITY-GATE ANCHOR: `scripts/emit-descriptors.sh` writes exactly these bytes to
`circuit/descriptors/by-name/adjacency-membership-wide.json`, which
`circuit/src/adjacency_witness.rs` `include_str!`s and `parse_vm_descriptor2` ingests. A drift on
either side breaks THIS `#guard` (Lean) or the Rust descriptor-drift gate. -/

/-- Exact emitted-wire golden (generated via `#eval repr (emitVmJson2 adjacencyWideDesc)`). -/
def ADJACENCY_WIDE_GOLDEN : String :=
  "{\"name\":\"dregg-membership-adjacency-wide::node8-v1\",\"ir\":2,\"trace_width\":88,\"public_input_count\":26,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":16}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":6}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":7}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":86}}}}}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25},{\"t\":\"var\",\"v\":26},{\"t\":\"var\",\"v\":27},{\"t\":\"var\",\"v\":28},{\"t\":\"var\",\"v\":29},{\"t\":\"var\",\"v\":30},{\"t\":\"var\",\"v\":31},{\"t\":\"var\",\"v\":32},{\"t\":\"var\",\"v\":33},{\"t\":\"var\",\"v\":34},{\"t\":\"var\",\"v\":35},{\"t\":\"var\",\"v\":36},{\"t\":\"var\",\"v\":37},{\"t\":\"var\",\"v\":38},{\"t\":\"var\",\"v\":39},{\"t\":\"var\",\"v\":40}]},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":33}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":34}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":35}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":36}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":37}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":38}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":39}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":40}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":41},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":42}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"var\",\"v\":59}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":59}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":60},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":51}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":69},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":52}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":70},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":53}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":46}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":71},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":54}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":47}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":72},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":48}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":73},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":56}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":57},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":49}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":74},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":57},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":57}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":67},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":50}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":75},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":58}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":84}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"var\",\"v\":86}}}}}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":60},{\"t\":\"var\",\"v\":61},{\"t\":\"var\",\"v\":62},{\"t\":\"var\",\"v\":63},{\"t\":\"var\",\"v\":64},{\"t\":\"var\",\"v\":65},{\"t\":\"var\",\"v\":66},{\"t\":\"var\",\"v\":67},{\"t\":\"var\",\"v\":68},{\"t\":\"var\",\"v\":69},{\"t\":\"var\",\"v\":70},{\"t\":\"var\",\"v\":71},{\"t\":\"var\",\"v\":72},{\"t\":\"var\",\"v\":73},{\"t\":\"var\",\"v\":74},{\"t\":\"var\",\"v\":75},{\"t\":\"var\",\"v\":76},{\"t\":\"var\",\"v\":77},{\"t\":\"var\",\"v\":78},{\"t\":\"var\",\"v\":79},{\"t\":\"var\",\"v\":80},{\"t\":\"var\",\"v\":81},{\"t\":\"var\",\"v\":82},{\"t\":\"var\",\"v\":83}]},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":76}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":77}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":78}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":46},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":79}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":47},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":80}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":48},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":81}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":82}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":50},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":83}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":84},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":85}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":87},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":86}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":86},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":87}}}},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":42,\"pi_index\":24},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":85,\"pi_index\":25},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":86},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":41}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":84}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":15},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":43,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":44,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":45,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":46,\"pi_index\":19},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":47,\"pi_index\":20},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":48,\"pi_index\":21},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":49,\"pi_index\":22},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":50,\"pi_index\":23},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":33,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":34,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":35,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":36,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":37,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":38,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":39,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":40,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":76,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":77,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":78,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":79,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":80,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":81,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":82,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":83,\"pi_index\":7},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":16}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":6}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":7}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":86}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"var\",\"v\":59}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":59}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":60},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":51}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":69},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":52}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":70},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":53}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":46}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":71},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":54}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":47}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":72},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":48}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":73},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":56}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":57},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":49}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":74},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":57},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":57}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":67},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":50}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":75},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":58}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":84}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"var\",\"v\":86}}}}}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 adjacencyWideDesc == ADJACENCY_WIDE_GOLDEN
#guard adjacencyWideDesc.constraints.length == 132

end Dregg2.Circuit.Emit.AdjacencyMembershipWideEmit
