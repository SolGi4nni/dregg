/-
# Dregg2.Circuit.Emit.AutomataflResolveMembership — STRUCTURED, n-INDEPENDENT gate-membership for
Leg R (`old → mid`).

## Why this file exists

`AutomataflResolveRefine`'s `_of_sat` extractions each need a fact of the shape
`cgH h ∈ automataflResolveDesc.constraints` (or `cg g ∈ …`) — "this specific emitted gate is in the
descriptor's constraint list". Historically each such fact was discharged by `by decide`: Lean
EVALUATES the entire concrete `n = 2` 379-element list and searches it for the gate. That is
(a) slow, (b) IMPOSSIBLE at `n = 11` (the list explodes with `n`), and (c) brittle — any change to
the list (e.g. the coming commitment swap) re-lays every position and breaks every `decide`.

This file replaces that with STRUCTURED membership: from the `List.append` / `List.range` / `List.map`
SHAPE of `NGen.resolveConstraints n` we prove, for ARBITRARY `n`, that "gate `g` of family `F` is a
member of `(automataflResolveDescN n).constraints`". The proofs are `List.mem_append` / `List.mem_map`
/ `List.mem_range` plumbing — NO enumerated `decide`, NO dependence on the concrete length.

Two layers:

  * **§1 top-level family membership** — `mem_resolve_of_mem_validateMove0`, `…_autoRead`,
    `…_srcNonVac`, … : `g ∈ (family n args) → g ∈ (automataflResolveDescN n).constraints`. These are
    the reusable, n-generic backbone: they navigate the fixed 13-way append spine
    (`onePin :: boardRange ++ autoRead ++ validateMove×2 ++ validateOcclusion×2 ++ srcNonVac ++
    pattern ++ selection ++ carry ++ flowThrough ++ writeMid ++ bindBoardRoots`). Only the NON-
    COMMITMENT families are exposed as stable seams — they PRECEDE `bindBoardRoots`, so their
    positions survive the commitment swap.

  * **§2 combinator membership** — `mem_rangeNonneg_bit`, `mem_rangeNonneg_head`,
    `mem_oneHot_*`, `mem_eqScalar_*`, `mem_forcedGe0_*`, `mem_decompose_*` : where a specific gate
    sits INSIDE a family (which is itself an append of the `builder.rs` combinators). These are also
    n-generic (functions of the `rbits`/selector-list arguments), by the same `List.mem_*` plumbing.

## How `AutomataflResolveRefine` uses these (the migration)

The refinement's membership goals are stated in the FROZEN (`NN = 2`) vocabulary over
`automataflResolveDesc.constraints`. Since `automataflResolveDesc.constraints` is DEFINITIONALLY
`NGen.resolveConstraints 2` (the design's defeq, `automataflResolveDesc := automataflResolveDescN 2`)
and every frozen column/gate def is defeq to its `NGen … 2` twin, an n-generic lemma instantiated at
`n = 2` closes the frozen goal by `exact` (Lean unifies up to defeq — it does NOT re-evaluate the
list). So the same proof term works at `n = 2` today and at `n = 11` after the descN cutover.

## Axiom hygiene

Pure list-membership lemmas; imports read-only. No `sorry`, no `native_decide`, no `decide` over the
whole list. `#assert_axioms` subset `{propext, Classical.choice, Quot.sound}` (in practice these are
`Eq`/`Iff`-free structural proofs, so the set is empty or `{propext}`).
-/
import Dregg2.Circuit.Emit.AutomataflResolveEmit

namespace Dregg2.Circuit.Emit.AutomataflResolveMembership

open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)

set_option autoImplicit false

open Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen

/-! ## §0 — The descriptor's constraint list IS the parametric fold. -/

/-- Unfold the descriptor projection to the `NGen` fold. Definitional, but naming it lets the
family lemmas rewrite the goal to the raw `++`-spine without re-deriving the projection each time. -/
theorem descN_constraints (n : Nat) :
    (automataflResolveDescN n).constraints = NGen.resolveConstraints n := rfl

/-! ## §1 — Top-level family membership. Navigate the fixed 13-way append spine.

`NGen.resolveConstraints n = onePin n :: (F₀ ++ F₁ ++ … ++ F₁₂)`. `++` is LEFT-associative, so the
tail is `((…((F₀ ++ F₁) ++ F₂)…) ++ F₁₂)`. To land in `Fᵢ` we skip the `onePin` cons
(`mem_cons_of_mem`), skip everything to the LEFT of `Fᵢ` with one `mem_append_right` (none for `F₀`),
then skip everything to the RIGHT with `(12 − i)` `mem_append_left`s. Each lemma is n-generic — it
never touches the LENGTH of any family, only the spine shape. -/

variable {g : VmConstraint2} {n : Nat}

/-- The reusable navigator base: after unfolding the descriptor to the parametric fold, the
constraint list is `onePin n :: (F₀ ++ F₁ ++ … ++ F₁₂)`. `++` is LEFT-associative, so the spine is
`((…((F₀ ++ F₁) ++ F₂)…) ++ F₁₂)`; family `Fᵢ` is reached by one `mem_append_right` (skip everything
left of `Fᵢ`, none for `F₀`) then `(12 − i)` `mem_append_left`s (skip everything right). Purely
structural — NO family LENGTH, NO atom evaluation, so it is n-generic and survives the commitment
swap for every family that PRECEDES `bindBoardRoots` (all twelve below). -/
theorem mem_resolve_of_mem_boardRange
    (h : g ∈ NGen.boardRangeConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (h))))))))))))))))))

theorem mem_resolve_of_mem_autoRead
    (h : g ∈ NGen.autoReadConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))))))))))))

theorem mem_resolve_of_mem_validateMove0
    (h : g ∈ NGen.validateMove n (NGen.mvBase n 0)) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))))))))))

theorem mem_resolve_of_mem_validateMove1
    (h : g ∈ NGen.validateMove n (NGen.mvBase n 1)) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))))))))))

theorem mem_resolve_of_mem_validateOcclusion0
    (h : g ∈ NGen.validateOcclusion n (NGen.mvBase n 0) (NGen.occBase n 0) (NGen.mvBase n 1)) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))))))))

theorem mem_resolve_of_mem_validateOcclusion1
    (h : g ∈ NGen.validateOcclusion n (NGen.mvBase n 1) (NGen.occBase n 1) (NGen.mvBase n 0)) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))))))))

theorem mem_resolve_of_mem_srcNonVac
    (h : g ∈ NGen.srcNonVacConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))))))

theorem mem_resolve_of_mem_patternBit
    (h : g ∈ NGen.patternBitConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))))))

theorem mem_resolve_of_mem_selection
    (h : g ∈ NGen.selectionConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))))

theorem mem_resolve_of_mem_carry
    (h : g ∈ NGen.carryConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))))

theorem mem_resolve_of_mem_flowThrough
    (h : g ∈ NGen.flowThroughConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))))

theorem mem_resolve_of_mem_writeMid
    (h : g ∈ NGen.writeMidConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))))

/-- The COMMITMENT family (`F₁₅` after the CHUNK-1 additive tail, still the packed board commitment)
is emitted LAST: one `mem_append_right`. Because it is STILL last, every family lemma above keeps its
spine position modulo the uniform `+3 mem_append_left` (the three new families inserted BEFORE it) —
which is why this navigator is unchanged and the commit-seam proofs are undisturbed. -/
theorem mem_resolve_of_mem_commit
    (h : g ∈ NGen.commitBoardsConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_right _ h)

/-! ### CHUNK-1/CHUNK-3 additive-tail navigators. Spine order after `writeMid`:
`… ++ writeMid ++ inclOcclusion(F₁₂) ++ nonLeave(F₁₃) ++ resolvable(F₁₄) ++ carryV2(F₁₅)
++ midV2(F₁₆) ++ commit(F₁₇)`. Each is reached by peeling the families to its RIGHT with
`mem_append_left`, then one `mem_append_right`. The CHUNK-3 insertion of `carryV2`/`midV2` before
`commit` added exactly `+2 mem_append_left` to every family that PRECEDES them (all above, and the
CHUNK-1 twelve); `commit` stays rightmost, so its navigator is unchanged. Chunk 2 (`occ_iff_blocked`)
consumes `_inclOcclusion`; chunk 4 (`resolve_sat_imp_resolveMovesN`) consumes `_carryV2` / `_midV2`
(and `_nonLeave` / `_resolvable`). -/

/-- The inclusive-occlusion family (`F₁₂`): peel commit, midV2, carryV2, resolvable, nonLeave (5),
then in. -/
theorem mem_resolve_of_mem_inclOcclusion
    (h : g ∈ NGen.inclOcclusionConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))))

/-- The non-leaver family (`F₁₃`): peel commit, resolvable (2), then in. -/
theorem mem_resolve_of_mem_nonLeave
    (h : g ∈ NGen.nonLeaveConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))))

/-- The resolvable family (`F₁₄`): peel commit, midV2, carryV2 (3), then in. -/
theorem mem_resolve_of_mem_resolvable
    (h : g ∈ NGen.resolvableConstraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))

/-- The CHUNK-3 corrected-carry family (`F₁₅`): peel commit, midV2 (2), then in. -/
theorem mem_resolve_of_mem_carryV2
    (h : g ∈ NGen.carryV2Constraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))

/-- The CHUNK-3 corrected board rewrite family (`F₁₆`): peel commit (1), then in. -/
theorem mem_resolve_of_mem_midV2
    (h : g ∈ NGen.midV2Constraints n) : g ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ h))

/-! ## §2a — Combinator membership. Where a specific gate sits INSIDE a `builder.rs` combinator.

Each family is an append of the shared `builder.rs` combinators (`rangeNonnegConstraints`,
`oneHotConstraints`/`oneHotAtCol`, `forcedGe0ConstraintsN`, `eqScalarConstraints`,
`oneHotGatedConstraints`, `NGen.decomposeConstraints`) plus singletons. These lemmas locate a gate
within ONE combinator, generically in the combinator's OWN arguments (`rbits`, the selector `sels`,
…) — never in `n` or a list LENGTH. `List.mem_map`/`List.mem_range`/`List.mem_append`/`mem_singleton`
plumbing only. -/

/-- The k-th boolean bit of a `range_nonneg` block. -/
theorem mem_rangeNonneg_bit (h : Head) (bit0 rbits k : Nat) (hk : k < rbits) :
    cg (gBin (bit0 + k)) ∈ rangeNonnegConstraints h bit0 rbits :=
  List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)

/-- The recomposition head of a `range_nonneg` block (its final gate). -/
theorem mem_rangeNonneg_head (h : Head) (bit0 rbits : Nat) :
    cgH ((List.range rbits).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k)) h)
      ∈ rangeNonnegConstraints h bit0 rbits :=
  List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- The k-th LOWER-edge bit of a `decompose_coord_le` block. -/
theorem mem_decompose_loBit (n col loBit0 hiBit0 k : Nat) (hk : k < NGen.COORD_RBITS n) :
    cg (gBin (loBit0 + k)) ∈ NGen.decomposeConstraints n col loBit0 hiBit0 := by
  rw [NGen.decomposeConstraints]
  exact List.mem_append_left _ (mem_rangeNonneg_bit _ _ _ _ hk)

/-- The LOWER-edge recomposition head of a `decompose_coord_le` block. -/
theorem mem_decompose_loHead (n col loBit0 hiBit0 : Nat) :
    cgH ((List.range (NGen.COORD_RBITS n)).foldl
        (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (loBit0 + k)) (Head.lin 1 col))
      ∈ NGen.decomposeConstraints n col loBit0 hiBit0 := by
  rw [NGen.decomposeConstraints]
  exact List.mem_append_left _ (mem_rangeNonneg_head _ _ _)

/-- The k-th UPPER-edge bit of a `decompose_coord_le` block. -/
theorem mem_decompose_hiBit (n col loBit0 hiBit0 k : Nat) (hk : k < NGen.COORD_RBITS n) :
    cg (gBin (hiBit0 + k)) ∈ NGen.decomposeConstraints n col loBit0 hiBit0 := by
  rw [NGen.decomposeConstraints]
  exact List.mem_append_right _ (mem_rangeNonneg_bit _ _ _ _ hk)

/-- The UPPER-edge recomposition head of a `decompose_coord_le` block. -/
theorem mem_decompose_hiHead (n col loBit0 hiBit0 : Nat) :
    cgH ((List.range (NGen.COORD_RBITS n)).foldl
        (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (hiBit0 + k)) ((Head.c ((n : ℤ) - 1)).addLin (-1) col))
      ∈ NGen.decomposeConstraints n col loBit0 hiBit0 := by
  rw [NGen.decomposeConstraints]
  exact List.mem_append_right _ (mem_rangeNonneg_head _ _ _)

/-- A selector boolean bit of a `one_hot` block. -/
theorem mem_oneHot_sel (sels : List Nat) (idx : Head) {s : Nat} (hs : s ∈ sels) :
    cg (gBin s) ∈ oneHotConstraints sels idx :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨s, hs, rfl⟩))

/-- The `Σ selⱼ == 1` head of a `one_hot` block. -/
theorem mem_oneHot_sumHead (sels : List Nat) (idx : Head) :
    cgH (sels.foldl (fun acc s => acc.addLin 1 s) (Head.c (-1))) ∈ oneHotConstraints sels idx :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

/-- The `Σ j·selⱼ == idx` head of a `one_hot` block. -/
theorem mem_oneHot_idxHead (sels : List Nat) (idx : Head) :
    cgH (((sels.zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero)).append
        (idx.scale (-1))) ∈ oneHotConstraints sels idx :=
  List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- Same three, phrased for `oneHotAtCol` (the bare-column index case). -/
theorem mem_oneHotAtCol_sel (sels : List Nat) (idxCol : Nat) {s : Nat} (hs : s ∈ sels) :
    cg (gBin s) ∈ oneHotAtCol sels idxCol := mem_oneHot_sel sels _ hs

theorem mem_oneHotAtCol_sumHead (sels : List Nat) (idxCol : Nat) :
    cgH (sels.foldl (fun acc s => acc.addLin 1 s) (Head.c (-1))) ∈ oneHotAtCol sels idxCol :=
  mem_oneHot_sumHead sels _

theorem mem_oneHotAtCol_idxHead (sels : List Nat) (idxCol : Nat) :
    cgH (((sels.zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero)).append
        ((Head.lin 1 idxCol).scale (-1))) ∈ oneHotAtCol sels idxCol :=
  mem_oneHot_idxHead sels _

/-- The gate boolean of a `one_hot_gated` block. -/
theorem mem_oneHotGated_sel (sels : List Nat) (gate : Nat) (idx : Head) {s : Nat} (hs : s ∈ sels) :
    cg (gBin s) ∈ oneHotGatedConstraints sels gate idx :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨s, hs, rfl⟩))

theorem mem_oneHotGated_sumHead (sels : List Nat) (gate : Nat) (idx : Head) :
    cgH (sels.foldl (fun acc s => acc.addLin 1 s) (Head.lin (-1) gate))
      ∈ oneHotGatedConstraints sels gate idx :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

theorem mem_oneHotGated_idxHead (sels : List Nat) (gate : Nat) (idx : Head) :
    cgH ((idx.terms.foldl (fun acc t => acc.addProd (-t.1) (gate :: t.2))
        (sels.zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero)).addProd
        (-idx.const) [gate]) ∈ oneHotGatedConstraints sels gate idx :=
  List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- `forced_ge0`'s own boolean `ib`. -/
theorem mem_forcedGe0N_ib (d : Head) (ib bit0 rbits : Nat) :
    cg (gBin ib) ∈ forcedGe0ConstraintsN d ib bit0 rbits :=
  List.mem_cons_self

/-- The k-th `range_nonneg` bit inside a `forced_ge0`. -/
theorem mem_forcedGe0N_bit (d : Head) (ib bit0 rbits k : Nat) (hk : k < rbits) :
    cg (gBin (bit0 + k)) ∈ forcedGe0ConstraintsN d ib bit0 rbits :=
  List.mem_cons_of_mem _ (mem_rangeNonneg_bit _ _ _ _ hk)

/-- The `range_nonneg` recomposition head inside a `forced_ge0`. -/
theorem mem_forcedGe0N_head (d : Head) (ib bit0 rbits : Nat) :
    cgH ((List.range rbits).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
        (forcedGe0Term d ib)) ∈ forcedGe0ConstraintsN d ib bit0 rbits :=
  List.mem_cons_of_mem _ (mem_rangeNonneg_head _ _ _)

/-- The `eq_scalar` squared-distance definition head (its first gate). -/
theorem mem_eqScalar_dsqHead (a c dsqCol neqCol bit0 eqCol : Nat) :
    cgH ((((Head.lin 1 dsqCol).addProd (-1) [a, a]).addProd 2 [a, c]).addProd (-1) [c, c])
      ∈ eqScalarConstraints a c dsqCol neqCol bit0 eqCol :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton.mpr rfl))

/-- The `neq` boolean of the `forced_ge0` inside `eq_scalar`. -/
theorem mem_eqScalar_neqIb (a c dsqCol neqCol bit0 eqCol : Nat) :
    cg (gBin neqCol) ∈ eqScalarConstraints a c dsqCol neqCol bit0 eqCol :=
  List.mem_append_left _ (List.mem_append_right _ (mem_forcedGe0N_ib _ _ _ _))

/-- The k-th `forced_ge0` range bit inside `eq_scalar`. -/
theorem mem_eqScalar_neqBit (a c dsqCol neqCol bit0 eqCol k : Nat) (hk : k < RBITS) :
    cg (gBin (bit0 + k)) ∈ eqScalarConstraints a c dsqCol neqCol bit0 eqCol :=
  List.mem_append_left _ (List.mem_append_right _ (mem_forcedGe0N_bit _ _ _ _ _ hk))

/-- The `eq == 1 − neq` head of `eq_scalar` (its final gate). -/
theorem mem_eqScalar_eqHead (a c dsqCol neqCol bit0 eqCol : Nat) :
    cgH (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1))
      ∈ eqScalarConstraints a c dsqCol neqCol bit0 eqCol :=
  List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-! ## §2b — `validateMove` gate membership (drives `MoveGates`). Each gate located in its piece of
the 14-piece `validate_move` append, generically in `n b`. -/

/-- `decompose_coord_le` always allocates at least one bit: `COORD_RBITS n ≥ 1`. -/
theorem coord_rbits_pos {n : Nat} : 0 < NGen.COORD_RBITS n := by
  rw [NGen.COORD_RBITS]; split <;> omega

theorem vm_fxBin (n b : Nat) :
    cg (gBin (NGen.cFxLo n b)) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_decompose_loBit n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b) 0 coord_rbits_pos)))))))))))))

theorem vm_fxHead (n b : Nat) :
    cgH ((List.range (NGen.COORD_RBITS n)).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (NGen.cFxLo n b + k)) (Head.lin 1 (NGen.cFx n b))) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_decompose_loHead n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b))))))))))))))

theorem vm_fyBin (n b : Nat) :
    cg (gBin (NGen.cFyLo n b)) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_decompose_loBit n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b) 0 coord_rbits_pos)))))))))))))

theorem vm_fyHead (n b : Nat) :
    cgH ((List.range (NGen.COORD_RBITS n)).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (NGen.cFyLo n b + k)) (Head.lin 1 (NGen.cFy n b))) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_decompose_loHead n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b))))))))))))))

theorem vm_txBin (n b : Nat) :
    cg (gBin (NGen.cTxLo n b)) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_decompose_loBit n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b) 0 coord_rbits_pos))))))))))))

theorem vm_txHead (n b : Nat) :
    cgH ((List.range (NGen.COORD_RBITS n)).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (NGen.cTxLo n b + k)) (Head.lin 1 (NGen.cTx n b))) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_decompose_loHead n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b)))))))))))))

theorem vm_tyBin (n b : Nat) :
    cg (gBin (NGen.cTyLo n b)) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_decompose_loBit n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b) 0 coord_rbits_pos)))))))))))

theorem vm_tyHead (n b : Nat) :
    cgH ((List.range (NGen.COORD_RBITS n)).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (NGen.cTyLo n b + k)) (Head.lin 1 (NGen.cTy n b))) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_decompose_loHead n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b))))))))))))

theorem vm_rook (n b : Nat) :
    cgH (NGen.rookAlignHead n b) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))))))))))

theorem vm_dsqDef (n b : Nat) :
    cgH (NGen.dsqHead n b) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))))))))

theorem vm_dsqNz (n b : Nat) :
    cg (gCondNonzero (NGen.ONE n) (NGen.cDsq n b) (NGen.cDistinctInv n b)) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))))))))

theorem vm_faDef (n b : Nat) :
    cgH (NGen.autoDistHead n (NGen.cFa n b) (NGen.cFx n b) (NGen.cFy n b)) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))))))

theorem vm_faNz (n b : Nat) :
    cg (gCondNonzero (NGen.ONE n) (NGen.cFa n b) (NGen.cFnaInv n b)) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))))))

theorem vm_taDef (n b : Nat) :
    cgH (NGen.autoDistHead n (NGen.cTa n b) (NGen.cTx n b) (NGen.cTy n b)) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))))

theorem vm_taNz (n b : Nat) :
    cg (gCondNonzero (NGen.ONE n) (NGen.cTa n b) (NGen.cTnaInv n b)) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))))

theorem vm_srRi (n b : Nat) :
    cgH (((NGen.selRowCols n b).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append ((Head.lin 1 (NGen.cFy n b)).scale (-1))) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_idxHead (NGen.selRowCols n b) (NGen.cFy n b))))

theorem vm_srRs (n b : Nat) :
    cgH ((NGen.selRowCols n b).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1))) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_sumHead (NGen.selRowCols n b) (NGen.cFy n b))))

theorem vm_srCi (n b : Nat) :
    cgH (((NGen.selColCols n b).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append ((Head.lin 1 (NGen.cFx n b)).scale (-1))) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_idxHead (NGen.selColCols n b) (NGen.cFx n b)))

theorem vm_srCs (n b : Nat) :
    cgH ((NGen.selColCols n b).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1))) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_sumHead (NGen.selColCols n b) (NGen.cFx n b)))

theorem vm_srcRd (n b : Nat) :
    cgH (NGen.sourceReadHead n b) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- The j-th source ROW selector boolean bit (needs `j < n`). -/
theorem vm_selRow (n b j : Nat) (hj : j < n) :
    cg (gBin (NGen.cSelRow n b j)) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_sel (NGen.selRowCols n b) (NGen.cFy n b) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))

/-- The j-th source COLUMN selector boolean bit (needs `j < n`). -/
theorem vm_selCol (n b j : Nat) (hj : j < n) :
    cg (gBin (NGen.cSelCol n b j)) ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_sel (NGen.selColCols n b) (NGen.cFx n b) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))

/-! ## §2c — `onePin`, the position-STABLE fixed-length families (via `List.getElem_mem` at a
STABLE index — those families are literal / global-`RBITS` lists whose LENGTH and positions do
NOT move with `n`), and the two `n`-dependent front families (`autoRead`, `boardRange`). -/

/-- The `one` pin is the cons-HEAD of the constraint list. -/
theorem mem_resolve_onePin (n : Nat) : NGen.onePin n ∈ (automataflResolveDescN n).constraints := by
  rw [descN_constraints, NGen.resolveConstraints]; exact List.mem_cons_self

/-- `selection` is a fixed-length (n-INDEPENDENT position) list: element `i` is a stable seam. -/
theorem mem_selection_idx (n i : Nat) (hi : i < (NGen.selectionConstraints n).length) :
    (NGen.selectionConstraints n)[i] ∈ (automataflResolveDescN n).constraints :=
  mem_resolve_of_mem_selection (List.getElem_mem hi)

/-- `carry` is a fixed-length (n-INDEPENDENT position) list: element `i` is a stable seam. -/
theorem mem_carry_idx (n i : Nat) (hi : i < (NGen.carryConstraints n).length) :
    (NGen.carryConstraints n)[i] ∈ (automataflResolveDescN n).constraints :=
  mem_resolve_of_mem_carry (List.getElem_mem hi)

/-- `flowThrough` is a fixed-length (n-INDEPENDENT position) list: element `i` is a stable seam. -/
theorem mem_flowThrough_idx (n i : Nat) (hi : i < (NGen.flowThroughConstraints n).length) :
    (NGen.flowThroughConstraints n)[i] ∈ (automataflResolveDescN n).constraints :=
  mem_resolve_of_mem_flowThrough (List.getElem_mem hi)

/-- `srcNonVac` is a fixed-length (n-INDEPENDENT position) list: element `i` is a stable seam. -/
theorem mem_srcNonVac_idx (n i : Nat) (hi : i < (NGen.srcNonVacConstraints n).length) :
    (NGen.srcNonVacConstraints n)[i] ∈ (automataflResolveDescN n).constraints :=
  mem_resolve_of_mem_srcNonVac (List.getElem_mem hi)

/-- `patternBit` is a fixed-length (n-INDEPENDENT position) list: element `i` is a stable seam. -/
theorem mem_patternBit_idx (n i : Nat) (hi : i < (NGen.patternBitConstraints n).length) :
    (NGen.patternBitConstraints n)[i] ∈ (automataflResolveDescN n).constraints :=
  mem_resolve_of_mem_patternBit (List.getElem_mem hi)

/-! ### autoRead — `n`-dependent (the two auto one-hots carry `n` selectors), so combinator-navigated. -/
theorem ar_selRowBit (n j : Nat) (hj : j < n) :
    cg (gBin (NGen.selAutoRow n j)) ∈ NGen.autoReadConstraints n := by
  rw [NGen.autoReadConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_sel ((List.range n).map (NGen.selAutoRow n)) (NGen.AY_C n) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
theorem ar_selRowSum (n : Nat) :
    cgH (((List.range n).map (NGen.selAutoRow n)).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1)))
      ∈ NGen.autoReadConstraints n := by
  rw [NGen.autoReadConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_sumHead ((List.range n).map (NGen.selAutoRow n)) (NGen.AY_C n))))
theorem ar_selRowIdx (n : Nat) :
    cgH ((((List.range n).map (NGen.selAutoRow n)).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append ((Head.lin 1 (NGen.AY_C n)).scale (-1)))
      ∈ NGen.autoReadConstraints n := by
  rw [NGen.autoReadConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_idxHead ((List.range n).map (NGen.selAutoRow n)) (NGen.AY_C n))))
theorem ar_selColBit (n j : Nat) (hj : j < n) :
    cg (gBin (NGen.selAutoCol n j)) ∈ NGen.autoReadConstraints n := by
  rw [NGen.autoReadConstraints]
  exact List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_sel ((List.range n).map (NGen.selAutoCol n)) (NGen.AX_C n) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
theorem ar_selColSum (n : Nat) :
    cgH (((List.range n).map (NGen.selAutoCol n)).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1)))
      ∈ NGen.autoReadConstraints n := by
  rw [NGen.autoReadConstraints]
  exact List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_sumHead ((List.range n).map (NGen.selAutoCol n)) (NGen.AX_C n)))
theorem ar_selColIdx (n : Nat) :
    cgH ((((List.range n).map (NGen.selAutoCol n)).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append ((Head.lin 1 (NGen.AX_C n)).scale (-1)))
      ∈ NGen.autoReadConstraints n := by
  rw [NGen.autoReadConstraints]
  exact List.mem_append_left _ (List.mem_append_right _ (mem_oneHotAtCol_idxHead ((List.range n).map (NGen.selAutoCol n)) (NGen.AX_C n)))
theorem ar_autoPin (n : Nat) :
    cgH (NGen.autoPinHead n) ∈ NGen.autoReadConstraints n := by
  rw [NGen.autoReadConstraints]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-! ### boardRange — `n`-dependent (2·KK n cells), navigated by `mem_map`/`mem_range`. -/
theorem br_old (n c : Nat) (hc : c < NGen.KK n) :
    cg (memberExpr (NGen.old n c) [0, 1, 2, 3]) ∈ NGen.boardRangeConstraints n := by
  rw [NGen.boardRangeConstraints]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)
theorem br_mid (n c : Nat) (hc : c < NGen.KK n) :
    cg (memberExpr (NGen.mid n c) [0, 1, 2, 3]) ∈ NGen.boardRangeConstraints n := by
  rw [NGen.boardRangeConstraints]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

/-! ## §2d — `validateOcclusion` (`IvGates`/`OccGates`) and `writeMid` (`writeCell`) gate membership.
`validateOcclusion` is `n`-dependent (line/endpoint one-hots carry `n` selectors), so navigated by
combinator lemmas over its 13-piece append; the `iv` block is `eq_scalar` (P0), the `occ` block a
`forced_ge0` (P12). -/

/-- The `forced_ge0` recomposition head inside an `eq_scalar` block (its Ge0Gates9 `recomp`). -/
theorem mem_eqScalar_neqHead (a c dsqCol neqCol bit0 eqCol : Nat) :
    cgH ((List.range RBITS).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
        (forcedGe0Term ((Head.lin 1 dsqCol).addConst (-1)) neqCol))
      ∈ eqScalarConstraints a c dsqCol neqCol bit0 eqCol :=
  List.mem_append_left _ (List.mem_append_right _ (mem_forcedGe0N_head _ _ _ _))

theorem vo_iv_dsq (n b o ob : Nat) :
    cgH ((((Head.lin 1 (NGen.cIvDsq n o)).addProd (-1) [NGen.cFx n b, NGen.cFx n b]).addProd 2 [NGen.cFx n b, NGen.cTx n b]).addProd (-1) [NGen.cTx n b, NGen.cTx n b]) ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion, NGen.isVerticalConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_eqScalar_dsqHead (NGen.cFx n b) (NGen.cTx n b) (NGen.cIvDsq n o) (NGen.cIvNeq n o) (NGen.ivNeqBit n o 0) (NGen.cIv n o)))))))))))))
theorem vo_iv_neqIb (n b o ob : Nat) :
    cg (gBin (NGen.cIvNeq n o)) ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion, NGen.isVerticalConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_eqScalar_neqIb (NGen.cFx n b) (NGen.cTx n b) (NGen.cIvDsq n o) (NGen.cIvNeq n o) (NGen.ivNeqBit n o 0) (NGen.cIv n o)))))))))))))
theorem vo_iv_neqBit (n b o ob k : Nat) (hk : k < RBITS) :
    cg (gBin (NGen.ivNeqBit n o 0 + k)) ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion, NGen.isVerticalConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_eqScalar_neqBit (NGen.cFx n b) (NGen.cTx n b) (NGen.cIvDsq n o) (NGen.cIvNeq n o) (NGen.ivNeqBit n o 0) (NGen.cIv n o) k hk))))))))))))
theorem vo_iv_neqHead (n b o ob : Nat) :
    cgH ((List.range RBITS).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (NGen.ivNeqBit n o 0 + k)) (forcedGe0Term ((Head.lin 1 (NGen.cIvDsq n o)).addConst (-1)) (NGen.cIvNeq n o))) ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion, NGen.isVerticalConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_eqScalar_neqHead (NGen.cFx n b) (NGen.cTx n b) (NGen.cIvDsq n o) (NGen.cIvNeq n o) (NGen.ivNeqBit n o 0) (NGen.cIv n o)))))))))))))
theorem vo_iv_eqPin (n b o ob : Nat) :
    cgH (((Head.lin 1 (NGen.cIv n o)).addLin 1 (NGen.cIvNeq n o)).addConst (-1)) ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion, NGen.isVerticalConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_eqScalar_eqHead (NGen.cFx n b) (NGen.cTx n b) (NGen.cIvDsq n o) (NGen.cIvNeq n o) (NGen.ivNeqBit n o 0) (NGen.cIv n o)))))))))))))

theorem vo_seg (n b o ob k : Nat) (hk : k < n) :
    cgH (NGen.segHead n o k) ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))))))
theorem vo_msum (n b o ob : Nat) :
    cgH (NGen.msumHead n o) ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
theorem vo_occ_ib (n b o ob : Nat) :
    cg (gBin (NGen.cOcc n o)) ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion]
  exact List.mem_append_right _ (mem_forcedGe0N_ib _ (NGen.cOcc n o) (NGen.occBit n o 0) RBITS)
theorem vo_occ_bit (n b o ob k : Nat) (hk : k < RBITS) :
    cg (gBin (NGen.occBit n o 0 + k)) ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion]
  exact List.mem_append_right _ (mem_forcedGe0N_bit _ (NGen.cOcc n o) (NGen.occBit n o 0) RBITS k hk)
theorem vo_occ_head (n b o ob : Nat) :
    cgH ((List.range RBITS).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (NGen.occBit n o 0 + k)) (forcedGe0Term ((Head.lin 1 (NGen.cMsum n o)).addConst (-1)) (NGen.cOcc n o)))
      ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion]
  exact List.mem_append_right _ (mem_forcedGe0N_head ((Head.lin 1 (NGen.cMsum n o)).addConst (-1)) (NGen.cOcc n o) (NGen.occBit n o 0) RBITS)

/-- `writeCell` gate: the per-cell rewrite equality, in the map tail of `writeMid` (P1). -/
theorem wm_writeCell (n c : Nat) (hc : c < NGen.KK n) :
    cgH (NGen.writeCellHead n c) ∈ NGen.writeMidConstraints n := by
  rw [NGen.writeMidConstraints]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)

/-! ## §2e — `writeEndpoint` (`srcIndicator`/`dstIndicator`) gate membership. `writeEndpoint` is a
`flatMap` over the two pieces, each a 4-way append of `one_hot` blocks (src row/col, dst row/col).
Located by `List.mem_flatMap` + the 4-way `mem_append` spine + the `one_hot` combinator lemmas. -/

/-- Lift a `writeEndpoint` membership up into `writeMid` (its P0). -/
theorem mem_writeMid_of_writeEndpoint {g : VmConstraint2} {n : Nat}
    (h : g ∈ NGen.writeEndpointConstraints n) : g ∈ NGen.writeMidConstraints n := by
  rw [NGen.writeMidConstraints]; exact List.mem_append_left _ h

theorem we_srcRow_sel (n i j : Nat) (hi2 : i < 2) (hj : j < n) :
    cg (gBin (NGen.wSrcRow n i j)) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_oneHot_sel ((List.range n).map (NGen.wSrcRow n i)) (Head.lin 1 (NGen.cFy n (NGen.mvBase n i))) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
theorem we_srcRow_sum (n i : Nat) (hi2 : i < 2) :
    cgH (((List.range n).map (NGen.wSrcRow n i)).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1))) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_oneHot_sumHead ((List.range n).map (NGen.wSrcRow n i)) (Head.lin 1 (NGen.cFy n (NGen.mvBase n i))))))
theorem we_srcRow_idx (n i : Nat) (hi2 : i < 2) :
    cgH ((((List.range n).map (NGen.wSrcRow n i)).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append ((Head.lin 1 (NGen.cFy n (NGen.mvBase n i))).scale (-1))) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_oneHot_idxHead ((List.range n).map (NGen.wSrcRow n i)) (Head.lin 1 (NGen.cFy n (NGen.mvBase n i))))))

theorem we_srcCol_sel (n i j : Nat) (hi2 : i < 2) (hj : j < n) :
    cg (gBin (NGen.wSrcCol n i j)) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_oneHot_sel ((List.range n).map (NGen.wSrcCol n i)) (Head.lin 1 (NGen.cFx n (NGen.mvBase n i))) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
theorem we_srcCol_sum (n i : Nat) (hi2 : i < 2) :
    cgH (((List.range n).map (NGen.wSrcCol n i)).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1))) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_oneHot_sumHead ((List.range n).map (NGen.wSrcCol n i)) (Head.lin 1 (NGen.cFx n (NGen.mvBase n i))))))
theorem we_srcCol_idx (n i : Nat) (hi2 : i < 2) :
    cgH ((((List.range n).map (NGen.wSrcCol n i)).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append ((Head.lin 1 (NGen.cFx n (NGen.mvBase n i))).scale (-1))) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_oneHot_idxHead ((List.range n).map (NGen.wSrcCol n i)) (Head.lin 1 (NGen.cFx n (NGen.mvBase n i))))))

theorem we_dstRow_sel (n i j : Nat) (hi2 : i < 2) (hj : j < n) :
    cg (gBin (NGen.wDstRow n i j)) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (List.mem_append_right _ (mem_oneHot_sel ((List.range n).map (NGen.wDstRow n i)) (destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i))) (if i == 0 then NGen.cFtA n else NGen.cFtB n)) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
theorem we_dstRow_sum (n i : Nat) (hi2 : i < 2) :
    cgH (((List.range n).map (NGen.wDstRow n i)).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1))) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (List.mem_append_right _ (mem_oneHot_sumHead ((List.range n).map (NGen.wDstRow n i)) (destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i))) (if i == 0 then NGen.cFtA n else NGen.cFtB n))))
theorem we_dstRow_idx (n i : Nat) (hi2 : i < 2) :
    cgH ((((List.range n).map (NGen.wDstRow n i)).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append ((destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i))) (if i == 0 then NGen.cFtA n else NGen.cFtB n)).scale (-1))) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (List.mem_append_right _ (mem_oneHot_idxHead ((List.range n).map (NGen.wDstRow n i)) (destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i))) (if i == 0 then NGen.cFtA n else NGen.cFtB n))))

theorem we_dstCol_sel (n i j : Nat) (hi2 : i < 2) (hj : j < n) :
    cg (gBin (NGen.wDstCol n i j)) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_right _ (mem_oneHot_sel ((List.range n).map (NGen.wDstCol n i)) (destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i))) (if i == 0 then NGen.cFtA n else NGen.cFtB n)) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
theorem we_dstCol_sum (n i : Nat) (hi2 : i < 2) :
    cgH (((List.range n).map (NGen.wDstCol n i)).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1))) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_right _ (mem_oneHot_sumHead ((List.range n).map (NGen.wDstCol n i)) (destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i))) (if i == 0 then NGen.cFtA n else NGen.cFtB n)))
theorem we_dstCol_idx (n i : Nat) (hi2 : i < 2) :
    cgH ((((List.range n).map (NGen.wDstCol n i)).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append ((destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i))) (if i == 0 then NGen.cFtA n else NGen.cFtB n)).scale (-1))) ∈ NGen.writeEndpointConstraints n := by
  rw [NGen.writeEndpointConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_right _ (mem_oneHot_idxHead ((List.range n).map (NGen.wDstCol n i)) (destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i))) (if i == 0 then NGen.cFtA n else NGen.cFtB n)))

end Dregg2.Circuit.Emit.AutomataflResolveMembership
