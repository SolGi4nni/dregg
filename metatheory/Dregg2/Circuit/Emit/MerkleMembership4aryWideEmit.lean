/-
# Dregg2.Circuit.Emit.MerkleMembership4aryWideEmit — the WIDE (8-lane node-fold) 4-ary membership

**This is Lean-authored AIR.** This module authors the algebra; Rust parses the emitted IR2 bytes
and supplies witnesses — it constructs no constraints.

## What this file IS

The WIDE additive replacement for the deployed 1-felt membership descriptor
`MerkleMembership4aryEmit.membership4aryDesc` (staged-additive-then-cutover). The deployed
descriptor is felt-width finding **#9** (`docs/WOUND-felt-width-boundaries-2026-07-19.md`,
`docs/DESIGN-felt-width-rotation-epoch-2026-07-19.md`): its node fold chains on **lane 0 only** —
each level absorbs the four children as four SINGLE felts and the continuity window ties
`next.cur = this.par` at one column — so every interior node (and the root PI) is a ~31-bit
(2^15.5-collidable) commitment, regardless of how many lanes the chip witnesses.

⚠ ANTI-MASQUERADE: exposing the top node's 8 lanes while the tree still chains lane-0 buys
nothing — the interior stays ~31-bit. This descriptor therefore widens the **fold**, not just the
PI: a genuine Merkle-scheme change.

## The widened scheme

* Every node of the tree is a FULL 8-felt Poseidon2 digest (`Digest8`), not a lane-0 squeeze.
* The 4-ary node fold absorbs all 8 lanes of each child. Four 8-felt children are 32 felts —
  double the chip rate (`CHIP_RATE = 16`) — so the fold is realized as a balanced pair of
  arity-16 absorbs, all three bound at full output width by `chipLookupTupleN`:

      node8W(c0,c1,c2,c3) = A16( A16(c0 ‖ c1) ‖ A16(c2 ‖ c3) )

  where `A16` is the same arity-16 pack8 absorb the deployed heap/cap `node8` rows already ride
  (one chip, arity-tag-separated domains — inherited deployed practice, not new sharing).
* Chain continuity is 8 window gates — `next.cur[k] = this.par[k]` for EVERY lane k — where the
  deployed family has one (lane 0).
* The position/arrangement gates are the deployed family's algebra applied per lane with SHARED
  position bits: the 8-felt running node sits at its `b0 + 2·b1` slot among the 8-felt siblings.
* PI layout `[leaf0..leaf7, root0..root7]` (piCount 16): the row-0 running node is pinned to the
  8 leaf PIs, the last-row parent to the 8 root PIs. The leaf is widened along with the root so
  this boundary does not re-pin a 1-felt key (the class-D lesson: widening a root while the key
  stays 31-bit does nothing).

## What is proved here (and the named residual)

* `wChildren_arranged_lane` / `wGroups_arranged` — the arrangement gates pin the four 8-felt
  children to the positional arrangement of the 8-felt running node and siblings.
* `wideNodeFold_sound` — under a sound WIDE chip table (`ChipTableSoundN`), the three lookups
  force the parent group to the genuine two-stage fold `wideFold4` of the four child groups: the
  full 8-felt node binding, per row.
* `wCont_all_zero_iff` — the 8 continuity windows hold iff the NEXT row's 8-felt running node IS
  this row's 8-felt parent (the widened chain, stated at `Digest8`).
* **The anti-masquerade tooth** `interior_forge_narrow_admits_wide_refuses`, in the
  collision-extraction discipline (`Coll8`; the injectivity-hypothesis style is refuted at
  deployed parameters — `Compress8CR` is false for the real chip): fix two child quadruples that
  agree on every lane 0 but differ at some lane of some child — EXACTLY the interior-forge class.
  Then (1) the deployed lane-0 fold is blind: its parents are literally equal, at zero cost; and
  (2) the wide fold refuses: equal wide parents hand back a specific, named, full-width chip
  collision (`wideFoldColl8Find`). The forge the 1-felt fold admitted for free now costs a
  genuine collision on the full ~124-bit-wide preimage domain.

NAMED RESIDUAL: the full multi-row `Satisfied2 ⇒` recomposed-Merkle-path refinement (the
`*Refine`-tier walk composing `wideNodeFold_sound` + `wCont_all_zero_iff` + `wGroups_arranged`
across the trace) is deferred to a `MerkleMembership4aryWideRefine` module. The deployed narrow
emit file carries no such refinement either; the per-row teeth here are strictly more than parity.

## DEFERRED coordinated deploy (integrator, one epoch)

The Rust consumer repoint (`turn/src/executor/membership_verifier.rs` — widen
`root_felt_from_slot`, bind the 16 PIs), the descriptor-JSON golden regen into
`circuit/descriptors/`, and the `vk_hash` registry rotation are the coordinated cutover; nothing
here changes the deployed descriptor or its registry entry.

## Axiom hygiene

Definitional descriptor + byte-pinned `#guard` on the wire string + non-vacuous shape/semantic
lemmas. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.MerkleMembership4aryEmit
import Dregg2.Circuit.DeployedCapTree

namespace Dregg2.Circuit.Emit.MerkleMembership4aryWideEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId Table chipLookupTupleN ChipTableSoundN
   chip_lookup_sound_N CHIP_RATE emitVmJson2 WindowExpr WindowConstraint)
open Dregg2.Circuit.Emit.BlindedMembershipEmit
  (bitBinaryBody gArrangeList ev ek eadd emul eneg esub eoneMinus)
open Dregg2.Circuit.Emit.MerkleMembership4aryEmit (membership4aryDesc)
open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 pack8_inj)

set_option autoImplicit false

/-! ## §1 — the trace column layout: every Merkle value is an 8-lane group.

One 4-ary level per trace row (depth = trace height), as in the deployed family — but the running
node, the three siblings, the four ordered children, and the parent are each a FULL 8-felt digest
group. The two position bits stay per-row scalars shared by all lanes (the position of an 8-felt
child is one position). -/

/-- The 8-felt running node (row 0 = the 8-felt member leaf; pinned to PIs 0..7). -/
def wCUR : Fin 8 → Nat := fun k => k.val
/-- The three 8-felt co-path siblings at this level (HIDDEN). -/
def wSIB0 : Fin 8 → Nat := fun k => 8 + k.val
def wSIB1 : Fin 8 → Nat := fun k => 16 + k.val
def wSIB2 : Fin 8 → Nat := fun k => 24 + k.val
/-- The two position bits (`position = b0 + 2·b1 ∈ {0,1,2,3}`) — per-row scalars. -/
def wB0 : Nat := 32
def wB1 : Nat := 33
/-- The four ordered 8-felt children (`children[position] = cur8`, siblings fill in order). -/
def wC0 : Fin 8 → Nat := fun k => 34 + k.val
def wC1 : Fin 8 → Nat := fun k => 42 + k.val
def wC2 : Fin 8 → Nat := fun k => 50 + k.val
def wC3 : Fin 8 → Nat := fun k => 58 + k.val
/-- Stage-1 left digest `A16(c0 ‖ c1)` — all 8 lanes bound. -/
def wH01 : Fin 8 → Nat := fun k => 66 + k.val
/-- Stage-1 right digest `A16(c2 ‖ c3)` — all 8 lanes bound. -/
def wH23 : Fin 8 → Nat := fun k => 74 + k.val
/-- The 8-felt parent `A16(h01 ‖ h23)`; last row pinned to the 8 root PIs. -/
def wPAR : Fin 8 → Nat := fun k => 82 + k.val
/-- Total main-trace width: 9 8-lane groups + 2 bits. -/
def WIDE_WIDTH : Nat := 90

/-- PI slots 0..7: the 8-felt member leaf. -/
def wPI_LEAF (k : Fin 8) : Nat := k.val
/-- PI slots 8..15: the committed 8-felt root. -/
def wPI_ROOT (k : Fin 8) : Nat := 8 + k.val
/-- Number of public inputs: `[leaf0..leaf7, root0..root7]`. -/
def WIDE_PI_COUNT : Nat := 16

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

/-! ## §2 — the per-row position/arrangement gates (the deployed algebra, per lane, shared bits).

The gate BODIES are the deployed family's `child0Body..child3Body` term-for-term, instantiated at
each lane's columns with the SHARED indicator polynomials over `wB0/wB1`. The arrangement they
enforce is the same `gArrangeList` — now holding lane-by-lane, i.e. of the whole 8-felt values. -/

-- The four Lagrange position indicators over the shared bits (degree 2, integer coefficients).
def wIndL0 : EmittedExpr := emul (eoneMinus (ev wB0)) (eoneMinus (ev wB1))
def wIndL1 : EmittedExpr := emul (ev wB0) (eoneMinus (ev wB1))
def wIndL2 : EmittedExpr := emul (eoneMinus (ev wB0)) (ev wB1)
def wIndL3 : EmittedExpr := emul (ev wB0) (ev wB1)

-- The per-lane child-selection gate bodies `c_j[k] - selection_j[k]` (the deployed arrangement).
def wChild0Body (k : Fin 8) : EmittedExpr :=
  esub (esub (ev (wC0 k)) (ev (wSIB0 k))) (emul wIndL0 (esub (ev (wCUR k)) (ev (wSIB0 k))))
def wChild1Body (k : Fin 8) : EmittedExpr :=
  esub (ev (wC1 k))
    (eadd (eadd (emul (ev (wSIB0 k)) wIndL0) (emul (ev (wCUR k)) wIndL1))
      (emul (ev (wSIB1 k)) (eadd wIndL2 wIndL3)))
def wChild2Body (k : Fin 8) : EmittedExpr :=
  esub (ev (wC2 k))
    (eadd (eadd (emul (ev (wSIB1 k)) (eadd wIndL0 wIndL1)) (emul (ev (wCUR k)) wIndL2))
      (emul (ev (wSIB2 k)) wIndL3))
def wChild3Body (k : Fin 8) : EmittedExpr :=
  esub (esub (ev (wC3 k)) (ev (wSIB2 k))) (emul wIndL3 (esub (ev (wCUR k)) (ev (wSIB2 k))))

/-- The four child-selection bodies at lane `k`, in the deployed order. -/
def wChildBodiesAt (k : Fin 8) : List EmittedExpr :=
  [wChild0Body k, wChild1Body k, wChild2Body k, wChild3Body k]

/-- The per-row constraint bodies: the two bit-binary gates, then the four child-selection gates
for each of the 8 lanes (lane-major). 2 + 8·4 = 34 bodies. -/
def wPerRowBodies : List EmittedExpr :=
  [bitBinaryBody wB0, bitBinaryBody wB1] ++ ((List.finRange 8).map wChildBodiesAt).flatten

/-- **`wChildren_arranged_lane`** — at EVERY lane `k`, a row satisfying the two bit-binary gates
and lane `k`'s four child-selection gates has its lane-`k` child slice equal to the positional
arrangement of the lane-`k` running-node/sibling slice. The per-lane port of the deployed
`gChildren_arranged`; the bits are shared, so all 8 lanes arrange at ONE position. -/
theorem wChildren_arranged_lane (a : Assignment) (k : Fin 8)
    (hb0 : (bitBinaryBody wB0).eval a = 0) (hb1 : (bitBinaryBody wB1).eval a = 0)
    (h0 : (wChild0Body k).eval a = 0) (h1 : (wChild1Body k).eval a = 0)
    (h2 : (wChild2Body k).eval a = 0) (h3 : (wChild3Body k).eval a = 0) :
    [a (wC0 k), a (wC1 k), a (wC2 k), a (wC3 k)]
      = gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
          (a wB0) (a wB1) := by
  simp only [bitBinaryBody, ev, ek, eadd, emul, eneg, EmittedExpr.eval] at hb0 hb1
  have e0 : a wB0 = 0 ∨ a wB0 = 1 := by
    have h : a wB0 * (a wB0 - 1) = 0 := by linear_combination hb0
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have e1 : a wB1 = 0 ∨ a wB1 = 1 := by
    have h : a wB1 * (a wB1 - 1) = 0 := by linear_combination hb1
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  simp only [wChild0Body, wChild1Body, wChild2Body, wChild3Body,
    wIndL0, wIndL1, wIndL2, wIndL3, ev, ek, eadd, emul, eneg, esub, eoneMinus,
    EmittedExpr.eval] at h0 h1 h2 h3
  rcases e0 with hb0v | hb0v <;> rcases e1 with hb1v | hb1v
  · have hr : gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
        (a wB0) (a wB1)
        = [a (wCUR k), a (wSIB0 k), a (wSIB1 k), a (wSIB2 k)] := by
      simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · have hr : gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
        (a wB0) (a wB1)
        = [a (wSIB0 k), a (wSIB1 k), a (wCUR k), a (wSIB2 k)] := by
      simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · have hr : gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
        (a wB0) (a wB1)
        = [a (wSIB0 k), a (wCUR k), a (wSIB1 k), a (wSIB2 k)] := by
      simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · have hr : gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
        (a wB0) (a wB1)
        = [a (wSIB0 k), a (wSIB1 k), a (wSIB2 k), a (wCUR k)] := by
      simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The positional arrangement lifted to whole `Digest8` children (the level step at width 8). -/
def wArrange8 (cur s0 s1 s2 : Digest8) (b0 b1 : ℤ) : List Digest8 :=
  if b1 = 0 then (if b0 = 0 then [cur, s0, s1, s2] else [s0, cur, s1, s2])
  else (if b0 = 0 then [s0, s1, cur, s2] else [s0, s1, s2, cur])

/-- **`wGroups_arranged`** — the GROUP-level keystone: on any row satisfying the bit-binary gates
and all 32 child-selection gates, the four 8-FELT children ARE the positional arrangement of the
8-FELT running node and siblings. A forger cannot place arbitrary 8-felt children under a level;
they must be the whole running digest (at its slot) plus the whole real siblings — every lane,
not lane 0. -/
theorem wGroups_arranged (a : Assignment)
    (hb0 : (bitBinaryBody wB0).eval a = 0) (hb1 : (bitBinaryBody wB1).eval a = 0)
    (hc : ∀ k : Fin 8, (wChild0Body k).eval a = 0 ∧ (wChild1Body k).eval a = 0
      ∧ (wChild2Body k).eval a = 0 ∧ (wChild3Body k).eval a = 0) :
    [wVal a wC0, wVal a wC1, wVal a wC2, wVal a wC3]
      = wArrange8 (wVal a wCUR) (wVal a wSIB0) (wVal a wSIB1) (wVal a wSIB2)
          (a wB0) (a wB1) := by
  have hlane : ∀ k : Fin 8,
      [a (wC0 k), a (wC1 k), a (wC2 k), a (wC3 k)]
        = gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
            (a wB0) (a wB1) :=
    fun k => wChildren_arranged_lane a k hb0 hb1 (hc k).1 (hc k).2.1 (hc k).2.2.1 (hc k).2.2.2
  simp only [bitBinaryBody, ev, ek, eadd, emul, eneg, EmittedExpr.eval] at hb0 hb1
  have e0 : a wB0 = 0 ∨ a wB0 = 1 := by
    have h : a wB0 * (a wB0 - 1) = 0 := by linear_combination hb0
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have e1 : a wB1 = 0 ∨ a wB1 = 1 := by
    have h : a wB1 * (a wB1 - 1) = 0 := by linear_combination hb1
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases e0 with hb0v | hb0v <;> rcases e1 with hb1v | hb1v
  · rw [hb0v, hb1v]
    have harr : wArrange8 (wVal a wCUR) (wVal a wSIB0) (wVal a wSIB1) (wVal a wSIB2) 0 0
        = [wVal a wCUR, wVal a wSIB0, wVal a wSIB1, wVal a wSIB2] := by simp [wArrange8]
    rw [harr]
    have hcomp : ∀ k : Fin 8, a (wC0 k) = a (wCUR k) ∧ a (wC1 k) = a (wSIB0 k)
        ∧ a (wC2 k) = a (wSIB1 k) ∧ a (wC3 k) = a (wSIB2 k) := by
      intro k
      have h := hlane k
      rw [hb0v, hb1v] at h
      simpa [gArrangeList] using h
    simp only [List.cons.injEq, and_true]
    exact ⟨funext fun k => (hcomp k).1, funext fun k => (hcomp k).2.1,
           funext fun k => (hcomp k).2.2.1, funext fun k => (hcomp k).2.2.2⟩
  · rw [hb0v, hb1v]
    have harr : wArrange8 (wVal a wCUR) (wVal a wSIB0) (wVal a wSIB1) (wVal a wSIB2) 0 1
        = [wVal a wSIB0, wVal a wSIB1, wVal a wCUR, wVal a wSIB2] := by simp [wArrange8]
    rw [harr]
    have hcomp : ∀ k : Fin 8, a (wC0 k) = a (wSIB0 k) ∧ a (wC1 k) = a (wSIB1 k)
        ∧ a (wC2 k) = a (wCUR k) ∧ a (wC3 k) = a (wSIB2 k) := by
      intro k
      have h := hlane k
      rw [hb0v, hb1v] at h
      simpa [gArrangeList] using h
    simp only [List.cons.injEq, and_true]
    exact ⟨funext fun k => (hcomp k).1, funext fun k => (hcomp k).2.1,
           funext fun k => (hcomp k).2.2.1, funext fun k => (hcomp k).2.2.2⟩
  · rw [hb0v, hb1v]
    have harr : wArrange8 (wVal a wCUR) (wVal a wSIB0) (wVal a wSIB1) (wVal a wSIB2) 1 0
        = [wVal a wSIB0, wVal a wCUR, wVal a wSIB1, wVal a wSIB2] := by simp [wArrange8]
    rw [harr]
    have hcomp : ∀ k : Fin 8, a (wC0 k) = a (wSIB0 k) ∧ a (wC1 k) = a (wCUR k)
        ∧ a (wC2 k) = a (wSIB1 k) ∧ a (wC3 k) = a (wSIB2 k) := by
      intro k
      have h := hlane k
      rw [hb0v, hb1v] at h
      simpa [gArrangeList] using h
    simp only [List.cons.injEq, and_true]
    exact ⟨funext fun k => (hcomp k).1, funext fun k => (hcomp k).2.1,
           funext fun k => (hcomp k).2.2.1, funext fun k => (hcomp k).2.2.2⟩
  · rw [hb0v, hb1v]
    have harr : wArrange8 (wVal a wCUR) (wVal a wSIB0) (wVal a wSIB1) (wVal a wSIB2) 1 1
        = [wVal a wSIB0, wVal a wSIB1, wVal a wSIB2, wVal a wCUR] := by simp [wArrange8]
    rw [harr]
    have hcomp : ∀ k : Fin 8, a (wC0 k) = a (wSIB0 k) ∧ a (wC1 k) = a (wSIB1 k)
        ∧ a (wC2 k) = a (wSIB2 k) ∧ a (wC3 k) = a (wCUR k) := by
      intro k
      have h := hlane k
      rw [hb0v, hb1v] at h
      simpa [gArrangeList] using h
    simp only [List.cons.injEq, and_true]
    exact ⟨funext fun k => (hcomp k).1, funext fun k => (hcomp k).2.1,
           funext fun k => (hcomp k).2.2.1, funext fun k => (hcomp k).2.2.2⟩

/-! ## §3 — the WIDE node fold: three arity-16 chip lookups, all 8 output lanes BOUND.

The deployed family's `gParentLookup` absorbs the four children as four SINGLE felts (arity 4)
and binds out0 only, WITNESSING lanes 1..7 without chaining them — that is the wound. Here every
absorb input is a whole 8-lane group and every output lane is bound by `chipLookupTupleN`. -/

/-- The 16 input expressions of one fold stage: the two 8-lane groups, in lane order. -/
def wStageIns (gL gR : Fin 8 → Nat) : List EmittedExpr :=
  (wCols gL ++ wCols gR).map EmittedExpr.var

/-- A fold-stage input list evaluates to exactly `pack8` of the two group values — the same
`L8 ‖ R8` block the deployed heap/cap `node8` absorbs. -/
theorem wStageIns_eval (a : Assignment) (gL gR : Fin 8 → Nat) :
    (wStageIns gL gR).map (·.eval a) = pack8 (wVal a gL) (wVal a gR) := by
  have hcomp : ∀ g : Fin 8 → Nat,
      ((wCols g).map EmittedExpr.var).map (·.eval a) = (wCols g).map a := by
    intro g
    rw [List.map_map]
    rfl
  simp only [wStageIns, List.map_append, hcomp, wCols_map]
  rfl

/-- Stage 1 left: `A16(c0 ‖ c1)` → the 8 `wH01` columns, every lane bound. -/
def wStageLLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (wStageIns wC0 wC1) (wCols wH01)⟩
/-- Stage 1 right: `A16(c2 ‖ c3)` → the 8 `wH23` columns, every lane bound. -/
def wStageRLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (wStageIns wC2 wC3) (wCols wH23)⟩
/-- Stage 2: `A16(h01 ‖ h23)` → the 8 `wPAR` columns — the 8-felt parent, every lane bound. -/
def wParentLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (wStageIns wH01 wH23) (wCols wPAR)⟩

/-- The wide permutation output of an 8-output absorb, as the `List ℤ` block a sound wide chip
table carries (the `heapPermOut` shape, scheme-free). -/
def wPermOut (absorb : List ℤ → Digest8) : List ℤ → List ℤ := fun xs => List.ofFn (absorb xs)

/-- **`wideFold4`** — the widened 4-ary node function: the balanced two-stage arity-16 fold over
whole 8-felt children. This is the Merkle-scheme change: all 32 child felts enter the preimage. -/
def wideFold4 (absorb : List ℤ → Digest8) (c0 c1 c2 c3 : Digest8) : Digest8 :=
  absorb (pack8 (absorb (pack8 c0 c1)) (absorb (pack8 c2 c3)))

/-- **`wideNodeFold_sound`** — under a SOUND WIDE chip table, a row whose three fold lookups hold
carries the genuine `wideFold4` of its four 8-felt children in the 8 parent columns. The wide
lever (`chip_lookup_sound_N`) forces every stage column-for-column; nothing rides lane 0 alone. -/
theorem wideNodeFold_sound (absorb : List ℤ → Digest8) (tbl : Table)
    (hChip : ChipTableSoundN (wPermOut absorb) tbl) (a : Assignment)
    (hL : (chipLookupTupleN (wStageIns wC0 wC1) (wCols wH01)).map (·.eval a) ∈ tbl)
    (hR : (chipLookupTupleN (wStageIns wC2 wC3) (wCols wH23)).map (·.eval a) ∈ tbl)
    (hP : (chipLookupTupleN (wStageIns wH01 wH23) (wCols wPAR)).map (·.eval a) ∈ tbl) :
    wVal a wPAR = wideFold4 absorb (wVal a wC0) (wVal a wC1) (wVal a wC2) (wVal a wC3) := by
  have hlen : ∀ gL gR : Fin 8 → Nat, (wStageIns gL gR).length ≤ CHIP_RATE := by
    intro gL gR
    simp [wStageIns, wCols, List.length_map, List.length_append, List.length_finRange, CHIP_RATE]
  have h1 := chip_lookup_sound_N (wPermOut absorb) tbl hChip a _ _ (hlen wC0 wC1) hL
  have h2 := chip_lookup_sound_N (wPermOut absorb) tbl hChip a _ _ (hlen wC2 wC3) hR
  have h3 := chip_lookup_sound_N (wPermOut absorb) tbl hChip a _ _ (hlen wH01 wH23) hP
  rw [wCols_map, wStageIns_eval] at h1 h2 h3
  have e1 : wVal a wH01 = absorb (pack8 (wVal a wC0) (wVal a wC1)) := List.ofFn_inj.mp h1
  have e2 : wVal a wH23 = absorb (pack8 (wVal a wC2) (wVal a wC3)) := List.ofFn_inj.mp h2
  have e3 : wVal a wPAR = absorb (pack8 (wVal a wH01) (wVal a wH23)) := List.ofFn_inj.mp h3
  rw [e3, e1, e2]
  rfl

/-! ## §4 — the 8-lane chain continuity + the 16 PI pins. -/

/-- Lane `k`'s cross-row continuity window: `next.cur[k] - this.par[k]`. -/
def wContWindow (k : Fin 8) : WindowExpr :=
  .add (.nxt (wCUR k)) (.mul (.const (-1)) (.loc (wPAR k)))

/-- The 8 continuity window gates — the level chain rides EVERY lane of the digest, where the
deployed family chains lane 0 only. -/
def wContinuity : List VmConstraint2 :=
  (List.finRange 8).map fun k => .windowGate ⟨wContWindow k, true⟩

/-- Lane `k`'s continuity body vanishes exactly when that lane chains. -/
theorem wCont_zero_iff (k : Fin 8) (env : VmRowEnv) :
    (wContWindow k).eval env = 0 ↔ env.nxt (wCUR k) = env.loc (wPAR k) := by
  simp only [wContWindow, WindowExpr.eval]
  constructor <;> intro h <;> omega

/-- **The widened chain, at `Digest8`**: all 8 continuity windows vanish iff the next row's
8-felt running node IS this row's 8-felt parent. The interior of the tree is chained at full
digest width — the property whose absence made the deployed interior ~31-bit. -/
theorem wCont_all_zero_iff (env : VmRowEnv) :
    (∀ k : Fin 8, (wContWindow k).eval env = 0)
      ↔ wVal env.nxt wCUR = wVal env.loc wPAR := by
  constructor
  · intro h
    funext k
    exact (wCont_zero_iff k env).mp (h k)
  · intro h k
    exact (wCont_zero_iff k env).mpr (congrFun h k)

/-- The 8 leaf pins: row-0 running node lane `k` = PI `k`. -/
def wLeafPins : List VmConstraint2 :=
  (List.finRange 8).map fun k => .base (.piBinding VmRow.first (wCUR k) (wPI_LEAF k))
/-- The 8 root pins: last-row parent lane `k` = PI `8 + k`. -/
def wRootPins : List VmConstraint2 :=
  (List.finRange 8).map fun k => .base (.piBinding VmRow.last (wPAR k) (wPI_ROOT k))

/-! ## §5 — the descriptor. -/

/-- The per-row transition gates (bit-binary + the 32 per-lane child selections). -/
def wPerRowGates : List VmConstraint2 :=
  wPerRowBodies.map fun b => .base (.gate b)

/-- The last-row re-lowering of the per-row bodies (transition gates are vacuous on the last row;
without this the top level's bits + children would be unconstrained — the deployed family's
last-row-repair shape). -/
def wLastRowBoundaries : List VmConstraint2 :=
  wPerRowBodies.map fun b => .base (.boundary VmRow.last b)

/-- The complete wide constraint block: per-row gates, the three fold lookups, the 8-lane
continuity, the 16 PI pins, the last-row re-lowerings. -/
def wideConstraints : List VmConstraint2 :=
  wPerRowGates ++ [wStageLLookup, wStageRLookup, wParentLookup]
    ++ wContinuity ++ wLeafPins ++ wRootPins ++ wLastRowBoundaries

/-- **`merkleMembership4aryWideDesc`** — the WIDE, depth-general, 4-ary Merkle-membership
descriptor: 8-felt nodes, 8-lane node fold, 8-lane chain, `[leaf0..7, root0..7]` PIs. Tree depth
is the trace height; the algebra is uniform for every supported power-of-two depth, exactly as
the deployed narrow descriptor's. The staged-additive twin of `membership4aryDesc`. -/
def merkleMembership4aryWideDesc : EffectVmDescriptor2 :=
  { name        := "dregg-merkle-membership-4ary-wide-general::v1"
  , traceWidth  := WIDE_WIDTH
  , piCount     := WIDE_PI_COUNT
  , tables      := []
  , constraints := wideConstraints
  , hashSites   := []
  , ranges      := [] }

theorem descriptor_has_complete_shape :
    merkleMembership4aryWideDesc.constraints =
      wPerRowGates ++ [wStageLLookup, wStageRLookup, wParentLookup]
        ++ wContinuity ++ wLeafPins ++ wRootPins ++ wLastRowBoundaries := rfl

-- Non-vacuous structural pins.
#guard merkleMembership4aryWideDesc.traceWidth == 90
#guard merkleMembership4aryWideDesc.piCount == 16
#guard merkleMembership4aryWideDesc.constraints.length == 95
#guard merkleMembership4aryWideDesc.tables.length == 0
#guard wPerRowBodies.length == 34
#guard (wStageIns wC0 wC1).length == 16
#guard (chipLookupTupleN (wStageIns wC0 wC1) (wCols wH01)).length == 25
#guard wCols wCUR == [0, 1, 2, 3, 4, 5, 6, 7]
#guard wCols wPAR == [82, 83, 84, 85, 86, 87, 88, 89]

-- The staged-additive adjacency: the deployed narrow descriptor this file replaces-at-cutover
-- pins ONE felt each for leaf and root; the wide twin pins 8 + 8. Distinct names, distinct VKs.
#guard membership4aryDesc.piCount == 2
#guard membership4aryDesc.traceWidth == 11
#guard membership4aryDesc.name != merkleMembership4aryWideDesc.name

-- Continuity non-vacuity: lane 0 accepts a chained window and rejects an unchained one.
#guard decide ((wContWindow 0).eval
  ⟨fun i => if i = wPAR 0 then 7 else 0, fun i => if i = wCUR 0 then 7 else 0, fun _ => 0⟩ = 0)
#guard decide (¬ ((wContWindow 0).eval
  ⟨fun _ => 0, fun i => if i = wCUR 0 then 7 else 0, fun _ => 0⟩ = 0))
-- The emitted-level interior canary: a next row that copies the parent's lane 0 but drops its
-- lane 7 satisfies the lane-0 window and FAILS the lane-7 window — the assignment class the
-- deployed single-window continuity admits wholesale is refused by the wide block.
#guard decide ((wContWindow 0).eval
  ⟨fun i => if i = wPAR 0 then 7 else if i = wPAR 7 then 9 else 0,
   fun i => if i = wCUR 0 then 7 else 0, fun _ => 0⟩ = 0)
#guard decide (¬ ((wContWindow 7).eval
  ⟨fun i => if i = wPAR 0 then 7 else if i = wPAR 7 then 9 else 0,
   fun i => if i = wCUR 0 then 7 else 0, fun _ => 0⟩ = 0))

/-! ## §6 — the byte-pinned wire golden (generated once via `#eval repr (emitVmJson2 …)`;
the Rust decoder ingests THIS string at the coordinated cutover). -/

/-- Exact emitted-wire golden (generated via `#eval repr (emitVmJson2 merkleMembership4aryWideDesc)`).
Rust includes these bytes verbatim at the coordinated cutover. -/
def MEMBERSHIP_4ARY_WIDE_GOLDEN : String :=
  "{\"name\":\"dregg-merkle-membership-4ary-wide-general::v1\",\"ir\":2,\"trace_width\":90,\"public_input_count\":16,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":34},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":60},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":57},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":31}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":31}}}}}}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":34},{\"t\":\"var\",\"v\":35},{\"t\":\"var\",\"v\":36},{\"t\":\"var\",\"v\":37},{\"t\":\"var\",\"v\":38},{\"t\":\"var\",\"v\":39},{\"t\":\"var\",\"v\":40},{\"t\":\"var\",\"v\":41},{\"t\":\"var\",\"v\":42},{\"t\":\"var\",\"v\":43},{\"t\":\"var\",\"v\":44},{\"t\":\"var\",\"v\":45},{\"t\":\"var\",\"v\":46},{\"t\":\"var\",\"v\":47},{\"t\":\"var\",\"v\":48},{\"t\":\"var\",\"v\":49},{\"t\":\"var\",\"v\":66},{\"t\":\"var\",\"v\":67},{\"t\":\"var\",\"v\":68},{\"t\":\"var\",\"v\":69},{\"t\":\"var\",\"v\":70},{\"t\":\"var\",\"v\":71},{\"t\":\"var\",\"v\":72},{\"t\":\"var\",\"v\":73}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":50},{\"t\":\"var\",\"v\":51},{\"t\":\"var\",\"v\":52},{\"t\":\"var\",\"v\":53},{\"t\":\"var\",\"v\":54},{\"t\":\"var\",\"v\":55},{\"t\":\"var\",\"v\":56},{\"t\":\"var\",\"v\":57},{\"t\":\"var\",\"v\":58},{\"t\":\"var\",\"v\":59},{\"t\":\"var\",\"v\":60},{\"t\":\"var\",\"v\":61},{\"t\":\"var\",\"v\":62},{\"t\":\"var\",\"v\":63},{\"t\":\"var\",\"v\":64},{\"t\":\"var\",\"v\":65},{\"t\":\"var\",\"v\":74},{\"t\":\"var\",\"v\":75},{\"t\":\"var\",\"v\":76},{\"t\":\"var\",\"v\":77},{\"t\":\"var\",\"v\":78},{\"t\":\"var\",\"v\":79},{\"t\":\"var\",\"v\":80},{\"t\":\"var\",\"v\":81}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":66},{\"t\":\"var\",\"v\":67},{\"t\":\"var\",\"v\":68},{\"t\":\"var\",\"v\":69},{\"t\":\"var\",\"v\":70},{\"t\":\"var\",\"v\":71},{\"t\":\"var\",\"v\":72},{\"t\":\"var\",\"v\":73},{\"t\":\"var\",\"v\":74},{\"t\":\"var\",\"v\":75},{\"t\":\"var\",\"v\":76},{\"t\":\"var\",\"v\":77},{\"t\":\"var\",\"v\":78},{\"t\":\"var\",\"v\":79},{\"t\":\"var\",\"v\":80},{\"t\":\"var\",\"v\":81},{\"t\":\"var\",\"v\":82},{\"t\":\"var\",\"v\":83},{\"t\":\"var\",\"v\":84},{\"t\":\"var\",\"v\":85},{\"t\":\"var\",\"v\":86},{\"t\":\"var\",\"v\":87},{\"t\":\"var\",\"v\":88},{\"t\":\"var\",\"v\":89}]},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":82}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":83}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":84}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":85}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":86}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":87}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":88}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":89}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":82,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":83,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":84,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":85,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":86,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":87,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":88,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":89,\"pi_index\":15},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":34},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":60},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":57},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":31}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":31}}}}}}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 merkleMembership4aryWideDesc == MEMBERSHIP_4ARY_WIDE_GOLDEN

/-! ## §7 — the anti-masquerade tooth (collision-extraction discipline).

The injectivity-hypothesis style is REFUTED at deployed parameters (`Compress8CR` is false for
the real chip — it compresses `List ℤ` into 8 bounded lanes), so the tooth follows the
`DeployedCapTree` `…_binds_or_collides` discipline: conclusions hand back the SPECIFIC colliding
pair a total extractor returns, never a bare `∃`. -/

/-- The deployed 1-felt node fold, stated of the same 8-felt data: absorb ONLY lane 0 of each
child (the emitted `gParentLookup` absorbs the four single child columns; arity 4). Lanes 1..7
never enter the preimage. -/
def narrowFold4Lane0 (absorb : List ℤ → Digest8) (c0 c1 c2 c3 : Digest8) : Digest8 :=
  absorb [c0 0, c1 0, c2 0, c3 0]

/-- The wide-fold collision extractor: given two child quadruples with equal wide parents but
unequal data, returns the specific stage preimage pair that collides. Total; branches are
decidable. -/
def wideFoldColl8Find (absorb : List ℤ → Digest8)
    (c0 c1 c2 c3 c0' c1' c2' c3' : Digest8) : List ℤ × List ℤ :=
  if pack8 c0 c1 ≠ pack8 c0' c1' ∧ absorb (pack8 c0 c1) = absorb (pack8 c0' c1') then
    (pack8 c0 c1, pack8 c0' c1')
  else if pack8 c2 c3 ≠ pack8 c2' c3' ∧ absorb (pack8 c2 c3) = absorb (pack8 c2' c3') then
    (pack8 c2 c3, pack8 c2' c3')
  else
    (pack8 (absorb (pack8 c0 c1)) (absorb (pack8 c2 c3)),
     pack8 (absorb (pack8 c0' c1')) (absorb (pack8 c2' c3')))

/-- **`wideFold4_binds_or_collides`** — equal wide parents EITHER force all four 8-felt children
equal, OR the extractor's pair is a genuine full-width chip collision, handed back by name. The
wide twin of `nodeOf8_binds_or_collides`, at 4-ary fan-in. -/
theorem wideFold4_binds_or_collides (absorb : List ℤ → Digest8)
    (c0 c1 c2 c3 c0' c1' c2' c3' : Digest8)
    (heq : wideFold4 absorb c0 c1 c2 c3 = wideFold4 absorb c0' c1' c2' c3') :
    (c0 = c0' ∧ c1 = c1' ∧ c2 = c2' ∧ c3 = c3')
      ∨ Coll8 absorb (wideFoldColl8Find absorb c0 c1 c2 c3 c0' c1' c2' c3') := by
  by_cases hb : c0 = c0' ∧ c1 = c1' ∧ c2 = c2' ∧ c3 = c3'
  · exact Or.inl hb
  right
  unfold wideFoldColl8Find
  by_cases hL : pack8 c0 c1 ≠ pack8 c0' c1' ∧ absorb (pack8 c0 c1) = absorb (pack8 c0' c1')
  · rw [if_pos hL]
    exact ⟨hL.1, hL.2⟩
  rw [if_neg hL]
  by_cases hR : pack8 c2 c3 ≠ pack8 c2' c3' ∧ absorb (pack8 c2 c3) = absorb (pack8 c2' c3')
  · rw [if_pos hR]
    exact ⟨hR.1, hR.2⟩
  rw [if_neg hR]
  refine ⟨?_, heq⟩
  intro hpk
  obtain ⟨hLL, hRR⟩ := pack8_inj hpk
  have hxy : pack8 c0 c1 = pack8 c0' c1' := by
    by_contra hne
    exact hL ⟨hne, hLL⟩
  have hzw : pack8 c2 c3 = pack8 c2' c3' := by
    by_contra hne
    exact hR ⟨hne, hRR⟩
  obtain ⟨h0, h1⟩ := pack8_inj hxy
  obtain ⟨h2, h3⟩ := pack8_inj hzw
  exact hb ⟨h0, h1, h2, h3⟩

/-- **⚑ THE ANTI-MASQUERADE TOOTH.** Fix two child quadruples that agree on EVERY lane 0 (so the
deployed 1-felt fold cannot tell them apart) but differ at lane `j` of the first child — the
interior-forge class finding #9 names. Field-faithfully:

1. the deployed lane-0 fold is BLIND: its outputs are literally equal — the forge is free; and
2. the WIDE fold REFUSES: if the wide parents are equal too, the extractor's pair is a genuine
   full-width chip collision. The forge now costs a real Poseidon2 collision over the full
   32-felt preimage domain instead of nothing.

(The hypotheses are jointly satisfiable exactly for `j ≠ 0` — the canaries below exhibit a
satisfying instance at `j = 1`.) -/
theorem interior_forge_narrow_admits_wide_refuses (absorb : List ℤ → Digest8)
    {c0 c1 c2 c3 c0' c1' c2' c3' : Digest8} (j : Fin 8)
    (hlane0 : c0 0 = c0' 0 ∧ c1 0 = c1' 0 ∧ c2 0 = c2' 0 ∧ c3 0 = c3' 0)
    (hdiff : c0 j ≠ c0' j) :
    narrowFold4Lane0 absorb c0 c1 c2 c3 = narrowFold4Lane0 absorb c0' c1' c2' c3'
    ∧ (wideFold4 absorb c0 c1 c2 c3 = wideFold4 absorb c0' c1' c2' c3' →
        Coll8 absorb (wideFoldColl8Find absorb c0 c1 c2 c3 c0' c1' c2' c3')) := by
  constructor
  · unfold narrowFold4Lane0
    rw [hlane0.1, hlane0.2.1, hlane0.2.2.1, hlane0.2.2.2]
  · intro heq
    rcases wideFold4_binds_or_collides absorb c0 c1 c2 c3 c0' c1' c2' c3' heq with hbind | hcoll
    · exact absurd (congrFun hbind.1 j) hdiff
    · exact hcoll

-- Satisfiability canaries for the tooth's hypothesis class (a lane-0-agreeing, lane-1-differing
-- pair EXISTS), plus a concrete run of the extractor returning a genuine collision under a toy
-- absorb — the collision disjunct is inhabited, not a free pass.
def toyAbsorb : List ℤ → Digest8 := fun _ _ => 0
def laneForged : Digest8 := fun k => if k.val = 1 then 5 else 0
def laneZero : Digest8 := fun _ => 0
#guard decide (laneForged 0 = laneZero 0)
#guard decide (laneForged 1 ≠ laneZero 1)
#guard decide (wideFold4 toyAbsorb laneForged laneZero laneZero laneZero
  = wideFold4 toyAbsorb laneZero laneZero laneZero laneZero)
#guard decide (Coll8 toyAbsorb
  (wideFoldColl8Find toyAbsorb laneForged laneZero laneZero laneZero
    laneZero laneZero laneZero laneZero))
-- And the blindness half on the same pair: the narrow fold literally cannot see the forge.
#guard decide (narrowFold4Lane0 toyAbsorb laneForged laneZero laneZero laneZero
  = narrowFold4Lane0 toyAbsorb laneZero laneZero laneZero laneZero)

/-! ## §8 — axiom hygiene on the keystones. -/

#assert_axioms descriptor_has_complete_shape
#assert_axioms wChildren_arranged_lane
#assert_axioms wGroups_arranged
#assert_axioms wCont_all_zero_iff
#assert_axioms wideNodeFold_sound
#assert_axioms wideFold4_binds_or_collides
#assert_axioms interior_forge_narrow_admits_wide_refuses

end Dregg2.Circuit.Emit.MerkleMembership4aryWideEmit
