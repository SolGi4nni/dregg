/-
# Dregg2.Circuit.Emit.AutomataflOcclusionGeneric — the OCCLUSION argument at ARBITRARY board size

## Why this file exists

`AutomataflResolveRefine.occ_of_sat` proves the emitted occlusion bit is `0`, and
`AutomataflResolveRefine.occluded_false_n2` proves the reference `occluded` is `false` — so the
occlusion leg of the Leg-R capstone is CLOSED at `n = 2`. It is closed BY VACUITY: a 2-line has no
strictly-interior cell, so `segHead`'s index set `{(j1, j2) | j1 < k < j2 < n}` is empty for every
`k`, the masked interior sum is identically `0`, and the threshold cannot fire. Nothing is occluded
because there is nowhere to stand.

At `n = 11` occlusion GENUINELY bites, and both of those lemmas are FALSE. This file supplies the
replacement: the occlusion refinement argument for an ARBITRARY `n` and an ARBITRARY rook move,
proven, with no appeal to board smallness.

## What is proven here

Everything is stated over `n` as a VARIABLE. The gate-shaped quantities are defined with EXACTLY
the fold/index structure the emitter uses (`AutomataflResolveEmit.segHead` / `.msumHead`), so these
are the semantics of the emitted heads, not a re-authored model of them:

  * `segVal_eq` — **the seg mask is the strictly-between indicator.** With `efrom` a one-hot at the
    move's along-axis SOURCE index `af` and `eto` a one-hot at its along-axis DESTINATION index
    `at_`, the emitted `seg[k]` head forces `seg k = 1` iff `k` lies strictly between `af` and
    `at_` (either order), else `0`. At `n = 2` this specialises to the old `seg[k] = 0`; at `n ≥ 3`
    it is the genuine order-independent between-mask.

  * `msumVal_eq_sum_between` — the masked interior sum ranges exactly over the strictly-interior
    indices, each term `(1 − osrc k)·line k`.

  * `msum_ge_one_iff` — **the threshold gate is the occlusion predicate.** Given the board-alphabet
    bound `0 ≤ line k ≤ 3` and `osrc` boolean, `msum ≥ 1` iff SOME strictly-interior index carries a
    non-vacuum, non-passable (not-an-other-source) cell. This is the step that is pure vacuity at
    `n = 2` and a real argument at `n > 2`: it needs every term non-negative (so no cancellation can
    hide an obstruction) and a witness extraction in the other direction.

  * `occluded_vert_iff` / `occluded_horiz_iff` — the REFERENCE side, n-generic: `Automatafl.occluded`
    unfolded to "∃ a strictly-between along-coordinate whose cell is non-vacuum and not a source".
    `interior` is characterised by `mem_interior_vert` / `mem_interior_horiz`, replacing the
    `interval_cases`-over-a-2×2-board proof of `interior_nil_n2`.

  * `occ_eq_occluded_vert` / `occ_eq_occluded_horiz` — **the bridge, and the point of the file.**
    Under the WITNESS HYPOTHESES that name what the surrounding descriptor columns must mean
    (`LineReadsVert`: `line k` is the felt code of the board cell at along-index `k` on the move's
    line; `OsrcIsOtherSource`: `osrc` is the passable-mask indicator of the other moving source),
    the emitted threshold bit equals the reference `occluded` — at any `n`, for any rook move.

## The honest seam — NOW DISCHARGED (see `AutomataflOcclusionBridge`)

These hypotheses (`LineReadsVert`, `OsrcIsOtherSource`, the one-hot pins) are exactly what
`AutomataflResolveEmit.lineHead` / `oneHotGatedConstraints` / `efromHead` / `etoHead` emit gates FOR.
`AutomataflResolveEmit.automataflResolveDesc` is now `NN`-PARAMETRIC (every column offset and gadget
family a function of `NN`, instantiated at `NN = 2` with the byte golden UNCHANGED), and
`AutomataflOcclusionBridge` discharges EVERY hypothesis of `occ_eq_occluded_vert/horiz` from
`Satisfied2 automataflResolveDesc`: `efrom_oneHot` / `eto_oneHot` (the `iv`-gated selection IS a
genuine along-axis one-hot), `lineReadsVert/Horiz_of_sat`, `osrcMeansVert/Horiz_of_sat`,
`lineRange_of_sat`, `occ_col_iff_msumVal`. The assembled `occ_iff_occluded_of_sat` is the emitted
`cOcc` = reference `occluded`, UNCONDITIONAL off `Satisfied2`, at the instantiated `NN = 2`. At that
board size both sides are `false` — but through THIS generic threshold/mask/one-hot machinery, not
`interior_nil_n2` vacuity; a contentful occlusion leg needs `NN ≥ 3`. Nothing here or there is stated
at `n = 11` as though the capstone reached it.

Axiom hygiene: definitions + theorems, no `sorry`, no `native_decide`. Imports the reference game
module only.
-/
import Dregg2.Games.Automatafl
import Dregg2.Games.AutomataflRules
import Dregg2.Tactics
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Dregg2.Circuit.Emit.AutomataflOcclusionGeneric

open Dregg2.Games.Automatafl
open Dregg2.Games.AutomataflRules (blockedB pathCells)

/-! ## §1 — Generic list helpers (the one-hot collapse). -/

/-- A `Nat`-indexed one-hot over `[0, n)`: `v` is `1` at `i` and `0` at every other in-range index.
This is precisely what `Builder::one_hot`'s two gates force (`Σ sel = 1`, `Σ j·sel j = i`) once the
selectors are pinned boolean — the shape `AutomataflResolveEmit.oneHotConstraints` emits. -/
def OneHotAt (v : Nat → ℤ) (n i : Nat) : Prop :=
  i < n ∧ ∀ j, j < n → v j = if j = i then 1 else 0

/-- Summing a one-hot's values over any duplicate-free index list picks out membership. -/
theorem sum_map_ite (l : List Nat) (hnd : l.Nodup) (i : Nat) (c : ℤ) :
    (l.map (fun j => if j = i then c else 0)).sum = if i ∈ l then c else 0 := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      rw [List.nodup_cons] at hnd
      obtain ⟨ha, hrest⟩ := hnd
      rw [List.map_cons, List.sum_cons, ih hrest]
      by_cases h : a = i
      · subst h
        rw [if_pos rfl, if_neg ha, if_pos (List.mem_cons_self ..)]
        ring
      · rw [if_neg h]
        by_cases hm : i ∈ rest
        · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]; ring
        · rw [if_neg hm, if_neg (by simp only [List.mem_cons, not_or]
                                    exact ⟨fun hc => h hc.symm, hm⟩)]
          ring

/-- The one-hot's sum over an in-range index list, stated against `OneHotAt`. -/
theorem sum_oneHot {v : Nat → ℤ} {n i : Nat} (hv : OneHotAt v n i)
    (l : List Nat) (hnd : l.Nodup) (hlt : ∀ j ∈ l, j < n) :
    (l.map v).sum = if i ∈ l then 1 else 0 := by
  have : l.map v = l.map (fun j => if j = i then (1 : ℤ) else 0) := by
    apply List.map_congr_left
    intro j hj
    exact hv.2 j (hlt j hj)
  rw [this, sum_map_ite l hnd i 1]

/-! ## §2 — The emitted `seg` mask, and its meaning at arbitrary `n`.

`AutomataflResolveEmit.segHead o k` emits the gate

    seg[k] − Σ_{j1 ∈ range k} Σ_{j2 ∈ range n, k < j2} (efrom[j1]·eto[j2] + eto[j1]·efrom[j2]) = 0

so a satisfying assignment has `seg k = segVal efrom eto n k`. `segVal` below is that double fold,
index set for index set. -/

/-- The value the emitted `seg[k]` gate forces, at board size `n`. -/
def segVal (efrom eto : Nat → ℤ) (n k : Nat) : ℤ :=
  ((List.range k).map (fun j1 =>
    (((List.range n).filter (fun j2 => decide (k < j2))).map (fun j2 =>
      efrom j1 * eto j2 + eto j1 * efrom j2)).sum)).sum

/-- Membership in the "strictly after `k`" index list. -/
theorem mem_after (n k j : Nat) :
    j ∈ (List.range n).filter (fun j2 => decide (k < j2)) ↔ j < n ∧ k < j := by
  simp [List.mem_filter, List.mem_range]

theorem nodup_after (n k : Nat) :
    ((List.range n).filter (fun j2 => decide (k < j2))).Nodup :=
  (List.nodup_range).filter _

/-- **The between-mask, n-generically.** With `efrom` a one-hot at the along-axis source index `af`
and `eto` a one-hot at the along-axis destination index `at_`, the emitted `seg[k]` head forces
`seg k = 1` exactly when `k` is strictly between them (in either order), and `0` otherwise.

This REPLACES `interior_nil_n2`. At `n = 2` no `k` can be strictly between two indices `< 2`, so the
old `seg k = 0` falls out as a corollary rather than as the whole story. -/
theorem segVal_eq {efrom eto : Nat → ℤ} {n af at_ : Nat}
    (hf : OneHotAt efrom n af) (ht : OneHotAt eto n at_) (k : Nat) :
    segVal efrom eto n k
      = if (af < k ∧ k < at_) ∨ (at_ < k ∧ k < af) then 1 else 0 := by
  have hafn : af < n := hf.1
  have hatn : at_ < n := ht.1
  -- the inner sum over j2, for a fixed j1
  have inner : ∀ j1, j1 < n →
      (((List.range n).filter (fun j2 => decide (k < j2))).map (fun j2 =>
        efrom j1 * eto j2 + eto j1 * efrom j2)).sum
        = efrom j1 * (if k < at_ then 1 else 0) + eto j1 * (if k < af then 1 else 0) := by
    intro j1 _
    set L := (List.range n).filter (fun j2 => decide (k < j2)) with hL
    have hsplit : (L.map (fun j2 => efrom j1 * eto j2 + eto j1 * efrom j2)).sum
        = efrom j1 * (L.map eto).sum + eto j1 * (L.map efrom).sum := by
      induction L with
      | nil => simp
      | cons a rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    rw [hsplit,
      sum_oneHot ht L (nodup_after n k) (fun j hj => ((mem_after n k j).mp hj).1),
      sum_oneHot hf L (nodup_after n k) (fun j hj => ((mem_after n k j).mp hj).1)]
    have e1 : (at_ ∈ L) = (k < at_) := by
      simp only [hL, eq_iff_iff, mem_after]
      exact ⟨fun h => h.2, fun h => ⟨hatn, h⟩⟩
    have e2 : (af ∈ L) = (k < af) := by
      simp only [hL, eq_iff_iff, mem_after]
      exact ⟨fun h => h.2, fun h => ⟨hafn, h⟩⟩
    simp only [e1, e2]
  -- now the outer sum over j1 ∈ range k
  have houter : segVal efrom eto n k
      = ((List.range k).map (fun j1 =>
          efrom j1 * (if k < at_ then 1 else 0) + eto j1 * (if k < af then 1 else 0))).sum
      ∨ True := Or.inr trivial
  clear houter
  -- If k ≥ n the range-k list contains out-of-range indices; handle k < n and k ≥ n separately.
  by_cases hkn : k < n
  · have hmap : (List.range k).map (fun j1 =>
        (((List.range n).filter (fun j2 => decide (k < j2))).map (fun j2 =>
          efrom j1 * eto j2 + eto j1 * efrom j2)).sum)
        = (List.range k).map (fun j1 =>
            efrom j1 * (if k < at_ then 1 else 0) + eto j1 * (if k < af then 1 else 0)) := by
      apply List.map_congr_left
      intro j1 hj1
      exact inner j1 (lt_trans (List.mem_range.mp hj1) hkn)
    have hsum : ((List.range k).map (fun j1 =>
        efrom j1 * (if k < at_ then 1 else 0) + eto j1 * (if k < af then 1 else 0))).sum
        = ((List.range k).map efrom).sum * (if k < at_ then 1 else 0)
          + ((List.range k).map eto).sum * (if k < af then 1 else 0) := by
      induction (List.range k) with
      | nil => simp
      | cons a rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    have hef : ((List.range k).map efrom).sum = if af < k then 1 else 0 := by
      rw [sum_oneHot hf _ List.nodup_range
        (fun j hj => lt_trans (List.mem_range.mp hj) hkn)]
      simp [List.mem_range]
    have het : ((List.range k).map eto).sum = if at_ < k then 1 else 0 := by
      rw [sum_oneHot ht _ List.nodup_range
        (fun j hj => lt_trans (List.mem_range.mp hj) hkn)]
      simp [List.mem_range]
    rw [segVal, hmap, hsum, hef, het]
    by_cases h1 : af < k <;> by_cases h2 : k < at_ <;> by_cases h3 : at_ < k <;>
      by_cases h4 : k < af <;>
      simp_all <;> omega
  · -- k ≥ n: nothing is strictly after k, so every inner sum is empty and seg k = 0;
    -- and no index `< n` can be strictly between while also exceeding k on the far side.
    have hempty : (List.range n).filter (fun j2 => decide (k < j2)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro j hj
      have : j < n := List.mem_range.mp hj
      simp only [decide_eq_true_eq]
      omega
    have : segVal efrom eto n k = 0 := by
      rw [segVal, hempty]
      simp
    rw [this]
    rw [eq_comm, if_neg]
    rintro (⟨_, h⟩ | ⟨_, h⟩) <;> omega

/-- The `n = 2` corollary — the old `seg k = 0`, now a consequence of the general mask rather than
the whole content of the leg. -/
theorem segVal_n2 {efrom eto : Nat → ℤ} {af at_ : Nat}
    (hf : OneHotAt efrom 2 af) (ht : OneHotAt eto 2 at_) (k : Nat) :
    segVal efrom eto 2 k = 0 := by
  rw [segVal_eq hf ht k, if_neg]
  have h1 := hf.1; have h2 := ht.1
  rintro (⟨a, b⟩ | ⟨a, b⟩) <;> omega

/-! ## §3 — The masked interior sum and the `msum ≥ 1` threshold.

`AutomataflResolveEmit.msumHead` emits `msum − Σ_k seg[k]·line[k] + Σ_k seg[k]·osrc[k]·line[k] = 0`,
i.e. `msum = Σ_{k<n} seg k · line k · (1 − osrc k)`. -/

/-- The value the emitted `msum` gate forces. -/
def msumVal (seg osrc line : Nat → ℤ) (n : Nat) : ℤ :=
  ((List.range n).map (fun k => seg k * line k - seg k * osrc k * line k)).sum

/-- `k` is strictly between the along-axis source and destination indices. -/
def Between (af at_ k : Nat) : Prop := (af < k ∧ k < at_) ∨ (at_ < k ∧ k < af)

instance (af at_ k : Nat) : Decidable (Between af at_ k) := by
  unfold Between; infer_instance

/-- **The threshold gate IS the occlusion predicate, at arbitrary `n`.**

Under the board-alphabet bound `0 ≤ line k ≤ 3` (which `AutomataflResolveEmit.boardRangeConstraints`
emits, and `AutomataflResolveRefine.boardvalid_of_sat` derives) and `osrc` boolean, the emitted
`msum ≥ 1` fires exactly when some strictly-interior index carries a non-vacuum cell that is not the
other move's (passable) source.

The `→` direction is the one with content: every term of `msum` is non-negative, so a positive sum
cannot arise from cancellation and must have a positive term, whose index is then the obstruction
witness. This is precisely the argument that `n = 2` never had to make. -/
theorem msum_ge_one_iff {efrom eto osrc line : Nat → ℤ} {n af at_ : Nat}
    (hf : OneHotAt efrom n af) (ht : OneHotAt eto n at_)
    (hosrc : ∀ k, k < n → osrc k = 0 ∨ osrc k = 1)
    (hline : ∀ k, k < n → 0 ≤ line k ∧ line k ≤ 3) :
    1 ≤ msumVal (segVal efrom eto n) osrc line n
      ↔ ∃ k, k < n ∧ Between af at_ k ∧ osrc k = 0 ∧ line k ≠ 0 := by
  -- Rewrite each summand into its evaluated form.
  have hterm : ∀ k, k < n →
      segVal efrom eto n k * line k - segVal efrom eto n k * osrc k * line k
        = if Between af at_ k ∧ osrc k = 0 then line k else 0 := by
    intro k hk
    rw [segVal_eq hf ht k]
    by_cases hb : Between af at_ k
    · have hb' : (af < k ∧ k < at_) ∨ (at_ < k ∧ k < af) := hb
      rw [if_pos hb']
      rcases hosrc k hk with h0 | h1
      · rw [if_pos ⟨hb, h0⟩, h0]; ring
      · rw [if_neg (by rintro ⟨-, h⟩; rw [h1] at h; exact absurd h (by norm_num)), h1]; ring
    · have hb' : ¬((af < k ∧ k < at_) ∨ (at_ < k ∧ k < af)) := hb
      rw [if_neg hb', if_neg (fun hc => hb hc.1)]; ring
  have hmap : (List.range n).map (fun k =>
      segVal efrom eto n k * line k - segVal efrom eto n k * osrc k * line k)
      = (List.range n).map (fun k => if Between af at_ k ∧ osrc k = 0 then line k else 0) := by
    apply List.map_congr_left
    intro k hk
    exact hterm k (List.mem_range.mp hk)
  rw [msumVal, hmap]
  -- Every entry is non-negative; the sum is ≥ 1 iff some entry is ≥ 1.
  set g : Nat → ℤ := fun k => if Between af at_ k ∧ osrc k = 0 then line k else 0 with hg
  have hgnn : ∀ k ∈ List.range n, 0 ≤ g k := by
    intro k hk
    have hk' := List.mem_range.mp hk
    by_cases hc : Between af at_ k ∧ osrc k = 0
    · simp only [hg, if_pos hc]; exact (hline k hk').1
    · simp only [hg, if_neg hc]; exact le_refl 0
  constructor
  · intro hsum
    -- a non-negative list with positive sum has a positive member
    by_contra hno
    simp only [not_exists, not_and] at hno
    have hzero : ∀ k ∈ List.range n, g k = 0 := by
      intro k hk
      have hk' := List.mem_range.mp hk
      by_cases hc : Between af at_ k ∧ osrc k = 0
      · have := hno k hk' hc.1 hc.2
        simp only [hg, if_pos hc]
        exact not_not.mp this
      · simp only [hg, if_neg hc]
    have : ((List.range n).map g).sum = 0 := by
      have : (List.range n).map g = (List.range n).map (fun _ => (0 : ℤ)) :=
        List.map_congr_left hzero
      rw [this]; simp
    omega
  · rintro ⟨k, hk, hb, ho, hne⟩
    have hmem : k ∈ List.range n := List.mem_range.mpr hk
    have hgk : g k = line k := by
      simp only [hg]; rw [if_pos (And.intro hb ho)]
    have hpos : 1 ≤ g k := by
      rw [hgk]
      have := (hline k hk).1
      omega
    -- non-negativity of every entry ⇒ any single entry bounds the sum from below
    have hnn : ∀ x ∈ (List.range n).map g, 0 ≤ x := by
      intro x hx
      obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hx
      exact hgnn k' hk'
    have hle : g k ≤ ((List.range n).map g).sum :=
      List.single_le_sum hnn (g k) (List.mem_map_of_mem hmem)
    omega

/-! ## §4 — The REFERENCE side, n-generically: what `Automatafl.occluded` says.

`interior_nil_n2` proved `interior = []` by `interval_cases` over a 2×2 board. That proof cannot
generalise (the statement is false at `n ≥ 3`). These are its replacements: an exact membership
characterisation of `interior`, at any size, in both orientations. -/

/-- `interior` on a VERTICAL move (shared `x`): the cells with the shared `x` and a `y` strictly
between the endpoints. -/
theorem mem_interior_vert (frm dst c : Coord) (h : frm.x = dst.x) :
    c ∈ interior frm dst ↔
      c.x = frm.x ∧ min frm.y dst.y < c.y ∧ c.y < max frm.y dst.y := by
  obtain ⟨cx, cy⟩ := c
  simp only [interior, if_pos h, List.mem_map, List.mem_range, Coord.mk.injEq]
  constructor
  · rintro ⟨k, hk, hx, hy⟩
    subst hx; subst hy
    exact ⟨rfl, by omega, by omega⟩
  · rintro ⟨hx, hlo, hhi⟩
    subst hx
    exact ⟨cy - (min frm.y dst.y + 1), by omega, rfl, by omega⟩

/-- `interior` on a HORIZONTAL move (distinct `x`): the cells with the source `y` and an `x`
strictly between the endpoints.

Note the reference `interior` branches on `frm.x = to.x` and takes the horizontal branch otherwise;
for a legal rook move (`validate_move`'s rook-align gate `(fx-tx)(fy-ty) = 0` plus distinctness)
`frm.x /= to.x` forces `frm.y = to.y`, so the source `y` really is the whole line's `y`. -/
theorem mem_interior_horiz (frm dst c : Coord) (h : frm.x ≠ dst.x) :
    c ∈ interior frm dst ↔
      c.y = frm.y ∧ min frm.x dst.x < c.x ∧ c.x < max frm.x dst.x := by
  obtain ⟨cx, cy⟩ := c
  simp only [interior, if_neg h, List.mem_map, List.mem_range, Coord.mk.injEq]
  constructor
  · rintro ⟨k, hk, hx, hy⟩
    subst hx; subst hy
    exact ⟨rfl, by omega, by omega⟩
  · rintro ⟨hy, hlo, hhi⟩
    subst hy
    exact ⟨cx - (min frm.x dst.x + 1), by omega, by omega, rfl⟩

/-- **The reference occlusion predicate, vertical, at any board size.** -/
theorem occluded_vert_iff (b : Board) (srcs : List Coord) (m : Move) (h : m.frm.x = m.to.x) :
    occluded b srcs m = true ↔
      ∃ y, min m.frm.y m.to.y < y ∧ y < max m.frm.y m.to.y ∧
        ¬ (b.cellAt ⟨m.frm.x, y⟩).isVacuum = true ∧ ¬ srcs.contains ⟨m.frm.x, y⟩ = true := by
  simp only [occluded, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, hv, hs⟩
    obtain ⟨hx, hlo, hhi⟩ := (mem_interior_vert m.frm m.to c h).mp hc
    refine ⟨c.y, hlo, hhi, ?_, ?_⟩
    · obtain ⟨cx, cy⟩ := c; simp only at hx; subst hx; exact hv
    · obtain ⟨cx, cy⟩ := c; simp only at hx; subst hx; exact hs
  · rintro ⟨y, hlo, hhi, hv, hs⟩
    exact ⟨⟨m.frm.x, y⟩, (mem_interior_vert m.frm m.to _ h).mpr ⟨rfl, hlo, hhi⟩, hv, hs⟩

/-- **The reference occlusion predicate, horizontal, at any board size.** -/
theorem occluded_horiz_iff (b : Board) (srcs : List Coord) (m : Move) (h : m.frm.x ≠ m.to.x) :
    occluded b srcs m = true ↔
      ∃ x, min m.frm.x m.to.x < x ∧ x < max m.frm.x m.to.x ∧
        ¬ (b.cellAt ⟨x, m.frm.y⟩).isVacuum = true ∧ ¬ srcs.contains ⟨x, m.frm.y⟩ = true := by
  simp only [occluded, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, hv, hs⟩
    obtain ⟨hy, hlo, hhi⟩ := (mem_interior_horiz m.frm m.to c h).mp hc
    refine ⟨c.x, hlo, hhi, ?_, ?_⟩
    · obtain ⟨cx, cy⟩ := c; simp only at hy; subst hy; exact hv
    · obtain ⟨cx, cy⟩ := c; simp only at hy; subst hy; exact hs
  · rintro ⟨x, hlo, hhi, hv, hs⟩
    exact ⟨⟨x, m.frm.y⟩, (mem_interior_horiz m.frm m.to _ h).mpr ⟨rfl, hlo, hhi⟩, hv, hs⟩

/-! ## §5 — The BRIDGE: emitted threshold bit = reference `occluded`, at arbitrary `n`.

The two hypotheses below name what the surrounding descriptor columns must mean. They are exactly
what `AutomataflResolveEmit`'s `lineHead` (the `iv`-gated column/row scan) and
`oneHotGatedConstraints` (the gated other-source one-hot) emit gates for; here they are the
interface, so the occlusion argument is proven independent of the descriptor's column arithmetic. -/

/-- The `line` columns read the move's line: on a vertical move at shared `x`, `line k` is the felt
code of the board cell `(x, k)`. Particle codes: vacuum `0`, and non-vacuum iff `≠ 0`. -/
def LineReadsVert (line : Nat → ℤ) (b : Board) (x n : Nat) : Prop :=
  ∀ k, k < n → (line k = 0 ↔ (b.cellAt ⟨x, k⟩).isVacuum = true)

/-- The `line` columns read the move's line, horizontal orientation: `line k` is the code of
`(k, y)`. -/
def LineReadsHoriz (line : Nat → ℤ) (b : Board) (y n : Nat) : Prop :=
  ∀ k, k < n → (line k = 0 ↔ (b.cellAt ⟨k, y⟩).isVacuum = true)

/-- The gated other-source mask marks exactly the STRICTLY-INTERIOR along-indices occupied by a
moving source on this line (`mark_passable`): for `k` strictly between the endpoints, `osrc k = 1`
iff the coordinate at along-index `k` is in `srcs`.

**The interior restriction is not a convenience, it is the emitted truth.** The descriptor's
`oneHotGatedConstraints` marks the OTHER move's source only, so at `k = m.frm.y` (this move's own
source, which IS in `srcs`) the mask reads `0` while `srcs.contains` is `true`. An unrestricted
version of this predicate is therefore FALSE of the emitted columns and could never be discharged.
Restricting to `Between` weakens the hypothesis — strengthening the theorem — and loses nothing:
`occluded` only ever inspects the interior, and the endpoints are excluded from `interior` by
construction. -/
def OsrcIsOtherSourceVert (osrc : Nat → ℤ) (srcs : List Coord) (x n af at_ : Nat) : Prop :=
  ∀ k, k < n → Between af at_ k → (osrc k = 1 ↔ srcs.contains ⟨x, k⟩ = true)

def OsrcIsOtherSourceHoriz (osrc : Nat → ℤ) (srcs : List Coord) (y n af at_ : Nat) : Prop :=
  ∀ k, k < n → Between af at_ k → (osrc k = 1 ↔ srcs.contains ⟨k, y⟩ = true)

/-- **THE OCCLUSION REFINEMENT, VERTICAL, AT ARBITRARY BOARD SIZE.**

For any `n`, any vertical rook move whose endpoints are in bounds, and any set of moving sources:
the emitted `msum ≥ 1` threshold bit equals the reference `Automatafl.occluded`.

At `n = 2` both sides are constantly `false` and this reduces to the old statement; at `n = 11` both
sides genuinely range over the nine possible interior cells. Nothing in the proof uses the board
being small — the between-mask is computed from the one-hots (§2), the sum is decomposed by
non-negativity (§3), and the reference side is characterised by membership (§4). -/
theorem occ_eq_occluded_vert {efrom eto osrc line : Nat → ℤ} {n : Nat}
    {b : Board} {srcs : List Coord} {m : Move}
    (hvert : m.frm.x = m.to.x)
    (hfy : m.frm.y < n) (hty : m.to.y < n)
    (hf : OneHotAt efrom n m.frm.y) (ht : OneHotAt eto n m.to.y)
    (hosrc : ∀ k, k < n → osrc k = 0 ∨ osrc k = 1)
    (hlineRange : ∀ k, k < n → 0 ≤ line k ∧ line k ≤ 3)
    (hlineRead : LineReadsVert line b m.frm.x n)
    (hosrcMeans : OsrcIsOtherSourceVert osrc srcs m.frm.x n m.frm.y m.to.y) :
    (1 ≤ msumVal (segVal efrom eto n) osrc line n) ↔ occluded b srcs m = true := by
  rw [msum_ge_one_iff hf ht hosrc hlineRange, occluded_vert_iff b srcs m hvert]
  constructor
  · rintro ⟨k, hk, hb, ho, hne⟩
    refine ⟨k, ?_, ?_, ?_, ?_⟩
    · rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · intro hvac
      exact hne ((hlineRead k hk).mpr hvac)
    · intro hcon
      have : osrc k = 1 := (hosrcMeans k hk hb).mpr hcon
      omega
  · rintro ⟨y, hlo, hhi, hv, hs⟩
    have hyn : y < n := by omega
    have hbet : Between m.frm.y m.to.y y := by
      unfold Between
      rcases Nat.lt_or_ge m.frm.y m.to.y with h | h
      · left; constructor <;> omega
      · right; constructor <;> omega
    refine ⟨y, hyn, hbet, ?_, ?_⟩
    · rcases hosrc y hyn with h0 | h1
      · exact h0
      · exact absurd ((hosrcMeans y hyn hbet).mp h1) hs
    · intro hz
      exact hv ((hlineRead y hyn).mp hz)

/-- **THE OCCLUSION REFINEMENT, HORIZONTAL, AT ARBITRARY BOARD SIZE.** The mirror of
`occ_eq_occluded_vert` for the row-scan branch (the branch the witnessed `iv = 0` selects). -/
theorem occ_eq_occluded_horiz {efrom eto osrc line : Nat → ℤ} {n : Nat}
    {b : Board} {srcs : List Coord} {m : Move}
    (hhoriz : m.frm.x ≠ m.to.x)
    (hfx : m.frm.x < n) (htx : m.to.x < n)
    (hf : OneHotAt efrom n m.frm.x) (ht : OneHotAt eto n m.to.x)
    (hosrc : ∀ k, k < n → osrc k = 0 ∨ osrc k = 1)
    (hlineRange : ∀ k, k < n → 0 ≤ line k ∧ line k ≤ 3)
    (hlineRead : LineReadsHoriz line b m.frm.y n)
    (hosrcMeans : OsrcIsOtherSourceHoriz osrc srcs m.frm.y n m.frm.x m.to.x) :
    (1 ≤ msumVal (segVal efrom eto n) osrc line n) ↔ occluded b srcs m = true := by
  rw [msum_ge_one_iff hf ht hosrc hlineRange, occluded_horiz_iff b srcs m hhoriz]
  constructor
  · rintro ⟨k, hk, hb, ho, hne⟩
    refine ⟨k, ?_, ?_, ?_, ?_⟩
    · rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · intro hvac
      exact hne ((hlineRead k hk).mpr hvac)
    · intro hcon
      have : osrc k = 1 := (hosrcMeans k hk hb).mpr hcon
      omega
  · rintro ⟨x, hlo, hhi, hv, hs⟩
    have hxn : x < n := by omega
    have hbet : Between m.frm.x m.to.x x := by
      unfold Between
      rcases Nat.lt_or_ge m.frm.x m.to.x with h | h
      · left; constructor <;> omega
      · right; constructor <;> omega
    refine ⟨x, hxn, hbet, ?_, ?_⟩
    · rcases hosrc x hxn with h0 | h1
      · exact h0
      · exact absurd ((hosrcMeans x hxn hbet).mp h1) hs
    · intro hz
      exact hv ((hlineRead x hxn).mp hz)

/-! ## §5b — THE INCLUSIVE (`blockedB`) BRIDGE: emitted threshold = reference `blockedB`.

The migration re-targets occlusion from the OLD `Automatafl.occluded` (which scans `interior`,
STRICTLY between the endpoints) to `AutomataflRules.blockedB`, which scans
`pathCells = interior ++ [dst]` — INCLUSIVE OF THE DESTINATION. Per the migration design this is
exactly ONE EXTRA TERM in the emitted `msum` fold: the destination endpoint contribution
`(1 − osrc[dst])·line[dst]`, picked out by the `eto` one-hot. Everything else — `segVal_eq`,
`msum_ge_one_iff`, `mem_interior_*` — is REUSED verbatim.

These are NEW lemmas ALONGSIDE the exclusive `occ_eq_occluded_*` (which the old-spec Leg R still uses
until cutover). The content they add is precisely the audit's 3.2 CRIT case: a non-moving piece
standing ON the destination now BLOCKS the move (and the mover is replaced at its origin), where the
old exclusive check let the mover overwrite — deleting the occupant. §5b.4 exhibits that at `n = 3`. -/

/-- Summing `v j · g j` over an in-range duplicate-free index list, with `v` a one-hot at `i`, picks
out `g i`. The `g`-weighted twin of `sum_oneHot`; this is how the emitted endpoint term (the `eto`
one-hot times `(1 − osrc)·line`) collapses to the single destination contribution. -/
theorem sum_oneHot_mul {v g : Nat → ℤ} {n i : Nat} (hv : OneHotAt v n i)
    (l : List Nat) (hnd : l.Nodup) (hlt : ∀ j ∈ l, j < n) :
    (l.map (fun j => v j * g j)).sum = if i ∈ l then g i else 0 := by
  have hmap : l.map (fun j => v j * g j) = l.map (fun j => if j = i then g i else 0) := by
    apply List.map_congr_left
    intro j hj
    rw [hv.2 j (hlt j hj)]
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [hmap, sum_map_ite l hnd i (g i)]

/-- **The value the INCLUSIVE `msum` gate forces.** The strictly-interior fold `msumVal (segVal …)`
plus the destination endpoint term `Σ_k eto[k]·(1 − osrc[k])·line[k]` — a single extra fold weighted
by the destination one-hot. This is the emitted change: the same `msum` head, one endpoint term
longer. -/
def msumInclVal (efrom eto osrc line : Nat → ℤ) (n : Nat) : ℤ :=
  msumVal (segVal efrom eto n) osrc line n
    + ((List.range n).map (fun k => eto k * ((1 - osrc k) * line k))).sum

/-- The endpoint fold collapses through the `eto` one-hot to the single destination contribution. -/
theorem endpoint_collapse {eto osrc line : Nat → ℤ} {n at_ : Nat} (ht : OneHotAt eto n at_) :
    ((List.range n).map (fun k => eto k * ((1 - osrc k) * line k))).sum
      = (1 - osrc at_) * line at_ := by
  rw [sum_oneHot_mul ht (List.range n) List.nodup_range (fun j hj => List.mem_range.mp hj),
    if_pos (List.mem_range.mpr ht.1)]

/-- The strictly-interior masked sum is NON-NEGATIVE: every term `seg·line·(1 − osrc)` is a product
of non-negatives. This is what lets `1 ≤ interior + endpoint` split into the two blocking cases. -/
theorem msumVal_segVal_nonneg {efrom eto osrc line : Nat → ℤ} {n af at_ : Nat}
    (hf : OneHotAt efrom n af) (ht : OneHotAt eto n at_)
    (hosrc : ∀ k, k < n → osrc k = 0 ∨ osrc k = 1)
    (hline : ∀ k, k < n → 0 ≤ line k ∧ line k ≤ 3) :
    0 ≤ msumVal (segVal efrom eto n) osrc line n := by
  unfold msumVal
  apply List.sum_nonneg
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  have hk' := List.mem_range.mp hk
  show 0 ≤ segVal efrom eto n k * line k - segVal efrom eto n k * osrc k * line k
  rw [segVal_eq hf ht k]
  by_cases hb : (af < k ∧ k < at_) ∨ (at_ < k ∧ k < af)
  · rw [if_pos hb]
    rcases hosrc k hk' with h0 | h1
    · rw [h0]; nlinarith [(hline k hk').1]
    · rw [h1]; nlinarith [(hline k hk').1]
  · rw [if_neg hb]; nlinarith [(hline k hk').1]

/-- The gated other-source mask, INCLUSIVE of the destination endpoint: for `k` strictly between the
endpoints OR at the destination, `osrc k = 1` iff the coordinate at along-index `k` is the source of
some move. (`blockedB`'s passability exempts every moving source — `mark_passable` — including a
source sitting on the destination, which is why the destination is in the inclusive range.) -/
def OsrcIsOtherSourceVertIncl (osrc : Nat → ℤ) (ms : List Move) (x n af at_ : Nat) : Prop :=
  ∀ k, k < n → (Between af at_ k ∨ k = at_) →
    (osrc k = 1 ↔ (ms.any (fun m' => m'.frm == (⟨x, k⟩ : Coord))) = true)

def OsrcIsOtherSourceHorizIncl (osrc : Nat → ℤ) (ms : List Move) (y n af at_ : Nat) : Prop :=
  ∀ k, k < n → (Between af at_ k ∨ k = at_) →
    (osrc k = 1 ↔ (ms.any (fun m' => m'.frm == (⟨k, y⟩ : Coord))) = true)

/-- The `blockedB` per-cell predicate, as a `Prop` pair (Bool `&&`/`!` unfolded once). -/
theorem blockedPred_iff (b : Board) (ms : List Move) (c : Coord) :
    (!(b.cellAt c).isVacuum && !(ms.any (fun m' => m'.frm == c))) = true
      ↔ (¬ (b.cellAt c).isVacuum = true ∧ ¬ (ms.any (fun m' => m'.frm == c)) = true) := by
  cases (b.cellAt c).isVacuum <;>
    cases (ms.any (fun m' => m'.frm == c)) <;> simp

/-- **The reference `blockedB`, VERTICAL, split into interior-blocks OR destination-blocks.** The
first disjunct is exactly the old `occluded_vert_iff` shape (strict interior); the second is the new
endpoint case — a non-passable piece on the destination. -/
theorem blocked_vert_iff (b : Board) (ms : List Move) (m : Move) (h : m.frm.x = m.to.x) :
    blockedB b ms m = true ↔
      (∃ y, min m.frm.y m.to.y < y ∧ y < max m.frm.y m.to.y
          ∧ ¬ (b.cellAt (⟨m.frm.x, y⟩ : Coord)).isVacuum = true
          ∧ ¬ (ms.any (fun m' => m'.frm == (⟨m.frm.x, y⟩ : Coord))) = true)
      ∨ (¬ (b.cellAt m.to).isVacuum = true ∧ ¬ (ms.any (fun m' => m'.frm == m.to)) = true) := by
  unfold blockedB pathCells
  rw [List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    List.any_eq_true]
  constructor
  · rintro (⟨c, hc, hp⟩ | hdst)
    · left
      obtain ⟨cx, cy⟩ := c
      obtain ⟨hx, hlo, hhi⟩ := (mem_interior_vert m.frm m.to ⟨cx, cy⟩ h).mp hc
      simp only at hx; subst hx
      have hp' := (blockedPred_iff b ms ⟨m.frm.x, cy⟩).mp hp
      exact ⟨cy, hlo, hhi, hp'.1, hp'.2⟩
    · right; exact (blockedPred_iff b ms m.to).mp hdst
  · rintro (⟨y, hlo, hhi, hv, hs⟩ | ⟨hv, hs⟩)
    · left
      exact ⟨⟨m.frm.x, y⟩, (mem_interior_vert m.frm m.to _ h).mpr ⟨rfl, hlo, hhi⟩,
        (blockedPred_iff b ms _).mpr ⟨hv, hs⟩⟩
    · right; exact (blockedPred_iff b ms m.to).mpr ⟨hv, hs⟩

/-- **The reference `blockedB`, HORIZONTAL, split into interior-blocks OR destination-blocks.** -/
theorem blocked_horiz_iff (b : Board) (ms : List Move) (m : Move) (h : m.frm.x ≠ m.to.x) :
    blockedB b ms m = true ↔
      (∃ x, min m.frm.x m.to.x < x ∧ x < max m.frm.x m.to.x
          ∧ ¬ (b.cellAt (⟨x, m.frm.y⟩ : Coord)).isVacuum = true
          ∧ ¬ (ms.any (fun m' => m'.frm == (⟨x, m.frm.y⟩ : Coord))) = true)
      ∨ (¬ (b.cellAt m.to).isVacuum = true ∧ ¬ (ms.any (fun m' => m'.frm == m.to)) = true) := by
  unfold blockedB pathCells
  rw [List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    List.any_eq_true]
  constructor
  · rintro (⟨c, hc, hp⟩ | hdst)
    · left
      obtain ⟨cx, cy⟩ := c
      obtain ⟨hy, hlo, hhi⟩ := (mem_interior_horiz m.frm m.to ⟨cx, cy⟩ h).mp hc
      simp only at hy; subst hy
      have hp' := (blockedPred_iff b ms ⟨cx, m.frm.y⟩).mp hp
      exact ⟨cx, hlo, hhi, hp'.1, hp'.2⟩
    · right; exact (blockedPred_iff b ms m.to).mp hdst
  · rintro (⟨x, hlo, hhi, hv, hs⟩ | ⟨hv, hs⟩)
    · left
      exact ⟨⟨x, m.frm.y⟩, (mem_interior_horiz m.frm m.to _ h).mpr ⟨rfl, hlo, hhi⟩,
        (blockedPred_iff b ms _).mpr ⟨hv, hs⟩⟩
    · right; exact (blockedPred_iff b ms m.to).mpr ⟨hv, hs⟩

/-- **THE INCLUSIVE OCCLUSION REFINEMENT, VERTICAL, AT ARBITRARY BOARD SIZE.** The emitted inclusive
threshold bit (`msumInclVal ≥ 1`) equals the reference `AutomataflRules.blockedB` — for any `n`, any
vertical rook move, any move list. The interior half reuses `msum_ge_one_iff` unchanged; the
destination half is the single endpoint term. NON-VACUOUS at `n = 3` (§5b.4). -/
theorem occ_eq_blockedB_vert {efrom eto osrc line : Nat → ℤ} {n : Nat}
    {b : Board} {ms : List Move} {m : Move}
    (hvert : m.frm.x = m.to.x)
    (hfy : m.frm.y < n) (hty : m.to.y < n)
    (hf : OneHotAt efrom n m.frm.y) (ht : OneHotAt eto n m.to.y)
    (hosrc : ∀ k, k < n → osrc k = 0 ∨ osrc k = 1)
    (hlineRange : ∀ k, k < n → 0 ≤ line k ∧ line k ≤ 3)
    (hlineRead : LineReadsVert line b m.frm.x n)
    (hosrcMeans : OsrcIsOtherSourceVertIncl osrc ms m.frm.x n m.frm.y m.to.y) :
    (1 ≤ msumInclVal efrom eto osrc line n) ↔ blockedB b ms m = true := by
  have hdst : (⟨m.frm.x, m.to.y⟩ : Coord) = m.to := by rw [hvert]
  have hcollapse : msumInclVal efrom eto osrc line n
      = msumVal (segVal efrom eto n) osrc line n + (1 - osrc m.to.y) * line m.to.y := by
    unfold msumInclVal; rw [endpoint_collapse ht]
  have hAnn : 0 ≤ msumVal (segVal efrom eto n) osrc line n :=
    msumVal_segVal_nonneg hf ht hosrc hlineRange
  have hBnn : 0 ≤ (1 - osrc m.to.y) * line m.to.y := by
    rcases hosrc m.to.y hty with h0 | h1
    · rw [h0]; nlinarith [(hlineRange m.to.y hty).1]
    · rw [h1]; nlinarith [(hlineRange m.to.y hty).1]
  -- interior half: reuse `msum_ge_one_iff`
  have hAiff : (1 ≤ msumVal (segVal efrom eto n) osrc line n) ↔
      (∃ y, min m.frm.y m.to.y < y ∧ y < max m.frm.y m.to.y
          ∧ ¬ (b.cellAt (⟨m.frm.x, y⟩ : Coord)).isVacuum = true
          ∧ ¬ (ms.any (fun m' => m'.frm == (⟨m.frm.x, y⟩ : Coord))) = true) := by
    rw [msum_ge_one_iff hf ht hosrc hlineRange]
    constructor
    · rintro ⟨k, hk, hbet, ho, hne⟩
      refine ⟨k, ?_, ?_, ?_, ?_⟩
      · rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · exact fun hc => hne ((hlineRead k hk).mpr hc)
      · exact fun hc => by
          have := (hosrcMeans k hk (Or.inl hbet)).mpr hc; rw [ho] at this
          exact absurd this (by norm_num)
    · rintro ⟨y, hlo, hhi, hv, hs⟩
      have hyn : y < n := by omega
      have hbet : Between m.frm.y m.to.y y := by
        unfold Between; rcases Nat.lt_or_ge m.frm.y m.to.y with hd | hd
        · left; constructor <;> omega
        · right; constructor <;> omega
      refine ⟨y, hyn, hbet, ?_, ?_⟩
      · rcases hosrc y hyn with h0 | h1
        · exact h0
        · exact absurd ((hosrcMeans y hyn (Or.inl hbet)).mp h1) hs
      · exact fun hz => hv ((hlineRead y hyn).mp hz)
  -- destination half: the single endpoint term
  have hBiff : (1 ≤ (1 - osrc m.to.y) * line m.to.y) ↔
      (¬ (b.cellAt m.to).isVacuum = true ∧ ¬ (ms.any (fun m' => m'.frm == m.to)) = true) := by
    rcases hosrc m.to.y hty with h0 | h1
    · rw [h0]; simp only [sub_zero, one_mul]
      constructor
      · intro hge
        refine ⟨?_, ?_⟩
        · intro hc
          have hv : (b.cellAt (⟨m.frm.x, m.to.y⟩ : Coord)).isVacuum = true := by rw [hdst]; exact hc
          have := (hlineRead m.to.y hty).mpr hv; omega
        · intro hc
          have hs : (ms.any (fun m' => m'.frm == (⟨m.frm.x, m.to.y⟩ : Coord))) = true := by
            rw [hdst]; exact hc
          have := (hosrcMeans m.to.y hty (Or.inr rfl)).mpr hs; omega
      · rintro ⟨hv, hs⟩
        have hne : line m.to.y ≠ 0 := by
          intro hz
          have := (hlineRead m.to.y hty).mp hz; rw [hdst] at this; exact hv this
        have := (hlineRange m.to.y hty).1; omega
    · rw [h1]; simp only [sub_self, zero_mul]
      constructor
      · intro hge; exact absurd hge (by norm_num)
      · rintro ⟨hv, hs⟩
        have := (hosrcMeans m.to.y hty (Or.inr rfl)).mp h1; rw [hdst] at this
        exact absurd this hs
  rw [hcollapse, blocked_vert_iff b ms m hvert, ← hAiff, ← hBiff]
  omega

/-- **THE INCLUSIVE OCCLUSION REFINEMENT, HORIZONTAL, AT ARBITRARY BOARD SIZE.** The mirror of
`occ_eq_blockedB_vert` for the row-scan branch. `hrow` (`m.frm.y = m.to.y`) is the rook alignment of
a horizontal move — it identifies the destination cell `m.to` with the along-line coordinate. -/
theorem occ_eq_blockedB_horiz {efrom eto osrc line : Nat → ℤ} {n : Nat}
    {b : Board} {ms : List Move} {m : Move}
    (hhoriz : m.frm.x ≠ m.to.x) (hrow : m.frm.y = m.to.y)
    (hfx : m.frm.x < n) (htx : m.to.x < n)
    (hf : OneHotAt efrom n m.frm.x) (ht : OneHotAt eto n m.to.x)
    (hosrc : ∀ k, k < n → osrc k = 0 ∨ osrc k = 1)
    (hlineRange : ∀ k, k < n → 0 ≤ line k ∧ line k ≤ 3)
    (hlineRead : LineReadsHoriz line b m.frm.y n)
    (hosrcMeans : OsrcIsOtherSourceHorizIncl osrc ms m.frm.y n m.frm.x m.to.x) :
    (1 ≤ msumInclVal efrom eto osrc line n) ↔ blockedB b ms m = true := by
  have hdst : (⟨m.to.x, m.frm.y⟩ : Coord) = m.to := by rw [hrow]
  have hcollapse : msumInclVal efrom eto osrc line n
      = msumVal (segVal efrom eto n) osrc line n + (1 - osrc m.to.x) * line m.to.x := by
    unfold msumInclVal; rw [endpoint_collapse ht]
  have hAnn : 0 ≤ msumVal (segVal efrom eto n) osrc line n :=
    msumVal_segVal_nonneg hf ht hosrc hlineRange
  have hBnn : 0 ≤ (1 - osrc m.to.x) * line m.to.x := by
    rcases hosrc m.to.x htx with h0 | h1
    · rw [h0]; nlinarith [(hlineRange m.to.x htx).1]
    · rw [h1]; nlinarith [(hlineRange m.to.x htx).1]
  have hAiff : (1 ≤ msumVal (segVal efrom eto n) osrc line n) ↔
      (∃ x, min m.frm.x m.to.x < x ∧ x < max m.frm.x m.to.x
          ∧ ¬ (b.cellAt (⟨x, m.frm.y⟩ : Coord)).isVacuum = true
          ∧ ¬ (ms.any (fun m' => m'.frm == (⟨x, m.frm.y⟩ : Coord))) = true) := by
    rw [msum_ge_one_iff hf ht hosrc hlineRange]
    constructor
    · rintro ⟨k, hk, hbet, ho, hne⟩
      refine ⟨k, ?_, ?_, ?_, ?_⟩
      · rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · exact fun hc => hne ((hlineRead k hk).mpr hc)
      · exact fun hc => by
          have := (hosrcMeans k hk (Or.inl hbet)).mpr hc; rw [ho] at this
          exact absurd this (by norm_num)
    · rintro ⟨x, hlo, hhi, hv, hs⟩
      have hxn : x < n := by omega
      have hbet : Between m.frm.x m.to.x x := by
        unfold Between; rcases Nat.lt_or_ge m.frm.x m.to.x with hd | hd
        · left; constructor <;> omega
        · right; constructor <;> omega
      refine ⟨x, hxn, hbet, ?_, ?_⟩
      · rcases hosrc x hxn with h0 | h1
        · exact h0
        · exact absurd ((hosrcMeans x hxn (Or.inl hbet)).mp h1) hs
      · exact fun hz => hv ((hlineRead x hxn).mp hz)
  have hBiff : (1 ≤ (1 - osrc m.to.x) * line m.to.x) ↔
      (¬ (b.cellAt m.to).isVacuum = true ∧ ¬ (ms.any (fun m' => m'.frm == m.to)) = true) := by
    rcases hosrc m.to.x htx with h0 | h1
    · rw [h0]; simp only [sub_zero, one_mul]
      constructor
      · intro hge
        refine ⟨?_, ?_⟩
        · intro hc
          have hv : (b.cellAt (⟨m.to.x, m.frm.y⟩ : Coord)).isVacuum = true := by rw [hdst]; exact hc
          have := (hlineRead m.to.x htx).mpr hv; omega
        · intro hc
          have hs : (ms.any (fun m' => m'.frm == (⟨m.to.x, m.frm.y⟩ : Coord))) = true := by
            rw [hdst]; exact hc
          have := (hosrcMeans m.to.x htx (Or.inr rfl)).mpr hs; omega
      · rintro ⟨hv, hs⟩
        have hne : line m.to.x ≠ 0 := by
          intro hz
          have := (hlineRead m.to.x htx).mp hz; rw [hdst] at this; exact hv this
        have := (hlineRange m.to.x htx).1; omega
    · rw [h1]; simp only [sub_self, zero_mul]
      constructor
      · intro hge; exact absurd hge (by norm_num)
      · rintro ⟨hv, hs⟩
        have := (hosrcMeans m.to.x htx (Or.inr rfl)).mp h1; rw [hdst] at this
        exact absurd this hs
  rw [hcollapse, blocked_horiz_iff b ms m hhoriz, ← hAiff, ← hBiff]
  omega

/-! ## §6 — NON-VACUITY: the generalisation is not empty at `n ≥ 3`.

`interior_nil_n2` / `occluded_false_n2` are true only because their conclusions are trivial. The
witnesses below show the new machinery has both truth values at `n = 3`, so `segVal_eq` and
`msum_ge_one_iff` are not dressed-up versions of the same vacuity. -/

/-- A 3-line HAS a strictly-interior cell — the fact that makes `interior_nil_n2` false at `n ≥ 3`
and this file necessary. -/
example : interior ⟨0, 0⟩ ⟨0, 2⟩ = [⟨0, 1⟩] := by decide

/-- The between-mask FIRES at `n = 3`: the emitted `seg[1]` head is `1` for a move from along-index
`0` to along-index `2`. (At `n = 2`, `segVal_n2` says every `seg` is `0`.) -/
example :
    segVal (fun j => if j = 0 then 1 else 0) (fun j => if j = 2 then 1 else 0) 3 1 = 1 := by
  decide

/-- …and does NOT fire outside the interval. -/
example :
    segVal (fun j => if j = 0 then 1 else 0) (fun j => if j = 2 then 1 else 0) 3 0 = 0 := by
  decide

/-- A blocking piece at the interior index makes the emitted threshold fire. -/
example :
    1 ≤ msumVal
      (segVal (fun j => if j = 0 then 1 else 0) (fun j => if j = 2 then 1 else 0) 3)
      (fun _ => 0) (fun k => if k = 1 then 2 else 0) 3 := by decide

/-- A `mark_passable`-d interior source does NOT occlude — the `(1 − osrc)` factor is load-bearing,
not decoration. -/
example :
    ¬ (1 ≤ msumVal
      (segVal (fun j => if j = 0 then 1 else 0) (fun j => if j = 2 then 1 else 0) 3)
      (fun k => if k = 1 then 1 else 0) (fun k => if k = 1 then 2 else 0) 3) := by decide

/-! ## §6.5 — THE GENERIC BRIDGE, DRIVEN CONTENTFULLY AT `n = 3` on a REAL `Board`.

§6's `decide`s exercise `segVal` / `msumVal` in isolation. This section drives the FULL generic
bridge theorem — `occ_eq_occluded_vert` / `occ_eq_occluded_horiz`, the one that equates the emitted
`msum ≥ 1` threshold with the reference `Automatafl.occluded` — at `n = 3`, on concrete 3×3 boards,
in the three configurations a 2×2 board structurally cannot express (its interior is empty):

  * **fires** — a non-vacuum, non-passable piece STRICTLY BETWEEN src and dst forces BOTH the
    threshold and the reference `occluded` to `true`;
  * **clear** — an empty interior forces BOTH to `false`;
  * **passable** — an interior piece that IS a moving source (`mark_passable`d) forces BOTH to
    `false`, and it is the `(1 − osrc)` factor — not board smallness — that suppresses it.

Every hypothesis of `occ_eq_occluded_vert/horiz` (the along-axis one-hots, the line-read, the
passable mask, the range/boolean side-conditions) is discharged for the concrete witnesses; the
biconditional AND the shared non-trivial truth value are both exhibited, so the correspondence is
NON-VACUOUS — this is what `occluded_false_n2` could not be. The witnesses are constructed by hand
(this validates the generic bridge THEOREM, not the off-`Satisfied2` discharge of its hypotheses
from an emitted descriptor). -/

/-- The `[· = i]` indicator really is `OneHotAt` at `i`, n-generically. -/
theorem oneHotAt_ite (n i : Nat) (hi : i < n) :
    OneHotAt (fun j => if j = i then (1 : ℤ) else 0) n i :=
  ⟨hi, fun _ _ => rfl⟩

/-- `0 ≤ line k ≤ 3` for the `felt = 1 at k = 1, else 0` line shape, `k < 3`. -/
theorem lineRange_ite1_3 : ∀ k, k < 3 →
    0 ≤ (if k = 1 then (1 : ℤ) else 0) ∧ (if k = 1 then (1 : ℤ) else 0) ≤ 3 := by
  intro k _
  by_cases h : k = 1
  · rw [if_pos h]; constructor <;> norm_num
  · rw [if_neg h]; constructor <;> norm_num

/-! ### Vertical instances: a rook move down the shared column `x = 0`, `y : 0 → 2`; interior `⟨0,1⟩`. -/

/-- A vertical rook move on the shared column `x = 0`, from `y = 0` to `y = 2`. Its interior is the
single cell `⟨0,1⟩` — the cell a 2-line does not have. -/
def mV3 : Move := ⟨0, ⟨0, 0⟩, ⟨0, 2⟩⟩
/-- The moving sources at the two endpoints (the interior `⟨0,1⟩` is NOT among them). -/
def srcsV3 : List Coord := [⟨0, 0⟩, ⟨0, 2⟩]
/-- The same, plus the interior cell registered as a moving source (`mark_passable`). -/
def srcsV3pass : List Coord := [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩]
/-- A 3×3 board with a repulsor STRICTLY BETWEEN the endpoints (at `⟨0,1⟩`), vacuum elsewhere. -/
def bV3blocked : Board where
  size := 3
  cells := fun c => if c = ⟨0, 1⟩ then Particle.repulsor else Particle.vacuum
  automaton := ⟨2, 2⟩
/-- The same board with a CLEAR interior — every cell vacuum. -/
def bV3clear : Board where
  size := 3
  cells := fun _ => Particle.vacuum
  automaton := ⟨2, 2⟩

/-- Along-axis source one-hot at index `0`. -/
def efromV3 : Nat → ℤ := fun j => if j = 0 then 1 else 0
/-- Along-axis destination one-hot at index `2`. -/
def etoV3 : Nat → ℤ := fun j => if j = 2 then 1 else 0
/-- The line down `x = 0` on the blocked board: felt `1` (a piece) at interior `k = 1`, else `0`. -/
def lineV3blocked : Nat → ℤ := fun k => if k = 1 then 1 else 0
/-- The line down `x = 0` on the clear board: vacuum everywhere. -/
def lineV3clear : Nat → ℤ := fun _ => 0
/-- No interior source ⇒ the passable mask is `0`. -/
def osrcV3zero : Nat → ℤ := fun _ => 0
/-- The interior cell IS a moving source ⇒ the passable mask marks `k = 1`. -/
def osrcV3one : Nat → ℤ := fun k => if k = 1 then 1 else 0

theorem efromV3_oneHot : OneHotAt efromV3 3 0 := oneHotAt_ite 3 0 (by decide)
theorem etoV3_oneHot : OneHotAt etoV3 3 2 := oneHotAt_ite 3 2 (by decide)

/-- **FIRES.** The interior blocker forces the emitted threshold AND the reference `occluded` to
`true`, and the generic bridge equates them — at `n = 3`, where a 2-line's empty interior cannot. -/
theorem occ_bridge_vert_fires_n3 :
    ((1 ≤ msumVal (segVal efromV3 etoV3 3) osrcV3zero lineV3blocked 3)
        ↔ occluded bV3blocked srcsV3 mV3 = true)
      ∧ (1 ≤ msumVal (segVal efromV3 etoV3 3) osrcV3zero lineV3blocked 3)
      ∧ occluded bV3blocked srcsV3 mV3 = true := by
  refine ⟨?_, by decide, by decide⟩
  refine occ_eq_occluded_vert (m := mV3) (b := bV3blocked) (srcs := srcsV3) (n := 3)
    rfl (by decide) (by decide) efromV3_oneHot etoV3_oneHot
    (fun k _ => Or.inl rfl) (fun k hk => lineRange_ite1_3 k hk) ?_ ?_
  · -- LineReadsVert: line k = 0 ↔ cell (0,k) vacuum
    intro k hk; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide
  · -- OsrcIsOtherSourceVert: on the interior (k = 1) the mask is 0 and ⟨0,1⟩ ∉ srcs
    intro k hk hbet; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      first | decide | exact absurd hbet (by decide)

/-- **CLEAR.** An empty interior forces BOTH sides to `false`. -/
theorem occ_bridge_vert_clear_n3 :
    ((1 ≤ msumVal (segVal efromV3 etoV3 3) osrcV3zero lineV3clear 3)
        ↔ occluded bV3clear srcsV3 mV3 = true)
      ∧ ¬ (1 ≤ msumVal (segVal efromV3 etoV3 3) osrcV3zero lineV3clear 3)
      ∧ occluded bV3clear srcsV3 mV3 = false := by
  refine ⟨?_, by decide, by decide⟩
  refine occ_eq_occluded_vert (m := mV3) (b := bV3clear) (srcs := srcsV3) (n := 3)
    rfl (by decide) (by decide) efromV3_oneHot etoV3_oneHot
    (fun k _ => Or.inl rfl) (fun k _ => by simp [lineV3clear]) ?_ ?_
  · intro k hk; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide
  · intro k hk hbet; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      first | decide | exact absurd hbet (by decide)

/-- **PASSABLE.** An interior piece that IS a moving source does NOT occlude: the `(1 − osrc)`
factor kills the term (threshold `false`) and `occluded`'s `¬ srcs.contains` guard drops the cell
(reference `false`). This is the load-bearing factor made visible at a real interior cell. -/
theorem occ_bridge_vert_passable_n3 :
    ((1 ≤ msumVal (segVal efromV3 etoV3 3) osrcV3one lineV3blocked 3)
        ↔ occluded bV3blocked srcsV3pass mV3 = true)
      ∧ ¬ (1 ≤ msumVal (segVal efromV3 etoV3 3) osrcV3one lineV3blocked 3)
      ∧ occluded bV3blocked srcsV3pass mV3 = false := by
  refine ⟨?_, by decide, by decide⟩
  refine occ_eq_occluded_vert (m := mV3) (b := bV3blocked) (srcs := srcsV3pass) (n := 3)
    rfl (by decide) (by decide) efromV3_oneHot etoV3_oneHot
    ?_ (fun k hk => lineRange_ite1_3 k hk) ?_ ?_
  · -- osrcV3one is boolean
    intro k _; by_cases h : k = 1
    · right; simp [osrcV3one, h]
    · left; simp [osrcV3one, h]
  · intro k hk; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide
  · -- on the interior (k = 1) the mask is 1 and ⟨0,1⟩ ∈ srcsV3pass
    intro k hk hbet; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      first | decide | exact absurd hbet (by decide)

/-! ### Horizontal instance: a rook move across the shared row `y = 0`, `x : 0 → 2`; interior `⟨1,0⟩`.
Exercises the OTHER generic bridge theorem (`occ_eq_occluded_horiz`, the row-scan branch). -/

/-- A horizontal rook move on the shared row `y = 0`, from `x = 0` to `x = 2`; interior `⟨1,0⟩`. -/
def mH3 : Move := ⟨0, ⟨0, 0⟩, ⟨2, 0⟩⟩
def srcsH3 : List Coord := [⟨0, 0⟩, ⟨2, 0⟩]
/-- A 3×3 board with an attractor STRICTLY BETWEEN the horizontal endpoints (at `⟨1,0⟩`). -/
def bH3blocked : Board where
  size := 3
  cells := fun c => if c = ⟨1, 0⟩ then Particle.attractor else Particle.vacuum
  automaton := ⟨2, 2⟩

/-- **FIRES (horizontal).** The interior blocker on the row forces both sides `true`, equated by
`occ_eq_occluded_horiz` at `n = 3`. -/
theorem occ_bridge_horiz_fires_n3 :
    ((1 ≤ msumVal (segVal efromV3 etoV3 3) osrcV3zero lineV3blocked 3)
        ↔ occluded bH3blocked srcsH3 mH3 = true)
      ∧ (1 ≤ msumVal (segVal efromV3 etoV3 3) osrcV3zero lineV3blocked 3)
      ∧ occluded bH3blocked srcsH3 mH3 = true := by
  refine ⟨?_, by decide, by decide⟩
  refine occ_eq_occluded_horiz (m := mH3) (b := bH3blocked) (srcs := srcsH3) (n := 3)
    (by decide) (by decide) (by decide) efromV3_oneHot etoV3_oneHot
    (fun k _ => Or.inl rfl) (fun k hk => lineRange_ite1_3 k hk) ?_ ?_
  · -- LineReadsHoriz: line k = 0 ↔ cell (k,0) vacuum
    intro k hk; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide
  · intro k hk hbet; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      first | decide | exact absurd hbet (by decide)

/-! ### §5b.4 — the INCLUSIVE endpoint BITES at `n = 3`: a piece ON THE DESTINATION blocks.

The audit's 3.2 CRIT case, made concrete. A vertical move `⟨0,0⟩ → ⟨0,2⟩` with a repulsor standing
on the DESTINATION `⟨0,2⟩` (interior `⟨0,1⟩` empty). Under the INCLUSIVE `blockedB` the move is
BLOCKED (and the mover is replaced at its origin); under the OLD EXCLUSIVE `occluded` it is NOT — the
old check would have let the mover overwrite the occupant, deleting it. The bridge equates the
inclusive threshold with `blockedB`, both `true`; the exclusive `msumVal` and `occluded` are `false`.
This is the exact content the extra endpoint term adds. -/

/-- A 3×3 board with a repulsor on the DESTINATION `⟨0,2⟩` (interior `⟨0,1⟩` empty, source vacated). -/
def bV3dstblocked : Board where
  size := 3
  cells := fun c => if c = ⟨0, 2⟩ then Particle.repulsor else Particle.vacuum
  automaton := ⟨2, 2⟩
/-- The line down `x = 0`: a piece (felt `1`) only at the DESTINATION index `k = 2`. -/
def lineV3dst : Nat → ℤ := fun k => if k = 2 then 1 else 0

theorem occ_bridge_vert_dst_fires_n3 :
    ((1 ≤ msumInclVal efromV3 etoV3 osrcV3zero lineV3dst 3)
        ↔ blockedB bV3dstblocked [mV3] mV3 = true)
      ∧ (1 ≤ msumInclVal efromV3 etoV3 osrcV3zero lineV3dst 3)   -- inclusive threshold FIRES
      ∧ blockedB bV3dstblocked [mV3] mV3 = true                  -- reference blockedB FIRES
      ∧ msumVal (segVal efromV3 etoV3 3) osrcV3zero lineV3dst 3 = 0  -- exclusive interior MISSES it
      ∧ occluded bV3dstblocked srcsV3 mV3 = false := by           -- old exclusive occluded MISSES it
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  refine occ_eq_blockedB_vert (m := mV3) (b := bV3dstblocked) (ms := [mV3]) (n := 3)
    rfl (by decide) (by decide) efromV3_oneHot etoV3_oneHot
    (fun k _ => Or.inl rfl) ?_ ?_ ?_
  · intro k hk; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide
  · intro k hk; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide
  · intro k hk hincl
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact absurd hincl (by decide)
    · decide
    · decide

/-! ## §7 — Axiom pins. -/

#assert_axioms sum_oneHot_mul
#assert_axioms msumVal_segVal_nonneg
#assert_axioms endpoint_collapse
#assert_axioms blocked_vert_iff
#assert_axioms blocked_horiz_iff
#assert_axioms occ_eq_blockedB_vert
#assert_axioms occ_eq_blockedB_horiz
#assert_axioms occ_bridge_vert_dst_fires_n3
#assert_axioms segVal_eq
#assert_axioms msum_ge_one_iff
#assert_axioms mem_interior_vert
#assert_axioms mem_interior_horiz
#assert_axioms occluded_vert_iff
#assert_axioms occluded_horiz_iff
#assert_axioms occ_eq_occluded_vert
#assert_axioms occ_eq_occluded_horiz
#assert_axioms occ_bridge_vert_fires_n3
#assert_axioms occ_bridge_vert_clear_n3
#assert_axioms occ_bridge_vert_passable_n3
#assert_axioms occ_bridge_horiz_fires_n3

end Dregg2.Circuit.Emit.AutomataflOcclusionGeneric
