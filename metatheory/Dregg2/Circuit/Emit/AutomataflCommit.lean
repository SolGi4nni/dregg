/-
# `AutomataflCommit` — the n-generic board commitment family (base-4 positional pack)

Step 1 of the AUTOMATAFL-NGENERIC rebuild (`docs/reference/AUTOMATAFL-NGENERIC-DESIGN.md` §1, §6.1).
LEAN-AUTHORED AIR: the pack gates and the PI-binding commitment are emitted here as
`VmConstraint2`; `dregg-automatafl/src/*.rs` is read as spec only. This file is ADDITIVE — it does
NOT touch the existing `bind_board_roots` / `node8Lookup` families in `AutomataflStepEmit` /
`AutomataflResolveEmit`; those are retired later in the `descN` refactor (§4). Nothing existing
changes.

THE PACK. A board cell holds a 2-bit code `{VAC=0, REP=1, ATT=2, AUTO=3}` (range-pinned by
`boardRangeCells` here, mirroring `boardRangeConstraints`). Pack `15` cells per BabyBear felt as a
base-4 number:

    packed_j := Σ_{i=0}^{14} cell[15·j + i] · 4^i,   j ∈ [0, ⌈n²/15⌉)

`4^15 − 1 = 2^30 − 1 = 1073741823 < p = 2013265921` (BabyBear), so a felt never wraps: `15` cells is
the maximum (`16` cells = `4^16 = 2^32` would wrap). At `n = 11`: `⌈121/15⌉ = 9` felts. The pack is
degree 1 (the `4^i` are constants; each gate is linear in the cell columns).

THE PAYOFF (`pack_injective`, `packBoard_injective`). Because each cell is in `{0,1,2,3}` and the
per-felt sum lands in `[0, 4^15) ⊂ [0, p)`, reduction mod `p` is the identity there and base-4
positional decode is unique — so equal packed felt-tuples FORCE cell-wise board agreement. This is a
PURE Lean theorem (no crypto). It is what discharges the whole-turn seam under Option A: equal
packed-felt PIs on the two legs ⇒ (by `pack_injective`) the two boards agree cell-wise.
-/
import Dregg2.Games.Automatafl
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Tactics
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Dregg2.Circuit.Emit.AutomataflCommit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTupleN)
open Dregg2.Games.Automatafl

set_option autoImplicit false

/-! ## §1 — Pack geometry (n-generic). -/

/-- Cells packed per BabyBear felt: `4^15 − 1 = 2^30 − 1 < p`, `16` would wrap. -/
def CELLS_PER_FELT : Nat := 15

/-- BabyBear prime `2^31 − 2^27 + 1`. -/
def BABYBEAR_P : ℤ := 2013265921

/-- Felt count `⌈n²/15⌉`. `feltCount 2 = 1`, `feltCount 11 = 9`, single-permutation through `n = 15`. -/
def feltCount (n : Nat) : Nat := (n * n + 14) / 15

/-! ## §2 — The pure semantic pack (the reference `packed_j`). -/

/-- Base-4 Horner evaluation `Σ_i cᵢ·4^i` of a coefficient list (`c₀ + 4·(c₁ + 4·(c₂ + …)) )`). -/
def horner4 : List ℤ → ℤ
  | []      => 0
  | c :: cs => c + 4 * horner4 cs

@[simp] theorem horner4_nil : horner4 [] = 0 := rfl
@[simp] theorem horner4_cons (c : ℤ) (cs : List ℤ) : horner4 (c :: cs) = c + 4 * horner4 cs := rfl

/-- The `j`-th packed felt of a cell-code column `cell : Nat → ℤ` (index = `y·n + x`):
`packed_j = Σ_{i<15} cell(15j+i)·4^i`. -/
def packCell (cell : Nat → ℤ) (j : Nat) : ℤ :=
  horner4 ((List.range 15).map (fun i => cell (15 * j + i)))

/-- The full packed felt-tuple: `⌈n²/15⌉` felts (`packCells cell (feltCount n)`). -/
def packCells (cell : Nat → ℤ) (fc : Nat) : List ℤ :=
  (List.range fc).map (packCell cell)

/-! ## §3 — Base-4 positional decode is injective on the `{0,1,2,3}` alphabet (the heart). -/

/-- `(range m).map f = (range m).map g` forces `f i = g i` pointwise on `[0, m)`. -/
theorem map_range_eq {α : Type*} (f g : Nat → α) (m : Nat)
    (h : (List.range m).map f = (List.range m).map g) (i : Nat) (hi : i < m) : f i = g i := by
  have hh := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.some.injEq] at hh
  exact hh

/-- **Base-4 digit uniqueness.** Two `{0,1,2,3}`-digit lists of equal length with equal base-4 value
are equal. The heart of `pack_injective`: at each position the low digit is forced (`a ≡ b [4]`,
both `< 4` ⇒ `a = b`), then divide by 4 and recurse. -/
theorem horner4_inj (l1 : List ℤ) : ∀ (l2 : List ℤ),
    (∀ x ∈ l1, 0 ≤ x ∧ x < 4) → (∀ x ∈ l2, 0 ≤ x ∧ x < 4) →
    l1.length = l2.length → horner4 l1 = horner4 l2 → l1 = l2 := by
  induction l1 with
  | nil =>
    intro l2 _ _ hlen _
    cases l2 with
    | nil => rfl
    | cons b bs => simp at hlen
  | cons a as ih =>
    intro l2 h1 h2 hlen heq
    cases l2 with
    | nil => simp at hlen
    | cons b bs =>
      have ha := h1 a (by simp)
      have hb := h2 b (by simp)
      rw [horner4_cons, horner4_cons] at heq
      have hlen' : as.length = bs.length := by simpa using hlen
      have hab : a = b := by omega
      have htail : horner4 as = horner4 bs := by omega
      have h1' : ∀ x ∈ as, 0 ≤ x ∧ x < 4 := fun x hx => h1 x (List.mem_cons_of_mem a hx)
      have h2' : ∀ x ∈ bs, 0 ≤ x ∧ x < 4 := fun x hx => h2 x (List.mem_cons_of_mem b hx)
      rw [hab, ih bs h1' h2' hlen' htail]

/-- Per-felt injectivity: equal `packed_j` on the `{0,1,2,3}` alphabet ⇒ the 15 cells agree. -/
theorem packCell_inj (cell1 cell2 : Nat → ℤ) (j : Nat)
    (h1 : ∀ i, i < 15 → 0 ≤ cell1 (15 * j + i) ∧ cell1 (15 * j + i) < 4)
    (h2 : ∀ i, i < 15 → 0 ≤ cell2 (15 * j + i) ∧ cell2 (15 * j + i) < 4)
    (heq : packCell cell1 j = packCell cell2 j) :
    ∀ i, i < 15 → cell1 (15 * j + i) = cell2 (15 * j + i) := by
  unfold packCell at heq
  have hb1 : ∀ x ∈ (List.range 15).map (fun i => cell1 (15 * j + i)), 0 ≤ x ∧ x < 4 := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.mem_range] at hi
    exact h1 i hi
  have hb2 : ∀ x ∈ (List.range 15).map (fun i => cell2 (15 * j + i)), 0 ≤ x ∧ x < 4 := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.mem_range] at hi
    exact h2 i hi
  have hlen : ((List.range 15).map (fun i => cell1 (15 * j + i))).length
            = ((List.range 15).map (fun i => cell2 (15 * j + i))).length := by simp
  have hlists := horner4_inj _ _ hb1 hb2 hlen heq
  intro i hi
  exact map_range_eq (fun i => cell1 (15 * j + i)) (fun i => cell2 (15 * j + i)) 15 hlists i hi

/-- **`pack_injective` — THE KEY THEOREM (n-generic, pure Lean).** Cell-code columns in `{0,1,2,3}`
with equal packed felt-tuples agree at every packed cell index `[0, 15·fc)` — in particular at every
in-bounds board index (`15·⌈n²/15⌉ ≥ n²`, `sq_le_feltCount`). No modular collision, no crypto. -/
theorem pack_injective (cell1 cell2 : Nat → ℤ) (fc : Nat)
    (h1 : ∀ i, i < 15 * fc → 0 ≤ cell1 i ∧ cell1 i < 4)
    (h2 : ∀ i, i < 15 * fc → 0 ≤ cell2 i ∧ cell2 i < 4)
    (heq : packCells cell1 fc = packCells cell2 fc) :
    ∀ i, i < 15 * fc → cell1 i = cell2 i := by
  unfold packCells at heq
  have hfelt : ∀ j, j < fc → packCell cell1 j = packCell cell2 j := by
    intro j hj
    exact map_range_eq (packCell cell1) (packCell cell2) fc heq j hj
  intro i hi
  have hjfc : i / 15 < fc := by omega
  have hr : i % 15 < 15 := by omega
  have hb1 : ∀ i', i' < 15 → 0 ≤ cell1 (15 * (i / 15) + i') ∧ cell1 (15 * (i / 15) + i') < 4 :=
    fun i' hi' => h1 _ (by omega)
  have hb2 : ∀ i', i' < 15 → 0 ≤ cell2 (15 * (i / 15) + i') ∧ cell2 (15 * (i / 15) + i') < 4 :=
    fun i' hi' => h2 _ (by omega)
  have hc := packCell_inj cell1 cell2 (i / 15) hb1 hb2 (hfelt (i / 15) hjfc) (i % 15) hr
  have hidx : 15 * (i / 15) + i % 15 = i := Nat.div_add_mod i 15
  rw [hidx] at hc
  exact hc

/-! ## §4 — No modular collision: each `packed_j ∈ [0, 4^15) ⊂ [0, p)`; the mod-p variant. -/

/-- A `{0,1,2,3}`-digit list has base-4 value in `[0, 4^length)`. -/
theorem horner4_nonneg (l : List ℤ) (h : ∀ x ∈ l, 0 ≤ x ∧ x < 4) :
    0 ≤ horner4 l ∧ horner4 l < 4 ^ l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have hrest : ∀ x ∈ as, 0 ≤ x ∧ x < 4 := fun x hx => h x (List.mem_cons_of_mem a hx)
    obtain ⟨hn, hlt⟩ := ih hrest
    rw [horner4_cons, List.length_cons, pow_succ]
    exact ⟨by omega, by omega⟩

/-- Every packed felt lands in `[0, p)` (no wrap): `packed_j < 4^15 < p`. Reduction mod `p` is the
identity on packed felts, so field-equality of felts IS integer-equality. -/
theorem packCell_nonneg (cell : Nat → ℤ) (j : Nat)
    (h : ∀ i, i < 15 → 0 ≤ cell (15 * j + i) ∧ cell (15 * j + i) < 4) :
    0 ≤ packCell cell j ∧ packCell cell j < BABYBEAR_P := by
  unfold packCell
  have hb : ∀ x ∈ (List.range 15).map (fun i => cell (15 * j + i)), 0 ≤ x ∧ x < 4 := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.mem_range] at hi
    exact h i hi
  obtain ⟨hn, hlt⟩ := horner4_nonneg _ hb
  refine ⟨hn, ?_⟩
  have hlen : ((List.range 15).map (fun i => cell (15 * j + i))).length = 15 := by simp
  rw [hlen] at hlt
  have hp : (4 : ℤ) ^ 15 < BABYBEAR_P := by norm_num [BABYBEAR_P]
  exact lt_trans hlt hp

/-- **Mod-p `pack_injective`.** Packed felts agreeing MOD `p` (the on-wire PI form) with the cell
alphabet pinned ⇒ cell-wise agreement — the no-wrap bound collapses field-equality to Int-equality,
then base-4 decode. This is the exact form the seam consumes (`board PIs are BabyBear felts`). -/
theorem pack_injective_modp (cell1 cell2 : Nat → ℤ) (fc : Nat)
    (h1 : ∀ i, i < 15 * fc → 0 ≤ cell1 i ∧ cell1 i < 4)
    (h2 : ∀ i, i < 15 * fc → 0 ≤ cell2 i ∧ cell2 i < 4)
    (heq : ∀ j, j < fc → packCell cell1 j % BABYBEAR_P = packCell cell2 j % BABYBEAR_P) :
    ∀ i, i < 15 * fc → cell1 i = cell2 i := by
  have hfe : ∀ j, j < fc → packCell cell1 j = packCell cell2 j := by
    intro j hj
    have hb1 : ∀ i, i < 15 → 0 ≤ cell1 (15 * j + i) ∧ cell1 (15 * j + i) < 4 :=
      fun i hi => h1 _ (by omega)
    have hb2 : ∀ i, i < 15 → 0 ≤ cell2 (15 * j + i) ∧ cell2 (15 * j + i) < 4 :=
      fun i hi => h2 _ (by omega)
    obtain ⟨n1lo, n1hi⟩ := packCell_nonneg cell1 j hb1
    obtain ⟨n2lo, n2hi⟩ := packCell_nonneg cell2 j hb2
    have hm := heq j hj
    rwa [Int.emod_eq_of_lt n1lo n1hi, Int.emod_eq_of_lt n2lo n2hi] at hm
  have hpk : packCells cell1 fc = packCells cell2 fc := by
    unfold packCells
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    exact hfe j hj
  exact pack_injective cell1 cell2 fc h1 h2 hpk

/-! ## §5 — Reference-board layer: `packBoard` on the `Games/Automatafl.Board` + the seam corollary. -/

/-- Cell felt code `{VAC=0, REP=1, ATT=2, AUTO=3}` (`reference.rs`; inverse of `StepRefine.codeToParticle`). -/
def particleCode : Particle → ℤ
  | .vacuum    => 0
  | .repulsor  => 1
  | .attractor => 2
  | .automaton => 3

/-- Every particle code is in the alphabet `{0,1,2,3}` — the `pack_injective` precondition is FREE
for a reference board. -/
theorem particleCode_mem (p : Particle) : 0 ≤ particleCode p ∧ particleCode p < 4 := by
  cases p <;> exact ⟨by decide, by decide⟩

/-- The code map is injective, so cell-code agreement gives particle agreement. -/
theorem particleCode_inj {p q : Particle} (h : particleCode p = particleCode q) : p = q := by
  cases p <;> cases q <;> first | rfl | exact absurd h (by decide)

/-- The board's cell-code column: code of the in-bounds cell at linear index `idx` (coord
`(idx%n, idx/n)`), `0` for the pad indices `[n², 15·⌈n²/15⌉)`. -/
def boardCode (b : Board) (n : Nat) (idx : Nat) : ℤ :=
  if idx < n * n then particleCode (b.cellAt ⟨idx % n, idx / n⟩) else 0

theorem boardCode_mem (b : Board) (n idx : Nat) : 0 ≤ boardCode b n idx ∧ boardCode b n idx < 4 := by
  unfold boardCode
  split
  · exact particleCode_mem _
  · exact ⟨le_refl 0, by decide⟩

/-- `⌈n²/15⌉` felts cover all `n²` in-bounds cells: `n² ≤ 15·⌈n²/15⌉`. -/
theorem sq_le_feltCount (n : Nat) : n * n ≤ 15 * feltCount n := by
  unfold feltCount
  set m := n * n
  omega

theorem idx_mod (n x y : Nat) (hx : x < n) : (y * n + x) % n = x := by
  rw [Nat.mul_add_mod_self_right]
  exact Nat.mod_eq_of_lt hx

theorem idx_div (n x y : Nat) (hx : x < n) : (y * n + x) / n = y := by
  have hn : 0 < n := by omega
  rw [Nat.mul_comm y n, Nat.mul_add_div hn, Nat.div_eq_of_lt hx, Nat.add_zero]

theorem boardCode_inbounds (b : Board) (n x y : Nat) (hx : x < n) (hy : y < n) :
    boardCode b n (y * n + x) = particleCode (b.cellAt ⟨x, y⟩) := by
  have hlt : y * n + x < n * n :=
    calc y * n + x < y * n + n := by omega
      _ = (y + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  unfold boardCode
  rw [if_pos hlt, idx_mod n x y hx, idx_div n x y hx]

/-- The reference-board pack: `⌈n²/15⌉` felts over the board's code columns. -/
def packBoard (b : Board) (n : Nat) : List ℤ := packCells (boardCode b n) (feltCount n)

/-- **`packBoard_injective` — the seam corollary.** Two boards with equal packed felt-tuples agree
cell-wise at every in-bounds coordinate. Under Option A (packed felts bound directly to PIs), Leg A's
and Leg R's boards binding the SAME packed felts is exactly this hypothesis, so the whole-turn seam
"the two decoded boards agree cell-wise" becomes a discharged theorem, not a named assumption. -/
theorem packBoard_injective (n : Nat) (b1 b2 : Board)
    (heq : packBoard b1 n = packBoard b2 n) :
    ∀ x y : Nat, x < n → y < n → b1.cellAt ⟨x, y⟩ = b2.cellAt ⟨x, y⟩ := by
  unfold packBoard at heq
  have hcodes := pack_injective (boardCode b1 n) (boardCode b2 n) (feltCount n)
    (fun i _ => boardCode_mem b1 n i) (fun i _ => boardCode_mem b2 n i) heq
  intro x y hx hy
  have hlt : y * n + x < n * n :=
    calc y * n + x < y * n + n := by omega
      _ = (y + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  have hidx : y * n + x < 15 * feltCount n := lt_of_lt_of_le hlt (sq_le_feltCount n)
  have hc := hcodes (y * n + x) hidx
  rw [boardCode_inbounds b1 n x y hx hy, boardCode_inbounds b2 n x y hx hy] at hc
  exact particleCode_inj hc

/-! ## §6 — The emitted family (LEAN-AUTHORED AIR).

Minimal degree-1 gate combinators (the `AutomataflStepEmit` / `DyckStackEmit` `.gate`/`EmittedExpr`
style, replicated locally so this leaf is self-contained and does not import the 120 KB step golden).
The pack gate uses only linear terms ⇒ degree 1; the commitment is a `piBinding` (boundary), not a
polynomial gate at all. -/

/-- One linear term `coeff·col` (`coeff = 1` elides the multiplier). -/
def varTerm : ℤ × Nat → EmittedExpr
  | (c, col) => if c == 1 then .var col else .mul (.const c) (.var col)

/-- Left-folded sum of gate terms (empty ↦ `0`). -/
def sumExpr : List EmittedExpr → EmittedExpr
  | []       => .const 0
  | e :: rest => rest.foldl (fun acc x => .add acc x) e

/-- A degree-1 gate `Σ coeffᵢ·colᵢ + k = 0` (zero-coeff terms dropped, matching `headToExpr`). -/
def linGate (terms : List (ℤ × Nat)) (k : ℤ) : VmConstraint2 :=
  let ts := (terms.filter (fun t => t.1 != 0)).map varTerm
  let ts := if k == 0 then ts else ts ++ [.const k]
  .base (.gate (sumExpr ts))

/-- The product `∏ vars` (empty ↦ `1`), left-associated — the local mirror of
`AutomataflStepEmit.varsProd`, so this leaf can author a degree-`k` term without importing the step
golden. -/
def varsProd : List Nat → EmittedExpr
  | []          => .const 1
  | co :: rest  => rest.foldl (fun acc v => .mul acc (.var v)) (.var co)

/-- One gate term `coeff · ∏ cols` (`coeff = 1` elides the multiplier; `cols = []` is a constant). -/
def prodTerm : ℤ × List Nat → EmittedExpr
  | (c, [])         => .const c
  | (c, co :: rest) =>
      if c == 1 then varsProd (co :: rest) else .mul (.const c) (varsProd (co :: rest))

/-- A gate `Σ coeffᵢ·∏colsᵢ + k = 0` of degree `max |colsᵢ|` (zero-coeff terms dropped, matching
`headToExpr`). `linGate` is the all-singleton special case. -/
def prodGate (terms : List (ℤ × List Nat)) (k : ℤ) : VmConstraint2 :=
  let ts := (terms.filter (fun t => t.1 != 0)).map prodTerm
  let ts := if k == 0 then ts else ts ++ [.const k]
  .base (.gate (sumExpr ts))

/-- `∏_{s∈set}(col − s)` — the alphabet membership gate (`assert_member`). -/
def memberExpr (col : Nat) (set : List ℤ) : EmittedExpr :=
  match set with
  | []        => .const 1
  | s :: rest => rest.foldl (fun acc t => .mul acc (.add (.var col) (.const (-t))))
                   (.add (.var col) (.const (-s)))

/-! ### §6.1 — Standalone column layout (the working `n²`-cell rep, then the packed felts). -/

/-- Board cell column `i` (the working representation stays 1 felt / cell, `AutomataflStepEmit.old i`). -/
def PACK_CELL (i : Nat) : Nat := i
/-- The packed felts are allocated right after the `n²` cell columns. -/
def PACK_FELT_BASE (n : Nat) : Nat := n * n
/-- Packed-felt column `j`. -/
def PACK_FELT (n j : Nat) : Nat := PACK_FELT_BASE n + j
/-- Public-input base for the packed board felts (`[16 …)`, mirroring `bind_board_roots`' `[16..24)`). -/
def COMMIT_PI_BASE : Nat := 16

/-- The board-cell alphabet range checks (`assert_member(cell, {0,1,2,3})` per cell) — what makes the
`{0,1,2,3}` precondition of `pack_injective` DERIVABLE from the descriptor rather than assumed. -/
def boardRangeCells (n : Nat) : List VmConstraint2 :=
  (List.range (n * n)).map (fun c => (.base (.gate (memberExpr (PACK_CELL c) [0, 1, 2, 3])) : VmConstraint2))

/-! ### §6.1b — THE RE-POINTED FAMILY: the same gates at ARBITRARY cell / felt column bases.

A host descriptor (Leg A / Leg R) carries SEVERAL boards in one row — `old` at one base, `new`/`mid`
at another — so the commitment family has to be emitted once per board at that board's own column
base, and bound to its own PI window. `cellCol` / `feltCol` / `piBase` are exactly those three
degrees of freedom; the standalone `§6.1` family is the instance at `PACK_CELL` / `PACK_FELT n` /
`COMMIT_PI_BASE`. Re-pointing is a PURE RE-INDEX: nothing about the base-4 pack, the alphabet
precondition or the injectivity argument mentions where the cells live. -/

/-- The linear terms of pack gate `j` at an arbitrary cell base:
`felt_j − Σ_{i, 15j+i < n²} 4^i·cell[15j+i]`. Padding cells (`15j+i ≥ n²`) contribute `0` — matching
`boardCode`'s pad convention. -/
def packTermsAt (n j : Nat) (cellCol : Nat → Nat) (feltCol : Nat → Nat) : List (ℤ × Nat) :=
  (1, feltCol j) :: ((List.range 15).filterMap (fun i =>
    let idx := 15 * j + i
    if idx < n * n then some (-(4 : ℤ) ^ i, cellCol idx) else none))

/-- The `⌈n²/15⌉` degree-1 pack gates over the board at `cellCol`, packing into `feltCol`. -/
def packBoardConstraintsAt (n : Nat) (cellCol feltCol : Nat → Nat) : List VmConstraint2 :=
  (List.range (feltCount n)).map (fun j => linGate (packTermsAt n j cellCol feltCol) 0)

/-- Bind the `⌈n²/15⌉` packed felts at `feltCol` to the PI window `[piBase, piBase + ⌈n²/15⌉)`. -/
def commitBoardConstraintsAt (n : Nat) (feltCol : Nat → Nat) (piBase : Nat) : List VmConstraint2 :=
  (List.range (feltCount n)).map (fun j =>
    (.base (.piBinding VmRow.first (feltCol j) (piBase + j)) : VmConstraint2))

/-- The AUTOMATON-COORDINATE half of the commitment: the two witnessed coordinate columns bound to
`PI[piBase]` / `PI[piBase+1]`. The packed felts commit the CELLS; a `Board` also carries the
automaton coordinate, and cell-agreement alone cannot recover it (nothing in the gate set forbids a
second `AUTO`-coded cell), so the coordinate is published too. Two `.piBinding`s, no gate. -/
def autoCoordCommitConstraints (axCol ayCol piBase : Nat) : List VmConstraint2 :=
  [ (.base (.piBinding VmRow.first axCol piBase) : VmConstraint2)
  , (.base (.piBinding VmRow.first ayCol (piBase + 1)) : VmConstraint2) ]

/-- The NEW-AUTOMATON-COORDINATE half of the commitment (Leg A only): two fresh columns
`nax`/`nay` pinned by the DEGREE-2 gates `nax − ax − m·ox == 0`, `nay − ay − m·oy == 0` over the
EXISTING auto-coordinate columns `ax`/`ay`, the chosen-offset columns `ox`/`oy`, and the MOVE MASK
column `m` (`m = offnz·tib·targ_vac`, the boolean the step block already computes), then bound to
`PI[piBase]`/`PI[piBase+1]`.

THE MASK IS LOAD-BEARING, not decoration. The reference `automatonStep` moves the automaton ONLY when
its guard fires: `automaton = if m = 1 then (ax+ox, ay+oy) else (ax, ay)`. The earlier degree-1 pin
`nax = ax + ox` agrees with that on ONE branch of the `if`, so the strongest transport statable over
it was the COLUMN-level `PI = ax + ox`; lifting that to the SEMANTIC `PI = (automatonStepCfg …)
.automaton` would need a reachability lemma about the reference (that a nonzero sensed offset always
targets an in-bounds vacuum cell), which nothing in the descriptor or the capstone has. `m·ox`
collapses to `0` exactly on the `m = 0` branch, so the mask pin discharges the case split AT THE GATE
and `AutomataflTurnCapstone.astep_newAuto_pi_of_sat` proves the full-semantics statement outright.
Degree 2, well inside the degree-7 budget; two gates + two boundary `.piBinding`s, no crypto.

SCOPE, HONESTLY: that reachability lemma is in fact TRUE of the reference (every `evaluate_axis` arm
yielding a nonzero offset carries a `dist > 1` guard, or picks the farther of two repulsors — pinned
by `dregg-automatafl/src/witness.rs::a_nonzero_sensed_offset_always_targets_an_in_bounds_vacuum_cell`
over the sensing configurations that decide it). So the degree-1 pin was not refusing REACHABLE
honest trajectories; what it could not do was carry the guarantee the fold seam quotes. -/
def newAutoCoordCommitConstraints (axCol oxCol ayCol oyCol mCol naxCol nayCol piBase : Nat) :
    List VmConstraint2 :=
  [ prodGate [(1, [naxCol]), (-1, [axCol]), (-1, [mCol, oxCol])] 0
  , prodGate [(1, [nayCol]), (-1, [ayCol]), (-1, [mCol, oyCol])] 0
  , (.base (.piBinding VmRow.first naxCol piBase) : VmConstraint2)
  , (.base (.piBinding VmRow.first nayCol (piBase + 1)) : VmConstraint2) ]

/-- The linear terms of pack gate `j`: `packed_j − Σ_{i, 15j+i < n²} 4^i·cell[15j+i]`. Padding cells
(`15j+i ≥ n²`) contribute `0` — matching `boardCode`'s pad convention. -/
def packTerms (n j : Nat) : List (ℤ × Nat) := packTermsAt n j PACK_CELL (PACK_FELT n)

/-- **`packBoardConstraints n`** — the `⌈n²/15⌉` degree-1 pack gates `packed_j − Σ 4^i·cell = 0`. -/
def packBoardConstraints (n : Nat) : List VmConstraint2 :=
  packBoardConstraintsAt n PACK_CELL (PACK_FELT n)

/-- **`commitBoardConstraints n` — Option A (recommended).** Bind each packed felt DIRECTLY to a PI
(`[16 …)`). No hash, no root columns, no crypto assumption: the packed felts ARE the (injective,
degree-1) board commitment, and root-injectivity is the `pack_injective` theorem. -/
def commitBoardConstraints (n : Nat) : List VmConstraint2 :=
  commitBoardConstraintsAt n (PACK_FELT n) COMMIT_PI_BASE

/-- **Option B — single hash-to-8-lanes (adapter, NOT primary).** One arity-16 Poseidon2 over the
`⌈n²/15⌉ ≤ 16` packed felts (padded to `CHIP_RATE`), output 8 lanes — the fixed-width digest the door
layer speaks, at the cost of one collision-resistance assumption (still NO Merkle tree). Use only
where a downstream layer demands a fixed 8-felt board digest; Option A is the standalone default. -/
def commitBoardHashLookup (n : Nat) (outCols : List Nat) : VmConstraint2 :=
  .lookup { table := TableId.poseidon2
          , tuple := chipLookupTupleN
              ((List.range (feltCount n)).map (fun j => EmittedExpr.var (PACK_FELT n j))) outCols }

/-- **`automataflCommitDesc n` — the standalone Option-A commitment descriptor**: `n²` cell columns
+ `⌈n²/15⌉` packed felts; constraints = alphabet range checks · pack gates · packed-felt PI bindings.
Author-in-Lean AIR; not yet byte-pinned (the disk golden lands with the `descN` wiring). -/
def automataflCommitDesc (n : Nat) : EffectVmDescriptor2 :=
  { name        := "dregg-automatafl-commit-optA"
  , traceWidth  := PACK_FELT_BASE n + feltCount n
  , piCount     := COMMIT_PI_BASE + feltCount n
  , tables      := []
  , constraints := boardRangeCells n ++ packBoardConstraints n ++ commitBoardConstraints n
  , hashSites   := []
  , ranges      := [] }

/-! ## §7 — Non-vacuity witnesses (`#guard`): the pack is REAL and computed correctly. -/

/-- Concrete `n = 2` code column `[REP, ATT, AUTO, VAC] = [1,2,3,0]` (pad `0`). `packed_0 = 1+8+48 = 57`. -/
def demoCells2 : Nat → ℤ := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else 0
/-- Same board with cell 2 flipped `AUTO→REP`; `packed_0 = 1+8+16 = 25 ≠ 57`. -/
def demoCells2' : Nat → ℤ := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 1 else 0
/-- Concrete `n = 11` code column: `cell i = i mod 4` (all four codes exercised across `9` felts). -/
def demoCells11 : Nat → ℤ := fun i => ((i % 4 : Nat) : ℤ)

-- n = 2: exactly one felt, computed correctly.
#guard feltCount 2 = 1
#guard packCells demoCells2 (feltCount 2) = [57]
-- non-vacuity of pack_injective: ONE differing cell ⇒ DIFFERENT packed tuple.
#guard packCells demoCells2 (feltCount 2) ≠ packCells demoCells2' (feltCount 2)

-- n = 11: exactly nine felts; felt 0 (cells 0..14) and felt 8 (cells 120..134) read the right slices.
#guard feltCount 11 = 9
#guard (packCells demoCells11 (feltCount 11)).length = 9
#guard packCell demoCells11 0 = horner4 [0,1,2,3,0,1,2,3,0,1,2,3,0,1,2]
#guard packCell demoCells11 8 = horner4 [0,1,2,3,0,1,2,3,0,1,2,3,0,1,2]
#guard packCell demoCells11 0 = 618980580

/-- `demoCells11` with the LAST cell of an 11×11 board (linear index `120`) flipped `VAC → REP`. -/
def demoCells11' : Nat → ℤ := fun i => if i = 120 then 1 else demoCells11 i
-- THE CANARY FOR THIS WHOLE RUNG: a change to cell 120 CHANGES the commitment. The retired
-- `board_root8` leaf absorbed cells `[0..8)` only, so it was BLIND to this flip — two different
-- 11×11 boards shared one committed root. The pack separates them (felt 8 differs).
#guard packCells demoCells11 (feltCount 11) ≠ packCells demoCells11' (feltCount 11)
#guard packCell demoCells11 8 ≠ packCell demoCells11' 8
-- and the felts BELOW the change are untouched — the difference is localized, not a hash smear.
#guard packCell demoCells11 0 = packCell demoCells11' 0

-- The reference `Board` pack agrees with the code pack, and separates a one-cell change.
/-- `n=2` board: REP@(0,0), ATT@(1,0), AUTO@(0,1), VAC@(1,1) ⇒ codes `[1,2,3,0]`, `packed_0 = 57`. -/
def demoBoard2 : Board := mkBoard 2 [(⟨0, 0⟩, .repulsor), (⟨1, 0⟩, .attractor)] ⟨0, 1⟩
/-- Same, but (1,0) is REP not ATT ⇒ codes `[1,1,3,0]`, `packed_0 = 1+4+48 = 53`. -/
def demoBoard2' : Board := mkBoard 2 [(⟨0, 0⟩, .repulsor), (⟨1, 0⟩, .repulsor)] ⟨0, 1⟩

#guard packBoard demoBoard2 2 = [57]
#guard packBoard demoBoard2 2 ≠ packBoard demoBoard2' 2

-- The emitted family: shape at n = 2 (1 felt) and n = 11 (9 felts).
#guard (packBoardConstraints 2).length = 1
#guard (packBoardConstraints 11).length = 9
#guard (commitBoardConstraints 2).length = 1
#guard (commitBoardConstraints 11).length = 9
-- the NEW-auto family: two mask-pin gates + two piBindings, at any column/pi assignment.
#guard (newAutoCoordCommitConstraints 8 207 9 208 247 254 255 20).length = 4
-- THE PIN IS DEGREE 2 (`m·ox`), not degree 1: the emitted gate body carries a var·var product.
-- `rfl` here is the real check — the body below is the literal `EmittedExpr` the wire carries.
example :
    (newAutoCoordCommitConstraints 8 207 9 208 247 254 255 20).head?
      = some (.base (.gate (.add (.add (.var 254) (.mul (.const (-1)) (.var 8)))
          (.mul (.const (-1)) (.mul (.var 247) (.var 207)))))) := rfl
example :
    (newAutoCoordCommitConstraints 8 207 9 208 247 254 255 20).tail.head?
      = some (.base (.gate (.add (.add (.var 255) (.mul (.const (-1)) (.var 9)))
          (.mul (.const (-1)) (.mul (.var 247) (.var 208)))))) := rfl
#guard (boardRangeCells 11).length = 121
#guard (automataflCommitDesc 11).traceWidth = 130          -- 121 cells + 9 felts
#guard (automataflCommitDesc 11).piCount = 25              -- 16 state prefix + 9 packed felts
#guard (automataflCommitDesc 11).constraints.length = 139  -- 121 range + 9 pack + 9 commit

/-! ## §8 — Axiom hygiene: the pack theorems rest only on the kernel triple. -/

#assert_axioms horner4_inj
#assert_axioms pack_injective
#assert_axioms packCell_inj
#assert_axioms pack_injective_modp
#assert_axioms packCell_nonneg
#assert_axioms sq_le_feltCount
#assert_axioms particleCode_inj
#assert_axioms packBoard_injective

end Dregg2.Circuit.Emit.AutomataflCommit
