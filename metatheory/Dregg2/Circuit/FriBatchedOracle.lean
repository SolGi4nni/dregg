/-
# `Dregg2.Circuit.FriBatchedOracle` — the deployed BATCHED MULTI-COLUMN FRI commitment,
as ONE reusable oracle shape (the L5 shared rung).

## What this module is

The FRI ladder's decode rungs (`DeployedTraceExtract` §3′, and R4a/R4b downstream) were typed
against a SINGLE-COLUMN oracle `Fin 16 → BabyBear`. The deployed plonky3 FRI does not commit a
single column: it commits a BATCHED MULTI-COLUMN LDE MATRIX — rows = the evaluation domain,
columns = the committed trace/poly columns — and each query opens ONE ROW of it (ALL columns at
the sampled row) through a single Merkle path. This module is that shape, defined ONCE:

  * `MatrixOracle ι c F` — the committed matrix: a word of `c`-column ROWS over the domain `ι`.
  * `row` — what ONE deployed query opening yields: all `c` columns at the opened row.
  * `col` — the per-column word the proximity/decoding math consumes.
  * `ofWord`/`toWord` — the single-column case IS the `c = 1` special case (round-trip proved),
    so nothing typed against the old single-column oracle regresses.
  * `RowAccepts` — sampled per-ROW agreement, and `rowAccepts_iff_col_accepts`: agreeing on a
    whole opened row ⟺ agreeing at that row in EVERY column. This is the Lean content of "one
    Merkle path opens all columns": a row sample carries every column's sample simultaneously,
    at the same positions.
  * `ColsClose` — every column `d`-close to the code (the multi-column proximity input the
    positive-radius trace decode consumes: EACH committed column must decode).

## The deployed shape this matches (cite the Rust, pinned rev `82cfad73`)

  * `p3_commit::BatchOpening`
    (`~/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/commit/src/mmcs.rs:163-169`):
    `opened_values: Vec<Vec<T>>` — "The opened row values from each matrix in the batch" — plus
    ONE `opening_proof`. A query's input opening is rows-of-all-columns, not a scalar.
  * `p3_fri::verifier::open_input`
    (`…/82cfad7/fri/src/verifier.rs:524`, check at `:590-597`): a SINGLE
    `input_mmcs.verify_batch(batch_commit, batch_dims, reduced_index, batch_opening)` verifies
    every matrix's opened row at the query's reduced row index — one Merkle path per batch
    commitment, all columns bound at once.
  * The in-tree deployed verifier model already carries the row shape:
    `FriVerifier.LayerOpening.leaf : List F` (`Dregg2/Circuit/FriVerifier.lean:277`) is the
    opened ROW, and `friQueryCheck` (`FriVerifier.lean:337-346`) Merkle-verifies that whole row
    against `traceCommit`.
  * Mirrored again by the recursion circuit:
    `~/dev/plonky3-recursion/recursion/src/pcs/fri/targets.rs:304-310`
    (`BatchOpeningTargets.opened_values: Vec<Vec<Target>>`).

`numCols` is a PARAMETER, not a constant: each matrix in the deployed batch has its own width
(e.g. the Poseidon2 wrap trace is 358 columns — `circuit/src/plonky3_prover.rs:257-260`), and
the batch flattens to one row-opened matrix per commitment. `c = 0` is degenerate but harmless
in the hypothesis-structure direction (an empty matrix gives a VACUOUS `ColsClose`, which makes
any decode field consuming it STRICTLY HARDER to supply, never easier).

## What is deliberately NOT here

Random-linear-combination (RLC) batching. The deployed verifier reduces the opened rows to one
fold-input word via `ro += alpha_pow * (p_at_z - p_at_x) / (z - x)`
(`…/82cfad7/fri/src/verifier.rs:620-640`) — that is the FRI FOLD's input reduction, a SEPARATE
concern (its soundness is the BCIKS correlated-agreement step). The COMMITMENT the oracle
models is the raw multi-column matrix the verifier Merkle-opens; consumers that need the RLC
word must name that reduction as its own seam, not smuggle it into the commitment type.

## Discipline

Sorry-free; no `axiom`; no carrier. `#assert_all_clean` ⊆ `{propext, Classical.choice,
Quot.sound}`. ADDITIVE: imports read-only.
-/
import Dregg2.Circuit.FriQuerySoundness
import Dregg2.Tactics

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriBatchedOracle

open Dregg2.Circuit.FriSoundness (closeN closeN_zero_iff_mem disagree disagree_eq_empty_iff)
open Dregg2.Circuit.FriQuerySoundness (Accepts)

/-- **The batched multi-column FRI commitment oracle** — the deployed committed object: a matrix
with rows over the evaluation domain `ι` and `c` committed columns
(`p3_commit::BatchOpening.opened_values : Vec<Vec<T>>`, one row per query opening). `M x` is the
full row at domain point `x` — exactly what one Merkle path opens. -/
def MatrixOracle (ι : Type*) (c : ℕ) (F : Type*) : Type _ := ι → Fin c → F

namespace MatrixOracle

variable {ι F : Type*} {c : ℕ}

/-- The opened ROW at domain point `x`: all `c` columns at once — the deployed per-query
opening unit (one Merkle path yields this whole vector). -/
def row (M : MatrixOracle ι c F) (x : ι) : Fin c → F := M x

/-- The `j`-th committed COLUMN, as the single word over the domain that the proximity and
decoding math consumes. -/
def col (M : MatrixOracle ι c F) (j : Fin c) : ι → F := fun x => M x j

/-- A single-column word, read as the `c = 1` matrix — the OLD single-column oracle is this
special case. -/
def ofWord (f : ι → F) : MatrixOracle ι 1 F := fun x _ => f x

/-- The single word of a one-column matrix. -/
def toWord (M : MatrixOracle ι 1 F) : ι → F := fun x => M x 0

@[simp] theorem col_ofWord (f : ι → F) (j : Fin 1) : (ofWord f).col j = f := rfl

@[simp] theorem toWord_ofWord (f : ι → F) : toWord (ofWord f) = f := rfl

@[simp] theorem col_zero_eq_toWord (M : MatrixOracle ι 1 F) : M.col 0 = M.toWord := rfl

/-- The `c = 1` round trip is the identity: single-column words and one-column matrices are the
SAME data — the bridge that guarantees the retype regresses nothing. -/
theorem ofWord_toWord (M : MatrixOracle ι 1 F) : ofWord M.toWord = M := by
  funext x j
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  rfl

@[simp] theorem row_ofWord (f : ι → F) (x : ι) (j : Fin 1) : (ofWord f).row x j = f x := rfl

/-! ## Sampled per-ROW agreement — "one Merkle path opens ALL columns". -/

/-- **Per-ROW sampled acceptance**: at every sampled position the FULL opened row of `M` agrees
with the claimed matrix `N` — the batched analogue of `FriQuerySoundness.Accepts`, faithful to
the deployed opening unit (`open_input` verifies whole rows, never lone cells). -/
def RowAccepts (M N : MatrixOracle ι c F) {k : ℕ} (Q : Fin k → ι) : Prop :=
  ∀ q, M.row (Q q) = N.row (Q q)

/-- **The batched-opening content, as an iff**: a sample accepts per-ROW exactly when EVERY
column's word accepts the same sample. One Merkle path per row means every column is spot-checked
at the SAME positions — column samples are never independent draws. -/
theorem rowAccepts_iff_col_accepts (M N : MatrixOracle ι c F) {k : ℕ} (Q : Fin k → ι) :
    RowAccepts M N Q ↔ ∀ j, Accepts (M.col j) (N.col j) Q := by
  constructor
  · intro h j q
    exact congrFun (h q) j
  · intro h q
    funext j
    exact h j q

/-! ## Multi-column proximity — every committed column close to the code. -/

section Close

variable [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- **Multi-column closeness**: EVERY committed column is `d`-close to the code `C`. This is the
proximity input the multi-column trace decode consumes — each committed column must decode to a
low-degree word (a trace column), so closeness of one designated column is NOT enough. -/
def ColsClose (C : Submodule F (ι → F)) (d : ℕ) (M : MatrixOracle ι c F) : Prop :=
  ∀ j, closeN C d (M.col j)

/-- At `c = 1` the multi-column closeness IS the single-word closeness (the bridge, decode
side): nothing typed against the old `closeN … oracle` shape regresses. -/
theorem colsClose_ofWord_iff (C : Submodule F (ι → F)) (d : ℕ) (f : ι → F) :
    ColsClose C d (ofWord f) ↔ closeN C d f := by
  constructor
  · intro h
    exact h 0
  · intro h j
    exact h

/-- `c = 1`, stated on the matrix side. -/
theorem colsClose_one_iff (C : Submodule F (ι → F)) (d : ℕ) (M : MatrixOracle ι 1 F) :
    ColsClose C d M ↔ closeN C d M.toWord := by
  constructor
  · intro h
    exact h 0
  · intro h j
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    exact h

/-- Every column a genuine codeword ⟹ every column `d`-close, at ANY radius `d` (`0`-closeness
weakened): the wire from per-column MEMBERSHIP (the full-cover idealization's conclusion) into a
positive-radius decode input. -/
theorem colsClose_of_forall_mem {C : Submodule F (ι → F)} {M : MatrixOracle ι c F}
    (hmem : ∀ j, M.col j ∈ C) (d : ℕ) : ColsClose C d M := by
  intro j
  obtain ⟨g, hgC, hcard⟩ := closeN_zero_iff_mem.mpr (hmem j)
  exact ⟨g, hgC, le_trans hcard (Nat.zero_le d)⟩

end Close

/-! ## Teeth — the shape is not degenerate. -/

/-- Distinct columns are genuinely DISTINCT words: `col` does not collapse the matrix (a
two-column ℚ-matrix with different columns). The multi-column retype carries strictly more data
than any single word. -/
theorem cols_genuinely_distinct :
    ∃ M : MatrixOracle (Fin 2) 2 ℚ, M.col 0 ≠ M.col 1 := by
  refine ⟨fun _ j => if j = 0 then 0 else 1, fun h => ?_⟩
  have h0 := congrFun h 0
  simp [col] at h0

/-- A full-row agreement fails when ANY single column disagrees at the sampled row — per-row
acceptance genuinely constrains every column (the batched opening cannot hide one bad column
behind good ones). -/
theorem rowAccepts_bites :
    ∃ (M N : MatrixOracle (Fin 2) 2 ℚ) (Q : Fin 1 → Fin 2),
      Accepts (M.col 0) (N.col 0) Q ∧ ¬ RowAccepts M N Q := by
  refine ⟨fun _ j => if j = 0 then 0 else 1, fun _ _ => 0, fun _ => 0, fun q => rfl, fun h => ?_⟩
  have h1 := congrFun (h 0) 1
  simp [row] at h1

#assert_all_clean [
  col_ofWord,
  toWord_ofWord,
  col_zero_eq_toWord,
  ofWord_toWord,
  row_ofWord,
  rowAccepts_iff_col_accepts,
  colsClose_ofWord_iff,
  colsClose_one_iff,
  colsClose_of_forall_mem,
  cols_genuinely_distinct,
  rowAccepts_bites
]

end MatrixOracle

end Dregg2.Circuit.FriBatchedOracle
