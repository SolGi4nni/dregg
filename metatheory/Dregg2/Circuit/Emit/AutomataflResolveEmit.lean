/-
# Dregg2.Circuit.Emit.AutomataflResolveEmit — the EMIT-FROM-LEAN author of the automatafl m=2
move-adjudication (Leg R, `old → mid`) descriptor (`dregg-automatafl-resolve-n2`).

## What this file IS, and the law it closes

Law #1: ZERO Rust-authored constraints. The automatafl RESOLUTION AIR (`old → mid`, the OTHER half
of the turn from `AutomataflStepEmit`'s automaton step `mid → new`) was authored in RUST
(`dregg-automatafl/src/moves.rs`, `emit_resolution` / `build_r`) with NO Lean emit. This file is the
Lean author that moves it off Rust: the Leg R constraints are authored here as IR-v2 `VmConstraint2`
nodes, byte-pinned by an `emitVmJson2` `#guard`, on the same template `AutomataflStepEmit.lean` used
for the step half.

The SEMANTIC target this descriptor refines (Stage 2, NOT in this file) is
`Dregg2.Games.Automatafl.resolve_mid` / `applyMoves` / `conflictResolve` — the m=2 reference
resolution. This file is Stage 1: the descriptor STRUCTURE + byte-pin.

## SCOPE — COMPLETE. All eight `emit_resolution` legs are authored here.

`emit_resolution` (moves.rs) emits, IN ORDER — every leg now Lean-authored:

  1. `validate_move(ma)` + `validate_move(mb)`  — THE VALIDITY GATES               §4
  2. `validate_occlusion(ma)` + `validate_occlusion(mb)`  — the masked line scans  §4.5
  3. `anz`/`bnz` source-non-vacuum bits                                            §4.6 leg 3
  4. the 4 `eq_coords` pattern bits + fork/collide/survive selection               §4.6 leg 4
  5. `carry_a`/`carry_b` (survive ∧ non-vac ∧ ¬occ)                                 §4.6 leg 5
  6. the `ft_a`/`ft_b` vacuum flow-through chain-endpoint destinations             §4.6 leg 6
  7. `write_mid_witnessed` — the one-hot board rewrite `mid == resolve_mid(old,..)` §4.6 leg 7
  8. the PACKED BOARD COMMITMENT — the base-4 pack gates + PI tail                  §4.6 leg 8

The descriptor is therefore CLOSED: it does not merely gate the two moves for validity, it FORCES
the resolved board. `write_mid_witnessed` equates every `mid` cell to the one-hot rewrite of `old`
at the witnessed source and (flow-through-interpolated) destination indices, and the PACKED BOARD
COMMITMENT publishes `pack(old)` and `pack(mid)` as CONSTRAINED public inputs — so the leaf
commits to precisely the boards it adjudicated, and Leg A's `mid8` seam has something to weld to.

## The WITNESSED discipline — two compile-time bakes converted, and the audit for the rest

This is NOT a transcription of the Rust. moves.rs specialises two gadgets on compile-time values,
each faithful for exactly ONE board / ONE move shape; both are replaced here by WITNESSED, pinned
columns:

  * **the automaton position.** moves.rs bakes `let (ax, ay) = old.auto` into the NOT-AUTO gates.
    §2.0 replaces it with an `ax`/`ay` row×column one-hot pinned where `old == AUTO`, so the gates
    range over wherever the automaton actually sits.
  * **the move direction.** moves.rs branches on `let is_vertical = m.frm.0 == m.to.0`, which
    selects the line scan, the endpoint one-hots, and the passable comparison. §2.2 replaces it
    with a witnessed `iv` bit pinned by an `eq_scalar` over the move's OWN coordinates, emits BOTH
    branches, and gates the SELECTION — covering any rook move.

Legs 3–8 were audited for the same class and need no conversion: their remaining compile-time reads
(`old.cell_at(ma.frm)`, `eq_coords`' `axv/ayv/bxv/byv`, `Placement.src_x_hot`, `dest_a_x_hot`, …)
are `Builder::alloc` WITNESS VALUES and one-hot hot-indices — the honest assignment — never
coefficients in an emitted head. Every leg-3–8 gate is already a polynomial in witnessed columns
(`fxa`, `txb`, `ft_a`, `carry_a`, …). See §2.3.

`validate_move` (per move) is:
  * `decompose_coord_le` on each of `fx/fy/tx/ty` — the `0 ≤ coord ≤ n−1` range, at `n=2` a
    `rbits = 1` bit-decomposition per edge (lower `coord = b_lo`, upper `(n−1) − coord = b_hi`);
  * the ROOK-ALIGN gate `(fx−tx)(fy−ty) == 0`;
  * DISTINCTNESS `(fx−tx)² + (fy−ty)² ≠ 0` (a witnessed squared distance `dsq` + a `cond_nonzero`);
  * NOT-THE-AUTOMATON `frm ≠ auto`, `to ≠ auto` (auto-relative squared distances `fa`/`ta` gated
    against the WITNESSED auto position + `cond_nonzero`s);
  * the WITNESSED SOURCE READ `fp == old[n·fy + fx]` through a row×column one-hot pinned to `(fx,fy)`
    (2n selectors), so the source particle is bound to the coordinates the move claims.

## The board size and the automaton position — n = 2, auto WITNESSED from the board

Mirroring `AutomataflStepEmit`, this authors the minimal complete instance `n = 2` (`k = n² = 4`
cells). The NOT-AUTO gate reads the auto position from the OLD board via a WITNESSED `ax`/`ay`
row×column one-hot pinned where `old == AUTO` (a shared 10-column block, `autoReadConstraints`,
`§2.0`), exactly like the step gadget's auto pin — NOT the compile-time `old.auto` constant moves.rs
bakes (`let (ax, ay) = old.auto`). The auto MOVES each turn, so a baked constant is faithful for only
one board; the `fa`/`ta` gates expand `(fx−ax)² + (fy−ay)²` / `(tx−ax)² + (ty−ay)²` over the
witnessed `(ax, ay)` columns (`autoDistHead`), gating the move against wherever the automaton
actually sits. This is a deliberate FAITHFULNESS UPGRADE over the Rust spec (which this Lean author
supersedes; Rust is the debt). Zero-coefficient terms are dropped exactly as `AutomataflStepEmit`'s
`headToExpr` canonicalizes (Lean is the source of truth for the emitted form).

## The public-input ABI (Leg R, moves.rs `build_r_bound`)

```text
  [ 0.. 8)  old8   the CELL's pre-state root  (add_pi'd, opaque, fold-connected)
  [ 8..16)  mid8   the CELL's post-state root (== Leg A's old8 — the seam)
  [16, 16+fc)      old_pack   CONSTRAINED pack(old), fc = ceil(n^2/15)  ]  emitted by the packed
  [16+fc, 16+2fc)  mid_pack   CONSTRAINED pack(mid)                     ]  commitment, leg 8
  [16+2fc], [+1]   auto x, y  CONSTRAINED (AX_C, AY_C)                  ]
```

The door prefix `[0..16)` rides 16 bare `add_pi`s, never constrained in `build_r` — faithful to
their opaque, fold-connected treatment. The board-root tail `[16..32)` is CONSTRAINED: leg 8 emits
the base-4 pack gates over the actual board columns and `bind_pi`s their
output lanes each, so a forged root has no satisfying witness. `piCount = 32`.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its full wire string + shape `#guard`s. NEW
file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.AutomataflCommit

namespace Dregg2.Circuit.Emit.AutomataflResolveEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTupleN emitVmJson2)

set_option autoImplicit false

/-! ## §1 — Constants (`reference.rs`). The board is `n×n`; the auto is a compile-time coord. -/

/-- The board dimension. EVERY gadget family and EVERY column offset below is a function of `NN`;
this file INSTANTIATES `n = 2` (the minimal complete instance, kept so the emitted artifact stays
byte-comparable with the pinned golden). Changing this single definition re-lays the whole trace:
the coordinate bit-widths (`COORD_RBITS`), the per-move block (`MV_BLOCK_WIDTH`), the occlusion
block (`OCC_BLOCK_WIDTH`), the adjudication base (`RES0`) and the total width (`R_WIDTH`) all move
with it. -/
def NN : Nat := 2
/-- `k = n²`, the number of board cells. -/
def KK : Nat := NN * NN

/-- `decompose_coord_le`'s bit width — `ceil(log2 n)`, the number of bits needed to hold a
coordinate in `[0, n)`. `1` at `n = 2`, `4` at `n = 11`. Both edges of the range decomposition
(`coord = Σ 2^k b_k` and `(n−1) − coord = Σ 2^k b'_k`) carry this many bits. -/
def COORD_RBITS : Nat := if NN ≤ 1 then 1 else Nat.log2 (NN - 1) + 1
/-- The automaton particle felt code (`reference.rs::AUTO`). The NOT-AUTO gates gate the move's
`frm`/`to` against the WITNESSED auto position — the cell where `old == AUTO`, read from the board
by a row×column one-hot (`autoReadConstraints`), exactly as `AutomataflStepEmit`'s auto pin — NOT a
compile-time-baked `old.auto` constant. The auto moves each turn, so a baked constant would only be
faithful for one board; the witnessed read gates against wherever the automaton actually sits. -/
def AUTO_CODE : ℤ := 3

/-! ## §2 — The column layout (the `build_r_bound` + `emit_resolution` `Builder::alloc` order).

Columns are allocated exactly in the Rust order so the emitted var indices mirror the gadget:
old cells `[0..k)`, mid cells `[k..2k)`, the `one` pin, then a fixed 23-column block per move. -/

/-- `old[i]` — cell `i` of the source board (columns `0..k`). All source reads are over this board. -/
def old (i : Nat) : Nat := i
/-- `mid[i]` — cell `i` of the claimed resolved board (columns `k..2k`). FORCED cell-by-cell by
`write_mid_witnessed` (leg 7) and committed by `pack(mid)` (leg 8). -/
def mid (i : Nat) : Nat := KK + i
/-- The `one` pin (a column forced to 1; the always-on `cond_nonzero` selector). -/
def ONE : Nat := 2 * KK

/-! ### §2.0 — The witnessed automaton-position read (the faithfulness fix).

The NOT-AUTO gates read the auto position from the OLD board rather than baking `old.auto`. A shared
10-column block (allocated once, after `one`, before the moves — the auto is a single board-global
position, so both moves' `fa`/`ta` gate against it) mirrors `AutomataflStepEmit`'s front-end auto
pin: `ax`/`ay` bit-decomposed to `0..n−1`, a row×column one-hot pinned to `(ax, ay)`, and the dot
product `AUTO == Σ selRow·selCol·old` forcing `(ax, ay)` to be the cell holding the automaton. -/

/-- The witnessed automaton x/y coordinate columns. -/
def AX_C : Nat := 2 * KK + 1
def AY_C : Nat := 2 * KK + 2
/-- `decompose_coord_le` bit runs for `ax` / `ay`, each `COORD_RBITS` wide, lower then upper edge
(at `n = 2`, `COORD_RBITS = 1`, so these are the single columns `2k+3 … 2k+6`). -/
def axLo : Nat := 2 * KK + 3
def axHi : Nat := 2 * KK + 3 + COORD_RBITS
def ayLo : Nat := 2 * KK + 3 + 2 * COORD_RBITS
def ayHi : Nat := 2 * KK + 3 + 3 * COORD_RBITS
/-- The auto ROW one-hot (pinned to `ay`) and COLUMN one-hot (pinned to `ax`), `n` selectors each. -/
def selAutoRow (y : Nat) : Nat := 2 * KK + 3 + 4 * COORD_RBITS + y
def selAutoCol (x : Nat) : Nat := 2 * KK + 3 + 4 * COORD_RBITS + NN + x
/-- Width of the shared auto-read block: `ax`/`ay` (2) + `4·COORD_RBITS` coord bits + `2n` one-hot
selectors. `6 + 2n` at `COORD_RBITS = 1`. -/
def AUTO_BLOCK_WIDTH : Nat := 2 + 4 * COORD_RBITS + 2 * NN

/-- Width of one `validate_move` block: 4 coordinate columns + `8·COORD_RBITS` range bits (two edges
on each of four coordinates) + `dsq`/`inv`/`fa`/`inv`/`ta`/`inv` (6) + the source particle (1) +
`2n` source one-hot selectors. `23` at `n = 2`. -/
def MV_BLOCK_WIDTH : Nat := 4 + 8 * COORD_RBITS + 6 + 1 + 2 * NN

/-- The first column of a move's `MV_BLOCK_WIDTH`-column `validate_move` block. Move A: base
`2k+1+autoBlock`; move B: that `+ MV_BLOCK_WIDTH`. (The auto-read block sits between `one` and the
moves.) -/
def mvBase (which : Nat) : Nat := 2 * KK + 1 + AUTO_BLOCK_WIDTH + MV_BLOCK_WIDTH * which

/-! ### §2.1 — The per-move column block, at base `b`. -/

/-- Witnessed move coordinates. -/
def cFx (b : Nat) : Nat := b + 0
def cFy (b : Nat) : Nat := b + 1
def cTx (b : Nat) : Nat := b + 2
def cTy (b : Nat) : Nat := b + 3
/-- `decompose_coord_le` bit runs (lower edge / upper edge) for each coordinate, `COORD_RBITS` wide
each, laid out `fx.lo fx.hi fy.lo fy.hi tx.lo tx.hi ty.lo ty.hi`. -/
def cFxLo (b : Nat) : Nat := b + 4
def cFxHi (b : Nat) : Nat := b + 4 + COORD_RBITS
def cFyLo (b : Nat) : Nat := b + 4 + 2 * COORD_RBITS
def cFyHi (b : Nat) : Nat := b + 4 + 3 * COORD_RBITS
def cTxLo (b : Nat) : Nat := b + 4 + 4 * COORD_RBITS
def cTxHi (b : Nat) : Nat := b + 4 + 5 * COORD_RBITS
def cTyLo (b : Nat) : Nat := b + 4 + 6 * COORD_RBITS
def cTyHi (b : Nat) : Nat := b + 4 + 7 * COORD_RBITS
/-- The first column after the coordinate range bits. -/
def mvPost (b : Nat) : Nat := b + 4 + 8 * COORD_RBITS
/-- Distinctness squared distance + its `cond_nonzero` witnessed inverse. -/
def cDsq (b : Nat) : Nat := mvPost b + 0
def cDistinctInv (b : Nat) : Nat := mvPost b + 1
/-- The `frm ≠ auto` squared distance + inverse. -/
def cFa (b : Nat) : Nat := mvPost b + 2
def cFnaInv (b : Nat) : Nat := mvPost b + 3
/-- The `to ≠ auto` squared distance + inverse. -/
def cTa (b : Nat) : Nat := mvPost b + 4
def cTnaInv (b : Nat) : Nat := mvPost b + 5
/-- The witnessed source particle `fp == old[n·fy + fx]`. -/
def cFp (b : Nat) : Nat := mvPost b + 6
/-- The source row / column one-hots (pinned to `fy` / `fx`), `n` selectors each. -/
def cSelRow (b j : Nat) : Nat := mvPost b + 7 + j
def cSelCol (b j : Nat) : Nat := mvPost b + 7 + NN + j
/-- The `n = 2` names, retained for the refinement's gate-membership fields. -/
def cSelRow0 (b : Nat) : Nat := cSelRow b 0
def cSelRow1 (b : Nat) : Nat := cSelRow b 1
def cSelCol0 (b : Nat) : Nat := cSelCol b 0
def cSelCol1 (b : Nat) : Nat := cSelCol b 1

/-! ### §2.2 — The per-move OCCLUSION block (leg 2), at base `o`.

`validate_occlusion` (moves.rs) branches on `let is_vertical = m.frm.0 == m.to.0` — a COMPILE-TIME
bool — and that branch selects (i) which line the extract pulls (column-scan vs row-scan), (ii)
which endpoint one-hots feed the between-mask, and (iii) which coordinate the other-source passable
gate compares. A move's direction VARIES per turn, so a compile-time-specialised occlusion is
faithful for exactly one move shape — the same bug class as the baked `old.auto` constant §2.0
fixes. This Lean author emits a WITNESSED `is_vertical` BIT instead:

  * `iv` is pinned to the ACTUAL geometry by the `eq_scalar` construction over the witnessed
    coordinate columns: `dxsq == (fx − tx)²`, `neq == [dxsq ≥ 1]` (a `forced_ge0` range gadget),
    `iv == 1 − neq`. So `iv = 1` IFF `fx == tx` — no prover choice. Together with `validate_move`'s
    rook-align gate `(fx−tx)(fy−ty) == 0`, `iv = 0` forces `fy == ty` (a horizontal move).
  * BOTH line-extracts are emitted into the SAME `line[k]` columns, each gated:
    `line[k] == iv·(column-scan) + (1−iv)·(row-scan)`.
  * BOTH along-axis endpoint one-hots are emitted (`ety` pinned to `ty`, `etx` pinned to `tx`) and
    the between-mask reads the GATED combination `eto[j] == iv·ety[j] + (1−iv)·etx[j]`; likewise
    `efrom[j] == iv·selRow[j] + (1−iv)·selCol[j]` over `validate_move`'s source one-hots. (Pinning
    both `e_to` one-hots unconditionally and gating the SELECTION is strictly stronger than gating
    the one-hots themselves: each stays a genuine one-hot of its real coordinate.)
  * BOTH passable-mask comparisons are emitted: `eqx == [other.fx == fx]`, `eqy == [other.fy == fy]`
    (two `eq_scalar`s), and the mask gate is `og == iv·eqx + (1−iv)·eqy`, with the gated one-hot's
    along-index head `iv·other.fy + (1−iv)·other.fx`.

Costs width, buys generality: the descriptor covers ANY rook move, not one shape. -/

/-- `DIFF_RBITS` (moves.rs) — the range width for the squared-distance is-zero / `msum` threshold.
Independent of the column LAYOUT but not of `n`: it must hold `2·(n−1)²` (the largest squared
coordinate distance) and `3n` (the largest masked interior sum). `9` bits covers both through
`n = 16`, so `n = 2` and the `n = 11` target share this width. -/
def RBITS : Nat := 9
/-- `SMALL_RBITS` (moves.rs) — the narrow range width, used by the source-non-vacuum bits (it ranges
over the particle alphabet `{0,1,2,3}` only, so it is `n`-independent). -/
def SMALL_RBITS : Nat := 5

/-- One `eq_scalar` / `forced_ge0` sub-block: `dsq`, the `neq` bit, its `RBITS` range bits, and the
`eq` bit. `12` columns at `RBITS = 9`. -/
def EQ_BLOCK_WIDTH : Nat := 3 + RBITS

/-- Width of one occlusion block: the `iv` `eq_scalar` pin (`EQ_BLOCK_WIDTH`) + six `n`-wide vectors
(`line`, `ety`, `etx`, `efrom`, `eto`, `seg`) + the two passable `eq_scalar`s (`2·EQ_BLOCK_WIDTH`) +
`og` (1) + the `n`-wide `osrc` + `msum`/`occ` and its `RBITS` range bits. `62` at `n = 2`. -/
def OCC_BLOCK_WIDTH : Nat := 3 * EQ_BLOCK_WIDTH + 7 * NN + 3 + RBITS

/-- The first column of a move's `OCC_BLOCK_WIDTH`-column occlusion block. The occlusion blocks
follow BOTH `validate_move` blocks, exactly as `emit_resolution` orders the allocation. -/
def occBase (which : Nat) : Nat :=
  2 * KK + 1 + AUTO_BLOCK_WIDTH + MV_BLOCK_WIDTH * 2 + OCC_BLOCK_WIDTH * which

/-- The witnessed `is_vertical` pin: `dxsq == (fx−tx)²`, its `forced_ge0` bit + range bits, and the
boolean `iv == 1 − [dxsq ≥ 1]`. -/
def cIvDsq (o : Nat) : Nat := o + 0
def cIvNeq (o : Nat) : Nat := o + 1
def ivNeqBit (o k : Nat) : Nat := o + 2 + k
def cIv (o : Nat) : Nat := o + 2 + RBITS
/-- The first column after the `iv` pin — the base of the six `n`-wide vectors. -/
def occVec (o : Nat) : Nat := o + EQ_BLOCK_WIDTH
/-- The gated line-extract `line[k]`. -/
def cLine (o k : Nat) : Nat := occVec o + k
/-- The `to`-endpoint one-hots: `ety` (pinned to `ty`, the vertical branch) and `etx` (`tx`). -/
def cEty (o j : Nat) : Nat := occVec o + NN + j
def cEtx (o j : Nat) : Nat := occVec o + 2 * NN + j
/-- The gated along-axis endpoint one-hots feeding the between-mask. -/
def cEfrom (o j : Nat) : Nat := occVec o + 3 * NN + j
def cEto (o j : Nat) : Nat := occVec o + 4 * NN + j
/-- The strictly-between mask. -/
def cSeg (o k : Nat) : Nat := occVec o + 5 * NN + k
/-- The base of the two passable-comparison `eq_scalar` blocks. -/
def occEq (o : Nat) : Nat := occVec o + 6 * NN
/-- `eqx == [other.fx == fx]` (the vertical branch's passable comparison). -/
def cEqxDsq (o : Nat) : Nat := occEq o + 0
def cEqxNeq (o : Nat) : Nat := occEq o + 1
def eqxBit (o k : Nat) : Nat := occEq o + 2 + k
def cEqx (o : Nat) : Nat := occEq o + 2 + RBITS
/-- `eqy == [other.fy == fy]` (the horizontal branch's passable comparison). -/
def cEqyDsq (o : Nat) : Nat := occEq o + EQ_BLOCK_WIDTH + 0
def cEqyNeq (o : Nat) : Nat := occEq o + EQ_BLOCK_WIDTH + 1
def eqyBit (o k : Nat) : Nat := occEq o + EQ_BLOCK_WIDTH + 2 + k
def cEqy (o : Nat) : Nat := occEq o + EQ_BLOCK_WIDTH + 2 + RBITS
/-- The base of the mask/threshold tail. -/
def occTail (o : Nat) : Nat := occEq o + 2 * EQ_BLOCK_WIDTH
/-- The gated other-source mask: its gate `og` and its gated one-hot. -/
def cOg (o : Nat) : Nat := occTail o + 0
def cOsrc (o j : Nat) : Nat := occTail o + 1 + j
/-- The masked interior sum and the `occ = [msum ≥ 1]` threshold bit + its range bits. -/
def cMsum (o : Nat) : Nat := occTail o + 1 + NN
def cOcc (o : Nat) : Nat := occTail o + 2 + NN
def occBit (o k : Nat) : Nat := occTail o + 3 + NN + k

/-! ### §2.3 — The ADJUDICATION columns (legs 3–8), continuing the `emit_resolution` alloc order.

Everything after the two occlusion blocks: the source-non-vacuum bits, the four `eq_coords` pattern
bits and the fork/collide/survive selection, the carries, the flow-through chain bits, the board
rewrite's one-hot endpoints, and the two packed board commitments.

The WITNESSED discipline audit for these legs: `emit_resolution`'s remaining compile-time reads
(`old.cell_at(ma.frm)`, `eq_coords`' `axv/ayv/bxv/byv`, `Placement.src_x_hot`, `dest_a_x_hot`, …)
are all `Builder::alloc` WITNESS VALUES / one-hot hot-indices — the *honest assignment*, never a
baked coefficient in an emitted head. Every emitted head in legs 3–8 is already a polynomial in
witnessed columns (`fxa`, `txb`, `ft_a`, `carry_a`, …), so unlike the `old.auto` constant (§2.0) and
the `is_vertical` branch (§2.2) there is nothing here to convert: the gates already range over any
board and any move shape. -/

/-- The first adjudication column — the end of the validity+occlusion prefix. -/
def RES0 : Nat := 2 * KK + 1 + AUTO_BLOCK_WIDTH + MV_BLOCK_WIDTH * 2 + OCC_BLOCK_WIDTH * 2

/-- Leg 3 — `anz`/`bnz`, each a `forced_ge0(fp − 1, SMALL_RBITS)` source-non-vacuum bit. -/
def cAnz : Nat := RES0
def anzBit (k : Nat) : Nat := RES0 + 1 + k
def cBnz : Nat := RES0 + 1 + SMALL_RBITS
def bnzBit (k : Nat) : Nat := RES0 + 2 + SMALL_RBITS + k

/-- The first column after the two non-vacuum bits. -/
def NZ_WIDTH : Nat := 2 * (1 + SMALL_RBITS)

/-- Leg 4 — the four `eq_coords` blocks (`eq_ff`, `eq_tt`, `eq_ab`, `eq_ba`), `EQ_BLOCK_WIDTH`
columns each: `dsq`, the `forced_ge0` bit + its `DIFF_RBITS` range bits, and the `eq` bit. -/
def eqBase (i : Nat) : Nat := RES0 + NZ_WIDTH + EQ_BLOCK_WIDTH * i
def cEqDsq (e : Nat) : Nat := e + 0
def cEqNeq (e : Nat) : Nat := e + 1
def eqBitAt (e k : Nat) : Nat := e + 2 + k
def cEqBit (e : Nat) : Nat := e + 2 + RBITS

/-- Leg 4 (cont.) — the selection truth table: `fork`, `¬eq_ff`, the collide product chain, `surv`. -/
def SEL0 : Nat := RES0 + NZ_WIDTH + 4 * EQ_BLOCK_WIDTH
def cFork : Nat := SEL0 + 0
def cNeqFf : Nat := SEL0 + 1
def cCol1 : Nat := SEL0 + 2
def cCol2 : Nat := SEL0 + 3
def cCollide : Nat := SEL0 + 4
def cSurv : Nat := SEL0 + 5

/-- Leg 5 — the carries `survive ∧ non-vac ∧ ¬occ`, each via one product column + one gate. -/
def CAR0 : Nat := SEL0 + 6
def cSa1 : Nat := CAR0 + 0
def cCarryA : Nat := CAR0 + 1
def cSb1 : Nat := CAR0 + 2
def cCarryB : Nat := CAR0 + 3

/-- Leg 6 — the vacuum flow-through chain bits (three `not_bit`s + a 4-product chain per side). -/
def FT0 : Nat := CAR0 + 4
def cNBnz : Nat := FT0 + 0
def cNOccb : Nat := FT0 + 1
def cNEqba : Nat := FT0 + 2
def cFa1 : Nat := FT0 + 3
def cFa2 : Nat := FT0 + 4
def cFa3 : Nat := FT0 + 5
def cFtA : Nat := FT0 + 6
def cNAnz : Nat := FT0 + 7
def cNOcca : Nat := FT0 + 8
def cNEqab : Nat := FT0 + 9
def cFb1 : Nat := FT0 + 10
def cFb2 : Nat := FT0 + 11
def cFb3 : Nat := FT0 + 12
def cFtB : Nat := FT0 + 13

/-- Leg 7 — `write_mid_witnessed`'s per-piece `one_hot_rowcol` endpoints: for each of the two
pieces, a source row/column one-hot pair then a destination row/column one-hot pair (`2n` selectors
per endpoint, `8` columns per piece, in `one_hot_rowcol`'s row-then-column order). -/
def WR0 : Nat := FT0 + 14
/-- Four `n`-wide one-hots per piece: source row, source column, destination row, destination
column. `8` columns per piece at `n = 2`. -/
def WR_PIECE_WIDTH : Nat := 4 * NN
def wSrcRow (i j : Nat) : Nat := WR0 + WR_PIECE_WIDTH * i + j
def wSrcCol (i j : Nat) : Nat := WR0 + WR_PIECE_WIDTH * i + NN + j
def wDstRow (i j : Nat) : Nat := WR0 + WR_PIECE_WIDTH * i + 2 * NN + j
def wDstCol (i j : Nat) : Nat := WR0 + WR_PIECE_WIDTH * i + 3 * NN + j

/-- Leg 8 — THE PACKED BOARD COMMITMENT: the packed felts of the OLD and MID boards. (Replaces the
retired `mh8_zero` pad column + two 8-felt `MerkleHash8` roots — see §4.6.) -/
def MH0 : Nat := WR0 + WR_PIECE_WIDTH * 2
/-- Packed felts per board, `⌈n²/15⌉`. -/
def RFC : Nat := AutomataflCommit.feltCount NN
def packOldFelt (j : Nat) : Nat := MH0 + j
def packMidFelt (j : Nat) : Nat := MH0 + RFC + j

/-! ### §2.4 — CHUNK-1 STAGED-ADDITIVE tail columns (AUTOMATAFL-MIGRATION-DESIGN Δ1/Δ3/Δ5).

These are the columns of the three NEW families that migrate Leg R from the OLD `occluded`/`applyMoves`
spec to the VALIDATED `blockedB`/`resolveMoves` spec. They are laid out entirely AFTER the packed
commitment (`INCL0 = MH0 + 2·RFC`, the OLD `R_WIDTH`), so EVERY pre-existing column index — old/mid
cells, auto/move/occlusion blocks, the adjudication legs, the write leg, the pack felts — is
UNTOUCHED, and every old proof that reads those columns is undisturbed. In THIS chunk the families
are emitted-but-unconsumed staging debt; chunk 2 (the `occ_iff_blocked` bridge) consumes `cOccIncl`
and chunk 3 (the `resolve_sat_imp_resolveMovesN` capstone) consumes `cNonLeave`/`cResolvable`. -/

/-- Base of the additive tail (the OLD `R_WIDTH`). -/
def INCL0 : Nat := MH0 + 2 * RFC

/-- (Δ1) The INCLUSIVE occlusion column pair, per move (`w ∈ {0,1}`): `msumIncl` (the strictly-interior
`msum` PLUS the destination endpoint term `Σ_k eto[k]·(1−osrc[k])·line[k]`, the emitted analog of
`AutomataflOcclusionGeneric.msumInclVal`), `occIncl = [msumIncl ≥ 1]`, and its `RBITS` threshold bits.
The `msum` bound rises `3n → 3n+3` (the endpoint adds `(1−osrc[dst])·line[dst] ≤ 3`), still `< 2^RBITS`
(`RBITS = 9` holds `3n+3` through `n = 16`), so the range gadget's width is unchanged. -/
def INCL_MV_WIDTH : Nat := 2 + RBITS
def inclBase (w : Nat) : Nat := INCL0 + INCL_MV_WIDTH * w
def cMsumIncl (w : Nat) : Nat := inclBase w + 0
def cOccIncl (w : Nat) : Nat := inclBase w + 1
def occInclBit (w k : Nat) : Nat := inclBase w + 2 + k

/-- (Δ3) The NON-LEAVER bit, per piece `i`: `landOld` (the OLD cell at piece `i`'s landing square,
read through the write leg's destination one-hots `wDstRow_i`/`wDstCol_i`), `landNz = [landOld ≠ vacuum]`
(a `SMALL_RBITS` `forced_ge0` + bits), and `nonLeave = landNz·(1 − carry_other)` — "the landing square
holds a piece that the OTHER move does not carry away". Fed into `carry_v2 = surv·nz·(1−occIncl)·(1−nonLeave)`
in chunk 3. -/
def NL0 : Nat := INCL0 + 2 * INCL_MV_WIDTH
def NL_PIECE_WIDTH : Nat := 3 + SMALL_RBITS
def nlBase (i : Nat) : Nat := NL0 + NL_PIECE_WIDTH * i
def cLandOld (i : Nat) : Nat := nlBase i + 0
def cLandNz (i : Nat) : Nat := nlBase i + 1
def landNzBit (i k : Nat) : Nat := nlBase i + 2 + k
def cNonLeave (i : Nat) : Nat := nlBase i + 2 + SMALL_RBITS

/-- (Δ5) The RESOLVABLE / merge-confluence surface: the two pieces' INTERPOLATED landing coordinates
as columns (`destHead`, post flow-through), an `eq_coords` over them (`resEq = [effective landings
coincide]` — the chain-confluence case `surv`/collide MISSES because collide reads the RAW `to`), and
the boolean logic pinning `resolvable = ¬merge ∧ ¬badA ∧ ¬badB`, `merge = bothCarry·resEq·¬identical`,
`bad_i = carry_i·nonLeave_i`. The emitted analog of `AutomataflRules.resolvableB` at `m = 2`. -/
def RESR0 : Nat := NL0 + 2 * NL_PIECE_WIDTH
def cDestX (i : Nat) : Nat := RESR0 + 2 * i
def cDestY (i : Nat) : Nat := RESR0 + 2 * i + 1
def resEqBase : Nat := RESR0 + 4
def cResEq : Nat := cEqBit resEqBase
def RESR_LOGIC : Nat := resEqBase + EQ_BLOCK_WIDTH
def cIdent : Nat := RESR_LOGIC + 0
def cBothCarry : Nat := RESR_LOGIC + 1
def cMc1 : Nat := RESR_LOGIC + 2
def cNotIdent : Nat := RESR_LOGIC + 3
def cMerge : Nat := RESR_LOGIC + 4
def cBadA : Nat := RESR_LOGIC + 5
def cBadB : Nat := RESR_LOGIC + 6
def cNMerge : Nat := RESR_LOGIC + 7
def cNBadA : Nat := RESR_LOGIC + 8
def cNBadB : Nat := RESR_LOGIC + 9
def cR1 : Nat := RESR_LOGIC + 10
def cResolvable : Nat := RESR_LOGIC + 11
/-- End of the CHUNK-1 additive tail columns (`INCL0 … RESR_END`); the base of the CHUNK-3 tail. -/
def RESR_END : Nat := RESR_LOGIC + 12

/-! ### §2.5 — CHUNK-3 STAGED-ADDITIVE tail columns (the NEW corrected board rewrite `cMidV2`).

Chunk 1 emitted the INGREDIENTS (`cOccIncl`, `cNonLeave`, `cResolvable`); the OLD `writeMid`/`carry`
still drive the emitted MID with the OLD carry `surv·nz·(1−occ_exclusive)`, so the emitted MID is the
BUGGY old board. This block emits, ADDITIVELY (after the whole chunk-1 tail at `CV2_0 = RESR_END`, so
every pre-existing column — including the OLD `writeMid`/`carry`/pack columns — is UNTOUCHED):

  * the CORRECTED carry `cCarryV2 i = surv·nz_i·(1−occIncl_i)·(1−nonLeave_i)`, staged through two
    intermediate columns (`cCv1 = surv·nz`, `cCv2 = cCv1·(1−occIncl)`) so every gate stays degree ≤ 2;
  * the corrected board `cMidV2[c] = cResolvable·(writeBoard-cell driven by cCarryV2) + (1−cResolvable)·
    old[c]`, with an intermediate `cWBoardV2[c]` holding the writeBoard-cell (the same one-hot
    placement/vacation structure `writeCellHead` uses, driven by `cCarryV2`) so the `cResolvable`
    selection gate stays degree 2 (`cWBoardV2` itself is the degree-7 rewrite, matching the OLD
    `writeMid` degree — the max constraint degree is UNCHANGED).

These are the emitted analog of `AutomataflRules.resolveMoves = if resolvableB then writeBoard … else b`,
consumed by chunk 4's `resolve_sat_imp_resolveMovesN`. In THIS chunk they are emitted-but-unconsumed
staging debt (cleared by chunk 4); the OLD `writeMid`/`carry`/capstone stay intact until chunk 5. -/

/-- Base of the CHUNK-3 tail (= the OLD chunk-1 `R_WIDTH`). -/
def CV2_0 : Nat := RESR_END
/-- The corrected-carry staging block for piece `i` (3 columns): `cCv1 = surv·nz`,
`cCv2 = cCv1·(1−occIncl)`, `cCarryV2 = cCv2·(1−nonLeave)`. -/
def cv2Base (i : Nat) : Nat := CV2_0 + 3 * i
def cCv1 (i : Nat) : Nat := cv2Base i + 0
def cCv2 (i : Nat) : Nat := cv2Base i + 1
def cCarryV2 (i : Nat) : Nat := cv2Base i + 2
/-- Base of the corrected board block: `KK` `cWBoardV2` cells (the writeBoard rewrite driven by
`cCarryV2`) then `KK` `cMidV2` cells (the `cResolvable`-gated final board). -/
def MIDV2_0 : Nat := CV2_0 + 6
def cWBoardV2 (c : Nat) : Nat := MIDV2_0 + c
def cMidV2 (c : Nat) : Nat := MIDV2_0 + KK + c
/-- End of the CHUNK-3 tail — the new total width. -/
def MV2_END : Nat := MIDV2_0 + 2 * KK

/-- Total main-trace width: the validity+occlusion prefix (`RES0`), the adjudication columns, the two
packed board commitments, the CHUNK-1 additive tail (`INCL0 … RESR_END`), and the CHUNK-3 corrected
board rewrite (`CV2_0 … MV2_END`). -/
def R_WIDTH : Nat := MV2_END
/-- PI index of the published automaton x-coordinate (y is the next one). -/
def AUTO_PI_BASE : Nat := 16 + 2 * RFC
/-- The full Leg-R public-input ABI: the opaque door prefix `[0..16)`, the packed OLD board
(`[16, 16+fc)`), the packed MID board (`[16+fc, 16+2fc)`), then the automaton coordinate. -/
def R_PI_COUNT : Nat := AUTO_PI_BASE + 2

/-! ## §3 — `Head`: the `builder.rs` linear/product head, in Lean (verbatim shape from
`AutomataflStepEmit`). `headToExpr` lowers it to the `EmittedExpr` gate polynomial (zero-coeff terms
dropped for a clean gate; Lean is the source of truth). -/

/-- A linear/product head: `Σ (coeff, cols) + constant`; `cols = []` is the constant term. -/
structure Head where
  terms : List (ℤ × List Nat)
  const : ℤ

namespace Head
def zero : Head := ⟨[], 0⟩
def c (k : ℤ) : Head := ⟨[], k⟩
def lin (coeff : ℤ) (col : Nat) : Head := ⟨[(coeff, [col])], 0⟩
def addLin (h : Head) (coeff : ℤ) (col : Nat) : Head := ⟨h.terms ++ [(coeff, [col])], h.const⟩
def addProd (h : Head) (coeff : ℤ) (cols : List Nat) : Head := ⟨h.terms ++ [(coeff, cols)], h.const⟩
def addConst (h : Head) (k : ℤ) : Head := ⟨h.terms, h.const + k⟩
def scale (h : Head) (k : ℤ) : Head := ⟨h.terms.map (fun t => (t.1 * k, t.2)), h.const * k⟩
def append (h o : Head) : Head := ⟨h.terms ++ o.terms, h.const + o.const⟩
end Head

instance : Inhabited Head := ⟨Head.zero⟩

/-- The product `∏ vars` (empty product `= 1`), left-associated. -/
def varsProd : List Nat → EmittedExpr
  | []        => .const 1
  | co :: rest => rest.foldl (fun acc v => .mul acc (.var v)) (.var co)

/-- One term `coeff · ∏ cols` as an `EmittedExpr` (coeff `1` elides the multiplier). -/
def termToExpr : ℤ × List Nat → EmittedExpr
  | (coeff, [])   => .const coeff
  | (coeff, cols) => if coeff == 1 then varsProd cols else .mul (.const coeff) (varsProd cols)

/-- Lower a `Head` to the gate `EmittedExpr` (a left-folded sum; zero-coeff terms dropped). -/
def headToExpr (h : Head) : EmittedExpr :=
  let ts := (h.terms.filter (fun t => t.1 != 0)).map termToExpr
  let ts := if h.const == 0 then ts else ts ++ [.const h.const]
  match ts with
  | []       => .const 0
  | e :: rest => rest.foldl (fun acc x => .add acc x) e

/-- `x·(x−1)` — the boolean pin (`assert_binary`). -/
def gBin (co : Nat) : EmittedExpr := .mul (.var co) (.add (.var co) (.const (-1)))

/-- `∏_{s∈set}(col − s)` — the membership gate (`assert_member`), left-associated, byte-identical to
`AutomataflStepEmit.memberExpr`. -/
def memberExpr (col : Nat) (set : List ℤ) : EmittedExpr :=
  match set with
  | []        => .const 1
  | s :: rest => rest.foldl (fun acc t => .mul acc (.add (.var col) (.const (-t))))
                   (.add (.var col) (.const (-s)))

/-- A per-row gate from a raw `EmittedExpr`. -/
def cg (e : EmittedExpr) : VmConstraint2 := .base (.gate e)
/-- A per-row gate from a `Head`. -/
def cgH (h : Head) : VmConstraint2 := .base (.gate (headToExpr h))

/-- `cond_nonzero(sel, val)` lowered as the gate `sel·(val·inv − 1) == 0` (the `AutomataflStepEmit`
lowering of `ConditionalNonzero`; a fresh witnessed inverse column `inv`). -/
def gCondNonzero (sel val inv : Nat) : EmittedExpr :=
  .mul (.var sel) (.add (.mul (.var val) (.var inv)) (.const (-1)))

/-! ### §3.1 — The `n`-generic range primitive (hoisted: `decomposeConstraints` uses it).

`Builder::range_nonneg(head, rbits)` with bits at `bit0 ..< bit0+rbits`: each bit boolean, then the
recomposition `head − Σ 2^k·b_k == 0`. A negative/over-range head has no satisfying bits, so the leaf
is UNSAT — the genuine non-negativity proof. -/
def rangeNonnegConstraints (h : Head) (bit0 rbits : Nat) : List VmConstraint2 :=
  (List.range rbits).map (fun k => cg (gBin (bit0 + k)))
  ++ [ cgH ((List.range rbits).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k)) h) ]

/-! ## §4 — `validate_move` (moves.rs), the per-move validity gate block at base `b`. -/

/-- `decompose_coord_le(col, n−1)` — the `COORD_RBITS`-bit range decomposition of BOTH edges: the
lower edge `col = Σ 2^k b_k` and the upper edge `(n−1) − col = Σ 2^k b'_k`, each bit boolean plus its
recomposition gate. At `n = 2` (`COORD_RBITS = 1`) this is the old two-bit form verbatim; at
`n = 11` it is four bits per edge. -/
def decomposeConstraints (col loBit0 hiBit0 : Nat) : List VmConstraint2 :=
  rangeNonnegConstraints (Head.lin 1 col) loBit0 COORD_RBITS
  ++ rangeNonnegConstraints ((Head.c ((NN : ℤ) - 1)).addLin (-1) col) hiBit0 COORD_RBITS

/-- A one-hot's gates (`Builder::one_hot`), `n`-generically over a selector LIST and a general index
HEAD (the `AutomataflStepEmit.oneHotConstraints` shape): every selector boolean, `Σ selⱼ == 1`, and
`Σ j·selⱼ == idx`. The `j = 0` term carries coefficient `0` and is dropped by `headToExpr`, so at
`n = 2` this emits byte-identically to the old hand-written pair. -/
def oneHotConstraints (sels : List Nat) (idx : Head) : List VmConstraint2 :=
  sels.map (fun s => cg (gBin s))
  ++ [ cgH (sels.foldl (fun acc s => acc.addLin 1 s) (Head.c (-1))) ]
  ++ [ cgH (((sels.zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero)).append
              (idx.scale (-1))) ]

/-- The one-hot pinned to a bare coordinate COLUMN — the common case. -/
def oneHotAtCol (sels : List Nat) (idxCol : Nat) : List VmConstraint2 :=
  oneHotConstraints sels (Head.lin 1 idxCol)

/-- The source row / column selector lists for the move at base `b`. -/
def selRowCols (b : Nat) : List Nat := (List.range NN).map (cSelRow b)
def selColCols (b : Nat) : List Nat := (List.range NN).map (cSelCol b)

/-- The witnessed source read `fp − Σ_y Σ_x selRow[y]·selCol[x]·old[y·n+x] == 0`, an `n×n` fold. -/
def sourceReadHead (b : Nat) : Head :=
  (List.range NN).foldl (fun h y =>
    (List.range NN).foldl (fun h2 x =>
      h2.addProd (-1) [cSelRow b y, cSelCol b x, old (y * NN + x)]) h) (Head.lin 1 (cFp b))

/-- The squared-distance definition `dsq − (fx−tx)² − (fy−ty)²`, expanded exactly as moves.rs
`validate_move`'s distinctness head. -/
def dsqHead (b : Nat) : Head :=
  ((((((Head.lin 1 (cDsq b)).addProd (-1) [cFx b, cFx b]).addProd 2 [cFx b, cTx b]).addProd (-1)
      [cTx b, cTx b]).addProd (-1) [cFy b, cFy b]).addProd 2 [cFy b, cTy b]).addProd (-1)
      [cTy b, cTy b]

/-- The auto-relative squared distance `out − (x−ax)² − (y−ay)²` for coordinate columns `(xc, yc)`
against the WITNESSED auto columns `(AX_C, AY_C)`, expanded as
`out − x² + 2·x·ax − ax² − y² + 2·y·ay − ay²` (every auto term a product of witnessed columns, not a
baked constant). -/
def autoDistHead (outCol xc yc : Nat) : Head :=
  ((((((Head.lin 1 outCol).addProd (-1) [xc, xc]).addProd 2 [xc, AX_C]).addProd (-1)
      [AX_C, AX_C]).addProd (-1) [yc, yc]).addProd 2 [yc, AY_C]).addProd (-1) [AY_C, AY_C]

/-- The AUTO pin: `AUTO == Σ_y Σ_x selAutoRow[y]·selAutoCol[x]·old[y·n+x]` — forces `(ax, ay)` (the
one-hot indices) to be the board cell holding the automaton (`AutomataflStepEmit.autoPinHead`). -/
def autoPinHead : Head :=
  (List.range NN).foldl (fun h (y : Nat) =>
    (List.range NN).foldl (fun h2 (x : Nat) =>
      h2.addProd 1 [selAutoRow y, selAutoCol x, old (y * NN + x)]) h) (Head.c (-AUTO_CODE))

/-- The shared witnessed automaton-position read: `ax`/`ay` bit-range decomposition, the row×column
one-hot pinned to `(ax, ay)`, and the `AUTO == Σ selRow·selCol·old` dot product. Emitted once, in
`AutomataflStepEmit`'s front-end order (decompose `ax`, decompose `ay`, row one-hot @ `ay`, column
one-hot @ `ax`, the auto pin). -/
def autoReadConstraints : List VmConstraint2 :=
  decomposeConstraints AX_C axLo axHi
  ++ decomposeConstraints AY_C ayLo ayHi
  ++ oneHotAtCol ((List.range NN).map selAutoRow) AY_C        -- auto row one-hot @ ay
  ++ oneHotAtCol ((List.range NN).map selAutoCol) AX_C        -- auto col one-hot @ ax
  ++ [ cgH autoPinHead ]

/-- The rook-alignment gate `(fx−tx)(fy−ty) == 0`, expanded as
`fx·fy − fx·ty − tx·fy + tx·ty`. -/
def rookAlignHead (b : Nat) : Head :=
  (((Head.zero.addProd 1 [cFx b, cFy b]).addProd (-1) [cFx b, cTy b]).addProd (-1)
      [cTx b, cFy b]).addProd 1 [cTx b, cTy b]

/-- The full `validate_move` constraint block for the move at base `b`, in emission order. -/
def validateMove (b : Nat) : List VmConstraint2 :=
  decomposeConstraints (cFx b) (cFxLo b) (cFxHi b)
  ++ decomposeConstraints (cFy b) (cFyLo b) (cFyHi b)
  ++ decomposeConstraints (cTx b) (cTxLo b) (cTxHi b)
  ++ decomposeConstraints (cTy b) (cTyLo b) (cTyHi b)
  ++ [ cgH (rookAlignHead b) ]                                       -- rook-aligned
  ++ [ cgH (dsqHead b) ]                                             -- dsq definition
  ++ [ cg (gCondNonzero ONE (cDsq b) (cDistinctInv b)) ]            -- distinct: dsq ≠ 0
  ++ [ cgH (autoDistHead (cFa b) (cFx b) (cFy b)) ]                 -- fa = |frm − auto|²
  ++ [ cg (gCondNonzero ONE (cFa b) (cFnaInv b)) ]                  -- frm ≠ auto
  ++ [ cgH (autoDistHead (cTa b) (cTx b) (cTy b)) ]                 -- ta = |to − auto|²
  ++ [ cg (gCondNonzero ONE (cTa b) (cTnaInv b)) ]                  -- to ≠ auto
  ++ oneHotAtCol (selRowCols b) (cFy b)                             -- source row one-hot @ fy
  ++ oneHotAtCol (selColCols b) (cFx b)                             -- source col one-hot @ fx
  ++ [ cgH (sourceReadHead b) ]                                     -- fp == old[n·fy + fx]

/-! ## §4.5 — The `builder.rs` range primitives, in Lean (`range_nonneg` / `forced_ge0` /
`eq_scalar` / `one_hot_gated`), then `validate_occlusion` with the WITNESSED direction bit. -/

/-- `Builder::forced_ge0`'s range head `2·ib·d + ib − d − 1` (verbatim term order). -/
def forcedGe0Term (d : Head) (ib : Nat) : Head :=
  ((((d.terms.foldl (fun acc t => acc.addProd (2 * t.1) (ib :: t.2)) Head.zero).addProd
      (2 * d.const) [ib]).addLin 1 ib).append (d.scale (-1))).addConst (-1)

/-- `Builder::forced_ge0(d)` — the boolean `ib` FORCED to `[d ≥ 0]`: `ib` boolean, then
`range_nonneg(2·ib·d + ib − d − 1)`. Only the honest bit admits a non-negative term. -/
def forcedGe0ConstraintsN (d : Head) (ib bit0 rbits : Nat) : List VmConstraint2 :=
  cg (gBin ib) :: rangeNonnegConstraints (forcedGe0Term d ib) bit0 rbits

/-- `forced_ge0` at the default `DIFF_RBITS` width. -/
def forcedGe0Constraints (d : Head) (ib bit0 : Nat) : List VmConstraint2 :=
  forcedGe0ConstraintsN d ib bit0 RBITS

/-- `eq_scalar(a, c)` — `eq == [a == c]`, pinned by an is-zero over `(a−c)²`: the witnessed
`dsq == a² − 2ac + c²`, `neq == [dsq ≥ 1]` (a `forced_ge0`), `eq == 1 − neq`. A PROVEN boolean
function of the two witnessed columns — no prover freedom. -/
def eqScalarConstraints (a c dsqCol neqCol bit0 eqCol : Nat) : List VmConstraint2 :=
  [ cgH ((((Head.lin 1 dsqCol).addProd (-1) [a, a]).addProd 2 [a, c]).addProd (-1) [c, c]) ]
  ++ forcedGe0Constraints ((Head.lin 1 dsqCol).addConst (-1)) neqCol bit0
  ++ [ cgH (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1)) ]

/-- `Builder::one_hot_gated`, `n`-generically: selectors boolean, `Σ sel == gate`, and
`Σ j·selⱼ == gate·indexHead` (the index head multiplied THROUGH the gate, term by term). -/
def oneHotGatedConstraints (sels : List Nat) (gate : Nat) (idx : Head) : List VmConstraint2 :=
  sels.map (fun s => cg (gBin s))
  ++ [ cgH (sels.foldl (fun acc s => acc.addLin 1 s) (Head.lin (-1) gate)) ]
  ++ [ cgH ((idx.terms.foldl (fun acc t => acc.addProd (-t.1) (gate :: t.2))
              (sels.zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero)).addProd
              (-idx.const) [gate]) ]

/-- The WITNESSED `is_vertical` bit: `iv == [fx == tx]`, by `eq_scalar` over the move's own
witnessed coordinate columns. THIS is the pin to the real geometry — the bit cannot disagree with
the move it gates. -/
def isVerticalConstraints (b o : Nat) : List VmConstraint2 :=
  eqScalarConstraints (cFx b) (cTx b) (cIvDsq o) (cIvNeq o) (ivNeqBit o 0) (cIv o)

/-- The GATED line-extract: `line[k] == iv·(Σ_x selCol[x]·old[k·n+x]) + (1−iv)·(Σ_y selRow[y]·
old[y·n+k])` — BOTH scans emitted, the column-scan gated by `iv`, the row-scan by `1−iv`. -/
def lineHead (b o k : Nat) : Head :=
  let hv := (List.range NN).foldl (fun h x =>
    h.addProd (-1) [cIv o, cSelCol b x, old (k * NN + x)]) (Head.lin 1 (cLine o k))
  (List.range NN).foldl (fun h y =>
    (h.addProd (-1) [cSelRow b y, old (y * NN + k)]).addProd 1
      [cIv o, cSelRow b y, old (y * NN + k)]) hv

/-- `efrom[j] == iv·selRow[j] + (1−iv)·selCol[j]` — the along-axis SOURCE one-hot, selected by the
witnessed bit from `validate_move`'s two source one-hots (vertical ⇒ the row index `fy`). -/
def efromHead (b o j : Nat) : Head :=
  (((Head.lin 1 (cEfrom o j)).addProd (-1) [cIv o, cSelRow b j]).addLin (-1)
      (cSelCol b j)).addProd 1 [cIv o, cSelCol b j]

/-- `eto[j] == iv·ety[j] + (1−iv)·etx[j]` — the along-axis DESTINATION one-hot, selected from the
two unconditionally-pinned endpoint one-hots. -/
def etoHead (o j : Nat) : Head :=
  (((Head.lin 1 (cEto o j)).addProd (-1) [cIv o, cEty o j]).addLin (-1)
      (cEtx o j)).addProd 1 [cIv o, cEtx o j]

/-- `seg[k] == Σ_{j1<k<j2} (efrom[j1]·eto[j2] + eto[j1]·efrom[j2])` — the ORDER-INDEPENDENT
strictly-between mask (no per-position range gadget). At `n = 2` the index set is empty for every
`k`, so the family forces `seg[k] == 0`: a 2-line has no strictly-interior cell. -/
def segHead (o k : Nat) : Head :=
  (List.range k).foldl (fun h j1 =>
    ((List.range NN).filter (fun j2 => k < j2)).foldl (fun h2 j2 =>
      (h2.addProd (-1) [cEfrom o j1, cEto o j2]).addProd (-1) [cEto o j1, cEfrom o j2]) h)
    (Head.lin 1 (cSeg o k))

/-- `og == iv·eqx + (1−iv)·eqy` — the other-source passable GATE: on a vertical move the other
source lies on this line iff its `x` matches, on a horizontal one iff its `y` does. BOTH comparisons
are emitted; the witnessed bit selects. -/
def ogHead (o : Nat) : Head :=
  (((Head.lin 1 (cOg o)).addProd (-1) [cIv o, cEqx o]).addLin (-1) (cEqy o)).addProd 1
    [cIv o, cEqy o]

/-- The masked interior sum `msum == Σ_k seg[k]·(1 − osrc[k])·line[k]`, expanded as
`Σ seg·line − Σ seg·osrc·line` (moves.rs' term order). -/
def msumHead (o : Nat) : Head :=
  (List.range NN).foldl (fun h k =>
    (h.addProd (-1) [cSeg o k, cLine o k]).addProd 1 [cSeg o k, cOsrc o k, cLine o k])
    (Head.lin 1 (cMsum o))

/-- **`validate_occlusion`** for the move at base `b`, occlusion block at `o`, whose OTHER moving
source is the move at base `ob` — authored with a WITNESSED direction bit so it covers ANY rook
move, in `validate_occlusion`'s emission order (iv pin, line extract, endpoint one-hots, between
mask, passable mask, masked sum + threshold). -/
def validateOcclusion (b o ob : Nat) : List VmConstraint2 :=
  isVerticalConstraints b o
  ++ (List.range NN).map (fun k => cgH (lineHead b o k))
  ++ oneHotAtCol ((List.range NN).map (cEty o)) (cTy b)           -- e_to (vertical) @ ty
  ++ oneHotAtCol ((List.range NN).map (cEtx o)) (cTx b)           -- e_to (horizontal) @ tx
  ++ (List.range NN).map (fun j => cgH (efromHead b o j))
  ++ (List.range NN).map (fun j => cgH (etoHead o j))
  ++ (List.range NN).map (fun k => cgH (segHead o k))
  ++ eqScalarConstraints (cFx ob) (cFx b) (cEqxDsq o) (cEqxNeq o) (eqxBit o 0) (cEqx o)
  ++ eqScalarConstraints (cFy ob) (cFy b) (cEqyDsq o) (cEqyNeq o) (eqyBit o 0) (cEqy o)
  ++ [ cgH (ogHead o) ]
  ++ oneHotGatedConstraints ((List.range NN).map (cOsrc o)) (cOg o)
       ((((Head.zero.addProd 1 [cIv o, cFy ob]).addLin 1 (cFx ob)).addProd (-1) [cIv o, cFx ob]))
  ++ [ cgH (msumHead o) ]
  ++ forcedGe0Constraints ((Head.lin 1 (cMsum o)).addConst (-1)) (cOcc o) (occBit o 0)

/-! ## §4.6 — The ADJUDICATION legs (3–8): non-vacuum bits, the pattern/selection truth table,
the carries, the flow-through chain, the board rewrite, and the board-root PI tail. -/

/-- `not_bit(col)` — a fresh column pinned to `1 − col`: `c + col − 1 == 0`. -/
def notBitPin (out col : Nat) : VmConstraint2 :=
  cgH (((Head.lin 1 out).addLin 1 col).addConst (-1))

/-- `Builder::alloc_prod(a, b)` — a fresh column pinned to the product: `−out + a·b == 0`. -/
def prodPin (out a b : Nat) : VmConstraint2 :=
  cgH ((Head.lin (-1) out).addProd 1 [a, b])

/-! ### Leg 3 — the source-non-vacuum bits `anz` / `bnz`.

`anz = [fp_a − 1 ≥ 0] = [fp_a ≠ vacuum]` (particle codes are `≥ 1`; vacuum is `0`), a `forced_ge0`
at `SMALL_RBITS` over the WITNESSED source-particle column `validate_move` already bound to
`old[n·fy + fx]`. Nothing compile-time survives into the head: the Rust's `old.cell_at(ma.frm)` is
the range gadget's witness assignment, not a coefficient. -/
def srcNonVacConstraints : List VmConstraint2 :=
  forcedGe0ConstraintsN ((Head.lin 1 (cFp (mvBase 0))).addConst (-1)) cAnz (anzBit 0) SMALL_RBITS
  ++ forcedGe0ConstraintsN ((Head.lin 1 (cFp (mvBase 1))).addConst (-1)) cBnz (bnzBit 0) SMALL_RBITS

/-! ### Leg 4 — the four `eq_coords` pattern bits + the fork/collide/survive selection. -/

/-- `eq_coords((xa,ya), (xb,yb))` — `eq == [(xa,ya) == (xb,yb)]`, the 2-D twin of `eq_scalar`: the
witnessed squared distance `dsq == (xa−xb)² + (ya−yb)²` (expanded in moves.rs' term order), the
`forced_ge0` bit `neq == [dsq ≥ 1]`, and `eq == 1 − neq`. A PROVEN boolean function of the four
witnessed coordinate columns. -/
def eqCoordsConstraints (xa ya xb yb e : Nat) : List VmConstraint2 :=
  [ cgH ((((((Head.lin 1 (cEqDsq e)).addProd (-1) [xa, xa]).addProd 2 [xa, xb]).addProd (-1)
      [xb, xb]).addProd (-1) [ya, ya]).addProd 2 [ya, yb] |>.addProd (-1) [yb, yb]) ]
  ++ forcedGe0Constraints ((Head.lin 1 (cEqDsq e)).addConst (-1)) (cEqNeq e) (eqBitAt e 0)
  ++ [ cgH (((Head.lin 1 (cEqBit e)).addLin 1 (cEqNeq e)).addConst (-1)) ]

/-- The four pattern bits, in `emit_resolution`'s order:
`eq_ff = [frm_a == frm_b]` (same source), `eq_tt = [to_a == to_b]` (same destination),
`eq_ab = [to_a == frm_b]` and `eq_ba = [to_b == frm_a]` (the chain relations). -/
def patternBitConstraints : List VmConstraint2 :=
  let a := mvBase 0; let b := mvBase 1
  eqCoordsConstraints (cFx a) (cFy a) (cFx b) (cFy b) (eqBase 0)   -- eq_ff
  ++ eqCoordsConstraints (cTx a) (cTy a) (cTx b) (cTy b) (eqBase 1) -- eq_tt
  ++ eqCoordsConstraints (cTx a) (cTy a) (cFx b) (cFy b) (eqBase 2) -- eq_ab
  ++ eqCoordsConstraints (cTx b) (cTy b) (cFx a) (cFy a) (eqBase 3) -- eq_ba

/-- The `n = 2` SELECTION truth table, derived from the pattern bits and the non-vacuum bits:
`fork = eq_ff ∧ ¬eq_tt` (same source, different destination ⇒ drop both);
`collide = eq_tt ∧ ¬eq_ff ∧ anz ∧ bnz` (same destination, two distinct non-vacuum sources ⇒ drop);
`survive = ¬fork ∧ ¬collide` (symmetric at `n = 2`, expanded as the inclusion–exclusion gate
`surv − 1 + fork + collide − fork·collide == 0`). -/
def selectionConstraints : List VmConstraint2 :=
  let eqFf := cEqBit (eqBase 0); let eqTt := cEqBit (eqBase 1)
  [ cgH (((Head.lin 1 cFork).addLin (-1) eqFf).addProd 1 [eqFf, eqTt])   -- fork = eq_ff·(1−eq_tt)
  , notBitPin cNeqFf eqFf
  , prodPin cCol1 eqTt cNeqFf
  , prodPin cCol2 cCol1 cAnz
  , prodPin cCollide cCol2 cBnz
  , cgH (((((Head.lin 1 cSurv).addConst (-1)).addLin 1 cFork).addLin 1 cCollide).addProd (-1)
      [cFork, cCollide]) ]

/-! ### Leg 5 — the carries. `carry_i = survive ∧ src_nonvac_i ∧ ¬occ_i`: the piece actually
journeys only if the turn survived adjudication, its source held a piece, and its line was clear. -/
def carryConstraints : List VmConstraint2 :=
  [ prodPin cSa1 cSurv cAnz
  , cgH (((Head.lin 1 cCarryA).addProd (-1) [cSa1]).addProd 1 [cSa1, cOcc (occBase 0)])
  , prodPin cSb1 cSurv cBnz
  , cgH (((Head.lin 1 cCarryB).addProd (-1) [cSb1]).addProd 1 [cSb1, cOcc (occBase 1)]) ]

/-! ### Leg 6 — the vacuum flow-through chain (the `m = 2` caterpillar).

A surviving carrying piece lands at its own `to` EXCEPT when it rides a square the other piece is
vacating: if A's destination IS B's source and that source is VACUUM (`¬bnz` — B's "move" is the
continuation of the chain, not a second piece), then A flows THROUGH to B's destination. The
`¬eq_ba` conjunct breaks the symmetric 2-cycle so at most one side flows through.

  `ft_a = eq_ab ∧ ¬bnz ∧ survive ∧ ¬occ_b ∧ ¬eq_ba`   ⇒  `dest_a = to_b`
  `ft_b = eq_ba ∧ ¬anz ∧ survive ∧ ¬occ_a ∧ ¬eq_ab`   ⇒  `dest_b = to_a` -/
def flowThroughConstraints : List VmConstraint2 :=
  let eqAb := cEqBit (eqBase 2); let eqBa := cEqBit (eqBase 3)
  [ notBitPin cNBnz cBnz
  , notBitPin cNOccb (cOcc (occBase 1))
  , notBitPin cNEqba eqBa
  , prodPin cFa1 eqAb cNBnz
  , prodPin cFa2 cFa1 cSurv
  , prodPin cFa3 cFa2 cNOccb
  , prodPin cFtA cFa3 cNEqba
  , notBitPin cNAnz cAnz
  , notBitPin cNOcca (cOcc (occBase 0))
  , notBitPin cNEqab eqAb
  , prodPin cFb1 eqBa cNAnz
  , prodPin cFb2 cFb1 cSurv
  , prodPin cFb3 cFb2 cNOcca
  , prodPin cFtB cFb3 cNEqab ]

/-- The flow-through destination head for piece `i`: `to_i + ft_i·(to_other − to_i)` — a linear
interpolation between the piece's own destination and the chain endpoint, over the WITNESSED
destination columns and the witnessed `ft` bit. (moves.rs' `dest_a_x_head` term order.) -/
def destHead (own other ft : Nat) : Head :=
  ((Head.lin 1 own).addProd 1 [ft, other]).addProd (-1) [ft, own]

/-! ### Leg 7 — `write_mid_witnessed`, the per-cell one-hot board rewrite. -/

/-- The carry column of piece `i`. -/
def carryCol (i : Nat) : Nat := if i == 0 then cCarryA else cCarryB
/-- The witnessed source particle of piece `i` (`validate_move`'s bound `fp`). -/
def particleCol (i : Nat) : Nat := cFp (mvBase i)

/-- `one_hot_rowcol` for both endpoints of both pieces, in `write_mid_witnessed`'s allocation order
(per piece: source row @ `fy`, source column @ `fx`, destination row @ the interpolated `dest_y`,
destination column @ `dest_x`). -/
def writeEndpointConstraints : List VmConstraint2 :=
  (List.range 2).flatMap (fun i =>
    let b := mvBase i; let ob := mvBase (1 - i); let ft := if i == 0 then cFtA else cFtB
    oneHotConstraints ((List.range NN).map (wSrcRow i)) (Head.lin 1 (cFy b))
    ++ oneHotConstraints ((List.range NN).map (wSrcCol i)) (Head.lin 1 (cFx b))
    ++ oneHotConstraints ((List.range NN).map (wDstRow i)) (destHead (cTy b) (cTy ob) ft)
    ++ oneHotConstraints ((List.range NN).map (wDstCol i)) (destHead (cTx b) (cTx ob) ft))

/-- The per-cell rewrite head. With `keep[c] = (1 − is_src[c])·(1 − land[c])`,
`mid[c] == keep[c]·old[c] + Σ_i carry_i·sel_dst_i[c]·particle_i`, expanded exactly as moves.rs:
`old − Σ_i carry_i·src_i[c]·old − Σ_i carry_i·dst_i[c]·old + Σ_i carry_i·dst_i[c]·particle_i`
plus, for `i ≠ j`, the SWAP-RESTORE term `carry_i·src_i[c]·carry_j·dst_j[c]·old` — a cell that is
BOTH a cleared source AND a landing target was subtracted twice, so it is added back once. The
`(1 − land)` factor makes a landing an OVERWRITE rather than a sum (the occlusion-aware
`apply_moves` case where a piece journeys onto an uncleared, non-journeying source).

**DEFECT #5, FIXED HERE — the SHARED-ENDPOINT inclusion–exclusion.** The per-piece sums above
double-count when the two moves share an endpoint, which happens on the IDENTICAL-MOVE turn
(`ma = mb`, both carrying) that `Automatafl.conflictResolve` explicitly does NOT treat as a
conflict. Two terms close it:

* SHARED SOURCE `A·C·old` (`A = carry_a·src_a[c]`, `C = carry_b·src_b[c]`): the old particle was
  subtracted once per piece, forcing `mid ≡ −old`, which DEFECT #4's alphabet gates then reject —
  the leaf was UNSATISFIABLE on a legal turn. Added back once, a shared source vacates exactly
  once (`mid = 0`).
* SHARED LANDING `B·D·old − B·D·particle_b`: symmetric double subtraction of `old` plus a doubled
  deposit `pa + pb`; the overlap correction leaves exactly ONE particle on the square.

Both are pure inclusion–exclusion on the SAME indicators the gate already carries, so no forged
board becomes admissible: the cell value is still pinned to a single reference-determined value
(`cellAlgebra` in `AutomataflResolveRefine` proves the pinned value IS the reference's, now over
all sixteen indicator combinations minus only the same-piece exclusions `A·B = C·D = 0`). -/
def writeCellHead (c : Nat) : Head :=
  let x := c % NN; let y := c / NN
  let base := (List.range 2).foldl (fun h i =>
    ((h.addProd (-1) [carryCol i, wSrcRow i y, wSrcCol i x, old c]).addProd (-1)
        [carryCol i, wDstRow i y, wDstCol i x, old c]).addProd 1
        [carryCol i, wDstRow i y, wDstCol i x, particleCol i]) (Head.lin 1 (old c))
  let full := (List.range 2).foldl (fun h i =>
    (List.range 2).foldl (fun h2 j =>
      if i == j then h2 else
        h2.addProd 1 [carryCol i, wSrcRow i y, wSrcCol i x,
                      carryCol j, wDstRow j y, wDstCol j x, old c]) h) base
  let ie := ((full.addProd 1 [carryCol 0, wSrcRow 0 y, wSrcCol 0 x,
                              carryCol 1, wSrcRow 1 y, wSrcCol 1 x, old c]).addProd 1
              [carryCol 0, wDstRow 0 y, wDstCol 0 x,
               carryCol 1, wDstRow 1 y, wDstCol 1 x, old c]).addProd (-1)
              [carryCol 0, wDstRow 0 y, wDstCol 0 x,
               carryCol 1, wDstRow 1 y, wDstCol 1 x, particleCol 1]
  (Head.lin 1 (mid c)).append (ie.scale (-1))

/-- **`write_mid_witnessed`** — the endpoint one-hots followed by the `k` cell equalities forcing
`mid == resolve_mid(old, [ma, mb])`. -/
def writeMidConstraints : List VmConstraint2 :=
  writeEndpointConstraints ++ (List.range KK).map (fun c => cgH (writeCellHead c))

/-! ### Leg 8 — THE PACKED BOARD COMMITMENT (replaces `bind_board_roots`).

WHAT WAS THERE: two `MerkleHash8` `node8` arity-16 Poseidon2 chip lookups, each absorbing the WHOLE
board as ONE zero-padded 8-lane leaf folded against a zero sibling, their 16 digest lanes bound to
PIs `[16..32)`. That leaf holds at most `8` cells, so the family was well-defined only at
`k = n² ≤ 8` (`n ≤ 2`) — the hard blocker on `descN 11` — and every root claim rested on a Poseidon2
wide-soundness assumption.

WHAT IS HERE: `AutomataflCommit`'s packed base-4 commitment, re-pointed to this leg's two board
bases. Each board becomes `⌈n²/15⌉` felts (15 cells per felt: `4^15 < p`, so no modular wrap), each
felt pinned by ONE degree-1 gate `felt_j − Σ 4^i·cell = 0` and bound directly to a public input.
The commitment is INJECTIVE by `AutomataflCommit.pack_injective` — a base-4 positional-decode
theorem, NOT a collision-resistance assumption — and it commits EVERY cell at EVERY `n`.

The alphabet precondition the pack needs is already emitted by `boardRangeConstraints` on both
boards, so nothing extra is asserted. The automaton coordinate is published alongside: a `Board` is
cells AND a coordinate, and no gate forbids a second `AUTO`-coded cell, so cell agreement alone
cannot recover it. -/

/-- **The Leg-R commitment family** — pack gates for OLD and MID, the PI bindings for both packs,
and the automaton-coordinate bindings. Emitted LAST, so the structured membership of every
preceding family keeps its position. -/
def commitBoardsConstraints : List VmConstraint2 :=
  AutomataflCommit.packBoardConstraintsAt NN old packOldFelt
  ++ AutomataflCommit.packBoardConstraintsAt NN mid packMidFelt
  ++ AutomataflCommit.commitBoardConstraintsAt NN packOldFelt 16
  ++ AutomataflCommit.commitBoardConstraintsAt NN packMidFelt (16 + RFC)
  ++ AutomataflCommit.autoCoordCommitConstraints AX_C AY_C AUTO_PI_BASE

/-! ## §5 — The descriptor: the `one` pin followed by `validate_move` for both moves. -/

/-- The `one_col` pin (`Head::lin(1, one).add_const(-1)` ⇒ `one − 1 == 0`). -/
def onePin : VmConstraint2 := cgH ((Head.lin 1 ONE).addConst (-1))

/-- **The board-cell RANGE CHECKS** (DEFECT #4, closed) — `assert_member(cell, {VAC,REP,ATT,AUTO})`
for every OLD and every MID board column, exactly as `AutomataflStepEmit.boardRangeConstraints`.

Without these the board columns are UNCONSTRAINED felts entering only the source read, the
`write_mid_witnessed` rewrite and the base-4 pack gate, so a witness could carry
`old[c] = 4`: the circuit's source-non-vacuum bit `anz = forced_ge0(fp − 1)` is then SATISFIED (the
cell "carries a piece") while the reference `codeToParticle 4 = vacuum` (an EMPTY cell) — the
descriptor and the reference genuinely DISAGREE on the whole window `fp ∈ [4, p)`, and the 5-bit
`SMALL_RBITS` comparison supplies no a-priori window of its own. That makes the Leg R capstone FALSE
over satisfying witnesses. These `KK` + `KK` membership gates close it, and they are what makes the
OLD-board validity envelope a THEOREM of the descriptor (`boardvalid_of_sat`) rather than an
`hvalid` hypothesis carried into the capstone. The MID columns are range-checked on the same footing
so the CLAIMED resolved board is decodable too (the refinement's conclusion is about
`boardDecode mid`). -/
def boardRangeConstraints : List VmConstraint2 :=
  ((List.range KK).map (fun c => cg (memberExpr (old c) [0, 1, 2, 3])))
  ++ ((List.range KK).map (fun c => cg (memberExpr (mid c) [0, 1, 2, 3])))

/-! ### §5-add — CHUNK-1 STAGED-ADDITIVE constraint families (AUTOMATAFL-MIGRATION-DESIGN Δ1/Δ3/Δ5).
Emitted BETWEEN `writeMid` and the commitment, so the commitment stays LAST (its membership + the
commit-seam proofs are undisturbed) and each preceding family shifts by exactly three `++` nodes. -/

/-- (Δ1) The inclusive-occlusion `msumIncl` head for the move whose occlusion block is at `o`, output
column `cMsumIncl w`: `msumIncl − cMsum − Σ_k (eto[k]·line[k] − eto[k]·osrc[k]·line[k]) = 0`, i.e.
`msumIncl = cMsum + Σ_k eto[k]·(1−osrc[k])·line[k]`. The endpoint fold collapses through the `eto`
one-hot to `(1−osrc[dst])·line[dst]` — the destination term the OLD strictly-interior `msum` omits. -/
def msumInclHead (w o : Nat) : Head :=
  (List.range NN).foldl (fun h k =>
    (h.addProd (-1) [cEto o k, cLine o k]).addProd 1 [cEto o k, cOsrc o k, cLine o k])
    ((Head.lin 1 (cMsumIncl w)).addLin (-1) (cMsum o))

/-- The inclusive-occlusion family for one move: the `msumIncl` definition gate, then
`occIncl = [msumIncl ≥ 1]` (a `forced_ge0` at the WIDER `3n+3` threshold, still within `RBITS`). -/
def inclOcclusionOne (w o : Nat) : List VmConstraint2 :=
  [ cgH (msumInclHead w o) ]
  ++ forcedGe0Constraints ((Head.lin 1 (cMsumIncl w)).addConst (-1)) (cOccIncl w) (occInclBit w 0)

def inclOcclusionConstraints : List VmConstraint2 :=
  inclOcclusionOne 0 (occBase 0) ++ inclOcclusionOne 1 (occBase 1)

/-- (Δ3) The OLD cell at piece `i`'s landing square, read through the write leg's destination
one-hots: `landOld − Σ_{y,x} wDstRow_i[y]·wDstCol_i[x]·old[y·n+x] = 0`. -/
def landOldHead (i : Nat) : Head :=
  (List.range NN).foldl (fun h y =>
    (List.range NN).foldl (fun h2 x =>
      h2.addProd (-1) [wDstRow i y, wDstCol i x, old (y * NN + x)]) h) (Head.lin 1 (cLandOld i))

/-- The non-leaver family for one piece: `landOld`, `landNz = [landOld ≥ 1]` (`SMALL_RBITS`), and
`nonLeave = landNz·(1 − carry_other)` (gate `nonLeave − landNz + landNz·carry_other = 0`). -/
def nonLeaveOne (i : Nat) : List VmConstraint2 :=
  [ cgH (landOldHead i) ]
  ++ forcedGe0ConstraintsN ((Head.lin 1 (cLandOld i)).addConst (-1)) (cLandNz i) (landNzBit i 0)
       SMALL_RBITS
  ++ [ cgH (((Head.lin 1 (cNonLeave i)).addLin (-1) (cLandNz i)).addProd 1
              [cLandNz i, carryCol (1 - i)]) ]

def nonLeaveConstraints : List VmConstraint2 :=
  nonLeaveOne 0 ++ nonLeaveOne 1

/-- (Δ5) The resolvable / merge-confluence surface: pin the two INTERPOLATED landing coordinates as
columns (the same `destHead` interpolation the write leg uses), test their equality (`resEq`), then
the boolean logic `resolvable = ¬merge · ¬badA · ¬badB` with `merge = bothCarry · resEq · ¬identical`
(`identical = eq_ff · eq_tt`, the dedup exemption) and `bad_i = carry_i · nonLeave_i`. At `m = 2` the
`merge` term catches the chain-confluence case (A flows through onto B's landing) that `collide`
(which compares RAW `to`) misses. -/
def resolvableConstraints : List VmConstraint2 :=
  let a := mvBase 0; let b := mvBase 1
  [ cgH ((Head.lin 1 (cDestX 0)).append ((destHead (cTx a) (cTx b) cFtA).scale (-1)))
  , cgH ((Head.lin 1 (cDestY 0)).append ((destHead (cTy a) (cTy b) cFtA).scale (-1)))
  , cgH ((Head.lin 1 (cDestX 1)).append ((destHead (cTx b) (cTx a) cFtB).scale (-1)))
  , cgH ((Head.lin 1 (cDestY 1)).append ((destHead (cTy b) (cTy a) cFtB).scale (-1))) ]
  ++ eqCoordsConstraints (cDestX 0) (cDestY 0) (cDestX 1) (cDestY 1) resEqBase
  ++ [ prodPin cIdent (cEqBit (eqBase 0)) (cEqBit (eqBase 1))       -- identical = eq_ff · eq_tt
     , prodPin cBothCarry cCarryA cCarryB
     , prodPin cMc1 cBothCarry cResEq                               -- bothCarry ∧ landings coincide
     , notBitPin cNotIdent cIdent
     , prodPin cMerge cMc1 cNotIdent                               -- merge conflict
     , prodPin cBadA cCarryA (cNonLeave 0)
     , prodPin cBadB cCarryB (cNonLeave 1)
     , notBitPin cNMerge cMerge
     , notBitPin cNBadA cBadA
     , notBitPin cNBadB cBadB
     , prodPin cR1 cNMerge cNBadA
     , prodPin cResolvable cR1 cNBadB ]                            -- resolvable = ¬merge·¬badA·¬badB

/-! ### §5-add2 — CHUNK-3 STAGED-ADDITIVE constraint families (the corrected carry + board rewrite).
Emitted BETWEEN `resolvable` and the commitment, so the commitment stays LAST (its membership + the
commit-seam proofs are undisturbed) and each preceding family shifts by exactly two more `++` nodes. -/

/-- The source-non-vacuum bit of piece `i` (`nz_0 = anz`, `nz_1 = bnz`). -/
def nzCol (i : Nat) : Nat := if i == 0 then cAnz else cBnz
/-- The CORRECTED-carry column of piece `i` (the `cCarryV2` staging output). -/
def carryV2Col (i : Nat) : Nat := cCarryV2 i

/-- `cCv2 = cCv1·(1−occIncl)` gate: `cCv2 − cCv1 + cCv1·occIncl = 0` (degree 2). -/
def cv2Head (i : Nat) : Head :=
  ((Head.lin 1 (cCv2 i)).addProd (-1) [cCv1 i]).addProd 1 [cCv1 i, cOccIncl i]
/-- `cCarryV2 = cCv2·(1−nonLeave)` gate: `cCarryV2 − cCv2 + cCv2·nonLeave = 0` (degree 2). -/
def carryV2Head (i : Nat) : Head :=
  ((Head.lin 1 (cCarryV2 i)).addProd (-1) [cCv2 i]).addProd 1 [cCv2 i, cNonLeave i]

/-- The corrected-carry family for one piece: `cCv1 = surv·nz` (degree 2), then the two staged
`(1−occIncl)` / `(1−nonLeave)` gates. The product `surv·nz·(1−occIncl)·(1−nonLeave)` is thus pinned
into the single column `cCarryV2 i` with every gate degree ≤ 2. -/
def carryV2One (i : Nat) : List VmConstraint2 :=
  [ prodPin (cCv1 i) cSurv (nzCol i)
  , cgH (cv2Head i)
  , cgH (carryV2Head i) ]

def carryV2Constraints : List VmConstraint2 := carryV2One 0 ++ carryV2One 1

/-- The `cWBoardV2[c]` rewrite head — `writeCellHead` with the OLD `carryCol` replaced by `cCarryV2`
and the output cell `cWBoardV2 c` (the emitted analog of `writeBoard`'s cell, driven by the corrected
carry). Same one-hot placement/vacation + inclusion–exclusion structure, so the same degree-7 max. -/
def writeCellV2Head (c : Nat) : Head :=
  let x := c % NN; let y := c / NN
  let base := (List.range 2).foldl (fun h i =>
    ((h.addProd (-1) [carryV2Col i, wSrcRow i y, wSrcCol i x, old c]).addProd (-1)
        [carryV2Col i, wDstRow i y, wDstCol i x, old c]).addProd 1
        [carryV2Col i, wDstRow i y, wDstCol i x, particleCol i]) (Head.lin 1 (old c))
  let full := (List.range 2).foldl (fun h i =>
    (List.range 2).foldl (fun h2 j =>
      if i == j then h2 else
        h2.addProd 1 [carryV2Col i, wSrcRow i y, wSrcCol i x,
                      carryV2Col j, wDstRow j y, wDstCol j x, old c]) h) base
  let ie := ((full.addProd 1 [carryV2Col 0, wSrcRow 0 y, wSrcCol 0 x,
                              carryV2Col 1, wSrcRow 1 y, wSrcCol 1 x, old c]).addProd 1
              [carryV2Col 0, wDstRow 0 y, wDstCol 0 x,
               carryV2Col 1, wDstRow 1 y, wDstCol 1 x, old c]).addProd (-1)
              [carryV2Col 0, wDstRow 0 y, wDstCol 0 x,
               carryV2Col 1, wDstRow 1 y, wDstCol 1 x, particleCol 1]
  (Head.lin 1 (cWBoardV2 c)).append (ie.scale (-1))

/-- `cMidV2[c] = cResolvable·cWBoardV2[c] + (1−cResolvable)·old[c]` gate:
`cMidV2 − cResolvable·cWBoardV2 − old + cResolvable·old = 0` (degree 2) — the emitted analog of
`resolveMoves = if resolvableB then writeBoard … else b`, cell-wise. -/
def midV2CellHead (c : Nat) : Head :=
  (((Head.lin 1 (cMidV2 c)).addProd (-1) [cResolvable, cWBoardV2 c]).addLin (-1) (old c)).addProd 1
    [cResolvable, old c]

/-- The corrected board rewrite: the `KK` `cWBoardV2` writeBoard-cell gates, then the `KK`
`cResolvable`-gated `cMidV2` cells. -/
def midV2Constraints : List VmConstraint2 :=
  ((List.range KK).map (fun c => cgH (writeCellV2Head c)))
  ++ ((List.range KK).map (fun c => cgH (midV2CellHead c)))

/-- The flat Leg-R constraint list, in `emit_resolution`'s emission order: the `one` pin, the shared
witnessed auto-read block, `validate_move` for both moves, then `validate_occlusion` for both moves
(each with the OTHER move as its passable moving source). -/
def resolveConstraints : List VmConstraint2 :=
  onePin :: (boardRangeConstraints
    ++ autoReadConstraints
    ++ validateMove (mvBase 0) ++ validateMove (mvBase 1)
    ++ validateOcclusion (mvBase 0) (occBase 0) (mvBase 1)
    ++ validateOcclusion (mvBase 1) (occBase 1) (mvBase 0)
    ++ srcNonVacConstraints                                      -- leg 3
    ++ patternBitConstraints ++ selectionConstraints             -- leg 4
    ++ carryConstraints                                          -- leg 5
    ++ flowThroughConstraints                                    -- leg 6
    ++ writeMidConstraints                                       -- leg 7
    ++ inclOcclusionConstraints                                  -- CHUNK-1 Δ1: inclusive occlusion
    ++ nonLeaveConstraints                                       -- CHUNK-1 Δ3: non-leaver bit
    ++ resolvableConstraints                                     -- CHUNK-1 Δ5: resolvable surface
    ++ carryV2Constraints                                        -- CHUNK-3: corrected carry
    ++ midV2Constraints                                          -- CHUNK-3: corrected board rewrite
    ++ commitBoardsConstraints)                                  -- leg 8

/-! ## §5b — `descN n`: the board size as an explicit PARAMETER (AUTOMATAFL-NGENERIC-DESIGN §4).

`NGen` holds an `n`-parametric copy of the ENTIRE Leg-R layout + family stack — identical in shape to
the `NN`-frozen defs above but threading the board dimension `n` through every width, every column
offset, and every `List.range` fold (`COORD_RBITS`, `KK = n*n`, the move / occlusion / write blocks).
The pure `Head`/gate combinators (`cgH`, `oneHotConstraints`, `forcedGe0Constraints`,
`eqScalarConstraints`, the pack combinators, …) are `n`-agnostic and REUSED as-is.

`automataflResolveDescN 2` is DEFINITIONALLY EQUAL to the byte-golden `automataflResolveDesc` object
below (same numerals, same list) — so every existing byte-golden `#guard` and every `by decide`
gate-membership proof over `automataflResolveDesc.constraints` is preserved unchanged.

The commitment leg (`NGen.commitBoardsConstraints`) is the PACKED base-4 family and is fully
`n`-generic: `⌈n²/15⌉` pack gates per board at EVERY `n`, so the `n = 11` commitment shape IS pinned
below (§7). It replaced a single zero-padded 8-lane `MerkleHash8` leaf that was well-defined only at
`k = n² ≤ 8`, and it drops that leg's Poseidon2 soundness assumption entirely. -/
namespace NGen

-- Several layout offsets (`cFx b := b + 0`, `cIvDsq o := o + 0`, …) carry `n` only for uniform
-- arity and never read it; the unused-binder lint would fire on each, so it is disabled in NGen.
set_option linter.unusedVariables false

def KK (n : Nat) : Nat := n * n
def COORD_RBITS (n : Nat) : Nat := if n ≤ 1 then 1 else Nat.log2 (n - 1) + 1
def old (n : Nat) (i : Nat) : Nat := i
def mid (n : Nat) (i : Nat) : Nat := (KK n) + i
def ONE (n : Nat) : Nat := 2 * (KK n)
def AX_C (n : Nat) : Nat := 2 * (KK n) + 1
def AY_C (n : Nat) : Nat := 2 * (KK n) + 2
def axLo (n : Nat) : Nat := 2 * (KK n) + 3
def axHi (n : Nat) : Nat := 2 * (KK n) + 3 + (COORD_RBITS n)
def ayLo (n : Nat) : Nat := 2 * (KK n) + 3 + 2 * (COORD_RBITS n)
def ayHi (n : Nat) : Nat := 2 * (KK n) + 3 + 3 * (COORD_RBITS n)
def selAutoRow (n : Nat) (y : Nat) : Nat := 2 * (KK n) + 3 + 4 * (COORD_RBITS n) + y
def selAutoCol (n : Nat) (x : Nat) : Nat := 2 * (KK n) + 3 + 4 * (COORD_RBITS n) + n + x
def AUTO_BLOCK_WIDTH (n : Nat) : Nat := 2 + 4 * (COORD_RBITS n) + 2 * n
def MV_BLOCK_WIDTH (n : Nat) : Nat := 4 + 8 * (COORD_RBITS n) + 6 + 1 + 2 * n
def mvBase (n : Nat) (which : Nat) : Nat := 2 * (KK n) + 1 + (AUTO_BLOCK_WIDTH n) + (MV_BLOCK_WIDTH n) * which
def cFx (n : Nat) (b : Nat) : Nat := b + 0
def cFy (n : Nat) (b : Nat) : Nat := b + 1
def cTx (n : Nat) (b : Nat) : Nat := b + 2
def cTy (n : Nat) (b : Nat) : Nat := b + 3
def cFxLo (n : Nat) (b : Nat) : Nat := b + 4
def cFxHi (n : Nat) (b : Nat) : Nat := b + 4 + (COORD_RBITS n)
def cFyLo (n : Nat) (b : Nat) : Nat := b + 4 + 2 * (COORD_RBITS n)
def cFyHi (n : Nat) (b : Nat) : Nat := b + 4 + 3 * (COORD_RBITS n)
def cTxLo (n : Nat) (b : Nat) : Nat := b + 4 + 4 * (COORD_RBITS n)
def cTxHi (n : Nat) (b : Nat) : Nat := b + 4 + 5 * (COORD_RBITS n)
def cTyLo (n : Nat) (b : Nat) : Nat := b + 4 + 6 * (COORD_RBITS n)
def cTyHi (n : Nat) (b : Nat) : Nat := b + 4 + 7 * (COORD_RBITS n)
def mvPost (n : Nat) (b : Nat) : Nat := b + 4 + 8 * (COORD_RBITS n)
def cDsq (n : Nat) (b : Nat) : Nat := (mvPost n) b + 0
def cDistinctInv (n : Nat) (b : Nat) : Nat := (mvPost n) b + 1
def cFa (n : Nat) (b : Nat) : Nat := (mvPost n) b + 2
def cFnaInv (n : Nat) (b : Nat) : Nat := (mvPost n) b + 3
def cTa (n : Nat) (b : Nat) : Nat := (mvPost n) b + 4
def cTnaInv (n : Nat) (b : Nat) : Nat := (mvPost n) b + 5
def cFp (n : Nat) (b : Nat) : Nat := (mvPost n) b + 6
def cSelRow (n : Nat) (b j : Nat) : Nat := (mvPost n) b + 7 + j
def cSelCol (n : Nat) (b j : Nat) : Nat := (mvPost n) b + 7 + n + j
def EQ_BLOCK_WIDTH (n : Nat) : Nat := 3 + RBITS
def OCC_BLOCK_WIDTH (n : Nat) : Nat := 3 * (EQ_BLOCK_WIDTH n) + 7 * n + 3 + RBITS
def occBase (n : Nat) (which : Nat) : Nat :=
  2 * (KK n) + 1 + (AUTO_BLOCK_WIDTH n) + (MV_BLOCK_WIDTH n) * 2 + (OCC_BLOCK_WIDTH n) * which
def cIvDsq (n : Nat) (o : Nat) : Nat := o + 0
def cIvNeq (n : Nat) (o : Nat) : Nat := o + 1
def ivNeqBit (n : Nat) (o k : Nat) : Nat := o + 2 + k
def cIv (n : Nat) (o : Nat) : Nat := o + 2 + RBITS
def occVec (n : Nat) (o : Nat) : Nat := o + (EQ_BLOCK_WIDTH n)
def cLine (n : Nat) (o k : Nat) : Nat := (occVec n) o + k
def cEty (n : Nat) (o j : Nat) : Nat := (occVec n) o + n + j
def cEtx (n : Nat) (o j : Nat) : Nat := (occVec n) o + 2 * n + j
def cEfrom (n : Nat) (o j : Nat) : Nat := (occVec n) o + 3 * n + j
def cEto (n : Nat) (o j : Nat) : Nat := (occVec n) o + 4 * n + j
def cSeg (n : Nat) (o k : Nat) : Nat := (occVec n) o + 5 * n + k
def occEq (n : Nat) (o : Nat) : Nat := (occVec n) o + 6 * n
def cEqxDsq (n : Nat) (o : Nat) : Nat := (occEq n) o + 0
def cEqxNeq (n : Nat) (o : Nat) : Nat := (occEq n) o + 1
def eqxBit (n : Nat) (o k : Nat) : Nat := (occEq n) o + 2 + k
def cEqx (n : Nat) (o : Nat) : Nat := (occEq n) o + 2 + RBITS
def cEqyDsq (n : Nat) (o : Nat) : Nat := (occEq n) o + (EQ_BLOCK_WIDTH n) + 0
def cEqyNeq (n : Nat) (o : Nat) : Nat := (occEq n) o + (EQ_BLOCK_WIDTH n) + 1
def eqyBit (n : Nat) (o k : Nat) : Nat := (occEq n) o + (EQ_BLOCK_WIDTH n) + 2 + k
def cEqy (n : Nat) (o : Nat) : Nat := (occEq n) o + (EQ_BLOCK_WIDTH n) + 2 + RBITS
def occTail (n : Nat) (o : Nat) : Nat := (occEq n) o + 2 * (EQ_BLOCK_WIDTH n)
def cOg (n : Nat) (o : Nat) : Nat := (occTail n) o + 0
def cOsrc (n : Nat) (o j : Nat) : Nat := (occTail n) o + 1 + j
def cMsum (n : Nat) (o : Nat) : Nat := (occTail n) o + 1 + n
def cOcc (n : Nat) (o : Nat) : Nat := (occTail n) o + 2 + n
def occBit (n : Nat) (o k : Nat) : Nat := (occTail n) o + 3 + n + k
def RES0 (n : Nat) : Nat := 2 * (KK n) + 1 + (AUTO_BLOCK_WIDTH n) + (MV_BLOCK_WIDTH n) * 2 + (OCC_BLOCK_WIDTH n) * 2
def cAnz (n : Nat) : Nat := (RES0 n)
def anzBit (n : Nat) (k : Nat) : Nat := (RES0 n) + 1 + k
def cBnz (n : Nat) : Nat := (RES0 n) + 1 + SMALL_RBITS
def bnzBit (n : Nat) (k : Nat) : Nat := (RES0 n) + 2 + SMALL_RBITS + k
def NZ_WIDTH (n : Nat) : Nat := 2 * (1 + SMALL_RBITS)
def eqBase (n : Nat) (i : Nat) : Nat := (RES0 n) + (NZ_WIDTH n) + (EQ_BLOCK_WIDTH n) * i
def cEqDsq (n : Nat) (e : Nat) : Nat := e + 0
def cEqNeq (n : Nat) (e : Nat) : Nat := e + 1
def eqBitAt (n : Nat) (e k : Nat) : Nat := e + 2 + k
def cEqBit (n : Nat) (e : Nat) : Nat := e + 2 + RBITS
def SEL0 (n : Nat) : Nat := (RES0 n) + (NZ_WIDTH n) + 4 * (EQ_BLOCK_WIDTH n)
def cFork (n : Nat) : Nat := (SEL0 n) + 0
def cNeqFf (n : Nat) : Nat := (SEL0 n) + 1
def cCol1 (n : Nat) : Nat := (SEL0 n) + 2
def cCol2 (n : Nat) : Nat := (SEL0 n) + 3
def cCollide (n : Nat) : Nat := (SEL0 n) + 4
def cSurv (n : Nat) : Nat := (SEL0 n) + 5
def CAR0 (n : Nat) : Nat := (SEL0 n) + 6
def cSa1 (n : Nat) : Nat := (CAR0 n) + 0
def cCarryA (n : Nat) : Nat := (CAR0 n) + 1
def cSb1 (n : Nat) : Nat := (CAR0 n) + 2
def cCarryB (n : Nat) : Nat := (CAR0 n) + 3
def FT0 (n : Nat) : Nat := (CAR0 n) + 4
def cNBnz (n : Nat) : Nat := (FT0 n) + 0
def cNOccb (n : Nat) : Nat := (FT0 n) + 1
def cNEqba (n : Nat) : Nat := (FT0 n) + 2
def cFa1 (n : Nat) : Nat := (FT0 n) + 3
def cFa2 (n : Nat) : Nat := (FT0 n) + 4
def cFa3 (n : Nat) : Nat := (FT0 n) + 5
def cFtA (n : Nat) : Nat := (FT0 n) + 6
def cNAnz (n : Nat) : Nat := (FT0 n) + 7
def cNOcca (n : Nat) : Nat := (FT0 n) + 8
def cNEqab (n : Nat) : Nat := (FT0 n) + 9
def cFb1 (n : Nat) : Nat := (FT0 n) + 10
def cFb2 (n : Nat) : Nat := (FT0 n) + 11
def cFb3 (n : Nat) : Nat := (FT0 n) + 12
def cFtB (n : Nat) : Nat := (FT0 n) + 13
def WR0 (n : Nat) : Nat := (FT0 n) + 14
def WR_PIECE_WIDTH (n : Nat) : Nat := 4 * n
def wSrcRow (n : Nat) (i j : Nat) : Nat := (WR0 n) + (WR_PIECE_WIDTH n) * i + j
def wSrcCol (n : Nat) (i j : Nat) : Nat := (WR0 n) + (WR_PIECE_WIDTH n) * i + n + j
def wDstRow (n : Nat) (i j : Nat) : Nat := (WR0 n) + (WR_PIECE_WIDTH n) * i + 2 * n + j
def wDstCol (n : Nat) (i j : Nat) : Nat := (WR0 n) + (WR_PIECE_WIDTH n) * i + 3 * n + j
def MH0 (n : Nat) : Nat := (WR0 n) + (WR_PIECE_WIDTH n) * 2
def RFC (n : Nat) : Nat := AutomataflCommit.feltCount n
def packOldFelt (n j : Nat) : Nat := (MH0 n) + j
def packMidFelt (n j : Nat) : Nat := (MH0 n) + (RFC n) + j
-- CHUNK-1 STAGED-ADDITIVE tail columns (parametric twins of §2.4).
def INCL0 (n : Nat) : Nat := (MH0 n) + 2 * (RFC n)
def INCL_MV_WIDTH : Nat := 2 + RBITS
def inclBase (n : Nat) (w : Nat) : Nat := (INCL0 n) + INCL_MV_WIDTH * w
def cMsumIncl (n : Nat) (w : Nat) : Nat := (inclBase n) w + 0
def cOccIncl (n : Nat) (w : Nat) : Nat := (inclBase n) w + 1
def occInclBit (n : Nat) (w k : Nat) : Nat := (inclBase n) w + 2 + k
def NL0 (n : Nat) : Nat := (INCL0 n) + 2 * INCL_MV_WIDTH
def NL_PIECE_WIDTH : Nat := 3 + SMALL_RBITS
def nlBase (n : Nat) (i : Nat) : Nat := (NL0 n) + NL_PIECE_WIDTH * i
def cLandOld (n : Nat) (i : Nat) : Nat := (nlBase n) i + 0
def cLandNz (n : Nat) (i : Nat) : Nat := (nlBase n) i + 1
def landNzBit (n : Nat) (i k : Nat) : Nat := (nlBase n) i + 2 + k
def cNonLeave (n : Nat) (i : Nat) : Nat := (nlBase n) i + 2 + SMALL_RBITS
def RESR0 (n : Nat) : Nat := (NL0 n) + 2 * NL_PIECE_WIDTH
def cDestX (n : Nat) (i : Nat) : Nat := (RESR0 n) + 2 * i
def cDestY (n : Nat) (i : Nat) : Nat := (RESR0 n) + 2 * i + 1
def resEqBase (n : Nat) : Nat := (RESR0 n) + 4
def cResEq (n : Nat) : Nat := (cEqBit n) (resEqBase n)
def RESR_LOGIC (n : Nat) : Nat := (resEqBase n) + (EQ_BLOCK_WIDTH n)
def cIdent (n : Nat) : Nat := (RESR_LOGIC n) + 0
def cBothCarry (n : Nat) : Nat := (RESR_LOGIC n) + 1
def cMc1 (n : Nat) : Nat := (RESR_LOGIC n) + 2
def cNotIdent (n : Nat) : Nat := (RESR_LOGIC n) + 3
def cMerge (n : Nat) : Nat := (RESR_LOGIC n) + 4
def cBadA (n : Nat) : Nat := (RESR_LOGIC n) + 5
def cBadB (n : Nat) : Nat := (RESR_LOGIC n) + 6
def cNMerge (n : Nat) : Nat := (RESR_LOGIC n) + 7
def cNBadA (n : Nat) : Nat := (RESR_LOGIC n) + 8
def cNBadB (n : Nat) : Nat := (RESR_LOGIC n) + 9
def cR1 (n : Nat) : Nat := (RESR_LOGIC n) + 10
def cResolvable (n : Nat) : Nat := (RESR_LOGIC n) + 11
def RESR_END (n : Nat) : Nat := (RESR_LOGIC n) + 12
-- CHUNK-3 STAGED-ADDITIVE tail columns (parametric twins of §2.5).
def CV2_0 (n : Nat) : Nat := RESR_END n
def cv2Base (n : Nat) (i : Nat) : Nat := (CV2_0 n) + 3 * i
def cCv1 (n : Nat) (i : Nat) : Nat := (cv2Base n) i + 0
def cCv2 (n : Nat) (i : Nat) : Nat := (cv2Base n) i + 1
def cCarryV2 (n : Nat) (i : Nat) : Nat := (cv2Base n) i + 2
def MIDV2_0 (n : Nat) : Nat := (CV2_0 n) + 6
def cWBoardV2 (n : Nat) (c : Nat) : Nat := (MIDV2_0 n) + c
def cMidV2 (n : Nat) (c : Nat) : Nat := (MIDV2_0 n) + (KK n) + c
def MV2_END (n : Nat) : Nat := (MIDV2_0 n) + 2 * (KK n)
def R_WIDTH (n : Nat) : Nat := MV2_END n
def AUTO_PI_BASE (n : Nat) : Nat := 16 + 2 * (RFC n)
def R_PI_COUNT (n : Nat) : Nat := (AUTO_PI_BASE n) + 2
def decomposeConstraints (n : Nat) (col loBit0 hiBit0 : Nat) : List VmConstraint2 :=
  rangeNonnegConstraints (Head.lin 1 col) loBit0 (COORD_RBITS n)
  ++ rangeNonnegConstraints ((Head.c ((n : ℤ) - 1)).addLin (-1) col) hiBit0 (COORD_RBITS n)
def selRowCols (n : Nat) (b : Nat) : List Nat := (List.range n).map ((cSelRow n) b)
def selColCols (n : Nat) (b : Nat) : List Nat := (List.range n).map ((cSelCol n) b)
def sourceReadHead (n : Nat) (b : Nat) : Head :=
  (List.range n).foldl (fun h y =>
    (List.range n).foldl (fun h2 x =>
      h2.addProd (-1) [(cSelRow n) b y, (cSelCol n) b x, (old n) (y * n + x)]) h) (Head.lin 1 ((cFp n) b))
def dsqHead (n : Nat) (b : Nat) : Head :=
  ((((((Head.lin 1 ((cDsq n) b)).addProd (-1) [(cFx n) b, (cFx n) b]).addProd 2 [(cFx n) b, (cTx n) b]).addProd (-1)
      [(cTx n) b, (cTx n) b]).addProd (-1) [(cFy n) b, (cFy n) b]).addProd 2 [(cFy n) b, (cTy n) b]).addProd (-1)
      [(cTy n) b, (cTy n) b]
def autoDistHead (n : Nat) (outCol xc yc : Nat) : Head :=
  ((((((Head.lin 1 outCol).addProd (-1) [xc, xc]).addProd 2 [xc, (AX_C n)]).addProd (-1)
      [(AX_C n), (AX_C n)]).addProd (-1) [yc, yc]).addProd 2 [yc, (AY_C n)]).addProd (-1) [(AY_C n), (AY_C n)]
def autoPinHead (n : Nat) : Head :=
  (List.range n).foldl (fun h (y : Nat) =>
    (List.range n).foldl (fun h2 (x : Nat) =>
      h2.addProd 1 [(selAutoRow n) y, (selAutoCol n) x, (old n) (y * n + x)]) h) (Head.c (-AUTO_CODE))
def autoReadConstraints (n : Nat) : List VmConstraint2 :=
  (decomposeConstraints n) (AX_C n) (axLo n) (axHi n)
  ++ (decomposeConstraints n) (AY_C n) (ayLo n) (ayHi n)
  ++ oneHotAtCol ((List.range n).map (selAutoRow n)) (AY_C n)        -- auto row one-hot @ ay
  ++ oneHotAtCol ((List.range n).map (selAutoCol n)) (AX_C n)        -- auto col one-hot @ ax
  ++ [ cgH (autoPinHead n) ]
def rookAlignHead (n : Nat) (b : Nat) : Head :=
  (((Head.zero.addProd 1 [(cFx n) b, (cFy n) b]).addProd (-1) [(cFx n) b, (cTy n) b]).addProd (-1)
      [(cTx n) b, (cFy n) b]).addProd 1 [(cTx n) b, (cTy n) b]
def validateMove (n : Nat) (b : Nat) : List VmConstraint2 :=
  (decomposeConstraints n) ((cFx n) b) ((cFxLo n) b) ((cFxHi n) b)
  ++ (decomposeConstraints n) ((cFy n) b) ((cFyLo n) b) ((cFyHi n) b)
  ++ (decomposeConstraints n) ((cTx n) b) ((cTxLo n) b) ((cTxHi n) b)
  ++ (decomposeConstraints n) ((cTy n) b) ((cTyLo n) b) ((cTyHi n) b)
  ++ [ cgH ((rookAlignHead n) b) ]                                       -- rook-aligned
  ++ [ cgH ((dsqHead n) b) ]                                             -- dsq definition
  ++ [ cg (gCondNonzero (ONE n) ((cDsq n) b) ((cDistinctInv n) b)) ]            -- distinct: dsq ≠ 0
  ++ [ cgH ((autoDistHead n) ((cFa n) b) ((cFx n) b) ((cFy n) b)) ]                 -- fa = |frm − auto|²
  ++ [ cg (gCondNonzero (ONE n) ((cFa n) b) ((cFnaInv n) b)) ]                  -- frm ≠ auto
  ++ [ cgH ((autoDistHead n) ((cTa n) b) ((cTx n) b) ((cTy n) b)) ]                 -- ta = |to − auto|²
  ++ [ cg (gCondNonzero (ONE n) ((cTa n) b) ((cTnaInv n) b)) ]                  -- to ≠ auto
  ++ oneHotAtCol ((selRowCols n) b) ((cFy n) b)                             -- source row one-hot @ fy
  ++ oneHotAtCol ((selColCols n) b) ((cFx n) b)                             -- source col one-hot @ fx
  ++ [ cgH ((sourceReadHead n) b) ]                                     -- fp == (old n)[n·fy + fx]
def isVerticalConstraints (n : Nat) (b o : Nat) : List VmConstraint2 :=
  eqScalarConstraints ((cFx n) b) ((cTx n) b) ((cIvDsq n) o) ((cIvNeq n) o) ((ivNeqBit n) o 0) ((cIv n) o)
def lineHead (n : Nat) (b o k : Nat) : Head :=
  let hv := (List.range n).foldl (fun h x =>
    h.addProd (-1) [(cIv n) o, (cSelCol n) b x, (old n) (k * n + x)]) (Head.lin 1 ((cLine n) o k))
  (List.range n).foldl (fun h y =>
    (h.addProd (-1) [(cSelRow n) b y, (old n) (y * n + k)]).addProd 1
      [(cIv n) o, (cSelRow n) b y, (old n) (y * n + k)]) hv
def efromHead (n : Nat) (b o j : Nat) : Head :=
  (((Head.lin 1 ((cEfrom n) o j)).addProd (-1) [(cIv n) o, (cSelRow n) b j]).addLin (-1)
      ((cSelCol n) b j)).addProd 1 [(cIv n) o, (cSelCol n) b j]
def etoHead (n : Nat) (o j : Nat) : Head :=
  (((Head.lin 1 ((cEto n) o j)).addProd (-1) [(cIv n) o, (cEty n) o j]).addLin (-1)
      ((cEtx n) o j)).addProd 1 [(cIv n) o, (cEtx n) o j]
def segHead (n : Nat) (o k : Nat) : Head :=
  (List.range k).foldl (fun h j1 =>
    ((List.range n).filter (fun j2 => k < j2)).foldl (fun h2 j2 =>
      (h2.addProd (-1) [(cEfrom n) o j1, (cEto n) o j2]).addProd (-1) [(cEto n) o j1, (cEfrom n) o j2]) h)
    (Head.lin 1 ((cSeg n) o k))
def ogHead (n : Nat) (o : Nat) : Head :=
  (((Head.lin 1 ((cOg n) o)).addProd (-1) [(cIv n) o, (cEqx n) o]).addLin (-1) ((cEqy n) o)).addProd 1
    [(cIv n) o, (cEqy n) o]
def msumHead (n : Nat) (o : Nat) : Head :=
  (List.range n).foldl (fun h k =>
    (h.addProd (-1) [(cSeg n) o k, (cLine n) o k]).addProd 1 [(cSeg n) o k, (cOsrc n) o k, (cLine n) o k])
    (Head.lin 1 ((cMsum n) o))
def validateOcclusion (n : Nat) (b o ob : Nat) : List VmConstraint2 :=
  (isVerticalConstraints n) b o
  ++ (List.range n).map (fun k => cgH ((lineHead n) b o k))
  ++ oneHotAtCol ((List.range n).map ((cEty n) o)) ((cTy n) b)           -- e_to (vertical) @ ty
  ++ oneHotAtCol ((List.range n).map ((cEtx n) o)) ((cTx n) b)           -- e_to (horizontal) @ tx
  ++ (List.range n).map (fun j => cgH ((efromHead n) b o j))
  ++ (List.range n).map (fun j => cgH ((etoHead n) o j))
  ++ (List.range n).map (fun k => cgH ((segHead n) o k))
  ++ eqScalarConstraints ((cFx n) ob) ((cFx n) b) ((cEqxDsq n) o) ((cEqxNeq n) o) ((eqxBit n) o 0) ((cEqx n) o)
  ++ eqScalarConstraints ((cFy n) ob) ((cFy n) b) ((cEqyDsq n) o) ((cEqyNeq n) o) ((eqyBit n) o 0) ((cEqy n) o)
  ++ [ cgH ((ogHead n) o) ]
  ++ oneHotGatedConstraints ((List.range n).map ((cOsrc n) o)) ((cOg n) o)
       ((((Head.zero.addProd 1 [(cIv n) o, (cFy n) ob]).addLin 1 ((cFx n) ob)).addProd (-1) [(cIv n) o, (cFx n) ob]))
  ++ [ cgH ((msumHead n) o) ]
  ++ forcedGe0Constraints ((Head.lin 1 ((cMsum n) o)).addConst (-1)) ((cOcc n) o) ((occBit n) o 0)
def srcNonVacConstraints (n : Nat) : List VmConstraint2 :=
  forcedGe0ConstraintsN ((Head.lin 1 ((cFp n) ((mvBase n) 0))).addConst (-1)) (cAnz n) ((anzBit n) 0) SMALL_RBITS
  ++ forcedGe0ConstraintsN ((Head.lin 1 ((cFp n) ((mvBase n) 1))).addConst (-1)) (cBnz n) ((bnzBit n) 0) SMALL_RBITS
def eqCoordsConstraints (n : Nat) (xa ya xb yb e : Nat) : List VmConstraint2 :=
  [ cgH ((((((Head.lin 1 ((cEqDsq n) e)).addProd (-1) [xa, xa]).addProd 2 [xa, xb]).addProd (-1)
      [xb, xb]).addProd (-1) [ya, ya]).addProd 2 [ya, yb] |>.addProd (-1) [yb, yb]) ]
  ++ forcedGe0Constraints ((Head.lin 1 ((cEqDsq n) e)).addConst (-1)) ((cEqNeq n) e) ((eqBitAt n) e 0)
  ++ [ cgH (((Head.lin 1 ((cEqBit n) e)).addLin 1 ((cEqNeq n) e)).addConst (-1)) ]
def patternBitConstraints (n : Nat) : List VmConstraint2 :=
  let a := (mvBase n) 0; let b := (mvBase n) 1
  (eqCoordsConstraints n) ((cFx n) a) ((cFy n) a) ((cFx n) b) ((cFy n) b) ((eqBase n) 0)   -- eq_ff
  ++ (eqCoordsConstraints n) ((cTx n) a) ((cTy n) a) ((cTx n) b) ((cTy n) b) ((eqBase n) 1) -- eq_tt
  ++ (eqCoordsConstraints n) ((cTx n) a) ((cTy n) a) ((cFx n) b) ((cFy n) b) ((eqBase n) 2) -- eq_ab
  ++ (eqCoordsConstraints n) ((cTx n) b) ((cTy n) b) ((cFx n) a) ((cFy n) a) ((eqBase n) 3) -- eq_ba
def selectionConstraints (n : Nat) : List VmConstraint2 :=
  let eqFf := (cEqBit n) ((eqBase n) 0); let eqTt := (cEqBit n) ((eqBase n) 1)
  [ cgH (((Head.lin 1 (cFork n)).addLin (-1) eqFf).addProd 1 [eqFf, eqTt])   -- fork = eq_ff·(1−eq_tt)
  , notBitPin (cNeqFf n) eqFf
  , prodPin (cCol1 n) eqTt (cNeqFf n)
  , prodPin (cCol2 n) (cCol1 n) (cAnz n)
  , prodPin (cCollide n) (cCol2 n) (cBnz n)
  , cgH (((((Head.lin 1 (cSurv n)).addConst (-1)).addLin 1 (cFork n)).addLin 1 (cCollide n)).addProd (-1)
      [(cFork n), (cCollide n)]) ]
def carryConstraints (n : Nat) : List VmConstraint2 :=
  [ prodPin (cSa1 n) (cSurv n) (cAnz n)
  , cgH (((Head.lin 1 (cCarryA n)).addProd (-1) [(cSa1 n)]).addProd 1 [(cSa1 n), (cOcc n) ((occBase n) 0)])
  , prodPin (cSb1 n) (cSurv n) (cBnz n)
  , cgH (((Head.lin 1 (cCarryB n)).addProd (-1) [(cSb1 n)]).addProd 1 [(cSb1 n), (cOcc n) ((occBase n) 1)]) ]
def flowThroughConstraints (n : Nat) : List VmConstraint2 :=
  let eqAb := (cEqBit n) ((eqBase n) 2); let eqBa := (cEqBit n) ((eqBase n) 3)
  [ notBitPin (cNBnz n) (cBnz n)
  , notBitPin (cNOccb n) ((cOcc n) ((occBase n) 1))
  , notBitPin (cNEqba n) eqBa
  , prodPin (cFa1 n) eqAb (cNBnz n)
  , prodPin (cFa2 n) (cFa1 n) (cSurv n)
  , prodPin (cFa3 n) (cFa2 n) (cNOccb n)
  , prodPin (cFtA n) (cFa3 n) (cNEqba n)
  , notBitPin (cNAnz n) (cAnz n)
  , notBitPin (cNOcca n) ((cOcc n) ((occBase n) 0))
  , notBitPin (cNEqab n) eqAb
  , prodPin (cFb1 n) eqBa (cNAnz n)
  , prodPin (cFb2 n) (cFb1 n) (cSurv n)
  , prodPin (cFb3 n) (cFb2 n) (cNOcca n)
  , prodPin (cFtB n) (cFb3 n) (cNEqab n) ]
def carryCol (n : Nat) (i : Nat) : Nat := if i == 0 then (cCarryA n) else (cCarryB n)
def particleCol (n : Nat) (i : Nat) : Nat := (cFp n) ((mvBase n) i)
def writeEndpointConstraints (n : Nat) : List VmConstraint2 :=
  (List.range 2).flatMap (fun i =>
    let b := (mvBase n) i; let ob := (mvBase n) (1 - i); let ft := if i == 0 then (cFtA n) else (cFtB n)
    oneHotConstraints ((List.range n).map ((wSrcRow n) i)) (Head.lin 1 ((cFy n) b))
    ++ oneHotConstraints ((List.range n).map ((wSrcCol n) i)) (Head.lin 1 ((cFx n) b))
    ++ oneHotConstraints ((List.range n).map ((wDstRow n) i)) (destHead ((cTy n) b) ((cTy n) ob) ft)
    ++ oneHotConstraints ((List.range n).map ((wDstCol n) i)) (destHead ((cTx n) b) ((cTx n) ob) ft))
def writeCellHead (n : Nat) (c : Nat) : Head :=
  let x := c % n; let y := c / n
  let base := (List.range 2).foldl (fun h i =>
    ((h.addProd (-1) [(carryCol n) i, (wSrcRow n) i y, (wSrcCol n) i x, (old n) c]).addProd (-1)
        [(carryCol n) i, (wDstRow n) i y, (wDstCol n) i x, (old n) c]).addProd 1
        [(carryCol n) i, (wDstRow n) i y, (wDstCol n) i x, (particleCol n) i]) (Head.lin 1 ((old n) c))
  let full := (List.range 2).foldl (fun h i =>
    (List.range 2).foldl (fun h2 j =>
      if i == j then h2 else
        h2.addProd 1 [(carryCol n) i, (wSrcRow n) i y, (wSrcCol n) i x,
                      (carryCol n) j, (wDstRow n) j y, (wDstCol n) j x, (old n) c]) h) base
  let ie := ((full.addProd 1 [(carryCol n) 0, (wSrcRow n) 0 y, (wSrcCol n) 0 x,
                              (carryCol n) 1, (wSrcRow n) 1 y, (wSrcCol n) 1 x, (old n) c]).addProd 1
              [(carryCol n) 0, (wDstRow n) 0 y, (wDstCol n) 0 x,
               (carryCol n) 1, (wDstRow n) 1 y, (wDstCol n) 1 x, (old n) c]).addProd (-1)
              [(carryCol n) 0, (wDstRow n) 0 y, (wDstCol n) 0 x,
               (carryCol n) 1, (wDstRow n) 1 y, (wDstCol n) 1 x, (particleCol n) 1]
  (Head.lin 1 ((mid n) c)).append (ie.scale (-1))
def writeMidConstraints (n : Nat) : List VmConstraint2 :=
  (writeEndpointConstraints n) ++ (List.range (KK n)).map (fun c => cgH ((writeCellHead n) c))
-- THE PACKED COMMITMENT, fully `n`-generic: `⌈n²/15⌉` pack gates per board + one `.piBinding` per
-- packed felt + the automaton coordinate. The retired single-padded-leaf `board_root8` was correct
-- only at `k = n*n ≤ 8`; this is the family that makes `descN 11` emit a real commitment.
def commitBoardsConstraints (n : Nat) : List VmConstraint2 :=
  AutomataflCommit.packBoardConstraintsAt n (old n) (packOldFelt n)
  ++ AutomataflCommit.packBoardConstraintsAt n (mid n) (packMidFelt n)
  ++ AutomataflCommit.commitBoardConstraintsAt n (packOldFelt n) 16
  ++ AutomataflCommit.commitBoardConstraintsAt n (packMidFelt n) (16 + RFC n)
  ++ AutomataflCommit.autoCoordCommitConstraints (AX_C n) (AY_C n) (AUTO_PI_BASE n)
def onePin (n : Nat) : VmConstraint2 := cgH ((Head.lin 1 (ONE n)).addConst (-1))
def boardRangeConstraints (n : Nat) : List VmConstraint2 :=
  ((List.range (KK n)).map (fun c => cg (memberExpr ((old n) c) [0, 1, 2, 3])))
  ++ ((List.range (KK n)).map (fun c => cg (memberExpr ((mid n) c) [0, 1, 2, 3])))
-- CHUNK-1 STAGED-ADDITIVE families (parametric twins of §5-add).
def msumInclHead (n : Nat) (w o : Nat) : Head :=
  (List.range n).foldl (fun h k =>
    (h.addProd (-1) [(cEto n) o k, (cLine n) o k]).addProd 1 [(cEto n) o k, (cOsrc n) o k, (cLine n) o k])
    ((Head.lin 1 ((cMsumIncl n) w)).addLin (-1) ((cMsum n) o))
def inclOcclusionOne (n : Nat) (w o : Nat) : List VmConstraint2 :=
  [ cgH ((msumInclHead n) w o) ]
  ++ forcedGe0Constraints ((Head.lin 1 ((cMsumIncl n) w)).addConst (-1)) ((cOccIncl n) w) ((occInclBit n) w 0)
def inclOcclusionConstraints (n : Nat) : List VmConstraint2 :=
  (inclOcclusionOne n) 0 ((occBase n) 0) ++ (inclOcclusionOne n) 1 ((occBase n) 1)
def landOldHead (n : Nat) (i : Nat) : Head :=
  (List.range n).foldl (fun h y =>
    (List.range n).foldl (fun h2 x =>
      h2.addProd (-1) [(wDstRow n) i y, (wDstCol n) i x, (old n) (y * n + x)]) h)
    (Head.lin 1 ((cLandOld n) i))
def nonLeaveOne (n : Nat) (i : Nat) : List VmConstraint2 :=
  [ cgH ((landOldHead n) i) ]
  ++ forcedGe0ConstraintsN ((Head.lin 1 ((cLandOld n) i)).addConst (-1)) ((cLandNz n) i)
       ((landNzBit n) i 0) SMALL_RBITS
  ++ [ cgH (((Head.lin 1 ((cNonLeave n) i)).addLin (-1) ((cLandNz n) i)).addProd 1
              [(cLandNz n) i, (carryCol n) (1 - i)]) ]
def nonLeaveConstraints (n : Nat) : List VmConstraint2 :=
  (nonLeaveOne n) 0 ++ (nonLeaveOne n) 1
def resolvableConstraints (n : Nat) : List VmConstraint2 :=
  let a := (mvBase n) 0; let b := (mvBase n) 1
  [ cgH ((Head.lin 1 ((cDestX n) 0)).append ((destHead ((cTx n) a) ((cTx n) b) (cFtA n)).scale (-1)))
  , cgH ((Head.lin 1 ((cDestY n) 0)).append ((destHead ((cTy n) a) ((cTy n) b) (cFtA n)).scale (-1)))
  , cgH ((Head.lin 1 ((cDestX n) 1)).append ((destHead ((cTx n) b) ((cTx n) a) (cFtB n)).scale (-1)))
  , cgH ((Head.lin 1 ((cDestY n) 1)).append ((destHead ((cTy n) b) ((cTy n) a) (cFtB n)).scale (-1))) ]
  ++ (eqCoordsConstraints n) ((cDestX n) 0) ((cDestY n) 0) ((cDestX n) 1) ((cDestY n) 1) (resEqBase n)
  ++ [ prodPin (cIdent n) ((cEqBit n) ((eqBase n) 0)) ((cEqBit n) ((eqBase n) 1))
     , prodPin (cBothCarry n) (cCarryA n) (cCarryB n)
     , prodPin (cMc1 n) (cBothCarry n) (cResEq n)
     , notBitPin (cNotIdent n) (cIdent n)
     , prodPin (cMerge n) (cMc1 n) (cNotIdent n)
     , prodPin (cBadA n) (cCarryA n) ((cNonLeave n) 0)
     , prodPin (cBadB n) (cCarryB n) ((cNonLeave n) 1)
     , notBitPin (cNMerge n) (cMerge n)
     , notBitPin (cNBadA n) (cBadA n)
     , notBitPin (cNBadB n) (cBadB n)
     , prodPin (cR1 n) (cNMerge n) (cNBadA n)
     , prodPin (cResolvable n) (cR1 n) (cNBadB n) ]
-- CHUNK-3 STAGED-ADDITIVE families (parametric twins of §5-add2).
def nzCol (n : Nat) (i : Nat) : Nat := if i == 0 then (cAnz n) else (cBnz n)
def carryV2Col (n : Nat) (i : Nat) : Nat := (cCarryV2 n) i
def cv2Head (n : Nat) (i : Nat) : Head :=
  ((Head.lin 1 ((cCv2 n) i)).addProd (-1) [(cCv1 n) i]).addProd 1 [(cCv1 n) i, (cOccIncl n) i]
def carryV2Head (n : Nat) (i : Nat) : Head :=
  ((Head.lin 1 ((cCarryV2 n) i)).addProd (-1) [(cCv2 n) i]).addProd 1 [(cCv2 n) i, (cNonLeave n) i]
def carryV2One (n : Nat) (i : Nat) : List VmConstraint2 :=
  [ prodPin ((cCv1 n) i) (cSurv n) ((nzCol n) i)
  , cgH ((cv2Head n) i)
  , cgH ((carryV2Head n) i) ]
def carryV2Constraints (n : Nat) : List VmConstraint2 := (carryV2One n) 0 ++ (carryV2One n) 1
def writeCellV2Head (n : Nat) (c : Nat) : Head :=
  let x := c % n; let y := c / n
  let base := (List.range 2).foldl (fun h i =>
    ((h.addProd (-1) [(carryV2Col n) i, (wSrcRow n) i y, (wSrcCol n) i x, (old n) c]).addProd (-1)
        [(carryV2Col n) i, (wDstRow n) i y, (wDstCol n) i x, (old n) c]).addProd 1
        [(carryV2Col n) i, (wDstRow n) i y, (wDstCol n) i x, (particleCol n) i]) (Head.lin 1 ((old n) c))
  let full := (List.range 2).foldl (fun h i =>
    (List.range 2).foldl (fun h2 j =>
      if i == j then h2 else
        h2.addProd 1 [(carryV2Col n) i, (wSrcRow n) i y, (wSrcCol n) i x,
                      (carryV2Col n) j, (wDstRow n) j y, (wDstCol n) j x, (old n) c]) h) base
  let ie := ((full.addProd 1 [(carryV2Col n) 0, (wSrcRow n) 0 y, (wSrcCol n) 0 x,
                              (carryV2Col n) 1, (wSrcRow n) 1 y, (wSrcCol n) 1 x, (old n) c]).addProd 1
              [(carryV2Col n) 0, (wDstRow n) 0 y, (wDstCol n) 0 x,
               (carryV2Col n) 1, (wDstRow n) 1 y, (wDstCol n) 1 x, (old n) c]).addProd (-1)
              [(carryV2Col n) 0, (wDstRow n) 0 y, (wDstCol n) 0 x,
               (carryV2Col n) 1, (wDstRow n) 1 y, (wDstCol n) 1 x, (particleCol n) 1]
  (Head.lin 1 ((cWBoardV2 n) c)).append (ie.scale (-1))
def midV2CellHead (n : Nat) (c : Nat) : Head :=
  (((Head.lin 1 ((cMidV2 n) c)).addProd (-1) [(cResolvable n), (cWBoardV2 n) c]).addLin (-1)
      ((old n) c)).addProd 1 [(cResolvable n), (old n) c]
def midV2Constraints (n : Nat) : List VmConstraint2 :=
  ((List.range (KK n)).map (fun c => cgH ((writeCellV2Head n) c)))
  ++ ((List.range (KK n)).map (fun c => cgH ((midV2CellHead n) c)))
def resolveConstraints (n : Nat) : List VmConstraint2 :=
  (onePin n) :: ((boardRangeConstraints n)
    ++ (autoReadConstraints n)
    ++ (validateMove n) ((mvBase n) 0) ++ (validateMove n) ((mvBase n) 1)
    ++ (validateOcclusion n) ((mvBase n) 0) ((occBase n) 0) ((mvBase n) 1)
    ++ (validateOcclusion n) ((mvBase n) 1) ((occBase n) 1) ((mvBase n) 0)
    ++ (srcNonVacConstraints n)                                      -- leg 3
    ++ (patternBitConstraints n) ++ (selectionConstraints n)             -- leg 4
    ++ (carryConstraints n)                                          -- leg 5
    ++ (flowThroughConstraints n)                                    -- leg 6
    ++ (writeMidConstraints n)                                       -- leg 7
    ++ (inclOcclusionConstraints n)                                  -- CHUNK-1 Δ1: inclusive occlusion
    ++ (nonLeaveConstraints n)                                       -- CHUNK-1 Δ3: non-leaver bit
    ++ (resolvableConstraints n)                                     -- CHUNK-1 Δ5: resolvable surface
    ++ (carryV2Constraints n)                                        -- CHUNK-3: corrected carry
    ++ (midV2Constraints n)                                          -- CHUNK-3: corrected board rewrite
    ++ (commitBoardsConstraints n))                                  -- leg 8

end NGen

/-- **`automataflResolveDescN n`** — the Leg-R (`old -> mid`) descriptor with the board size `n` an
EXPLICIT parameter (AUTOMATAFL-NGENERIC-DESIGN §4). Downstream `n`-generic refinements can now
quantify `∀ n, …` over the actual emitted object. `automataflResolveDescN 2` is defeq to the
byte-golden `automataflResolveDesc`; the commitment leg is `n`-generic (packed base-4). -/
def automataflResolveDescN (n : Nat) : EffectVmDescriptor2 :=
  { name        := "dregg-automatafl-resolve-n2"
  , traceWidth  := NGen.R_WIDTH n
  , piCount     := NGen.R_PI_COUNT n
  , tables      := []
  , constraints := NGen.resolveConstraints n
  , hashSites   := []
  , ranges      := [] }

/-- **`automataflResolveDesc`** — the automatafl m=2 move-adjudication (Leg R) descriptor, AUTHORED
IN LEAN, COMPLETE: `validate_move ×2` · `validate_occlusion ×2` (witnessed direction bit) · the
source-non-vacuum bits · the four `eq_coords` pattern bits and the fork/collide/survive selection ·
the carries · the vacuum flow-through chain · `write_mid_witnessed` (the one-hot board rewrite
forcing `mid == resolve_mid(old, [ma, mb])`) · THE PACKED BOARD COMMITMENT (the `⌈n²/15⌉` base-4
pack gates per board, their `.piBinding`s and the automaton coordinate). -/
def automataflResolveDesc : EffectVmDescriptor2 := automataflResolveDescN 2

/-! ## §6 — The byte-pinned wire golden + shape pins. -/

#guard automataflResolveDesc.name == "dregg-automatafl-resolve-n2"
#guard automataflResolveDesc.traceWidth == 371
#guard automataflResolveDesc.traceWidth == R_WIDTH
#guard automataflResolveDesc.traceWidth == NGen.R_WIDTH 2
#guard automataflResolveDesc.piCount == 20
#guard automataflResolveDesc.piCount == R_PI_COUNT
#guard automataflResolveDesc.piCount == NGen.R_PI_COUNT 2
-- 437 (post-CHUNK-1) + the CHUNK-3 corrected rewrite (carryV2 6 + midV2 8 = 14) = 451.
#guard automataflResolveDesc.constraints.length == 451
#guard boardRangeConstraints.length == 8
#guard automataflResolveDesc.tables.length == 0
#guard automataflResolveDesc.hashSites.length == 0
#guard automataflResolveDesc.ranges.length == 0
#guard autoReadConstraints.length == 17
#guard (validateMove (mvBase 0)).length == 32
#guard (validateMove (mvBase 1)).length == 32
#guard (validateOcclusion (mvBase 0) (occBase 0) (mvBase 1)).length == 72
#guard (validateOcclusion (mvBase 1) (occBase 1) (mvBase 0)).length == 72
-- the occlusion blocks tile the trace tail exactly: occBase 0 == the validity width, and the last
-- allocated column (`occBit o 8`) is the final column of the trace.
#guard occBase 0 == 65
#guard occBase 1 == occBase 0 + OCC_BLOCK_WIDTH
#guard occBit (occBase 1) 8 + 1 == RES0
-- the PARAMETRIC widths agree with the n=2 instance they replaced (the re-derivation canary: these
-- are now computed from NN / COORD_RBITS / RBITS, not written down)
#guard COORD_RBITS == 1
#guard MV_BLOCK_WIDTH == 23
#guard OCC_BLOCK_WIDTH == 62
#guard EQ_BLOCK_WIDTH == 12
#guard AUTO_BLOCK_WIDTH == 10
#guard WR_PIECE_WIDTH == 8
#guard NZ_WIDTH == 12
-- the per-move block tiles: the last source-column selector is the block's final column
#guard cSelCol (mvBase 0) (NN - 1) + 1 == mvBase 1
#guard cSelCol (mvBase 1) (NN - 1) + 1 == occBase 0
-- the coordinate bit runs tile the block without overlap
#guard cTyHi (mvBase 0) + COORD_RBITS == mvPost (mvBase 0)
-- the occlusion sub-blocks tile
#guard cIv (occBase 0) + 1 == occVec (occBase 0)
#guard cSeg (occBase 0) (NN - 1) + 1 == occEq (occBase 0)
#guard cEqy (occBase 0) + 1 == occTail (occBase 0)
#guard occBit (occBase 0) (RBITS - 1) + 1 == occBase 1
-- the adjudication sub-blocks tile
#guard bnzBit (SMALL_RBITS - 1) + 1 == eqBase 0
#guard cEqBit (eqBase 3) + 1 == SEL0
#guard wDstCol 1 (NN - 1) + 1 == MH0
-- COORD_RBITS is the real ceil(log2 n): it holds n−1 and no fewer bits would
#guard NN - 1 < 2 ^ COORD_RBITS
-- the witnessed direction bit is pinned by an eq_scalar over the move's OWN coordinate columns
#guard (isVerticalConstraints (mvBase 0) (occBase 0)).length == 13
-- the ADJUDICATION legs (3-8) tile the trace tail exactly: they start where the occlusion blocks
-- end, and the last board-root column is the final column of the trace.
#guard RES0 == 189
#guard srcNonVacConstraints.length == 14
#guard patternBitConstraints.length == 52
#guard (eqCoordsConstraints 0 1 2 3 (eqBase 0)).length == 13
#guard selectionConstraints.length == 6
#guard carryConstraints.length == 4
#guard flowThroughConstraints.length == 14
#guard writeEndpointConstraints.length == 32
#guard writeMidConstraints.length == 36
#guard commitBoardsConstraints.length == 6
#guard RFC == 1
#guard packOldFelt 0 == 289
#guard packMidFelt 0 == 290
#guard packMidFelt (RFC - 1) + 1 == INCL0   -- the pack felts now abut the CHUNK-1 additive tail
-- CHUNK-1 additive-tail shape pins (§2.4 columns / §5-add families).
#guard INCL0 == 291
#guard cResolvable + 1 == CV2_0          -- the CHUNK-1 tail ends where the CHUNK-3 tail begins
#guard NL0 == inclBase 1 + INCL_MV_WIDTH
#guard RESR0 == nlBase 1 + NL_PIECE_WIDTH
#guard inclOcclusionConstraints.length == 24
#guard nonLeaveConstraints.length == 18
#guard resolvableConstraints.length == 29
-- CHUNK-3 additive-tail shape pins (§2.5 columns / §5-add2 families).
#guard R_WIDTH == 371
#guard CV2_0 == 357                       -- the CHUNK-3 tail abuts the CHUNK-1 tail (old R_WIDTH)
#guard cCarryV2 1 == 362
#guard MIDV2_0 == 363
#guard cWBoardV2 0 == 363
#guard cMidV2 0 == 367
#guard cMidV2 (KK - 1) + 1 == R_WIDTH     -- the corrected board is the trace tail
#guard MV2_END == R_WIDTH
#guard carryV2Constraints.length == 6
#guard midV2Constraints.length == 8
-- The additive tail is defeq to its NGen twin at n = 2 (frozen-vocabulary agreement).
#guard NGen.R_WIDTH 2 == R_WIDTH
#guard NGen.INCL0 2 == INCL0
#guard NGen.CV2_0 2 == CV2_0
#guard NGen.MIDV2_0 2 == MIDV2_0
#guard (NGen.inclOcclusionConstraints 2).length == 24
#guard (NGen.nonLeaveConstraints 2).length == 18
#guard (NGen.resolvableConstraints 2).length == 29
#guard (NGen.carryV2Constraints 2).length == 6
#guard (NGen.midV2Constraints 2).length == 8
-- Two-sided VALUE canary: on a witness with the DESTINATION occupied (line[dst]=1) and the interior
-- clear, the exclusive `msum` value is 0 (occlusion MISSES), while the emitted inclusive gate forces
-- `msumIncl = 1` (the endpoint term fires ⇒ `occIncl` DETECTS the blocking piece). The wrong value 0
-- is REJECTED by the inclusive gate; the exclusive `msum` gate accepts 0.
#guard (headToExpr (msumHead (occBase 0))).eval
    (fun v => if v == cEto (occBase 0) 1 then 1 else if v == cLine (occBase 0) 1 then 1 else 0) == 0
#guard (headToExpr (msumInclHead 0 (occBase 0))).eval
    (fun v => if v == cMsumIncl 0 then 1 else if v == cEto (occBase 0) 1 then 1
              else if v == cLine (occBase 0) 1 then 1 else 0) == 0
#guard (headToExpr (msumInclHead 0 (occBase 0))).eval
    (fun v => if v == cMsumIncl 0 then 0 else if v == cEto (occBase 0) 1 then 1
              else if v == cLine (occBase 0) 1 then 1 else 0) != 0
-- Two-sided DEFECT-#8 canary (the occluded-STAYER: a piece on B's landing that does NOT leave, so
-- `cNonLeave 1 = 1`). The NEW `carryV2` gate FORCES `cCarryV2 1 = 0` — it KEEPS the stayer: the
-- correct value 0 is accepted, the overwrite value 1 is REJECTED. The OLD `carryB` gate accepts
-- `cCarryB = 1` (OVERWRITES the stayer) on the SAME witness (exclusive occ = 0) — the exact defect,
-- corrected only in the new column. (`cCv2 1 = 1` = surv·bnz·(1−occIncl); `cSb1 = 1` = surv·bnz.)
#guard (headToExpr (carryV2Head 1)).eval
    (fun v => if v == cCv2 1 then 1 else if v == cNonLeave 1 then 1 else 0) == 0    -- cCarryV2=0 accepted
#guard (headToExpr (carryV2Head 1)).eval
    (fun v => if v == cCarryV2 1 then 1 else if v == cCv2 1 then 1
              else if v == cNonLeave 1 then 1 else 0) != 0                          -- cCarryV2=1 rejected
#guard (headToExpr (((Head.lin 1 cCarryB).addProd (-1) [cSb1]).addProd 1 [cSb1, cOcc (occBase 1)])).eval
    (fun v => if v == cCarryB then 1 else if v == cSb1 then 1 else 0) == 0          -- OLD overwrite accepted
-- the corrected board rewrite reaches EVERY cell (both the writeBoard staging and the gated mid)
#guard (List.range KK).all (fun c => cMidV2 c == MIDV2_0 + KK + c)
-- the board rewrite reaches EVERY cell, and each pack gate absorbs its OWN board
#guard (List.range KK).all (fun c => mid c == KK + c)
-- THE COMMITMENT IS NO LONGER A LOOKUP: the retired `board_root8` pair was this descriptor's ONLY
-- chip lookup, so Leg R is now gates + PI bindings, with no Poseidon2 table dependency at all.
#guard automataflResolveDesc.constraints.all (fun c => match c with | .lookup _ => false | _ => true)

-- THE WIRE GOLDEN (byte-pinned; captured from the emitter). Stage R1+R2: `one` + the witnessed
-- auto-read + `validate_move ×2` + `validate_occlusion ×2` (WITNESSED direction bit).
-- THE WIRE GOLDEN (byte-pinned; captured from the emitter). The COMPLETE Leg R gate set:
-- `one` + the witnessed auto-read + `validate_move` x2 + `validate_occlusion` x2 (WITNESSED
-- direction bit) + the non-vacuum bits + the pattern/selection truth table + the carries + the
-- flow-through chain + `write_mid_witnessed` + the CHUNK-1 tail + the CHUNK-3 corrected board rewrite
-- (`carryV2` + `cWBoardV2`/`cMidV2`) + THE PACKED BOARD COMMITMENT -- 451 constraints over 371
-- columns and 20 public inputs (CHUNK-3 corrected rewrite: +14 cols, +14 constraints over CHUNK-1).
#guard emitVmJson2 automataflResolveDesc ==
"{\"name\":\"dregg-automatafl-resolve-n2\",\"ir\":2,\"trace_width\":371,\"public_input_count\":20,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"const\",\"v\":-3}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":23}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":22}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":34}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"var\",\"v\":36}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":39}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":46}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":47}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":48}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":49}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":50}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":51}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":52}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":53}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":43}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":45}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"var\",\"v\":55}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"var\",\"v\":57}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":10}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"var\",\"v\":59}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":62}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":60},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":67},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":67},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":68},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":69},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":69},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":70},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":70},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":71},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":71},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":72},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":72},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":73},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":73},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":74},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":74},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":75},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":75},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":66},\"r\":{\"t\":\"var\",\"v\":65}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":66}}},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":65}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":67}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":68}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":69}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":70}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":71}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":72}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":73}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":74}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":75}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":77},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":38}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":39}},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":78},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":40}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":41}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":38}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":39}},\"r\":{\"t\":\"var\",\"v\":3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":79},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":79},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":79},\"r\":{\"t\":\"var\",\"v\":80}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":80},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":81},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":81},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":82},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":82},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":81},\"r\":{\"t\":\"var\",\"v\":82}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":82},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":83},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":38}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":40}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":40}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":84},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":39}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":41}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":41}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":79}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":81}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":81}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":86},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":80}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":82}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":82}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":87}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":88}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":89},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":90},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":90},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":91},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":91},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":92},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":93},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":93},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":94},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":94},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":95},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":95},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":96},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":96},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":97},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":97},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":98},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":98},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":99},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":99},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":90},\"r\":{\"t\":\"var\",\"v\":89}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":90}}},\"r\":{\"t\":\"var\",\"v\":90}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":89}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":91}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":92}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":93}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":94}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":95}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":96}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":97}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":98}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":99}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":100},\"r\":{\"t\":\"var\",\"v\":90}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":101},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":102},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":102},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":103},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":103},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":104},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":104},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":105},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":105},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":106},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":106},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":107},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":107},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":108},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":108},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":109},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":110},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":111},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":102},\"r\":{\"t\":\"var\",\"v\":101}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":102}}},\"r\":{\"t\":\"var\",\"v\":102}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":101}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":103}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":104}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":105}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":106}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":107}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":108}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":109}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":110}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":111}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":112},\"r\":{\"t\":\"var\",\"v\":102}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":100}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":112}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":76},\"r\":{\"t\":\"var\",\"v\":112}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":114},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":114},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":113}},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":115}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":115},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"var\",\"v\":76}},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":113},\"r\":{\"t\":\"var\",\"v\":76}},\"r\":{\"t\":\"var\",\"v\":42}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":116},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":87},\"r\":{\"t\":\"var\",\"v\":77}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":87},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":77}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":88},\"r\":{\"t\":\"var\",\"v\":78}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":88},\"r\":{\"t\":\"var\",\"v\":115}},\"r\":{\"t\":\"var\",\"v\":78}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":117},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":117},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":118},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":118},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":119},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":119},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":120},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":120},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":121},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":121},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":122},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":122},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":123},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":123},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":124},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":124},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":125},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":125},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":126},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":126},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":117},\"r\":{\"t\":\"var\",\"v\":116}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":117}}},\"r\":{\"t\":\"var\",\"v\":117}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":116}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":118}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":119}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":120}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":121}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":122}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":123}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":124}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":125}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":126}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":127},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":128},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":128},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":129},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":129},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":130},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":130},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":131},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":131},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":132},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":132},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":133},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":133},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":134},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":134},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":135},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":135},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":136},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":136},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":137},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":137},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":128},\"r\":{\"t\":\"var\",\"v\":127}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":128}}},\"r\":{\"t\":\"var\",\"v\":128}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":127}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":129}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":130}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":131}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":132}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":133}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":134}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":135}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":136}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":137}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":128}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":139},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":62}},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":140},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":63}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":64}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":61}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":62}},\"r\":{\"t\":\"var\",\"v\":3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":141},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":141},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":142},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":142},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":141},\"r\":{\"t\":\"var\",\"v\":142}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":142},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":143},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":143},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":144},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":144},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":143},\"r\":{\"t\":\"var\",\"v\":144}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":144},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":145},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":61}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":63}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":63}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":146},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":62}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":64}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":64}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":147},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":141}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":143}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":143}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":148},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":142}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":144}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":144}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":149}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":150}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":151},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":153},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":153},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":154},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":154},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":155},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":155},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":156},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":156},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":157},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":157},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":158},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":158},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":159},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":159},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":160},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":160},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":161},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":161},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":152},\"r\":{\"t\":\"var\",\"v\":151}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":152}}},\"r\":{\"t\":\"var\",\"v\":152}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":151}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":153}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":154}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":155}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":156}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":157}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":158}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":159}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":160}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":161}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":162},\"r\":{\"t\":\"var\",\"v\":152}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":163},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":164},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":164},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":165},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":165},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":166},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":166},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":167},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":167},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":168},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":168},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":169},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":169},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":170},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":170},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":171},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":171},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":172},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":172},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":173},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":164},\"r\":{\"t\":\"var\",\"v\":163}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":164}}},\"r\":{\"t\":\"var\",\"v\":164}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":163}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":165}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":166}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":167}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":168}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":169}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":170}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":171}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":172}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":173}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":174},\"r\":{\"t\":\"var\",\"v\":164}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":162}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":174}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":138},\"r\":{\"t\":\"var\",\"v\":174}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":176},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":176},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":177},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":177},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":175}},\"r\":{\"t\":\"var\",\"v\":176}},\"r\":{\"t\":\"var\",\"v\":177}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":177},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"var\",\"v\":138}},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":175},\"r\":{\"t\":\"var\",\"v\":138}},\"r\":{\"t\":\"var\",\"v\":19}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":178},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":149},\"r\":{\"t\":\"var\",\"v\":139}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":149},\"r\":{\"t\":\"var\",\"v\":176}},\"r\":{\"t\":\"var\",\"v\":139}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":150},\"r\":{\"t\":\"var\",\"v\":140}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":150},\"r\":{\"t\":\"var\",\"v\":177}},\"r\":{\"t\":\"var\",\"v\":140}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":179},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":179},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":180},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":180},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":181},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":181},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":182},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":182},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":183},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":183},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":184},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":184},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":185},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":185},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":186},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":186},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":187},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":187},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":188},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":188},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":179},\"r\":{\"t\":\"var\",\"v\":178}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":179}}},\"r\":{\"t\":\"var\",\"v\":179}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":178}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":180}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":181}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":182}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":183}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":184}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":185}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":186}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":187}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":188}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":189},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":189},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":190},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":190},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":191},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":191},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":192},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":192},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":193},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":193},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":194},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":194},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":189},\"r\":{\"t\":\"var\",\"v\":37}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":189}}},\"r\":{\"t\":\"var\",\"v\":189}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":37}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":190}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":191}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":192}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":193}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":194}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":195},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":195},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":196},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":196},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":197},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":197},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":198},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":198},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":199},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":199},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":200},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":195},\"r\":{\"t\":\"var\",\"v\":60}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":195}}},\"r\":{\"t\":\"var\",\"v\":195}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":60}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":196}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":197}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":198}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":199}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":200}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":201},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":202},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":202},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":203},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":203},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":204},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":204},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":205},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":205},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":206},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":206},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":207},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":207},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":208},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":208},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":209},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":209},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":210},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":210},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":211},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":211},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":202},\"r\":{\"t\":\"var\",\"v\":201}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":202}}},\"r\":{\"t\":\"var\",\"v\":202}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":201}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":203}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":204}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":205}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":206}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":207}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":208}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":209}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":210}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":211}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":212},\"r\":{\"t\":\"var\",\"v\":202}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":213},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":214},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":214},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":215},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":215},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":216},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":216},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":217},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":217},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":218},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":218},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":219},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":219},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":220},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":220},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":221},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":221},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":222},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":222},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":223},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":223},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":214},\"r\":{\"t\":\"var\",\"v\":213}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":214}}},\"r\":{\"t\":\"var\",\"v\":214}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":213}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":215}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":216}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":217}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":218}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":219}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":220}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":221}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":222}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":223}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":224},\"r\":{\"t\":\"var\",\"v\":214}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":225},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"var\",\"v\":42}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":43}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"var\",\"v\":43}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":226},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":226},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":227},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":227},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":228},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":228},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":229},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":229},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":230},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":230},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":231},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":231},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":232},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":232},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":233},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":233},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":234},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":234},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":235},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":235},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":226},\"r\":{\"t\":\"var\",\"v\":225}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":226}}},\"r\":{\"t\":\"var\",\"v\":226}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":225}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":227}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":228}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":229}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":230}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":231}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":232}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":233}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":234}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":235}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":236},\"r\":{\"t\":\"var\",\"v\":226}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":237},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":20}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":238},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":238},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":239},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":239},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":240},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":240},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":241},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":241},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":242},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":242},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":243},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":243},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":244},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":244},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":245},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":245},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":246},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":246},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":247},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":238},\"r\":{\"t\":\"var\",\"v\":237}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":238}}},\"r\":{\"t\":\"var\",\"v\":238}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":237}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":239}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":240}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":241}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":242}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":243}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":244}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":245}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":246}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":247}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":248},\"r\":{\"t\":\"var\",\"v\":238}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":249},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":212}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":212},\"r\":{\"t\":\"var\",\"v\":224}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":250},\"r\":{\"t\":\"var\",\"v\":212}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":251}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":224},\"r\":{\"t\":\"var\",\"v\":250}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":252}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":251},\"r\":{\"t\":\"var\",\"v\":189}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":253}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":252},\"r\":{\"t\":\"var\",\"v\":195}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":254},\"r\":{\"t\":\"var\",\"v\":249}},\"r\":{\"t\":\"var\",\"v\":253}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":249},\"r\":{\"t\":\"var\",\"v\":253}}}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":255}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":254},\"r\":{\"t\":\"var\",\"v\":189}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":255}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":255},\"r\":{\"t\":\"var\",\"v\":117}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":257}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":254},\"r\":{\"t\":\"var\",\"v\":195}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":257}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":257},\"r\":{\"t\":\"var\",\"v\":179}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":259},\"r\":{\"t\":\"var\",\"v\":195}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":260},\"r\":{\"t\":\"var\",\"v\":179}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":261},\"r\":{\"t\":\"var\",\"v\":248}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":262}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":236},\"r\":{\"t\":\"var\",\"v\":259}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":263}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":262},\"r\":{\"t\":\"var\",\"v\":254}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":264}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":263},\"r\":{\"t\":\"var\",\"v\":260}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":265}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":264},\"r\":{\"t\":\"var\",\"v\":261}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":266},\"r\":{\"t\":\"var\",\"v\":189}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":267},\"r\":{\"t\":\"var\",\"v\":117}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":268},\"r\":{\"t\":\"var\",\"v\":236}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":269}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":248},\"r\":{\"t\":\"var\",\"v\":266}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":270}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":269},\"r\":{\"t\":\"var\",\"v\":254}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":271}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":270},\"r\":{\"t\":\"var\",\"v\":267}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":272}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":271},\"r\":{\"t\":\"var\",\"v\":268}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":273},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":273},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":274},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":274},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":273},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":274},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":20}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":275},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":275},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":276},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":276},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":275},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":276},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":277},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":277},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":278},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":278},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":277},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":278},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":22}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":279},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":279},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":280},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":280},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":279},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":280},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":21}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":281},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":281},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":282},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":282},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":281},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":282},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":43}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":283},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":283},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":284},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":284},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":283},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":284},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":42}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":285},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":285},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":286},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":286},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":285},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":286},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":45}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":287},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":287},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":288},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":288},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":287},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":288},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":44}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":256}},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":256}},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":256}},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":256}},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":258}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":291},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":116}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"var\",\"v\":77}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"var\",\"v\":114}},\"r\":{\"t\":\"var\",\"v\":77}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":86},\"r\":{\"t\":\"var\",\"v\":78}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":86},\"r\":{\"t\":\"var\",\"v\":115}},\"r\":{\"t\":\"var\",\"v\":78}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":292},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":292},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":293},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":293},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":294},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":294},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":295},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":295},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":296},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":296},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":297},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":297},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":298},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":298},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":299},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":299},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":300},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":300},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":301},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":301},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":292},\"r\":{\"t\":\"var\",\"v\":291}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":292}}},\"r\":{\"t\":\"var\",\"v\":292}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":291}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":293}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":294}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":295}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":296}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":297}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":298}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":299}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":300}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":301}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":302},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":178}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":147},\"r\":{\"t\":\"var\",\"v\":139}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":147},\"r\":{\"t\":\"var\",\"v\":176}},\"r\":{\"t\":\"var\",\"v\":139}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":148},\"r\":{\"t\":\"var\",\"v\":140}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":148},\"r\":{\"t\":\"var\",\"v\":177}},\"r\":{\"t\":\"var\",\"v\":140}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":303},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":303},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":304},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":304},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":305},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":305},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":306},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":306},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":307},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":307},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":308},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":308},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":309},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":309},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":310},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":310},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":311},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":311},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":312},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":312},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":303},\"r\":{\"t\":\"var\",\"v\":302}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":303}}},\"r\":{\"t\":\"var\",\"v\":303}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":302}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":304}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":305}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":306}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":307}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":308}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":309}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":310}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":311}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":312}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":313},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":277},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":277},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":278},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":278},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":314},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":314},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":315},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":315},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":316},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":316},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":317},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":317},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":318},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":318},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":319},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":319},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":314},\"r\":{\"t\":\"var\",\"v\":313}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":314}}},\"r\":{\"t\":\"var\",\"v\":314}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":313}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":315}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":316}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":317}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":318}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":319}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":320},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":314}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":314},\"r\":{\"t\":\"var\",\"v\":258}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":321},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":285},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":285},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":286},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":286},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":322},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":322},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":323},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":323},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":324},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":324},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":325},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":325},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":326},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":326},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":327},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":327},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":322},\"r\":{\"t\":\"var\",\"v\":321}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":322}}},\"r\":{\"t\":\"var\",\"v\":322}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":321}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":323}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":324}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":325}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":326}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":327}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":328},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":322}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":322},\"r\":{\"t\":\"var\",\"v\":256}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":329},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":44}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":21}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":330},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":45}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":265},\"r\":{\"t\":\"var\",\"v\":22}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":331},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":44}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":44}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":332},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":45}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":272},\"r\":{\"t\":\"var\",\"v\":45}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":333},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":329},\"r\":{\"t\":\"var\",\"v\":329}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":329},\"r\":{\"t\":\"var\",\"v\":331}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":331},\"r\":{\"t\":\"var\",\"v\":331}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":330},\"r\":{\"t\":\"var\",\"v\":330}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":330},\"r\":{\"t\":\"var\",\"v\":332}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":332},\"r\":{\"t\":\"var\",\"v\":332}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":334},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":334},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":335},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":335},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":336},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":336},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":337},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":337},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":338},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":338},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":339},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":339},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":340},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":340},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":341},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":341},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":342},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":342},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":343},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":343},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":334},\"r\":{\"t\":\"var\",\"v\":333}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":334}}},\"r\":{\"t\":\"var\",\"v\":334}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":333}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":335}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":336}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":337}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-8},\"r\":{\"t\":\"var\",\"v\":338}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":339}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-32},\"r\":{\"t\":\"var\",\"v\":340}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":341}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-128},\"r\":{\"t\":\"var\",\"v\":342}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-256},\"r\":{\"t\":\"var\",\"v\":343}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":344},\"r\":{\"t\":\"var\",\"v\":334}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":345}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":212},\"r\":{\"t\":\"var\",\"v\":224}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":346}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":258}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":347}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":346},\"r\":{\"t\":\"var\",\"v\":344}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":348},\"r\":{\"t\":\"var\",\"v\":345}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":349}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":347},\"r\":{\"t\":\"var\",\"v\":348}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":350}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":320}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":351}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":258},\"r\":{\"t\":\"var\",\"v\":328}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":352},\"r\":{\"t\":\"var\",\"v\":349}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":353},\"r\":{\"t\":\"var\",\"v\":350}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":354},\"r\":{\"t\":\"var\",\"v\":351}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":355}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":352},\"r\":{\"t\":\"var\",\"v\":353}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":356}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":355},\"r\":{\"t\":\"var\",\"v\":354}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":357}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":254},\"r\":{\"t\":\"var\",\"v\":189}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":358},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":357}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":357},\"r\":{\"t\":\"var\",\"v\":292}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":358}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":358},\"r\":{\"t\":\"var\",\"v\":320}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":360}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":254},\"r\":{\"t\":\"var\",\"v\":195}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":361},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":360}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":360},\"r\":{\"t\":\"var\",\"v\":303}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":361}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":361},\"r\":{\"t\":\"var\",\"v\":328}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":363},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":359}},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":0}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":364},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":359}},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":273}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":281}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":1}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":277}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":285}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":365},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":359}},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":275}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":283}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":2}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":279}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":287}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":366},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":37}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":362},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":359}},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":274}},\"r\":{\"t\":\"var\",\"v\":276}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":282}},\"r\":{\"t\":\"var\",\"v\":284}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":3}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":359},\"r\":{\"t\":\"var\",\"v\":278}},\"r\":{\"t\":\"var\",\"v\":280}},\"r\":{\"t\":\"var\",\"v\":362}},\"r\":{\"t\":\"var\",\"v\":286}},\"r\":{\"t\":\"var\",\"v\":288}},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":367},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":356},\"r\":{\"t\":\"var\",\"v\":363}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":356},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":368},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":356},\"r\":{\"t\":\"var\",\"v\":364}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":356},\"r\":{\"t\":\"var\",\"v\":1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":369},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":356},\"r\":{\"t\":\"var\",\"v\":365}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":356},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":370},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":356},\"r\":{\"t\":\"var\",\"v\":366}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":356},\"r\":{\"t\":\"var\",\"v\":3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":289},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":290},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-4},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-16},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-64},\"r\":{\"t\":\"var\",\"v\":7}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":289,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":290,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":19}],\"hash_sites\":[],\"ranges\":[]}"


/-! ## §7 — `descN 11` shape pins: the parts that ARE correctly `n`-parametric.

`automataflResolveDescN 11` is a well-formed term. These pin the board-cell count, the move/occlusion
block widths, AND — new with the commitment swap — the COMMITMENT itself at the deployed target
`n = 11` (`k = 121`). The retired padded-leaf `board_root8` could not be pinned here at all: one
8-lane leaf cannot hold 121 cells. The pack emits `feltCount 11 = 9` gates per board. -/
example : EffectVmDescriptor2 := automataflResolveDescN 11
-- board-cell count: 2·n² range gates (n² old + n² mid), the cleanly-parametric part.
#guard (NGen.boardRangeConstraints 11).length == 2 * 121
#guard (NGen.boardRangeConstraints 11).length == 242
-- coordinate bit width and the move/occlusion block WIDTHS at n = 11.
#guard NGen.COORD_RBITS 11 == 4
#guard NGen.AUTO_BLOCK_WIDTH 11 == 40
#guard NGen.MV_BLOCK_WIDTH 11 == 65
#guard NGen.OCC_BLOCK_WIDTH 11 == 125
#guard NGen.EQ_BLOCK_WIDTH 11 == 12
-- the move/occlusion CONSTRAINT blocks re-emit at the larger fold count.
#guard (NGen.validateMove 11 (NGen.mvBase 11 0)).length == 74
#guard (NGen.validateOcclusion 11 (NGen.mvBase 11 0) (NGen.occBase 11 0) (NGen.mvBase 11 1)).length == 135
-- descN 2 is the frozen object: the parametric layout agrees with the n = 2 pins above.
#guard NGen.COORD_RBITS 2 == COORD_RBITS
#guard NGen.MV_BLOCK_WIDTH 2 == MV_BLOCK_WIDTH
#guard NGen.OCC_BLOCK_WIDTH 2 == OCC_BLOCK_WIDTH
#guard NGen.R_WIDTH 2 == R_WIDTH
#guard NGen.R_PI_COUNT 2 == R_PI_COUNT
#guard (NGen.resolveConstraints 2).length == 451
-- THE COMMITMENT EMITS AT n = 11 — the thing the padded 8-lane leaf could never do.
#guard NGen.RFC 11 == 9
#guard (AutomataflCommit.packBoardConstraintsAt 11 (NGen.old 11) (NGen.packOldFelt 11)).length == 9
#guard (AutomataflCommit.packBoardConstraintsAt 11 (NGen.mid 11) (NGen.packMidFelt 11)).length == 9
#guard (AutomataflCommit.commitBoardConstraintsAt 11 (NGen.packOldFelt 11) 16).length == 9
#guard (NGen.commitBoardsConstraints 11).length == 38
#guard (automataflResolveDescN 11).piCount == 36
-- every cell of the 11x11 board is covered by some pack gate
#guard 11 * 11 <= 15 * NGen.RFC 11
-- the packed felts close the trace at BOTH sizes: no overlap with the write-endpoint block below.
#guard NGen.packOldFelt 11 0 == NGen.MH0 11
#guard NGen.packMidFelt 11 (NGen.RFC 11 - 1) + 1 == NGen.INCL0 11
#guard NGen.packMidFelt 2 (NGen.RFC 2 - 1) + 1 == NGen.INCL0 2
-- descN 11: the additive tail is n-parametric too (occlusion pair ×2, non-leaver ×2, resolvable).
#guard (NGen.inclOcclusionConstraints 11).length == 24
#guard (NGen.nonLeaveConstraints 11).length == 18
#guard (NGen.resolvableConstraints 11).length == 29
#guard NGen.cResolvable 11 + 1 == NGen.CV2_0 11   -- the CHUNK-1 tail ends where the CHUNK-3 tail begins
-- descN 11: the CHUNK-3 corrected rewrite is n-parametric (carryV2 = 6 gates; midV2 = 2·n² cells).
#guard NGen.CV2_0 11 == NGen.RESR_END 11
#guard (NGen.carryV2Constraints 11).length == 6
#guard (NGen.midV2Constraints 11).length == 242     -- 2 · 11² = 2 · KK 11
#guard NGen.cMidV2 11 (NGen.KK 11 - 1) + 1 == NGen.R_WIDTH 11   -- the corrected board is the trace tail
#guard NGen.MV2_END 11 == NGen.R_WIDTH 11

end Dregg2.Circuit.Emit.AutomataflResolveEmit
