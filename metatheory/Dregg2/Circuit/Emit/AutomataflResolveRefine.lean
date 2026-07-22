/-
# Dregg2.Circuit.Emit.AutomataflResolveRefine — LEG R, the SAT ⇒ SEMANTICS refinement of the
byte-pinned automatafl m=2 move-adjudication descriptor (`automataflResolveDesc`).

## What this file IS

`AutomataflResolveEmit.lean` is Stage 1: the Leg R descriptor STRUCTURE, byte-pinned by an
`emitVmJson2` `#guard` (306 columns, 371 constraints, 32 public inputs). This file is Stage 2: for
each of the descriptor's eight legs, a theorem DERIVING the reference semantics
(`Dregg2.Games.Automatafl`) from the EMITTED constraints on a satisfying, canonical trace. Nothing
is assumed: every fact is extracted from a constraint proved to be a MEMBER of the byte-pinned
`automataflResolveDesc.constraints` (`by decide` over the fold-generated list), exactly as
`AutomataflStepRefine.lean` closed Leg A.

The field glue (`Canon`, `bin_of_gate`, `eq_of_modEq_canon`, `forcedGe0_core`, `StepCanon`,
`codeToParticle`) is REUSED from `AutomataflStepRefine`; it is descriptor-agnostic.

## DEFECT #4, FOUND HERE AND NOW FIXED AT SOURCE — the board cells were NOT range-checked

`automataflStepDesc` carries `boardRangeConstraints` — `assert_member(cell, {0,1,2,3})` on every
OLD and NEW board column. That family is what let Leg A's capstone be UNCONDITIONAL.

`automataflResolveDesc` HAD NO SUCH FAMILY, and that was LOAD-BEARING, not cosmetic. The
source-non-vacuum bit is `anz = forced_ge0(fp − 1, SMALL_RBITS=5)`, so a witnessed source particle
`fp = 4` satisfies `anz = 1` (the circuit treats the cell as CARRYING A PIECE) while
`codeToParticle 4 = .vacuum` (the reference treats it as EMPTY) — and the 5-bit comparison supplies
no a-priori window that would exclude it. A satisfying witness with an out-of-alphabet cell
therefore made the capstone FALSE.

FIXED: `AutomataflResolveEmit.boardRangeConstraints` now emits `assert_member(cell, {0,1,2,3})` on
every OLD and MID board column (constraints 371 → 379, wire golden re-pinned, descriptor
regenerated). The `BoardAlphabet` envelope is consequently a THEOREM here — `boardvalid_of_sat` —
extracted from the byte-pinned constraint list, and `srcNonVac_of_sat` no longer takes it as a
hypothesis. Every result in this file is UNCONDITIONAL: there is no assumed envelope left.

## DEFECT #5, FOUND HERE AND NOW FIXED AT SOURCE — the identical-move turn was UNSATISFIABLE

`write_mid_witnessed`'s cell polynomial subtracted `carry_i·src_i[c]·old[c]` once PER PIECE. When
both moves cleared the SAME square (`frm_a = frm_b` with both sources carrying — two players
proposing the identical move, which the reference explicitly does NOT treat as a conflict, see
`Automatafl.conflictResolve`) the old particle was subtracted TWICE, forcing `mid[frm] ≡ −old[frm]`.
Since DEFECT #4's alphabet gates pin both cells into `{0,1,2,3}`, that forced `old[frm] = 0` —
contradicting the carry. The leaf was UNSATISFIABLE on that legal turn: a COMPLETENESS defect
(soundness was never at risk — a legal turn was refused, no forged board admitted).

FIXED: `AutomataflResolveEmit.writeCellHead` now carries the SHARED-ENDPOINT inclusion–exclusion —
`+ A·C·old` (a shared source is vacated exactly once) and `+ B·D·old − B·D·particle_b` (a shared
landing deposits exactly one particle). Constraint COUNT is unchanged (379); the wire golden was
re-pinned and `circuit/descriptors/by-name/automatafl-resolve.json` regenerated (drift gate PASS).
The canary polarity is FLIPPED: `canonDoubleGood` now SATISFIES both the cell gate and the alphabet
gate at `mid = 0`, and the two forges (`mid = −1`, the OLD forced value; `mid = 1`, source not
vacated) are REJECTED — so the fix MOVED the pinned value rather than widening the gate.
`noSharedSource` is replaced by `sharedSourceVacatesOnce`, and `cellAlgebra` no longer takes
`A·C = 0` / `B·D = 0` as hypotheses: those two configurations are now LIVE, satisfiable cases.

## What is CLOSED here, and what is NOT (the honest residual)

CLOSED: R1 (auto pin) · R2 (`validate_move` ⇒ `MoveValid`, witnessed source read) · R3 (witnessed
`is_vertical`, occlusion) · the R4 pattern bits, selection truth table and `srcNonVac`
(unconditional) · (a) `boardvalid_of_sat` · (b) `conflictResolve_pair` · (c) THE `m = 2`
CATERPILLAR, BOTH SIDES (`chainDest_a`/`chainDest_b`; `carry_of_sat`/`ft_of_sat` and their four
instances) · (d) R6's EXTRACTORS AND ALGEBRA (§5.8): `dstOneHot_of_sat`, `writeCell_of_sat`,
`cellAlgebra` (eleven live cases of sixteen, the five excluded ones being ONLY the same-piece
`A·B = C·D = 0`) · (e) NEW, §5.8.2 — THE INDICATOR GLUE, residual (i), CLOSED:
`oneHotPair_indicator`, `srcIndicator_of_sat` and `dstIndicator_of_sat` identify the emitted
products `carry·srcRow·srcCol` / `carry·dstRow·dstCol` with the decidable `Coord` predicates
`⟨x,y⟩ = frm_k` / `⟨x,y⟩ = dest_k` (the interpolated `to_own + ft·(to_other − to_own)`), per cell,
via the `Int.toNat` bridge — memberships `decide`d against the byte-pinned constraint list.

Also CLOSED, in `Dregg2.Games.Automatafl` (reference side, no circuit content):

  * §8b THE SEAM LEMMA — `automatonStep_congr`: two boards agreeing on `size`, `automaton`,
    `useColumnRule` and every IN-BOUNDS cell step to boards agreeing on every in-bounds cell.
    This is what the whole-turn composition needs, because the Leg R → Leg A seam is a CELL-WISE
    agreement (what a `mid_root` PI equality gives) and NOT a `Board` equality. Built on
    `raycastFuel_congr` / `raycast_congr` / `automatonOffset_congr`.
  * §8c THE REFERENCE UNFOLDING, residual (ii), CLOSED — `applyMoves_cell_TT/TF/FT/FF`: the
    `filter`/`map`/`find?` pipeline of `applyMoves bd [ma, mb]` evaluated per cell in all FOUR
    `(anz, bnz)` shapes of `pieceSrcs`, into the same per-cell if-chain the gate computes
    (landing-A first, then landing-B, then vacuum on a cleared source, else the old cell — the
    reference's `find?` list order IS the gate's `B`-before-`D` priority).

Also CLOSED — residual (iii), THE ASSEMBLY (§6.5):

  * `resolve_sat_imp_resolveMid` — **LEG R'S CAPSTONE, UNCONDITIONAL.** On any satisfying,
    canonical trace the decoded MID board IS `Automatafl.resolveMid` of the decoded OLD board and
    the two decoded moves, cell-wise over every in-bounds cell. `resolveFacts_of_sat` derives the
    per-row semantics ONCE (validity, alphabet, the four pattern bits read as `Coord` equalities,
    the survive verdict as the reference's fork/collide disjunction, the carries, the flow-through
    bits, and the four one-hot indicators as `Coord` predicates); `midCell_of_facts` then cases on
    the survive verdict and on which sources carry, matches each shape to the corresponding
    `applyMoves_cell_*` lemma, resolves the landing through `chainDest_a`/`chainDest_b`, and pins
    the cell with `cellAlgebra` through the indicator glue. `forkCollide_bool_of_sat` supplies the
    fork/collide range `selection_of_sat` did not, which is what makes the NON-surviving direction
    (`surv = 0 ⇒ the reference really does drop both moves`) provable rather than one-sided.
  * THE WHOLE TURN now lives at the deployed `n = 11` in `AutomataflTurnCapstone.
    turn_sat_imp_roundStep_pi` (over `roundStep` / `resolveMoves` / the FINAL corrected board
    `cMidV4`), not here. The V2 `resolve_step_sat_imp_applyTurn` (`new = applyTurn(old, moves)` at
    `NN = 2`, over the buggy `resolveMid` board) is RETIRED — see §D.6b: its crypto-free seam rode
    the `mid` commitment, and the commitment now packs `cMidV4`. This file supplies the Leg-R side
    of that emitted seam via `resolve_midPack_pi_of_sat` (re-pointed to `cMidV4`).

There is no `sorry`, no assumed arithmetization hypothesis, no assumed mid-board link beyond that
named seam, and no weakened or vacuous capstone standing in for either.

## Axiom hygiene

`#print axioms` on every exported theorem; the subset is `{propext, Classical.choice, Quot.sound}`.
No `sorry`, no `native_decide`, no assumed arithmetization hypothesis.
-/
import Dregg2.Circuit.Emit.AutomataflResolveEmit
import Dregg2.Circuit.Emit.AutomataflResolveMembership
import Dregg2.Circuit.Emit.AutomataflStepRefine
import Dregg2.Circuit.Emit.AutomataflCoord
import Dregg2.Circuit.Emit.AutomataflCommitRefine
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Games.Automatafl
import Dregg2.Games.AutomataflRules

namespace Dregg2.Circuit.Emit.AutomataflResolveRefine

open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Circuit.Emit.AutomataflResolveMembership
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Circuit.Emit.AutomataflStepRefine
  (Canon canon_zero canon_one canon_two canon_three eq_of_modEq_canon eq_of_modEq_small
   eq_of_modEq_win bin_of_gate StepCanon canon_loc forcedGe0_core codeToParticle)
open Dregg2.Games.Automatafl (Board Coord Particle Move MoveValid moveValidB conflictResolve
  occluded applyMoves interior frmConflict toConflict hasTwoDistinct)

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! ## §0 — The single-row gate extraction, keyed on the BYTE-PINNED `automataflResolveDesc`. -/

/-- A per-row gate `cg g` of the Leg-R descriptor forces its body to vanish mod `p` on a non-last
row. The `hg` argument is discharged by `decide` against the fold-generated constraint list, so
every downstream fact is anchored to the byte-pinned descriptor. -/
theorem rgate {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace} (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {g : EmittedExpr} (hg : cg g ∈ automataflResolveDesc.constraints) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have h : i + 1 ≠ t.rows.length := by omega
    simpa using h
  simpa only [cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- The `Head` form of `rgate` (`cgH h` is `cg (headToExpr h)` definitionally). -/
theorem rgateH {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace} (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {h : Head}
    (hg : cgH h ∈ automataflResolveDesc.constraints) :
    (headToExpr h).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] :=
  rgate hsat i hi hg

/-! ## §0.2 — Reusable extractors for the two gadget families the descriptor is built from. -/

section Extractors
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **The `Builder::one_hot` extractor.** A two-selector one-hot pinned to a BARE coordinate column
forces `sel1 = idx`, `sel0 = 1 − idx`, and `idx ∈ {0,1} = [0, n)`. Every one-hot in the descriptor
(the auto read, both source reads, both `e_to` endpoint pins) is an instance. -/
theorem oneHot_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (s0 s1 idx : Nat)
    (h0 : cg (gBin s0) ∈ automataflResolveDesc.constraints)
    (h1 : cg (gBin s1) ∈ automataflResolveDesc.constraints)
    (hs : cgH (((Head.c (-1)).addLin 1 s0).addLin 1 s1) ∈ automataflResolveDesc.constraints)
    (hx : cgH ((Head.lin 1 s1).addLin (-1) idx) ∈ automataflResolveDesc.constraints) :
    ((envAt t i).loc idx = 0 ∨ (envAt t i).loc idx = 1)
      ∧ (envAt t i).loc s1 = (envAt t i).loc idx
      ∧ (envAt t i).loc s0 = 1 - (envAt t i).loc idx := by
  set e := envAt t i with he
  have b0 : e.loc s0 = 0 ∨ e.loc s0 = 1 :=
    bin_of_gate (rgate hsat i hi h0) (canon_loc hc i _)
  have b1 : e.loc s1 = 0 ∨ e.loc s1 = 1 :=
    bin_of_gate (rgate hsat i hi h1) (canon_loc hc i _)
  have hsum : e.loc s0 + e.loc s1 = 1 := by
    have hg := rgateH hsat i hi hs
    have hE : (headToExpr (((Head.c (-1)).addLin 1 s0).addLin 1 s1)).eval e.loc
        = e.loc s0 + e.loc s1 + (-1) := rfl
    rw [hE] at hg
    have := (gate_modEq_iff (x := e.loc s0 + e.loc s1 + -1)
      (a := e.loc s0 + e.loc s1) (b := 1) (by ring)).mp hg
    rcases b0 with h | h <;> rcases b1 with h' | h' <;>
      exact eq_of_modEq_small (by rw [h, h']; norm_num) (by norm_num) this
  have hidx : e.loc s1 = e.loc idx := by
    have hg := rgateH hsat i hi hx
    have hE : (headToExpr ((Head.lin 1 s1).addLin (-1) idx)).eval e.loc
        = e.loc s1 + (-1) * e.loc idx := rfl
    rw [hE] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  exact ⟨hidx ▸ b1, hidx, by omega⟩

/-- **The `one` pin.** The always-on `cond_nonzero` selector column really is `1`. -/
theorem one_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc ONE = 1 := by
  have hg := rgateH hsat i hi (h := (Head.lin 1 ONE).addConst (-1)) (mem_resolve_onePin 2)
  have hE : (headToExpr ((Head.lin 1 ONE).addConst (-1))).eval (envAt t i).loc
      = (envAt t i).loc ONE + (-1) := rfl
  rw [hE] at hg
  exact eq_of_modEq_canon (canon_loc hc i _) canon_one ((gate_modEq_iff (by ring)).mp hg)

/-- **The `cond_nonzero` extractor.** `one·(v·inv − 1) == 0` with `one = 1` forces `v ≢ 0 [ZMOD p]`;
for a value already known to lie in a small window that is `v ≠ 0` over ℤ. -/
theorem condNonzero_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (v inv : Nat)
    (hg : cg (gCondNonzero ONE v inv) ∈ automataflResolveDesc.constraints) :
    ¬ ((envAt t i).loc v ≡ 0 [ZMOD 2013265921]) := by
  set e := envAt t i with he
  have hone := one_of_sat hsat hc i hi
  rw [← he] at hone
  have h := rgate hsat i hi hg
  simp only [gCondNonzero, EmittedExpr.eval] at h
  rw [hone, one_mul] at h
  intro hz
  have : (e.loc v * e.loc inv + -1) ≡ (0 * e.loc inv + -1) [ZMOD 2013265921] :=
    Int.ModEq.add (Int.ModEq.mul hz (Int.ModEq.refl _)) (Int.ModEq.refl _)
  have h2 : (0 : ℤ) ≡ -1 [ZMOD 2013265921] := by
    calc (0 : ℤ) ≡ e.loc v * e.loc inv + -1 [ZMOD 2013265921] := h.symm
    _ ≡ 0 * e.loc inv + -1 [ZMOD 2013265921] := this
    _ = -1 := by ring
  exact absurd (eq_of_modEq_small (by norm_num) (by norm_num) h2) (by norm_num)

end Extractors

/-! ## §1 — R1: the WITNESSED auto read pins `(ax, ay)` to the board cell holding AUTO.

The direct mirror of `AutomataflStepRefine.autoPin_of_sat`, keyed on the Leg-R descriptor's own
auto-read block (`autoReadConstraints`, columns `AX_C`/`AY_C` + the `2n` selectors). -/

/-- Decode a satisfying Leg-R row's OLD-board columns into the reference `Board`: size `n`, the
automaton at the witnessed `(AX_C, AY_C)`, cell `(x,y)` the felt-decode of `old[y·n+x]`. -/
def boardDecodeOld (e : VmRowEnv) : Board where
  size          := NN
  automaton     := ⟨(e.loc AX_C).toNat, (e.loc AY_C).toNat⟩
  cells         := fun c => codeToParticle (e.loc (old (c.y * NN + c.x)))
  useColumnRule := true

/-- The same decode over the CLAIMED MID board columns (the automaton is unmoved by resolution —
`applyMoves` never relocates it, and `validate_move` forbids either endpoint being the auto cell). -/
def boardDecodeMid (e : VmRowEnv) : Board where
  size          := NN
  automaton     := ⟨(e.loc AX_C).toNat, (e.loc AY_C).toNat⟩
  cells         := fun c => codeToParticle (e.loc (mid (c.y * NN + c.x)))
  useColumnRule := true

section AutoPin
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **R1 — `autoPinR_of_sat`.** On a satisfying, canonical trace the witnessed `(AX_C, AY_C)` are
legal board coordinates and the OLD board genuinely holds the AUTO particle there. Derived: the
auto row/column one-hots collapse `Σ selRow·selCol·old` to the single selected cell, which
`autoPinHead` forces to `AUTO_CODE = 3`. -/
theorem autoPinR_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ∃ X Y : Nat, X < NN ∧ Y < NN
      ∧ (envAt t i).loc AX_C = (X : ℤ) ∧ (envAt t i).loc AY_C = (Y : ℤ)
      ∧ (envAt t i).loc (old (Y * NN + X)) = AUTO_CODE := by
  set e := envAt t i with he
  obtain ⟨hay, hr1, hr0⟩ :=
    oneHot_of_sat hsat hc i hi (selAutoRow 0) (selAutoRow 1) AY_C
      (mem_resolve_of_mem_autoRead (ar_selRowBit 2 0 (by decide)))
      (mem_resolve_of_mem_autoRead (ar_selRowBit 2 1 (by decide)))
      (mem_resolve_of_mem_autoRead (ar_selRowSum 2))
      (mem_resolve_of_mem_autoRead (ar_selRowIdx 2))
  obtain ⟨hax, hc1, hc0⟩ :=
    oneHot_of_sat hsat hc i hi (selAutoCol 0) (selAutoCol 1) AX_C
      (mem_resolve_of_mem_autoRead (ar_selColBit 2 0 (by decide)))
      (mem_resolve_of_mem_autoRead (ar_selColBit 2 1 (by decide)))
      (mem_resolve_of_mem_autoRead (ar_selColSum 2))
      (mem_resolve_of_mem_autoRead (ar_selColIdx 2))
  rw [← he] at hay hr1 hr0 hax hc1 hc0
  have hEval : (headToExpr autoPinHead).eval e.loc
      = e.loc (selAutoRow 0) * e.loc (selAutoCol 0) * e.loc (old 0)
        + e.loc (selAutoRow 0) * e.loc (selAutoCol 1) * e.loc (old 1)
        + e.loc (selAutoRow 1) * e.loc (selAutoCol 0) * e.loc (old 2)
        + e.loc (selAutoRow 1) * e.loc (selAutoCol 1) * e.loc (old 3) + (-3) := rfl
  have hAuto := rgateH hsat i hi (h := autoPinHead) (mem_resolve_of_mem_autoRead (ar_autoPin 2))
  rw [hEval, hr0, hr1, hc0, hc1] at hAuto
  rcases hay with ay | ay <;> rcases hax with ax | ax
  · refine ⟨0, 0, by norm_num [NN], by norm_num [NN], by exact_mod_cast ax, by exact_mod_cast ay, ?_⟩
    rw [ax, ay] at hAuto
    show e.loc (old 0) = 3
    exact eq_of_modEq_canon (canon_loc hc i _) canon_three ((gate_modEq_iff (by ring)).mp hAuto)
  · refine ⟨1, 0, by norm_num [NN], by norm_num [NN], by exact_mod_cast ax, by exact_mod_cast ay, ?_⟩
    rw [ax, ay] at hAuto
    show e.loc (old 1) = 3
    exact eq_of_modEq_canon (canon_loc hc i _) canon_three ((gate_modEq_iff (by ring)).mp hAuto)
  · refine ⟨0, 1, by norm_num [NN], by norm_num [NN], by exact_mod_cast ax, by exact_mod_cast ay, ?_⟩
    rw [ax, ay] at hAuto
    show e.loc (old 2) = 3
    exact eq_of_modEq_canon (canon_loc hc i _) canon_three ((gate_modEq_iff (by ring)).mp hAuto)
  · refine ⟨1, 1, by norm_num [NN], by norm_num [NN], by exact_mod_cast ax, by exact_mod_cast ay, ?_⟩
    rw [ax, ay] at hAuto
    show e.loc (old 3) = 3
    exact eq_of_modEq_canon (canon_loc hc i _) canon_three ((gate_modEq_iff (by ring)).mp hAuto)

/-- **R1, in `Board` terms.** The decoded OLD board carries the AUTO particle at the decoded
automaton coordinate — the descriptor forces `(ax, ay)` to BE the automaton's cell, not merely a
claimed coordinate, so the `frm ≠ auto` / `to ≠ auto` gates below gate against the real automaton. -/
theorem decodedOld_auto_holds_automaton
    (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (boardDecodeOld (envAt t i)).cellAt (boardDecodeOld (envAt t i)).automaton
      = Particle.automaton := by
  obtain ⟨X, Y, hX, hY, hAX, hAY, hcell⟩ := autoPinR_of_sat hsat hc i hi
  have hxn : ((envAt t i).loc AX_C).toNat = X := by rw [hAX]; simp
  have hyn : ((envAt t i).loc AY_C).toNat = Y := by rw [hAY]; simp
  simp only [Board.cellAt, boardDecodeOld]
  rw [hxn, hyn, hcell, if_pos ⟨hX, hY⟩]
  simp [codeToParticle, AUTO_CODE]

end AutoPin

/-! ## §2 — R2: `validate_move` ⇒ the reference `MoveValid`, and `fp` is the REAL source cell. -/

/-- Decode a move's witnessed coordinate columns into the reference `Move`. -/
def moveDecode (e : VmRowEnv) (which : Nat) : Move :=
  Move.mk 0
    ⟨(e.loc (cFx (mvBase which))).toNat, (e.loc (cFy (mvBase which))).toNat⟩
    ⟨(e.loc (cTx (mvBase which))).toNat, (e.loc (cTy (mvBase which))).toNat⟩

/-- The `validate_move` gate bundle for the move at base `b`, as membership facts in the
BYTE-PINNED constraint list. Both instances are discharged by `decide`, so every R2 fact is
anchored to the emitted descriptor. -/
structure MoveGates (b : Nat) : Prop where
  fxBin  : cg (gBin (cFxLo b)) ∈ automataflResolveDesc.constraints
  fxPin  : cgH ((Head.lin 1 (cFx b)).addLin (-1) (cFxLo b)) ∈ automataflResolveDesc.constraints
  fyBin  : cg (gBin (cFyLo b)) ∈ automataflResolveDesc.constraints
  fyPin  : cgH ((Head.lin 1 (cFy b)).addLin (-1) (cFyLo b)) ∈ automataflResolveDesc.constraints
  txBin  : cg (gBin (cTxLo b)) ∈ automataflResolveDesc.constraints
  txPin  : cgH ((Head.lin 1 (cTx b)).addLin (-1) (cTxLo b)) ∈ automataflResolveDesc.constraints
  tyBin  : cg (gBin (cTyLo b)) ∈ automataflResolveDesc.constraints
  tyPin  : cgH ((Head.lin 1 (cTy b)).addLin (-1) (cTyLo b)) ∈ automataflResolveDesc.constraints
  rook   : cgH (rookAlignHead b) ∈ automataflResolveDesc.constraints
  dsqDef : cgH (dsqHead b) ∈ automataflResolveDesc.constraints
  dsqNz  : cg (gCondNonzero ONE (cDsq b) (cDistinctInv b)) ∈ automataflResolveDesc.constraints
  faDef  : cgH (autoDistHead (cFa b) (cFx b) (cFy b)) ∈ automataflResolveDesc.constraints
  faNz   : cg (gCondNonzero ONE (cFa b) (cFnaInv b)) ∈ automataflResolveDesc.constraints
  taDef  : cgH (autoDistHead (cTa b) (cTx b) (cTy b)) ∈ automataflResolveDesc.constraints
  taNz   : cg (gCondNonzero ONE (cTa b) (cTnaInv b)) ∈ automataflResolveDesc.constraints
  srR0   : cg (gBin (cSelRow0 b)) ∈ automataflResolveDesc.constraints
  srR1   : cg (gBin (cSelRow1 b)) ∈ automataflResolveDesc.constraints
  srRs   : cgH (((Head.c (-1)).addLin 1 (cSelRow0 b)).addLin 1 (cSelRow1 b))
             ∈ automataflResolveDesc.constraints
  srRi   : cgH ((Head.lin 1 (cSelRow1 b)).addLin (-1) (cFy b)) ∈ automataflResolveDesc.constraints
  srC0   : cg (gBin (cSelCol0 b)) ∈ automataflResolveDesc.constraints
  srC1   : cg (gBin (cSelCol1 b)) ∈ automataflResolveDesc.constraints
  srCs   : cgH (((Head.c (-1)).addLin 1 (cSelCol0 b)).addLin 1 (cSelCol1 b))
             ∈ automataflResolveDesc.constraints
  srCi   : cgH ((Head.lin 1 (cSelCol1 b)).addLin (-1) (cFx b)) ∈ automataflResolveDesc.constraints
  srcRd  : cgH (sourceReadHead b) ∈ automataflResolveDesc.constraints

/-- STRUCTURED extraction (was `by constructor <;> decide` over the concrete 379-list): each field is
`the-family-is-in-resolveConstraints ∘ the-gate-is-in-validate_move`, both n-generic. -/
theorem moveGates_a : MoveGates (mvBase 0) :=
  ⟨mem_resolve_of_mem_validateMove0 (vm_fxBin 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_fxHead 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_fyBin 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_fyHead 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_txBin 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_txHead 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_tyBin 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_tyHead 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_rook 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_dsqDef 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_dsqNz 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_faDef 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_faNz 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_taDef 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_taNz 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_selRow 2 (mvBase 0) 0 (by decide))
  , mem_resolve_of_mem_validateMove0 (vm_selRow 2 (mvBase 0) 1 (by decide))
  , mem_resolve_of_mem_validateMove0 (vm_srRs 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_srRi 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_selCol 2 (mvBase 0) 0 (by decide))
  , mem_resolve_of_mem_validateMove0 (vm_selCol 2 (mvBase 0) 1 (by decide))
  , mem_resolve_of_mem_validateMove0 (vm_srCs 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_srCi 2 (mvBase 0))
  , mem_resolve_of_mem_validateMove0 (vm_srcRd 2 (mvBase 0))⟩
theorem moveGates_b : MoveGates (mvBase 1) :=
  ⟨mem_resolve_of_mem_validateMove1 (vm_fxBin 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_fxHead 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_fyBin 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_fyHead 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_txBin 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_txHead 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_tyBin 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_tyHead 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_rook 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_dsqDef 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_dsqNz 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_faDef 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_faNz 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_taDef 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_taNz 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_selRow 2 (mvBase 1) 0 (by decide))
  , mem_resolve_of_mem_validateMove1 (vm_selRow 2 (mvBase 1) 1 (by decide))
  , mem_resolve_of_mem_validateMove1 (vm_srRs 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_srRi 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_selCol 2 (mvBase 1) 0 (by decide))
  , mem_resolve_of_mem_validateMove1 (vm_selCol 2 (mvBase 1) 1 (by decide))
  , mem_resolve_of_mem_validateMove1 (vm_srCs 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_srCi 2 (mvBase 1))
  , mem_resolve_of_mem_validateMove1 (vm_srcRd 2 (mvBase 1))⟩

section ValidateMove
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- A `decompose_coord_le` edge pins its column to its lower bit, hence into `{0,1} = [0, n)`. -/
theorem coord01_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (col lo : Nat)
    (hb : cg (gBin lo) ∈ automataflResolveDesc.constraints)
    (hp : cgH ((Head.lin 1 col).addLin (-1) lo) ∈ automataflResolveDesc.constraints) :
    (envAt t i).loc col = 0 ∨ (envAt t i).loc col = 1 := by
  set e := envAt t i with he
  have hbit : e.loc lo = 0 ∨ e.loc lo = 1 := bin_of_gate (rgate hsat i hi hb) (canon_loc hc i _)
  have hg := rgateH hsat i hi hp
  have hE : (headToExpr ((Head.lin 1 col).addLin (-1) lo)).eval e.loc
      = e.loc col + (-1) * e.loc lo := rfl
  rw [hE] at hg
  have heq : e.loc col = e.loc lo :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  exact heq ▸ hbit

/-- **PURE**: a witnessed squared-distance column over two `{0,1}` coordinate pairs is exactly the
integer squared distance. The window `[0,2] ⊂ [0,p)` makes the field congruence an ℤ equality. -/
theorem sqdist_pure {d x1 x2 y1 y2 : ℤ} (hd : Canon d)
    (hx1 : x1 = 0 ∨ x1 = 1) (hx2 : x2 = 0 ∨ x2 = 1)
    (hy1 : y1 = 0 ∨ y1 = 1) (hy2 : y2 = 0 ∨ y2 = 1)
    (h : d + (-1) * (x1 * x1) + 2 * (x1 * x2) + (-1) * (x2 * x2)
          + (-1) * (y1 * y1) + 2 * (y1 * y2) + (-1) * (y2 * y2) ≡ 0 [ZMOD 2013265921]) :
    d = (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2) := by
  have hval : Canon ((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)) := by
    rcases hx1 with h1 | h1 <;> rcases hx2 with h2 | h2 <;> rcases hy1 with h3 | h3 <;>
      rcases hy2 with h4 | h4 <;> subst h1 <;> subst h2 <;> subst h3 <;> subst h4 <;>
      exact ⟨by norm_num, by norm_num⟩
  exact eq_of_modEq_canon hd hval ((gate_modEq_iff (by ring)).mp h)

/-- **R2 — `validMove_of_sat`.** The `validate_move` block for the move at base `b` FORCES the
reference `MoveValid` on the decoded OLD board: rook-aligned, source ≠ destination, both endpoints
in bounds, and neither endpoint the (witnessed, R1-pinned) automaton cell. -/
theorem validMove_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which b : Nat)
    (hb : b = mvBase which) (mg : MoveGates b) :
    MoveValid (boardDecodeOld (envAt t i)) (moveDecode (envAt t i) which) := by
  subst hb
  set e := envAt t i with he
  set b := mvBase which with hbdef
  have hfx : e.loc (cFx b) = 0 ∨ e.loc (cFx b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.fxBin mg.fxPin
  have hfy : e.loc (cFy b) = 0 ∨ e.loc (cFy b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.fyBin mg.fyPin
  have htx : e.loc (cTx b) = 0 ∨ e.loc (cTx b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.txBin mg.txPin
  have hty : e.loc (cTy b) = 0 ∨ e.loc (cTy b) = 1 :=
    coord01_of_sat hsat hc i hi _ _ mg.tyBin mg.tyPin
  obtain ⟨X, Y, hXlt, hYlt, hAX, hAY, _⟩ := autoPinR_of_sat hsat hc i hi
  rw [← he] at hAX hAY
  have hax : e.loc AX_C = 0 ∨ e.loc AX_C = 1 := by
    rw [hAX]; have : X < 2 := by simpa [NN] using hXlt
    interval_cases X <;> simp
  have hay : e.loc AY_C = 0 ∨ e.loc AY_C = 1 := by
    rw [hAY]; have : Y < 2 := by simpa [NN] using hYlt
    interval_cases Y <;> simp
  -- rook alignment
  have hrook : (e.loc (cFx b) - e.loc (cTx b)) * (e.loc (cFy b) - e.loc (cTy b)) = 0 := by
    have hg := rgateH hsat i hi mg.rook
    have hE : (headToExpr (rookAlignHead b)).eval e.loc
        = e.loc (cFx b) * e.loc (cFy b) + (-1) * (e.loc (cFx b) * e.loc (cTy b))
          + (-1) * (e.loc (cTx b) * e.loc (cFy b)) + e.loc (cTx b) * e.loc (cTy b) := rfl
    rw [hE] at hg
    have hmod : (e.loc (cFx b) - e.loc (cTx b)) * (e.loc (cFy b) - e.loc (cTy b))
        ≡ 0 [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hg
    refine eq_of_modEq_small ?_ (by norm_num) hmod
    rcases hfx with h1 | h1 <;> rcases htx with h2 | h2 <;> rcases hfy with h3 | h3 <;>
      rcases hty with h4 | h4 <;> rw [h1, h2, h3, h4] <;> norm_num
  -- distinctness
  have hdsq : e.loc (cDsq b)
      = (e.loc (cFx b) - e.loc (cTx b)) * (e.loc (cFx b) - e.loc (cTx b))
        + (e.loc (cFy b) - e.loc (cTy b)) * (e.loc (cFy b) - e.loc (cTy b)) := by
    have hg := rgateH hsat i hi mg.dsqDef
    have hE : (headToExpr (dsqHead b)).eval e.loc
        = e.loc (cDsq b) + (-1) * (e.loc (cFx b) * e.loc (cFx b))
          + 2 * (e.loc (cFx b) * e.loc (cTx b)) + (-1) * (e.loc (cTx b) * e.loc (cTx b))
          + (-1) * (e.loc (cFy b) * e.loc (cFy b)) + 2 * (e.loc (cFy b) * e.loc (cTy b))
          + (-1) * (e.loc (cTy b) * e.loc (cTy b)) := rfl
    rw [hE] at hg
    exact sqdist_pure (canon_loc hc i _) hfx htx hfy hty hg
  have hdnz : ¬ ((e.loc (cDsq b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzero_of_sat hsat hc i hi (cDsq b) (cDistinctInv b) mg.dsqNz
    rwa [← he] at this
  have hdistinct : ¬ (e.loc (cFx b) = e.loc (cTx b) ∧ e.loc (cFy b) = e.loc (cTy b)) := by
    rintro ⟨h1, h2⟩
    exact hdnz (by rw [hdsq, h1, h2]; simp [Int.ModEq])
  -- frm ≠ auto
  have hfa : e.loc (cFa b)
      = (e.loc (cFx b) - e.loc AX_C) * (e.loc (cFx b) - e.loc AX_C)
        + (e.loc (cFy b) - e.loc AY_C) * (e.loc (cFy b) - e.loc AY_C) := by
    have hg := rgateH hsat i hi mg.faDef
    have hE : (headToExpr (autoDistHead (cFa b) (cFx b) (cFy b))).eval e.loc
        = e.loc (cFa b) + (-1) * (e.loc (cFx b) * e.loc (cFx b))
          + 2 * (e.loc (cFx b) * e.loc AX_C) + (-1) * (e.loc AX_C * e.loc AX_C)
          + (-1) * (e.loc (cFy b) * e.loc (cFy b)) + 2 * (e.loc (cFy b) * e.loc AY_C)
          + (-1) * (e.loc AY_C * e.loc AY_C) := rfl
    rw [hE] at hg
    exact sqdist_pure (canon_loc hc i _) hfx hax hfy hay hg
  have hfanz : ¬ ((e.loc (cFa b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzero_of_sat hsat hc i hi (cFa b) (cFnaInv b) mg.faNz
    rwa [← he] at this
  have hfnotauto : ¬ (e.loc (cFx b) = e.loc AX_C ∧ e.loc (cFy b) = e.loc AY_C) := by
    rintro ⟨h1, h2⟩
    exact hfanz (by rw [hfa, h1, h2]; simp [Int.ModEq])
  -- to ≠ auto
  have hta : e.loc (cTa b)
      = (e.loc (cTx b) - e.loc AX_C) * (e.loc (cTx b) - e.loc AX_C)
        + (e.loc (cTy b) - e.loc AY_C) * (e.loc (cTy b) - e.loc AY_C) := by
    have hg := rgateH hsat i hi mg.taDef
    have hE : (headToExpr (autoDistHead (cTa b) (cTx b) (cTy b))).eval e.loc
        = e.loc (cTa b) + (-1) * (e.loc (cTx b) * e.loc (cTx b))
          + 2 * (e.loc (cTx b) * e.loc AX_C) + (-1) * (e.loc AX_C * e.loc AX_C)
          + (-1) * (e.loc (cTy b) * e.loc (cTy b)) + 2 * (e.loc (cTy b) * e.loc AY_C)
          + (-1) * (e.loc AY_C * e.loc AY_C) := rfl
    rw [hE] at hg
    exact sqdist_pure (canon_loc hc i _) htx hax hty hay hg
  have htanz : ¬ ((e.loc (cTa b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzero_of_sat hsat hc i hi (cTa b) (cTnaInv b) mg.taNz
    rwa [← he] at this
  have htnotauto : ¬ (e.loc (cTx b) = e.loc AX_C ∧ e.loc (cTy b) = e.loc AY_C) := by
    rintro ⟨h1, h2⟩
    exact htanz (by rw [hta, h1, h2]; simp [Int.ModEq])
  -- assemble `MoveValid`
  have hcast : ∀ z : ℤ, (z = 0 ∨ z = 1) → ((z.toNat : ℤ) = z ∧ z.toNat < 2) := by
    rintro z (h | h) <;> subst h <;> exact ⟨rfl, by norm_num⟩
  obtain ⟨cfx, lfx⟩ := hcast _ hfx
  obtain ⟨cfy, lfy⟩ := hcast _ hfy
  obtain ⟨ctx', ltx⟩ := hcast _ htx
  obtain ⟨cty, lty⟩ := hcast _ hty
  obtain ⟨cax, lax⟩ := hcast _ hax
  obtain ⟨cay, lay⟩ := hcast _ hay
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- frm ≠ to
    intro hEq
    simp only [moveDecode, ← hbdef, Coord.mk.injEq] at hEq
    exact hdistinct ⟨by omega, by omega⟩
  · -- rook-aligned
    simp only [moveDecode, ← hbdef]
    rcases mul_eq_zero.mp hrook with h | h
    · left; omega
    · right; omega
  · simpa [moveDecode, ← hbdef, boardDecodeOld, NN] using lfx
  · simpa [moveDecode, ← hbdef, boardDecodeOld, NN] using lfy
  · simpa [moveDecode, ← hbdef, boardDecodeOld, NN] using ltx
  · simpa [moveDecode, ← hbdef, boardDecodeOld, NN] using lty
  · -- frm is not the automaton
    intro hEq
    simp only [Board.isAutomaton, boardDecodeOld, moveDecode, ← hbdef, Coord.mk.injEq] at hEq
    exact hfnotauto ⟨by omega, by omega⟩
  · -- to is not the automaton
    intro hEq
    simp only [Board.isAutomaton, boardDecodeOld, moveDecode, ← hbdef, Coord.mk.injEq] at hEq
    exact htnotauto ⟨by omega, by omega⟩
  · simp [Board.isConflict, boardDecodeOld]
  · simp [Board.isConflict, boardDecodeOld]

/-- **R2 (cont.) — `sourceRead_of_sat`.** The witnessed source particle `fp` IS the OLD board cell
the move claims to move from: the row×column one-hot collapses `Σ selRow·selCol·old` to the single
cell at `(fx, fy)`. So the non-vacuum bit downstream reads the REAL board, not a free column. -/
theorem sourceRead_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b : Nat) (mg : MoveGates b) :
    ∃ X Y : Nat, X < NN ∧ Y < NN
      ∧ (envAt t i).loc (cFx b) = (X : ℤ) ∧ (envAt t i).loc (cFy b) = (Y : ℤ)
      ∧ (envAt t i).loc (cFp b) = (envAt t i).loc (old (Y * NN + X)) := by
  set e := envAt t i with he
  obtain ⟨hfy, hr1, hr0⟩ :=
    oneHot_of_sat hsat hc i hi (cSelRow0 b) (cSelRow1 b) (cFy b) mg.srR0 mg.srR1 mg.srRs mg.srRi
  obtain ⟨hfx, hc1, hc0⟩ :=
    oneHot_of_sat hsat hc i hi (cSelCol0 b) (cSelCol1 b) (cFx b) mg.srC0 mg.srC1 mg.srCs mg.srCi
  rw [← he] at hfy hr1 hr0 hfx hc1 hc0
  have hg := rgateH hsat i hi mg.srcRd
  have hE : (headToExpr (sourceReadHead b)).eval e.loc
      = e.loc (cFp b)
        + (-1) * (e.loc (cSelRow0 b) * e.loc (cSelCol0 b) * e.loc (old 0))
        + (-1) * (e.loc (cSelRow0 b) * e.loc (cSelCol1 b) * e.loc (old 1))
        + (-1) * (e.loc (cSelRow1 b) * e.loc (cSelCol0 b) * e.loc (old 2))
        + (-1) * (e.loc (cSelRow1 b) * e.loc (cSelCol1 b) * e.loc (old 3)) := rfl
  rw [hE, hr0, hr1, hc0, hc1] at hg
  rcases hfy with hy | hy <;> rcases hfx with hx | hx
  · refine ⟨0, 0, by norm_num [NN], by norm_num [NN], by rw [hx]; rfl, by rw [hy]; rfl, ?_⟩
    rw [hx, hy] at hg
    show e.loc (cFp b) = e.loc (old 0)
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  · refine ⟨1, 0, by norm_num [NN], by norm_num [NN], by rw [hx]; rfl, by rw [hy]; rfl, ?_⟩
    rw [hx, hy] at hg
    show e.loc (cFp b) = e.loc (old 1)
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  · refine ⟨0, 1, by norm_num [NN], by norm_num [NN], by rw [hx]; rfl, by rw [hy]; rfl, ?_⟩
    rw [hx, hy] at hg
    show e.loc (cFp b) = e.loc (old 2)
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  · refine ⟨1, 1, by norm_num [NN], by norm_num [NN], by rw [hx]; rfl, by rw [hy]; rfl, ?_⟩
    rw [hx, hy] at hg
    show e.loc (cFp b) = e.loc (old 3)
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)

end ValidateMove

/-! ## §3 — The `forced_ge0` extractor.

EVERY threshold bit in the descriptor (`iv`, `eqx`, `eqy`, `occ`, `anz`, `bnz`, the four
`eq_coords` bits) is `forced_ge0` over the SAME head shape `(Head.lin 1 val).addConst (-1)`, i.e.
`ib == [val − 1 ≥ 0] == [val ≥ 1]`. One extractor therefore serves the whole descriptor. -/

/-- The `DIFF_RBITS = 9` no-wrap window (the 5-bit twin is `AutomataflStepRefine.forcedGe0_core`).
Given `ib ∈ {0,1}`, a 9-bit range-sum `S ∈ [0, 511]`, and `2·ib·D + ib − D − 1 ≡ S [ZMOD p]` for a
SMALL `D`, the bit IS the comparison — a forged bit has no satisfying decomposition. -/
theorem forcedGe0_wide {ib D S : ℤ}
    (hib : ib = 0 ∨ ib = 1) (hS0 : 0 ≤ S) (hS1 : S ≤ 511)
    (hmod : (2 * ib * D + ib - D - 1) ≡ S [ZMOD 2013265921])
    (hDlo : -1000 ≤ D) (hDhi : D ≤ 1000) :
    (ib = 1 → 0 ≤ D) ∧ (ib = 0 → D ≤ -1) := by
  rcases hib with h | h
  · subst h
    rw [show (2 * (0:ℤ) * D + 0 - D - 1) = -D - 1 by ring] at hmod
    have heq : -D - 1 = S := eq_of_modEq_win (by omega) (by omega) hmod
    exact ⟨by intro hcx; omega, by intro _; omega⟩
  · subst h
    rw [show (2 * (1:ℤ) * D + 1 - D - 1) = D by ring] at hmod
    have heq : D = S := eq_of_modEq_win (by omega) (by omega) hmod
    exact ⟨by intro _; omega, by intro hcx; omega⟩

/-- The 9-bit `forced_ge0` gate bundle at a site `(val, ib, bit0)`. -/
structure Ge0Gates9 (val ib bit0 : Nat) : Prop where
  ibBin : cg (gBin ib) ∈ automataflResolveDesc.constraints
  rb0 : cg (gBin (bit0 + 0)) ∈ automataflResolveDesc.constraints
  rb1 : cg (gBin (bit0 + 1)) ∈ automataflResolveDesc.constraints
  rb2 : cg (gBin (bit0 + 2)) ∈ automataflResolveDesc.constraints
  rb3 : cg (gBin (bit0 + 3)) ∈ automataflResolveDesc.constraints
  rb4 : cg (gBin (bit0 + 4)) ∈ automataflResolveDesc.constraints
  rb5 : cg (gBin (bit0 + 5)) ∈ automataflResolveDesc.constraints
  rb6 : cg (gBin (bit0 + 6)) ∈ automataflResolveDesc.constraints
  rb7 : cg (gBin (bit0 + 7)) ∈ automataflResolveDesc.constraints
  rb8 : cg (gBin (bit0 + 8)) ∈ automataflResolveDesc.constraints
  recomp : cgH ((List.range 9).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
                 (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))
             ∈ automataflResolveDesc.constraints

/-- The `eq == 1 − neq` closing gate of an `eq_scalar` / `eq_coords` block. -/
structure EqPinGate (eqCol neqCol : Nat) : Prop where
  pin : cgH (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1))
          ∈ automataflResolveDesc.constraints

section Ge0
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **The 9-bit `forced_ge0` site extractor.** The witnessed bit `ib` is EXACTLY `[val ≥ 1]`,
provided `val` is known to sit in a small window (which the callers establish from the geometry —
it is never assumed). Derived from the emitted booleanity + recomposition gates. -/
theorem ge0_9_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (val ib bit0 : Nat)
    (gg : Ge0Gates9 val ib bit0)
    (hlo : -999 ≤ (envAt t i).loc val) (hhi : (envAt t i).loc val ≤ 999) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 → 1 ≤ (envAt t i).loc val)
      ∧ ((envAt t i).loc ib = 0 → (envAt t i).loc val ≤ 0) := by
  set e := envAt t i with he
  have hib : e.loc ib = 0 ∨ e.loc ib = 1 :=
    bin_of_gate (rgate hsat i hi gg.ibBin) (canon_loc hc i _)
  have B : ∀ k : Nat, cg (gBin (bit0 + k)) ∈ automataflResolveDesc.constraints →
      (0 ≤ e.loc (bit0 + k) ∧ e.loc (bit0 + k) ≤ 1) := by
    intro k hk
    have hb : e.loc (bit0 + k) = 0 ∨ e.loc (bit0 + k) = 1 :=
      bin_of_gate (rgate hsat i hi hk) (canon_loc hc i _)
    rcases hb with h | h <;> omega
  have h0 := B 0 gg.rb0
  have h1 := B 1 gg.rb1
  have h2 := B 2 gg.rb2
  have h3 := B 3 gg.rb3
  have h4 := B 4 gg.rb4
  have h5 := B 5 gg.rb5
  have h6 := B 6 gg.rb6
  have h7 := B 7 gg.rb7
  have h8 := B 8 gg.rb8
  set S : ℤ := e.loc (bit0 + 0) + 2 * e.loc (bit0 + 1) + 4 * e.loc (bit0 + 2)
    + 8 * e.loc (bit0 + 3) + 16 * e.loc (bit0 + 4) + 32 * e.loc (bit0 + 5)
    + 64 * e.loc (bit0 + 6) + 128 * e.loc (bit0 + 7) + 256 * e.loc (bit0 + 8) with hS
  have hS0 : 0 ≤ S := by rw [hS]; omega
  have hS1 : S ≤ 511 := by rw [hS]; omega
  have hg := rgateH hsat i hi gg.recomp
  have hE : (headToExpr ((List.range 9).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
        (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))).eval e.loc
      = 2 * (e.loc ib * e.loc val) + (-2) * e.loc ib + e.loc ib + (-1) * e.loc val
        + (-1) * e.loc (bit0 + 0) + (-2) * e.loc (bit0 + 1) + (-4) * e.loc (bit0 + 2)
        + (-8) * e.loc (bit0 + 3) + (-16) * e.loc (bit0 + 4) + (-32) * e.loc (bit0 + 5)
        + (-64) * e.loc (bit0 + 6) + (-128) * e.loc (bit0 + 7)
        + (-256) * e.loc (bit0 + 8) := by rfl
  rw [hE] at hg
  have hmod : (2 * e.loc ib * (e.loc val - 1) + e.loc ib - (e.loc val - 1) - 1)
      ≡ S [ZMOD 2013265921] := by
    refine (gate_modEq_iff ?_).mp hg
    rw [hS]; ring
  obtain ⟨hp, hn⟩ := forcedGe0_wide hib hS0 hS1 hmod (by omega) (by omega)
  exact ⟨hib, fun h => by have := hp h; omega, fun h => by have := hn h; omega⟩

/-- The `eq == 1 − neq` gate: the equality bit is the boolean complement of the threshold bit. -/
theorem eqPin_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (eqCol neqCol : Nat)
    (gp : EqPinGate eqCol neqCol)
    (hneq : (envAt t i).loc neqCol = 0 ∨ (envAt t i).loc neqCol = 1) :
    (envAt t i).loc eqCol = 1 - (envAt t i).loc neqCol := by
  set e := envAt t i with he
  have hg := rgateH hsat i hi gp.pin
  have hE : (headToExpr (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1))).eval e.loc
      = e.loc eqCol + e.loc neqCol + (-1) := rfl
  rw [hE] at hg
  have hmod := (gate_modEq_iff (x := e.loc eqCol + e.loc neqCol + -1)
    (a := e.loc eqCol) (b := 1 - e.loc neqCol) (by ring)).mp hg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ hmod
  rcases hneq with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩

end Ge0

/-! ## §4 — R3: the WITNESSED `is_vertical` bit IS the real geometry, and `occ` IS `occluded`. -/

/-- **PURE**: a witnessed 1-D squared-distance column over two `{0,1}` coordinates is exactly the
integer squared difference (the `eq_scalar` head). -/
theorem sq1d_pure {d a c : ℤ} (hd : Canon d) (ha : a = 0 ∨ a = 1) (hcv : c = 0 ∨ c = 1)
    (h : d + (-1) * (a * a) + 2 * (a * c) + (-1) * (c * c) ≡ 0 [ZMOD 2013265921]) :
    d = (a - c) * (a - c) := by
  have hval : Canon ((a - c) * (a - c)) := by
    rcases ha with h1 | h1 <;> rcases hcv with h2 | h2 <;> subst h1 <;> subst h2 <;>
      exact ⟨by norm_num, by norm_num⟩
  exact eq_of_modEq_canon hd hval ((gate_modEq_iff (by ring)).mp h)

/-- The `is_vertical` pin gate bundle for the move at base `b`, occlusion block at `o`. -/
structure IvGates (b o : Nat) : Prop where
  dsqDef : cgH ((((Head.lin 1 (cIvDsq o)).addProd (-1) [cFx b, cFx b]).addProd 2
              [cFx b, cTx b]).addProd (-1) [cTx b, cTx b]) ∈ automataflResolveDesc.constraints
  ge0    : Ge0Gates9 (cIvDsq o) (cIvNeq o) (ivNeqBit o 0)
  eqPin  : EqPinGate (cIv o) (cIvNeq o)

/-- The occlusion tail gate bundle: the two `seg` gates, the masked-sum gate, and the `occ`
threshold site. -/
structure OccGates (o : Nat) : Prop where
  seg0 : cgH (segHead o 0) ∈ automataflResolveDesc.constraints
  seg1 : cgH (segHead o 1) ∈ automataflResolveDesc.constraints
  msum : cgH (msumHead o) ∈ automataflResolveDesc.constraints
  ge0  : Ge0Gates9 (cMsum o) (cOcc o) (occBit o 0)

theorem ivGates_a : IvGates (mvBase 0) (occBase 0) :=
  ⟨mem_resolve_of_mem_validateOcclusion0 (vo_iv_dsq 2 (mvBase 0) (occBase 0) (mvBase 1)),
   ⟨mem_resolve_of_mem_validateOcclusion0 (vo_iv_neqIb 2 (mvBase 0) (occBase 0) (mvBase 1)),
   mem_resolve_of_mem_validateOcclusion0 (vo_iv_neqBit 2 (mvBase 0) (occBase 0) (mvBase 1) 0 (by decide)),
   mem_resolve_of_mem_validateOcclusion0 (vo_iv_neqBit 2 (mvBase 0) (occBase 0) (mvBase 1) 1 (by decide)),
   mem_resolve_of_mem_validateOcclusion0 (vo_iv_neqBit 2 (mvBase 0) (occBase 0) (mvBase 1) 2 (by decide)),
   mem_resolve_of_mem_validateOcclusion0 (vo_iv_neqBit 2 (mvBase 0) (occBase 0) (mvBase 1) 3 (by decide)),
   mem_resolve_of_mem_validateOcclusion0 (vo_iv_neqBit 2 (mvBase 0) (occBase 0) (mvBase 1) 4 (by decide)),
   mem_resolve_of_mem_validateOcclusion0 (vo_iv_neqBit 2 (mvBase 0) (occBase 0) (mvBase 1) 5 (by decide)),
   mem_resolve_of_mem_validateOcclusion0 (vo_iv_neqBit 2 (mvBase 0) (occBase 0) (mvBase 1) 6 (by decide)),
   mem_resolve_of_mem_validateOcclusion0 (vo_iv_neqBit 2 (mvBase 0) (occBase 0) (mvBase 1) 7 (by decide)),
   mem_resolve_of_mem_validateOcclusion0 (vo_iv_neqBit 2 (mvBase 0) (occBase 0) (mvBase 1) 8 (by decide)),
   mem_resolve_of_mem_validateOcclusion0 (vo_iv_neqHead 2 (mvBase 0) (occBase 0) (mvBase 1))⟩,
   ⟨mem_resolve_of_mem_validateOcclusion0 (vo_iv_eqPin 2 (mvBase 0) (occBase 0) (mvBase 1))⟩⟩
theorem ivGates_b : IvGates (mvBase 1) (occBase 1) :=
  ⟨mem_resolve_of_mem_validateOcclusion1 (vo_iv_dsq 2 (mvBase 1) (occBase 1) (mvBase 0)),
   ⟨mem_resolve_of_mem_validateOcclusion1 (vo_iv_neqIb 2 (mvBase 1) (occBase 1) (mvBase 0)),
   mem_resolve_of_mem_validateOcclusion1 (vo_iv_neqBit 2 (mvBase 1) (occBase 1) (mvBase 0) 0 (by decide)),
   mem_resolve_of_mem_validateOcclusion1 (vo_iv_neqBit 2 (mvBase 1) (occBase 1) (mvBase 0) 1 (by decide)),
   mem_resolve_of_mem_validateOcclusion1 (vo_iv_neqBit 2 (mvBase 1) (occBase 1) (mvBase 0) 2 (by decide)),
   mem_resolve_of_mem_validateOcclusion1 (vo_iv_neqBit 2 (mvBase 1) (occBase 1) (mvBase 0) 3 (by decide)),
   mem_resolve_of_mem_validateOcclusion1 (vo_iv_neqBit 2 (mvBase 1) (occBase 1) (mvBase 0) 4 (by decide)),
   mem_resolve_of_mem_validateOcclusion1 (vo_iv_neqBit 2 (mvBase 1) (occBase 1) (mvBase 0) 5 (by decide)),
   mem_resolve_of_mem_validateOcclusion1 (vo_iv_neqBit 2 (mvBase 1) (occBase 1) (mvBase 0) 6 (by decide)),
   mem_resolve_of_mem_validateOcclusion1 (vo_iv_neqBit 2 (mvBase 1) (occBase 1) (mvBase 0) 7 (by decide)),
   mem_resolve_of_mem_validateOcclusion1 (vo_iv_neqBit 2 (mvBase 1) (occBase 1) (mvBase 0) 8 (by decide)),
   mem_resolve_of_mem_validateOcclusion1 (vo_iv_neqHead 2 (mvBase 1) (occBase 1) (mvBase 0))⟩,
   ⟨mem_resolve_of_mem_validateOcclusion1 (vo_iv_eqPin 2 (mvBase 1) (occBase 1) (mvBase 0))⟩⟩
theorem occGates_a : OccGates (occBase 0) :=
  ⟨mem_resolve_of_mem_validateOcclusion0 (vo_seg 2 (mvBase 0) (occBase 0) (mvBase 1) 0 (by decide)),
   mem_resolve_of_mem_validateOcclusion0 (vo_seg 2 (mvBase 0) (occBase 0) (mvBase 1) 1 (by decide)),
   mem_resolve_of_mem_validateOcclusion0 (vo_msum 2 (mvBase 0) (occBase 0) (mvBase 1)),
   ⟨mem_resolve_of_mem_validateOcclusion0 (vo_occ_ib 2 (mvBase 0) (occBase 0) (mvBase 1)),
    mem_resolve_of_mem_validateOcclusion0 (vo_occ_bit 2 (mvBase 0) (occBase 0) (mvBase 1) 0 (by decide)),
    mem_resolve_of_mem_validateOcclusion0 (vo_occ_bit 2 (mvBase 0) (occBase 0) (mvBase 1) 1 (by decide)),
    mem_resolve_of_mem_validateOcclusion0 (vo_occ_bit 2 (mvBase 0) (occBase 0) (mvBase 1) 2 (by decide)),
    mem_resolve_of_mem_validateOcclusion0 (vo_occ_bit 2 (mvBase 0) (occBase 0) (mvBase 1) 3 (by decide)),
    mem_resolve_of_mem_validateOcclusion0 (vo_occ_bit 2 (mvBase 0) (occBase 0) (mvBase 1) 4 (by decide)),
    mem_resolve_of_mem_validateOcclusion0 (vo_occ_bit 2 (mvBase 0) (occBase 0) (mvBase 1) 5 (by decide)),
    mem_resolve_of_mem_validateOcclusion0 (vo_occ_bit 2 (mvBase 0) (occBase 0) (mvBase 1) 6 (by decide)),
    mem_resolve_of_mem_validateOcclusion0 (vo_occ_bit 2 (mvBase 0) (occBase 0) (mvBase 1) 7 (by decide)),
    mem_resolve_of_mem_validateOcclusion0 (vo_occ_bit 2 (mvBase 0) (occBase 0) (mvBase 1) 8 (by decide)),
    mem_resolve_of_mem_validateOcclusion0 (vo_occ_head 2 (mvBase 0) (occBase 0) (mvBase 1))⟩⟩
theorem occGates_b : OccGates (occBase 1) :=
  ⟨mem_resolve_of_mem_validateOcclusion1 (vo_seg 2 (mvBase 1) (occBase 1) (mvBase 0) 0 (by decide)),
   mem_resolve_of_mem_validateOcclusion1 (vo_seg 2 (mvBase 1) (occBase 1) (mvBase 0) 1 (by decide)),
   mem_resolve_of_mem_validateOcclusion1 (vo_msum 2 (mvBase 1) (occBase 1) (mvBase 0)),
   ⟨mem_resolve_of_mem_validateOcclusion1 (vo_occ_ib 2 (mvBase 1) (occBase 1) (mvBase 0)),
    mem_resolve_of_mem_validateOcclusion1 (vo_occ_bit 2 (mvBase 1) (occBase 1) (mvBase 0) 0 (by decide)),
    mem_resolve_of_mem_validateOcclusion1 (vo_occ_bit 2 (mvBase 1) (occBase 1) (mvBase 0) 1 (by decide)),
    mem_resolve_of_mem_validateOcclusion1 (vo_occ_bit 2 (mvBase 1) (occBase 1) (mvBase 0) 2 (by decide)),
    mem_resolve_of_mem_validateOcclusion1 (vo_occ_bit 2 (mvBase 1) (occBase 1) (mvBase 0) 3 (by decide)),
    mem_resolve_of_mem_validateOcclusion1 (vo_occ_bit 2 (mvBase 1) (occBase 1) (mvBase 0) 4 (by decide)),
    mem_resolve_of_mem_validateOcclusion1 (vo_occ_bit 2 (mvBase 1) (occBase 1) (mvBase 0) 5 (by decide)),
    mem_resolve_of_mem_validateOcclusion1 (vo_occ_bit 2 (mvBase 1) (occBase 1) (mvBase 0) 6 (by decide)),
    mem_resolve_of_mem_validateOcclusion1 (vo_occ_bit 2 (mvBase 1) (occBase 1) (mvBase 0) 7 (by decide)),
    mem_resolve_of_mem_validateOcclusion1 (vo_occ_bit 2 (mvBase 1) (occBase 1) (mvBase 0) 8 (by decide)),
    mem_resolve_of_mem_validateOcclusion1 (vo_occ_head 2 (mvBase 1) (occBase 1) (mvBase 0))⟩⟩

section Occlusion
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **R3a — `iv_of_sat`.** The witnessed direction bit is boolean and is EXACTLY the real
geometry: `iv = 1 ↔ fx = tx`. The bit that selects the line scan, the endpoint one-hots and the
passable comparison therefore cannot disagree with the move it gates — this is the property the
compile-time `let is_vertical = …` bake in `moves.rs` could not have. -/
theorem iv_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o : Nat)
    (ig : IvGates b o)
    (hfx : (envAt t i).loc (cFx b) = 0 ∨ (envAt t i).loc (cFx b) = 1)
    (htx : (envAt t i).loc (cTx b) = 0 ∨ (envAt t i).loc (cTx b) = 1) :
    ((envAt t i).loc (cIv o) = 0 ∨ (envAt t i).loc (cIv o) = 1)
      ∧ ((envAt t i).loc (cIv o) = 1 ↔ (envAt t i).loc (cFx b) = (envAt t i).loc (cTx b)) := by
  set e := envAt t i with he
  have hdsq : e.loc (cIvDsq o)
      = (e.loc (cFx b) - e.loc (cTx b)) * (e.loc (cFx b) - e.loc (cTx b)) := by
    have hg := rgateH hsat i hi ig.dsqDef
    have hE : (headToExpr ((((Head.lin 1 (cIvDsq o)).addProd (-1) [cFx b, cFx b]).addProd 2
          [cFx b, cTx b]).addProd (-1) [cTx b, cTx b])).eval e.loc
        = e.loc (cIvDsq o) + (-1) * (e.loc (cFx b) * e.loc (cFx b))
          + 2 * (e.loc (cFx b) * e.loc (cTx b))
          + (-1) * (e.loc (cTx b) * e.loc (cTx b)) := rfl
    rw [hE] at hg
    exact sq1d_pure (canon_loc hc i _) hfx htx hg
  have hbnd : -999 ≤ e.loc (cIvDsq o) ∧ e.loc (cIvDsq o) ≤ 999 := by
    rw [hdsq]; rcases hfx with h1 | h1 <;> rcases htx with h2 | h2 <;> rw [h1, h2] <;> norm_num
  obtain ⟨hnb, hn1, hn0⟩ :=
    ge0_9_of_sat hsat hc i hi (cIvDsq o) (cIvNeq o) (ivNeqBit o 0) ig.ge0 hbnd.1 hbnd.2
  rw [← he] at hnb hn1 hn0
  have hiv : e.loc (cIv o) = 1 - e.loc (cIvNeq o) := by
    have := eqPin_of_sat hsat hc i hi (cIv o) (cIvNeq o) ig.eqPin hnb
    rwa [← he] at this
  refine ⟨by rcases hnb with h | h <;> rw [hiv, h] <;> norm_num, ?_⟩
  constructor
  · intro h1
    have hn : e.loc (cIvNeq o) = 0 := by omega
    have := hn0 hn
    rw [hdsq] at this
    rcases hfx with a | a <;> rcases htx with c | c <;> rw [a, c] at this ⊢ <;>
      first | rfl | (exfalso; revert this; norm_num)
  · intro heq
    have hz : e.loc (cIvDsq o) = 0 := by rw [hdsq, heq]; ring
    have : e.loc (cIvNeq o) = 0 := by
      rcases hnb with h | h
      · exact h
      · have := hn1 h; omega
    omega

/-- **R3b — `occ_of_sat`.** The occlusion bit is FORCED to `0`. At `n = 2` the strictly-between
mask is empty (`segHead` reduces to `seg[k] == 0`), so the masked interior sum is `0` and the
`forced_ge0(msum − 1)` threshold cannot fire. Derived from the emitted gates, not from the
emitter's comment. -/
theorem occ_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (o : Nat) (og : OccGates o) :
    (envAt t i).loc (cOcc o) = 0 := by
  set e := envAt t i with he
  have hseg : ∀ k : Nat, cgH (segHead o k) ∈ automataflResolveDesc.constraints →
      (headToExpr (segHead o k)).eval e.loc = e.loc (cSeg o k) → e.loc (cSeg o k) = 0 := by
    intro k hk hE
    have hg := rgateH hsat i hi hk
    rw [hE] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hs0 : e.loc (cSeg o 0) = 0 := hseg 0 og.seg0 rfl
  have hs1 : e.loc (cSeg o 1) = 0 := hseg 1 og.seg1 rfl
  have hmsum : e.loc (cMsum o) = 0 := by
    have hg := rgateH hsat i hi og.msum
    have hE : (headToExpr (msumHead o)).eval e.loc
        = e.loc (cMsum o) + (-1) * (e.loc (cSeg o 0) * e.loc (cLine o 0))
          + e.loc (cSeg o 0) * e.loc (cOsrc o 0) * e.loc (cLine o 0)
          + (-1) * (e.loc (cSeg o 1) * e.loc (cLine o 1))
          + e.loc (cSeg o 1) * e.loc (cOsrc o 1) * e.loc (cLine o 1) := rfl
    rw [hE, hs0, hs1] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  obtain ⟨hb, h1, _⟩ :=
    ge0_9_of_sat hsat hc i hi (cMsum o) (cOcc o) (occBit o 0) og.ge0
      (by rw [← he, hmsum]; norm_num) (by rw [← he, hmsum]; norm_num)
  rw [← he] at hb h1
  rcases hb with h | h
  · exact h
  · exact absurd (h1 h) (by rw [hmsum]; norm_num)

end Occlusion

/-- **R3b, the reference side.** At `n = 2` a rook move has NO strictly-interior cell, so the
reference `occluded` is constantly `false`. Together with `occ_of_sat` this closes the occlusion
leg: circuit bit `= 0 =` reference predicate, for EVERY in-bounds move and every source set. -/
theorem interior_nil_n2 (f g : Coord) (hf : f.x < 2 ∧ f.y < 2) (hg : g.x < 2 ∧ g.y < 2) :
    interior f g = [] := by
  obtain ⟨fx, fy⟩ := f; obtain ⟨gx, gy⟩ := g
  obtain ⟨h1, h2⟩ := hf; obtain ⟨h3, h4⟩ := hg
  simp only at h1 h2 h3 h4
  interval_cases fx <;> interval_cases fy <;> interval_cases gx <;> interval_cases gy <;> decide

theorem occluded_false_n2 (bd : Board) (srcs : List Coord) (m : Move)
    (hf : m.frm.x < 2 ∧ m.frm.y < 2) (ht : m.to.x < 2 ∧ m.to.y < 2) :
    occluded bd srcs m = false := by
  simp [occluded, interior_nil_n2 m.frm m.to hf ht]

/-! ## §5 — R4: the four `eq_coords` pattern bits + the fork/collide/survive selection.

The pattern bits (§5.1) and the selection ALGEBRA (§5.2) are UNCONDITIONAL. Tying the selection to
the reference `conflictResolve` (§5.4) additionally needs the source-non-vacuum bits to mean
"the source cell is non-vacuum", which is where the descriptor's MISSING board-alphabet range check
(§0, the defect) becomes load-bearing: it is carried as the explicit `BoardAlphabet` envelope. -/

/-- **THE PARTICLE-ALPHABET ENVELOPE — now a THEOREM (`boardvalid_of_sat`), not a hypothesis.**

DEFECT #4, as this refinement found it: `automataflResolveDesc` emitted NO
`assert_member(cell,{0,1,2,3})` family (contrast `AutomataflStepEmit.boardRangeConstraints`, which is
exactly what made Leg A's capstone unconditional). Without it a satisfying witness could carry
`old c = 4`, which `codeToParticle` decodes to VACUUM while the circuit's
`anz = forced_ge0(fp − 1, 5)` reads as NON-VACUUM — a genuine descriptor/reference DISAGREEMENT over
the whole window `fp ∈ [4, p)`, which made the naive capstone FALSE.

FIXED AT SOURCE: `AutomataflResolveEmit.boardRangeConstraints` now emits the `KK + KK` membership
gates on every OLD and MID board column, the wire golden was re-pinned (371 → 379 constraints), and
this predicate is DERIVED from the descriptor by `boardvalid_of_sat` below. It survives as a named
`Prop` only because it is the convenient shape to thread through the alphabet-sensitive lemmas. -/
def BoardAlphabet (e : VmRowEnv) : Prop :=
  ∀ c, c < KK →
    ((e.loc (old c) = 0 ∨ e.loc (old c) = 1 ∨ e.loc (old c) = 2 ∨ e.loc (old c) = 3)
      ∧ (e.loc (mid c) = 0 ∨ e.loc (mid c) = 1 ∨ e.loc (mid c) = 2 ∨ e.loc (mid c) = 3))

/-- The 5-bit (`SMALL_RBITS`) `forced_ge0` gate bundle — the shape the `anz`/`bnz` bits use. -/
structure Ge0Gates5 (val ib bit0 : Nat) : Prop where
  ibBin : cg (gBin ib) ∈ automataflResolveDesc.constraints
  rb0 : cg (gBin (bit0 + 0)) ∈ automataflResolveDesc.constraints
  rb1 : cg (gBin (bit0 + 1)) ∈ automataflResolveDesc.constraints
  rb2 : cg (gBin (bit0 + 2)) ∈ automataflResolveDesc.constraints
  rb3 : cg (gBin (bit0 + 3)) ∈ automataflResolveDesc.constraints
  rb4 : cg (gBin (bit0 + 4)) ∈ automataflResolveDesc.constraints
  recomp : cgH ((List.range 5).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
                 (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))
             ∈ automataflResolveDesc.constraints

/-- An `eq_coords` block: the 2-D squared-distance definition, the threshold site, the `eq` pin. -/
structure EqCoordsGates (xa ya xb yb ec : Nat) : Prop where
  dsqDef : cgH ((((((Head.lin 1 (cEqDsq ec)).addProd (-1) [xa, xa]).addProd 2 [xa, xb]).addProd (-1)
              [xb, xb]).addProd (-1) [ya, ya]).addProd 2 [ya, yb] |>.addProd (-1) [yb, yb])
             ∈ automataflResolveDesc.constraints
  ge0    : Ge0Gates9 (cEqDsq ec) (cEqNeq ec) (eqBitAt ec 0)
  eqPin  : EqPinGate (cEqBit ec) (cEqNeq ec)

section Selection
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **(a) — `boardvalid_of_sat`: THE ALPHABET ENVELOPE IS A THEOREM.** Every OLD and MID board cell
of a satisfying, canonical Leg-R trace lies in the particle alphabet `{VAC, REP, ATT, AUTO}`,
because the descriptor now EMITS `assert_member(cell, {0,1,2,3})` on each of them
(`AutomataflResolveEmit.boardRangeConstraints`). Each membership gate is proved a MEMBER of the
byte-pinned constraint list by `decide`, so this is anchored to the emitted object — not assumed.
With it, `srcNonVac_of_sat` (and everything above it) becomes UNCONDITIONAL. -/
theorem boardvalid_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    BoardAlphabet (envAt t i) := by
  intro c hcK
  have hK : c < 4 := by simpa [KK, NN] using hcK
  interval_cases c <;>
    exact ⟨AutomataflStepRefine.mem4_of_gate
             (rgate hsat i hi (g := memberExpr (old _) [0, 1, 2, 3]) (mem_resolve_of_mem_boardRange (br_old 2 _ (by decide))))
             (canon_loc hc i _),
           AutomataflStepRefine.mem4_of_gate
             (rgate hsat i hi (g := memberExpr (mid _) [0, 1, 2, 3]) (mem_resolve_of_mem_boardRange (br_mid 2 _ (by decide))))
             (canon_loc hc i _)⟩

/-- The 5-bit `forced_ge0` site extractor (the `anz`/`bnz` twin of `ge0_9_of_sat`). -/
theorem ge0_5_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (val ib bit0 : Nat)
    (gg : Ge0Gates5 val ib bit0)
    (hlo : -99 ≤ (envAt t i).loc val) (hhi : (envAt t i).loc val ≤ 99) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 → 1 ≤ (envAt t i).loc val)
      ∧ ((envAt t i).loc ib = 0 → (envAt t i).loc val ≤ 0) := by
  set e := envAt t i with he
  have hib : e.loc ib = 0 ∨ e.loc ib = 1 :=
    bin_of_gate (rgate hsat i hi gg.ibBin) (canon_loc hc i _)
  have B : ∀ k : Nat, cg (gBin (bit0 + k)) ∈ automataflResolveDesc.constraints →
      (0 ≤ e.loc (bit0 + k) ∧ e.loc (bit0 + k) ≤ 1) := by
    intro k hk
    have hb : e.loc (bit0 + k) = 0 ∨ e.loc (bit0 + k) = 1 :=
      bin_of_gate (rgate hsat i hi hk) (canon_loc hc i _)
    rcases hb with h | h <;> omega
  have h0 := B 0 gg.rb0
  have h1 := B 1 gg.rb1
  have h2 := B 2 gg.rb2
  have h3 := B 3 gg.rb3
  have h4 := B 4 gg.rb4
  set S : ℤ := e.loc (bit0 + 0) + 2 * e.loc (bit0 + 1) + 4 * e.loc (bit0 + 2)
    + 8 * e.loc (bit0 + 3) + 16 * e.loc (bit0 + 4) with hS
  have hS0 : 0 ≤ S := by rw [hS]; omega
  have hS1 : S ≤ 31 := by rw [hS]; omega
  have hg := rgateH hsat i hi gg.recomp
  have hE : (headToExpr ((List.range 5).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
        (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))).eval e.loc
      = 2 * (e.loc ib * e.loc val) + (-2) * e.loc ib + e.loc ib + (-1) * e.loc val
        + (-1) * e.loc (bit0 + 0) + (-2) * e.loc (bit0 + 1) + (-4) * e.loc (bit0 + 2)
        + (-8) * e.loc (bit0 + 3) + (-16) * e.loc (bit0 + 4) := by rfl
  rw [hE] at hg
  have hmod : (2 * e.loc ib * (e.loc val - 1) + e.loc ib - (e.loc val - 1) - 1)
      ≡ S [ZMOD 2013265921] := by
    refine (gate_modEq_iff ?_).mp hg
    rw [hS]; ring
  obtain ⟨hp, hn⟩ := forcedGe0_core hib hS0 hS1 hmod (by omega) (by omega)
  exact ⟨hib, fun h => by have := hp h; omega, fun h => by have := hn h; omega⟩

/-- **R4a — `eqCoords_of_sat`.** An `eq_coords` bit is EXACTLY the coordinate-pair equality of the
two witnessed coordinate pairs. Unconditional: the coordinates are pinned to `{0,1}` by
`validate_move`'s `decompose_coord_le`, so the squared distance sits in the `[0,2]` no-wrap window
and the 9-bit `forced_ge0` decides it. -/
theorem eqCoords_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (xa ya xb yb ec : Nat)
    (eg : EqCoordsGates xa ya xb yb ec)
    (h1 : (envAt t i).loc xa = 0 ∨ (envAt t i).loc xa = 1)
    (h2 : (envAt t i).loc ya = 0 ∨ (envAt t i).loc ya = 1)
    (h3 : (envAt t i).loc xb = 0 ∨ (envAt t i).loc xb = 1)
    (h4 : (envAt t i).loc yb = 0 ∨ (envAt t i).loc yb = 1) :
    ((envAt t i).loc (cEqBit ec) = 0 ∨ (envAt t i).loc (cEqBit ec) = 1)
      ∧ ((envAt t i).loc (cEqBit ec) = 1 ↔
          ((envAt t i).loc xa = (envAt t i).loc xb ∧ (envAt t i).loc ya = (envAt t i).loc yb)) := by
  set e := envAt t i with he
  have hdsq : e.loc (cEqDsq ec)
      = (e.loc xa - e.loc xb) * (e.loc xa - e.loc xb)
        + (e.loc ya - e.loc yb) * (e.loc ya - e.loc yb) := by
    have hg := rgateH hsat i hi eg.dsqDef
    have hE : (headToExpr ((((((Head.lin 1 (cEqDsq ec)).addProd (-1) [xa, xa]).addProd 2
          [xa, xb]).addProd (-1) [xb, xb]).addProd (-1) [ya, ya]).addProd 2 [ya, yb]
          |>.addProd (-1) [yb, yb])).eval e.loc
        = e.loc (cEqDsq ec) + (-1) * (e.loc xa * e.loc xa) + 2 * (e.loc xa * e.loc xb)
          + (-1) * (e.loc xb * e.loc xb) + (-1) * (e.loc ya * e.loc ya)
          + 2 * (e.loc ya * e.loc yb) + (-1) * (e.loc yb * e.loc yb) := rfl
    rw [hE] at hg
    exact sqdist_pure (canon_loc hc i _) h1 h3 h2 h4 hg
  have hbnd : -999 ≤ e.loc (cEqDsq ec) ∧ e.loc (cEqDsq ec) ≤ 999 := by
    rw [hdsq]; rcases h1 with a|a <;> rcases h2 with b|b <;> rcases h3 with c|c <;>
      rcases h4 with d|d <;> rw [a, b, c, d] <;> norm_num
  obtain ⟨hnb, hn1, hn0⟩ :=
    ge0_9_of_sat hsat hc i hi (cEqDsq ec) (cEqNeq ec) (eqBitAt ec 0) eg.ge0 hbnd.1 hbnd.2
  rw [← he] at hnb hn1 hn0
  have hbit : e.loc (cEqBit ec) = 1 - e.loc (cEqNeq ec) := by
    have := eqPin_of_sat hsat hc i hi (cEqBit ec) (cEqNeq ec) eg.eqPin hnb
    rwa [← he] at this
  refine ⟨by rcases hnb with h | h <;> rw [hbit, h] <;> norm_num, ?_⟩
  constructor
  · intro hone
    have hn : e.loc (cEqNeq ec) = 0 := by omega
    have hle := hn0 hn
    rw [hdsq] at hle
    rcases h1 with a|a <;> rcases h2 with b|b <;> rcases h3 with c|c <;> rcases h4 with d|d <;>
      rw [a, b, c, d] at hle ⊢ <;> first | exact ⟨rfl, rfl⟩ | (exfalso; revert hle; norm_num)
  · rintro ⟨e1, e2⟩
    have hz : e.loc (cEqDsq ec) = 0 := by rw [hdsq, e1, e2]; ring
    have : e.loc (cEqNeq ec) = 0 := by
      rcases hnb with h | h
      · exact h
      · have := hn1 h; omega
    omega

/-- **R4b — `selection_of_sat`, the SELECTION TRUTH TABLE.** The emitted `fork`, `collide` and
`surv` columns are booleans, and each is EXACTLY its reference condition as a function of the four
pattern bits and the two non-vacuum bits:
`fork ↔ eq_ff ∧ ¬eq_tt`, `collide ↔ eq_tt ∧ ¬eq_ff ∧ anz ∧ bnz`, `surv ↔ ¬fork ∧ ¬collide`.
Unconditional — pure gate algebra over columns already known boolean. -/
theorem selection_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hff : (envAt t i).loc (cEqBit (eqBase 0)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 0)) = 1)
    (htt : (envAt t i).loc (cEqBit (eqBase 1)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 1)) = 1)
    (hanz : (envAt t i).loc cAnz = 0 ∨ (envAt t i).loc cAnz = 1)
    (hbnz : (envAt t i).loc cBnz = 0 ∨ (envAt t i).loc cBnz = 1) :
    ((envAt t i).loc cFork = 1 ↔
        ((envAt t i).loc (cEqBit (eqBase 0)) = 1 ∧ (envAt t i).loc (cEqBit (eqBase 1)) = 0))
    ∧ ((envAt t i).loc cCollide = 1 ↔
        ((envAt t i).loc (cEqBit (eqBase 1)) = 1 ∧ (envAt t i).loc (cEqBit (eqBase 0)) = 0
          ∧ (envAt t i).loc cAnz = 1 ∧ (envAt t i).loc cBnz = 1))
    ∧ ((envAt t i).loc cSurv = 0 ∨ (envAt t i).loc cSurv = 1)
    ∧ ((envAt t i).loc cSurv = 1 ↔
        ((envAt t i).loc cFork = 0 ∧ (envAt t i).loc cCollide = 0)) := by
  set e := envAt t i with he
  have hforkv : e.loc cFork
      = e.loc (cEqBit (eqBase 0)) - e.loc (cEqBit (eqBase 0)) * e.loc (cEqBit (eqBase 1)) := by
    have hg := rgateH hsat i hi
      (h := ((Head.lin 1 cFork).addLin (-1) (cEqBit (eqBase 0))).addProd 1
              [cEqBit (eqBase 0), cEqBit (eqBase 1)]) (mem_selection_idx 2 0 (by decide))
    have hE : (headToExpr (((Head.lin 1 cFork).addLin (-1) (cEqBit (eqBase 0))).addProd 1
          [cEqBit (eqBase 0), cEqBit (eqBase 1)])).eval e.loc
        = e.loc cFork + (-1) * e.loc (cEqBit (eqBase 0))
          + e.loc (cEqBit (eqBase 0)) * e.loc (cEqBit (eqBase 1)) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rcases htt with b | b <;> rw [a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hnff : e.loc cNeqFf = 1 - e.loc (cEqBit (eqBase 0)) := by
    have hg := rgateH hsat i hi (h := ((Head.lin 1 cNeqFf).addLin 1 (cEqBit (eqBase 0))).addConst (-1)) (mem_selection_idx 2 1 (by decide))
    have hE : (headToExpr (((Head.lin 1 cNeqFf).addLin 1 (cEqBit (eqBase 0))).addConst (-1))).eval
        e.loc = e.loc cNeqFf + e.loc (cEqBit (eqBase 0)) + (-1) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rw [a] <;> exact ⟨by norm_num, by norm_num⟩
  have hcol1 : e.loc cCol1 = e.loc (cEqBit (eqBase 1)) * e.loc cNeqFf := by
    have hg := rgateH hsat i hi (h := (Head.lin (-1) cCol1).addProd 1 [cEqBit (eqBase 1), cNeqFf]) (mem_selection_idx 2 2 (by decide))
    have hE : (headToExpr ((Head.lin (-1) cCol1).addProd 1
        [cEqBit (eqBase 1), cNeqFf])).eval e.loc
        = (-1) * e.loc cCol1 + e.loc (cEqBit (eqBase 1)) * e.loc cNeqFf := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rw [hnff, a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hcol2 : e.loc cCol2 = e.loc cCol1 * e.loc cAnz := by
    have hg := rgateH hsat i hi (h := (Head.lin (-1) cCol2).addProd 1 [cCol1, cAnz]) (mem_selection_idx 2 3 (by decide))
    have hE : (headToExpr ((Head.lin (-1) cCol2).addProd 1 [cCol1, cAnz])).eval e.loc
        = (-1) * e.loc cCol2 + e.loc cCol1 * e.loc cAnz := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rw [hcol1, hnff, a, b, c] <;> exact ⟨by norm_num, by norm_num⟩
  have hcollv : e.loc cCollide = e.loc cCol2 * e.loc cBnz := by
    have hg := rgateH hsat i hi (h := (Head.lin (-1) cCollide).addProd 1 [cCol2, cBnz]) (mem_selection_idx 2 4 (by decide))
    have hE : (headToExpr ((Head.lin (-1) cCollide).addProd 1 [cCol2, cBnz])).eval e.loc
        = (-1) * e.loc cCollide + e.loc cCol2 * e.loc cBnz := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rcases hbnz with d | d <;> rw [hcol2, hcol1, hnff, a, b, c, d] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hsurvv : e.loc cSurv
      = 1 - e.loc cFork - e.loc cCollide + e.loc cFork * e.loc cCollide := by
    have hg := rgateH hsat i hi
      (h := ((((Head.lin 1 cSurv).addConst (-1)).addLin 1 cFork).addLin 1 cCollide).addProd (-1)
              [cFork, cCollide]) (mem_selection_idx 2 5 (by decide))
    have hE : (headToExpr (((((Head.lin 1 cSurv).addConst (-1)).addLin 1 cFork).addLin 1
        cCollide).addProd (-1) [cFork, cCollide])).eval e.loc
        = e.loc cSurv + e.loc cFork + e.loc cCollide
          + (-1) * (e.loc cFork * e.loc cCollide) + (-1) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rcases hbnz with d | d <;> rw [hforkv, hcollv, hcol2, hcol1, hnff, a, b, c, d] <;>
      exact ⟨by norm_num, by norm_num⟩
  rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
    rcases hbnz with d | d <;>
    rw [hcollv, hcol2, hcol1, hnff] at hsurvv ⊢ <;> rw [hforkv] at hsurvv ⊢ <;>
    rw [a, b, c, d] at hsurvv ⊢ <;> norm_num at hsurvv ⊢ <;>
    simp_all


/-- **R4c — `srcNonVac_of_sat`.** The source-non-vacuum bit is EXACTLY the reference predicate
"the decoded OLD board carries a piece at this move's source". This is the ONE place where the
board-alphabet range check is load-bearing: without it a witness may set `fp = 4`, satisfying
`anz = 1` while `codeToParticle 4 = .vacuum`. That check is now EMITTED (DEFECT #4, fixed), so the
envelope arrives from `boardvalid_of_sat` and this theorem is UNCONDITIONAL. -/
theorem srcNonVac_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which ib bit0 : Nat)
    (mg : MoveGates (mvBase which)) (gg : Ge0Gates5 (cFp (mvBase which)) ib bit0) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 ↔
          ((boardDecodeOld (envAt t i)).cellAt (moveDecode (envAt t i) which).frm).isVacuum
            = false) := by
  have halpha : BoardAlphabet (envAt t i) := boardvalid_of_sat hsat hc i hi
  set e := envAt t i with he
  obtain ⟨X, Y, hX, hY, hfx, hfy, hfp⟩ := sourceRead_of_sat hsat hc i hi (mvBase which) mg
  rw [← he] at hfx hfy hfp
  have hXY : Y * NN + X < KK := by
    have : X < 2 := by simpa [NN] using hX
    have : Y < 2 := by simpa [NN] using hY
    simp only [KK, NN]; omega
  obtain ⟨hcellAlpha, _⟩ := halpha (Y * NN + X) hXY
  have hbnd : -99 ≤ e.loc (cFp (mvBase which)) ∧ e.loc (cFp (mvBase which)) ≤ 99 := by
    rw [hfp]; rcases hcellAlpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  obtain ⟨hb, h1, h0⟩ :=
    ge0_5_of_sat hsat hc i hi (cFp (mvBase which)) ib bit0 gg hbnd.1 hbnd.2
  rw [← he] at hb h1 h0
  -- the decoded board cell at the move's source IS `fp`
  have hcell : (boardDecodeOld e).cellAt (moveDecode e which).frm
      = codeToParticle (e.loc (cFp (mvBase which))) := by
    have hxn : (e.loc (cFx (mvBase which))).toNat = X := by rw [hfx]; simp
    have hyn : (e.loc (cFy (mvBase which))).toNat = Y := by rw [hfy]; simp
    simp only [Board.cellAt, boardDecodeOld, moveDecode]
    rw [hxn, hyn, if_pos ⟨by simpa [NN] using hX, by simpa [NN] using hY⟩, hfp]
  rw [hcell]
  have hfpv : e.loc (cFp (mvBase which)) = 0 ∨ e.loc (cFp (mvBase which)) = 1
      ∨ e.loc (cFp (mvBase which)) = 2 ∨ e.loc (cFp (mvBase which)) = 3 := by
    rw [hfp]; exact hcellAlpha
  refine ⟨hb, ?_⟩
  rcases hfpv with hv | hv | hv | hv <;> rw [hv] at h1 h0 ⊢ <;>
    norm_num [codeToParticle, Particle.isVacuum] <;>
    (first
      | (intro hone; have := h1 hone; omega)
      | (rcases hb with hz | ho
         · exact absurd (h0 hz) (by norm_num)
         · exact ho))

/-! ## §5.5 — (b) R4 COROLLARY: the emitted selection IS the reference `conflictResolve`.

The circuit's leg 4 computes three booleans (`fork`, `collide`, `surv`) out of four coordinate-pair
equality bits and two source-non-vacuum bits. The reference computes a LIST: it filters `[ma, mb]`
by "touches no conflicted source and no conflicted destination", where each conflict is an
order-free `hasTwoDistinct` over a sub-list. These are different shapes; this section proves them
the same object at `m = 2`.

The key structural facts, both proved below by exhausting the four decidable equalities: at a
2-element move list `frmConflict` and `toConflict` take the SAME value on `ma` as on `mb` — so the
filter keeps BOTH moves or NEITHER — and those values are literally the circuit's `fork` and
`collide` patterns. -/

section ConflictPair

/-- `frmConflict` at `m = 2` is the circuit's `fork` pattern `eq_ff ∧ ¬eq_tt`, on either move. -/
theorem frmConflict_pair (ma mb : Move) :
    (frmConflict [ma, mb] ma = true ↔ (ma.frm = mb.frm ∧ ma.to ≠ mb.to))
      ∧ (frmConflict [ma, mb] mb = true ↔ (ma.frm = mb.frm ∧ ma.to ≠ mb.to)) := by
  constructor <;>
    (by_cases hf : ma.frm = mb.frm <;> by_cases ht : ma.to = mb.to <;>
      simp [frmConflict, hasTwoDistinct, hf, ht, eq_comm])

/-- `toConflict` at `m = 2` is the circuit's `collide` pattern
`eq_tt ∧ ¬eq_ff ∧ anz ∧ bnz`, on either move. The two non-vacuum conjuncts enter because the
reference's destination-conflict filter only counts sources that CARRY a piece — exactly the
`anz`/`bnz` conjuncts of `selectionConstraints`. -/
theorem toConflict_pair (bd : Board) (ma mb : Move) :
    (toConflict bd [ma, mb] ma = true ↔
        (ma.to = mb.to ∧ ma.frm ≠ mb.frm
          ∧ (bd.cellAt ma.frm).isVacuum = false ∧ (bd.cellAt mb.frm).isVacuum = false))
      ∧ (toConflict bd [ma, mb] mb = true ↔
        (ma.to = mb.to ∧ ma.frm ≠ mb.frm
          ∧ (bd.cellAt ma.frm).isVacuum = false ∧ (bd.cellAt mb.frm).isVacuum = false)) := by
  constructor <;>
    (by_cases hf : ma.frm = mb.frm <;> by_cases ht : ma.to = mb.to <;>
      by_cases hva : (bd.cellAt ma.frm).isVacuum = true <;>
      by_cases hvb : (bd.cellAt mb.frm).isVacuum = true <;>
      simp_all [toConflict, hasTwoDistinct, Particle.isVacuum] <;>
      first
        | exact ⟨fun h => ht h.symm, fun h => absurd h.symm ht⟩
        | exact fun h => absurd h.symm ht
        | exact fun h => absurd h.symm hf
        | tauto)

/-- **(b) — `conflictResolve_pair`: THE R4 COROLLARY.** On the 2-element move list the reference
conflict resolution is ALL-OR-NOTHING, and the "all" branch is precisely the circuit's `surv = 1`:

    conflictResolve bd [ma, mb] = if fork ∨ collide then [] else [ma, mb]

with `fork` and `collide` spelled in exactly the terms `selection_of_sat` delivers. -/
theorem conflictResolve_pair (bd : Board) (ma mb : Move) :
    conflictResolve bd [ma, mb]
      = if (ma.frm = mb.frm ∧ ma.to ≠ mb.to)
           ∨ (ma.to = mb.to ∧ ma.frm ≠ mb.frm
               ∧ (bd.cellAt ma.frm).isVacuum = false ∧ (bd.cellAt mb.frm).isVacuum = false)
        then [] else [ma, mb] := by
  obtain ⟨hfa, hfb⟩ := frmConflict_pair ma mb
  obtain ⟨hta, htb⟩ := toConflict_pair bd ma mb
  by_cases hcond : (ma.frm = mb.frm ∧ ma.to ≠ mb.to)
           ∨ (ma.to = mb.to ∧ ma.frm ≠ mb.frm
               ∧ (bd.cellAt ma.frm).isVacuum = false ∧ (bd.cellAt mb.frm).isVacuum = false)
  · rcases hcond with h | h
    · simp [conflictResolve, List.filter, hfa.mpr h, hfb.mpr h,
        if_pos (show (ma.frm = mb.frm ∧ ma.to ≠ mb.to)
           ∨ (ma.to = mb.to ∧ ma.frm ≠ mb.frm
               ∧ (bd.cellAt ma.frm).isVacuum = false
               ∧ (bd.cellAt mb.frm).isVacuum = false) from Or.inl h)]
    · simp [conflictResolve, List.filter, hta.mpr h, htb.mpr h,
        if_pos (show (ma.frm = mb.frm ∧ ma.to ≠ mb.to)
           ∨ (ma.to = mb.to ∧ ma.frm ≠ mb.frm
               ∧ (bd.cellAt ma.frm).isVacuum = false
               ∧ (bd.cellAt mb.frm).isVacuum = false) from Or.inr h)]
  · have h1 : frmConflict [ma, mb] ma = false := by
      simpa using fun h => hcond (Or.inl (hfa.mp h))
    have h2 : frmConflict [ma, mb] mb = false := by
      simpa using fun h => hcond (Or.inl (hfb.mp h))
    have h3 : toConflict bd [ma, mb] ma = false := by
      simpa using fun h => hcond (Or.inr (hta.mp h))
    have h4 : toConflict bd [ma, mb] mb = false := by
      simpa using fun h => hcond (Or.inr (htb.mp h))
    simp [conflictResolve, List.filter, h1, h2, h3, h4, if_neg hcond]

end ConflictPair

/-! ## §5.6 — (c), the REFERENCE HALF of R5: the `m = 2` caterpillar, resolved.

Leg 6 of the descriptor computes two flow-through bits and interpolates each piece's landing square
between its own `to` and the other piece's `to`. The reference computes the same landing by
`followChain` over the move graph `nextOf`. These four lemmas resolve the reference side completely
at `n = 2`: the move graph is a two-entry lookup table (`nextOf_pair` — using `occluded_false_n2`,
so no occlusion survives at this board size), and the chain terminates in exactly the three shapes
the circuit's `ft` bit distinguishes:

  * `followChain_own` — no chain relation (`to_a ≠ frm_b`): the piece lands on its OWN `to`;
  * `followChain_own_landing` — the chain relation holds but the next square is a PIECE source
    (`bnz`, the circuit's `¬ft` conjunct): the caterpillar STOPS there, again the piece's own `to`;
  * `followChain_flowThrough` — the chain relation holds, the next square is VACATING (`¬bnz`) and
    the 2-cycle is broken (`to_b ≠ frm_a`, the circuit's `¬eq_ba` conjunct): the piece flows
    THROUGH to `to_b`. This is exactly `ft_a = 1 ⇒ dest_a = to_b`.

The three cases are jointly exhaustive and pairwise exclusive on the same conditions the emitted
`flowThroughConstraints` branch on, so the reference landing square is a function of precisely the
circuit's `ft` bit. What is NOT yet proven here is the CIRCUIT half of R5 (an `ft_of_sat` extractor
tying the `cFtA`/`cFtB` columns to those conditions) — see the file header for the residual. -/

section Caterpillar

open Dregg2.Games.Automatafl (nextOf followChain)

/-- The `m = 2` move graph is a two-entry lookup: `frm_a ↦ to_a`, `frm_b ↦ to_b`, nothing else.
At `n = 2` no rook move has a strictly-interior cell, so `occluded` never fires (`interior_nil_n2`)
and the graph is unconditional in the board. -/
theorem nextOf_pair (bd : Board) (ma mb : Move) (c : Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2) :
    nextOf bd [ma, mb] [ma.frm, mb.frm] c
      = if c = ma.frm then some ma.to else if c = mb.frm then some mb.to else none := by
  have oa := occluded_false_n2 bd [ma.frm, mb.frm] ma h1 h2
  have ob := occluded_false_n2 bd [ma.frm, mb.frm] mb h3 h4
  by_cases ha : c = ma.frm
  · subst ha; simp [nextOf, oa]
  · by_cases hb : c = mb.frm
    · subst hb; simp [nextOf, oa, ob, Ne.symm ha, ha]
    · simp [nextOf, oa, ob, ha, hb, Ne.symm ha, Ne.symm hb]

/-- NO chain relation (`to_a ≠ frm_b`) and the destination is not a carrying source ⇒ the piece
lands on its own destination. -/
theorem followChain_own (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hd : ma.frm ≠ ma.to) (hne : ma.to ≠ mb.frm) (hps : ps.contains ma.to = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1) = ma.to := by
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [if_neg (by simp : ¬ ([] : List Coord).contains ma.to = true),
    if_neg (by rw [hps]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb ma.to h1 h2 h3 h4, if_neg (Ne.symm hd), if_neg hne]

/-- **DEFECT #8'S CASE, AT `n = 2`.** The destination is a CARRYING source with no move of its own
(`to_a ≠ frm_b`, so no edge leaves it): the piece there does NOT vacate, so A's move FAILS TO EXECUTE
and A stays on `frm_a` keeping its particle. The pre-fix chain landed A on `to_a` regardless, which
put two journeys on one square and dropped a piece. NOT a conflict — nothing is flagged. -/
theorem followChain_blocked (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hd : ma.frm ≠ ma.to) (hne : ma.to ≠ mb.frm) (hps : ps.contains ma.to = true) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1) = ma.frm := by
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [if_neg (by simp : ¬ ([] : List Coord).contains ma.to = true), if_pos hps,
    nextOf_pair bd ma mb ma.to h1 h2 h3 h4, if_neg (Ne.symm hd), if_neg hne]
  simp

/-- The next square is itself a PIECE source (the circuit's `bnz` conjunct, which NEGATES `ft`) AND
it is the OTHER MOVE'S source, so it has an edge and vacates ⇒ the caterpillar STOPS there: the piece
lands on its own destination. (The `ma.to = mb.frm` hypothesis is what defect #8's fix demands —
without an edge out of `to_a` the move fails instead, `followChain_blocked`.) -/
theorem followChain_own_landing (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hd : ma.frm ≠ ma.to) (hab : ma.to = mb.frm) (hps : ps.contains ma.to = true) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1) = ma.to := by
  have hfrm : mb.frm ≠ ma.frm := by rw [← hab]; exact fun h => hd h.symm
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [if_neg (by simp : ¬ ([] : List Coord).contains ma.to = true), if_pos hps, hab,
    nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg hfrm, if_pos rfl]
  simp

/-- **THE FLOW-THROUGH CASE.** `to_a = frm_b` (the circuit's `eq_ab`), `frm_b` is NOT a piece source
(`¬bnz`), and the 2-cycle is broken (`to_b ≠ frm_a`, the circuit's `¬eq_ba`) ⇒ the piece rides the
vacating square and lands on `to_b`. This IS `ft_a = 1 ⇒ dest_a = to_b`, on the reference side. -/
theorem followChain_flowThrough (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (hab : ma.to = mb.frm) (hba : mb.to ≠ ma.frm)
    (hps : ps.contains mb.frm = false) (hpsb : ps.contains mb.to = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1) = mb.to := by
  have hfrm : mb.frm ≠ ma.frm := by rw [← hab]; exact fun h => hda h.symm
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [hab, if_neg (by simp : ¬ ([] : List Coord).contains mb.frm = true),
    if_neg (by rw [hps]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg hfrm, if_pos rfl]
  dsimp only
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg hfrm, if_pos rfl]
  dsimp only
  rw [if_neg (by simpa using hba), if_neg (by rw [hpsb]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb mb.to h1 h2 h3 h4, if_neg hba, if_neg (Ne.symm hdb)]

/-- **THE FOURTH CASE — the 2-CYCLE, which the other three lemmas do NOT cover.** `to_a = frm_b`
(the chain relation), `frm_b` is vacating (`¬bnz`, so the caterpillar does not stop there) and
`to_b = frm_a` — the two moves swap. `followChain` detects the revisit of `frm_a` and returns the
square it was standing on, i.e. `to_a`. The circuit agrees by NEGATION: `ft_a` carries the `¬eq_ba`
conjunct, so `ft_a = 0` and the interpolated destination is the piece's own `to_a`.

FOUND WHILE CLOSING R5: the three earlier lemmas are NOT jointly exhaustive — `to_a = mb.frm`,
`¬ps.contains mb.frm`, `to_b = frm_a` falls through all of them. This lemma closes that hole. -/
theorem followChain_twoCycle (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hda : ma.frm ≠ ma.to) (hab : ma.to = mb.frm) (hba : mb.to = ma.frm)
    (hps : ps.contains mb.frm = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1) = ma.to := by
  have hfrm : mb.frm ≠ ma.frm := by rw [← hab]; exact fun h => hda h.symm
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [hab, if_neg (by simp : ¬ ([] : List Coord).contains mb.frm = true),
    if_neg (by rw [hps]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg hfrm, if_pos rfl]
  dsimp only
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg hfrm, if_pos rfl]
  dsimp only
  rw [hba, if_pos (by simp : ([ma.frm] : List Coord).contains ma.frm = true)]

/-- **THE A-SIDE LANDING, ALL FIVE CASES.** The reference chain destination from `frm_a` is `to_b`
EXACTLY on the circuit's `ft_a` pattern (`eq_ab ∧ ¬bnz ∧ ¬eq_ba`, with `surv`/`¬occ` already
discharged); it is `frm_a` — the move FAILS TO EXECUTE, defect #8's fix — when `to_a` holds a
carrying piece with no move of its own; and the piece's own `to_a` otherwise. This is the reference
half of R5, complete.

The MIDDLE branch is the one the pre-fix reference got wrong (it landed on `to_a` and dropped the
piece standing there). It is EMPTY at the descriptor's call sites — see the two uses in §C, where
`ps` is `[frm_a]` / `[frm_b]` / `[frm_a, frm_b]` and the conjunct is unsatisfiable — which is why
the emitted `ft` gates still match the reference at `NN = 2`. -/
theorem chainDest_a (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (hpsb : ma.to = mb.frm → ps.contains mb.frm = false → mb.to ≠ ma.frm →
      ps.contains mb.to = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps ma.frm [] (f + 1 + 1)
      = if ma.to = mb.frm ∧ ps.contains mb.frm = false ∧ mb.to ≠ ma.frm then mb.to
        else if ps.contains ma.to = true ∧ ma.to ≠ mb.frm then ma.frm
        else ma.to := by
  by_cases hab : ma.to = mb.frm
  · have hmid : ¬ (ps.contains ma.to = true ∧ ma.to ≠ mb.frm) := by
      rintro ⟨-, h⟩; exact h hab
    rw [if_neg hmid]
    by_cases hbnz : ps.contains mb.frm = false
    · by_cases hba : mb.to = ma.frm
      · rw [if_neg (by rintro ⟨_, _, h⟩; exact h hba)]
        exact followChain_twoCycle bd ma mb ps h1 h2 h3 h4 hda hab hba hbnz f
      · rw [if_pos ⟨hab, hbnz, hba⟩]
        exact followChain_flowThrough bd ma mb ps h1 h2 h3 h4 hda hdb hab hba hbnz
          (hpsb hab hbnz hba) f
    · rw [if_neg (by rintro ⟨_, h, _⟩; exact hbnz h)]
      exact followChain_own_landing bd ma mb ps h1 h2 h3 h4 hda hab
        (by rw [hab]; simpa using hbnz) (f + 1)
  · rw [if_neg (by rintro ⟨h, _, _⟩; exact hab h)]
    by_cases hps : ps.contains ma.to = true
    · rw [if_pos ⟨hps, hab⟩]
      exact followChain_blocked bd ma mb ps h1 h2 h3 h4 hda hab hps (f + 1)
    · rw [if_neg (by rintro ⟨h, -⟩; exact hps h)]
      exact followChain_own bd ma mb ps h1 h2 h3 h4 hda hab (by simpa using hps) (f + 1)

/-! ### The B-SIDE mirrors. `nextOf`'s lookup table is scanned in list order, so the B-side chain
needs the sources DISTINCT (`frm_a ≠ frm_b`) for `frm_b`'s edge to be reachable — which is exactly
the configuration the capstone establishes whenever piece B carries. -/

theorem followChain_ownB (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hne : ma.frm ≠ mb.frm) (hd : mb.frm ≠ mb.to) (hnb : mb.to ≠ ma.frm)
    (hps : ps.contains mb.to = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1) = mb.to := by
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg (Ne.symm hne), if_pos rfl]
  dsimp only
  rw [if_neg (by simp : ¬ ([] : List Coord).contains mb.to = true),
    if_neg (by rw [hps]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb mb.to h1 h2 h3 h4, if_neg hnb, if_neg (Ne.symm hd)]

/-- **DEFECT #8'S CASE, B SIDE.** `to_b` carries a piece with no move of its own ⇒ B's move fails to
execute and B stays on `frm_b`. -/
theorem followChain_blockedB (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hne : ma.frm ≠ mb.frm) (hd : mb.frm ≠ mb.to) (hnb : mb.to ≠ ma.frm)
    (hps : ps.contains mb.to = true) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1) = mb.frm := by
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg (Ne.symm hne), if_pos rfl]
  dsimp only
  rw [if_neg (by simp : ¬ ([] : List Coord).contains mb.to = true), if_pos hps,
    nextOf_pair bd ma mb mb.to h1 h2 h3 h4, if_neg hnb, if_neg (Ne.symm hd)]
  simp

theorem followChain_own_landingB (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hne : ma.frm ≠ mb.frm) (hba : mb.to = ma.frm) (hps : ps.contains mb.to = true) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1) = mb.to := by
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg (Ne.symm hne), if_pos rfl]
  dsimp only
  rw [if_neg (by simp : ¬ ([] : List Coord).contains mb.to = true), if_pos hps, hba,
    nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  simp

theorem followChain_flowThroughB (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hne : ma.frm ≠ mb.frm) (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (hba : mb.to = ma.frm) (hab : ma.to ≠ mb.frm)
    (hps : ps.contains ma.frm = false) (hpsa : ps.contains ma.to = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1) = ma.to := by
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg (Ne.symm hne), if_pos rfl]
  dsimp only
  rw [hba, if_neg (by simp : ¬ ([] : List Coord).contains ma.frm = true),
    if_neg (by rw [hps]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [if_neg (by simpa using hab), if_neg (by rw [hpsa]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb ma.to h1 h2 h3 h4, if_neg (Ne.symm hda), if_neg hab]

theorem followChain_twoCycleB (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hne : ma.frm ≠ mb.frm) (hdb : mb.frm ≠ mb.to)
    (hba : mb.to = ma.frm) (hab : ma.to = mb.frm)
    (hps : ps.contains ma.frm = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1) = mb.to := by
  rw [followChain, nextOf_pair bd ma mb mb.frm h1 h2 h3 h4, if_neg (Ne.symm hne), if_pos rfl]
  dsimp only
  rw [hba, if_neg (by simp : ¬ ([] : List Coord).contains ma.frm = true),
    if_neg (by rw [hps]; exact Bool.false_ne_true),
    nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [followChain, nextOf_pair bd ma mb ma.frm h1 h2 h3 h4, if_pos rfl]
  dsimp only
  rw [hab, if_pos (by simp : ([mb.frm] : List Coord).contains mb.frm = true)]

/-- **THE B-SIDE LANDING, ALL FIVE CASES** — the mirror of `chainDest_a`, under distinct sources. -/
theorem chainDest_b (bd : Board) (ma mb : Move) (ps : List Coord)
    (h1 : ma.frm.x < 2 ∧ ma.frm.y < 2) (h2 : ma.to.x < 2 ∧ ma.to.y < 2)
    (h3 : mb.frm.x < 2 ∧ mb.frm.y < 2) (h4 : mb.to.x < 2 ∧ mb.to.y < 2)
    (hne : ma.frm ≠ mb.frm) (hda : ma.frm ≠ ma.to) (hdb : mb.frm ≠ mb.to)
    (hpsa : mb.to = ma.frm → ps.contains ma.frm = false → ma.to ≠ mb.frm →
      ps.contains ma.to = false) (f : Nat) :
    followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) ps mb.frm [] (f + 1 + 1)
      = if mb.to = ma.frm ∧ ps.contains ma.frm = false ∧ ma.to ≠ mb.frm then ma.to
        else if ps.contains mb.to = true ∧ mb.to ≠ ma.frm then mb.frm
        else mb.to := by
  by_cases hba : mb.to = ma.frm
  · have hmid : ¬ (ps.contains mb.to = true ∧ mb.to ≠ ma.frm) := by
      rintro ⟨-, h⟩; exact h hba
    rw [if_neg hmid]
    by_cases hanz : ps.contains ma.frm = false
    · by_cases hab : ma.to = mb.frm
      · rw [if_neg (by rintro ⟨_, _, h⟩; exact h hab)]
        exact followChain_twoCycleB bd ma mb ps h1 h2 h3 h4 hne hdb hba hab hanz f
      · rw [if_pos ⟨hba, hanz, hab⟩]
        exact followChain_flowThroughB bd ma mb ps h1 h2 h3 h4 hne hda hdb hba hab hanz
          (hpsa hba hanz hab) f
    · rw [if_neg (by rintro ⟨_, h, _⟩; exact hanz h)]
      exact followChain_own_landingB bd ma mb ps h1 h2 h3 h4 hne hba
        (by rw [hba]; simpa using hanz) (f + 1)
  · rw [if_neg (by rintro ⟨h, _, _⟩; exact hba h)]
    by_cases hps : ps.contains mb.to = true
    · rw [if_pos ⟨hps, hba⟩]
      exact followChain_blockedB bd ma mb ps h1 h2 h3 h4 hne hdb hba hps (f + 1)
    · rw [if_neg (by rintro ⟨h, -⟩; exact hps h)]
      exact followChain_ownB bd ma mb ps h1 h2 h3 h4 hne hdb hba (by simpa using hps) (f + 1)

end Caterpillar

/-! ## §5.7 — (1) THE CIRCUIT HALF OF R5: `carry_of_sat` and `ft_of_sat`.

Leg 5 and leg 6 of the descriptor are built from exactly two primitives — `Builder::alloc_prod`
(`prodPin`) and `not_bit` (`notBitPin`) — so two mechanical extractors serve both legs. The results
tie `cCarryA`/`cCarryB` and `cFtA`/`cFtB` to PRECISELY the conditions the four `chainDest_*` cases
branch on, which is what makes the reference landing a function of the circuit's `ft` bit. -/

/-- `Builder::alloc_prod(a, b)` forces the fresh column to the product. -/
theorem prod_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (out a b : Nat)
    (hg : cgH ((Head.lin (-1) out).addProd 1 [a, b]) ∈ automataflResolveDesc.constraints)
    (ha : (envAt t i).loc a = 0 ∨ (envAt t i).loc a = 1)
    (hb : (envAt t i).loc b = 0 ∨ (envAt t i).loc b = 1) :
    (envAt t i).loc out = (envAt t i).loc a * (envAt t i).loc b := by
  set e := envAt t i with he
  have hgg := rgateH hsat i hi hg
  have hE : (headToExpr ((Head.lin (-1) out).addProd 1 [a, b])).eval e.loc
      = (-1) * e.loc out + e.loc a * e.loc b := rfl
  rw [hE] at hgg
  refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hgg)).symm
  rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;>
    exact ⟨by norm_num, by norm_num⟩

/-- `not_bit(col)` forces the fresh column to `1 − col`. -/
theorem notBit_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (out col : Nat)
    (hg : notBitPin out col ∈ automataflResolveDesc.constraints)
    (hb : (envAt t i).loc col = 0 ∨ (envAt t i).loc col = 1) :
    (envAt t i).loc out = 1 - (envAt t i).loc col := by
  set e := envAt t i with he
  have hgg := rgateH hsat i hi hg
  have hE : (headToExpr (((Head.lin 1 out).addLin 1 col).addConst (-1))).eval e.loc
      = e.loc out + e.loc col + (-1) := rfl
  rw [hE] at hgg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hgg)
  rcases hb with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩

/-- **(1a) — `carry_of_sat`.** The carry column is EXACTLY "the turn survived adjudication AND this
move's source carried a piece AND its line was clear": `carry = surv ∧ nz ∧ ¬occ`. -/
theorem carry_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (sa1 carry surv nz occ : Nat)
    (hp : cgH ((Head.lin (-1) sa1).addProd 1 [surv, nz]) ∈ automataflResolveDesc.constraints)
    (hq : cgH (((Head.lin 1 carry).addProd (-1) [sa1]).addProd 1 [sa1, occ])
            ∈ automataflResolveDesc.constraints)
    (hsurv : (envAt t i).loc surv = 0 ∨ (envAt t i).loc surv = 1)
    (hnz : (envAt t i).loc nz = 0 ∨ (envAt t i).loc nz = 1)
    (hocc : (envAt t i).loc occ = 0 ∨ (envAt t i).loc occ = 1) :
    ((envAt t i).loc carry = 0 ∨ (envAt t i).loc carry = 1)
      ∧ ((envAt t i).loc carry = 1 ↔
          ((envAt t i).loc surv = 1 ∧ (envAt t i).loc nz = 1 ∧ (envAt t i).loc occ = 0)) := by
  set e := envAt t i with he
  have hsa : e.loc sa1 = e.loc surv * e.loc nz := by
    exact prod_of_sat hsat hc i hi sa1 surv nz hp hsurv hnz
  have hcv : e.loc carry = e.loc sa1 - e.loc sa1 * e.loc occ := by
    have hgg := rgateH hsat i hi hq
    have hE : (headToExpr (((Head.lin 1 carry).addProd (-1) [sa1]).addProd 1 [sa1, occ])).eval e.loc
        = e.loc carry + (-1) * e.loc sa1 + e.loc sa1 * e.loc occ := rfl
    rw [hE] at hgg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hgg)
    rcases hsurv with a | a <;> rcases hnz with b | b <;> rcases hocc with c | c <;>
      rw [hsa, a, b, c] <;> exact ⟨by norm_num, by norm_num⟩
  rcases hsurv with a | a <;> rcases hnz with b | b <;> rcases hocc with c | c <;>
    rw [hsa, a, b, c] at hcv <;> norm_num at hcv <;> rw [hcv, a, b, c] <;> norm_num

/-- **(1b) — `ft_of_sat`.** The flow-through bit is EXACTLY the five-way conjunction the emitted
chain computes: `ft = eq_chain ∧ ¬other_nz ∧ surv ∧ ¬occ_other ∧ ¬eq_back`. These are precisely the
conditions `chainDest_a` / `chainDest_b` branch on, so the reference landing square is a function of
this bit. -/
theorem ft_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (nB nO nE f1 f2 f3 ft eqAb bnz occB eqBa surv : Nat)
    (g1 : notBitPin nB bnz ∈ automataflResolveDesc.constraints)
    (g2 : notBitPin nO occB ∈ automataflResolveDesc.constraints)
    (g3 : notBitPin nE eqBa ∈ automataflResolveDesc.constraints)
    (g4 : cgH ((Head.lin (-1) f1).addProd 1 [eqAb, nB]) ∈ automataflResolveDesc.constraints)
    (g5 : cgH ((Head.lin (-1) f2).addProd 1 [f1, surv]) ∈ automataflResolveDesc.constraints)
    (g6 : cgH ((Head.lin (-1) f3).addProd 1 [f2, nO]) ∈ automataflResolveDesc.constraints)
    (g7 : cgH ((Head.lin (-1) ft).addProd 1 [f3, nE]) ∈ automataflResolveDesc.constraints)
    (hab : (envAt t i).loc eqAb = 0 ∨ (envAt t i).loc eqAb = 1)
    (hbnz : (envAt t i).loc bnz = 0 ∨ (envAt t i).loc bnz = 1)
    (hocc : (envAt t i).loc occB = 0 ∨ (envAt t i).loc occB = 1)
    (hba : (envAt t i).loc eqBa = 0 ∨ (envAt t i).loc eqBa = 1)
    (hsurv : (envAt t i).loc surv = 0 ∨ (envAt t i).loc surv = 1) :
    ((envAt t i).loc ft = 0 ∨ (envAt t i).loc ft = 1)
      ∧ ((envAt t i).loc ft = 1 ↔
          ((envAt t i).loc eqAb = 1 ∧ (envAt t i).loc bnz = 0 ∧ (envAt t i).loc surv = 1
            ∧ (envAt t i).loc occB = 0 ∧ (envAt t i).loc eqBa = 0)) := by
  set e := envAt t i with he
  have hnB : e.loc nB = 1 - e.loc bnz := by
    exact notBit_of_sat hsat hc i hi nB bnz g1 hbnz
  have hnO : e.loc nO = 1 - e.loc occB := by
    exact notBit_of_sat hsat hc i hi nO occB g2 hocc
  have hnE : e.loc nE = 1 - e.loc eqBa := by
    exact notBit_of_sat hsat hc i hi nE eqBa g3 hba
  have bnB : e.loc nB = 0 ∨ e.loc nB = 1 := by rcases hbnz with h | h <;> rw [hnB, h] <;> norm_num
  have bnO : e.loc nO = 0 ∨ e.loc nO = 1 := by rcases hocc with h | h <;> rw [hnO, h] <;> norm_num
  have bnE : e.loc nE = 0 ∨ e.loc nE = 1 := by rcases hba with h | h <;> rw [hnE, h] <;> norm_num
  have hf1 : e.loc f1 = e.loc eqAb * e.loc nB := by
    exact prod_of_sat hsat hc i hi f1 eqAb nB g4 hab bnB
  have bf1 : e.loc f1 = 0 ∨ e.loc f1 = 1 := by
    rcases hab with a | a <;> rcases bnB with b | b <;> rw [hf1, a, b] <;> norm_num
  have hf2 : e.loc f2 = e.loc f1 * e.loc surv := by
    exact prod_of_sat hsat hc i hi f2 f1 surv g5 bf1 hsurv
  have bf2 : e.loc f2 = 0 ∨ e.loc f2 = 1 := by
    rcases bf1 with a | a <;> rcases hsurv with b | b <;> rw [hf2, a, b] <;> norm_num
  have hf3 : e.loc f3 = e.loc f2 * e.loc nO := by
    exact prod_of_sat hsat hc i hi f3 f2 nO g6 bf2 bnO
  have bf3 : e.loc f3 = 0 ∨ e.loc f3 = 1 := by
    rcases bf2 with a | a <;> rcases bnO with b | b <;> rw [hf3, a, b] <;> norm_num
  have hft : e.loc ft = e.loc f3 * e.loc nE := by
    exact prod_of_sat hsat hc i hi ft f3 nE g7 bf3 bnE
  rcases hab with a | a <;> rcases hbnz with b | b <;> rcases hsurv with c | c <;>
    rcases hocc with d | d <;> rcases hba with f | f <;>
    rw [hft, hf3, hf2, hf1, hnB, hnO, hnE, a, b, c, d, f] <;> norm_num

/-- The Leg-5 / Leg-6 gate memberships, `decide`d against the byte-pinned constraint list. -/
theorem carryA_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hsurv : (envAt t i).loc cSurv = 0 ∨ (envAt t i).loc cSurv = 1)
    (hnz : (envAt t i).loc cAnz = 0 ∨ (envAt t i).loc cAnz = 1)
    (hocc : (envAt t i).loc (cOcc (occBase 0)) = 0 ∨ (envAt t i).loc (cOcc (occBase 0)) = 1) :
    ((envAt t i).loc cCarryA = 0 ∨ (envAt t i).loc cCarryA = 1)
      ∧ ((envAt t i).loc cCarryA = 1 ↔
          ((envAt t i).loc cSurv = 1 ∧ (envAt t i).loc cAnz = 1
            ∧ (envAt t i).loc (cOcc (occBase 0)) = 0)) :=
  carry_of_sat hsat hc i hi cSa1 cCarryA cSurv cAnz (cOcc (occBase 0))
    (mem_carry_idx 2 0 (by decide)) (mem_carry_idx 2 1 (by decide))
    hsurv hnz hocc

theorem carryB_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hsurv : (envAt t i).loc cSurv = 0 ∨ (envAt t i).loc cSurv = 1)
    (hnz : (envAt t i).loc cBnz = 0 ∨ (envAt t i).loc cBnz = 1)
    (hocc : (envAt t i).loc (cOcc (occBase 1)) = 0 ∨ (envAt t i).loc (cOcc (occBase 1)) = 1) :
    ((envAt t i).loc cCarryB = 0 ∨ (envAt t i).loc cCarryB = 1)
      ∧ ((envAt t i).loc cCarryB = 1 ↔
          ((envAt t i).loc cSurv = 1 ∧ (envAt t i).loc cBnz = 1
            ∧ (envAt t i).loc (cOcc (occBase 1)) = 0)) :=
  carry_of_sat hsat hc i hi cSb1 cCarryB cSurv cBnz (cOcc (occBase 1))
    (mem_carry_idx 2 2 (by decide)) (mem_carry_idx 2 3 (by decide))
    hsurv hnz hocc

theorem ftA_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hab : (envAt t i).loc (cEqBit (eqBase 2)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 2)) = 1)
    (hbnz : (envAt t i).loc cBnz = 0 ∨ (envAt t i).loc cBnz = 1)
    (hocc : (envAt t i).loc (cOcc (occBase 1)) = 0 ∨ (envAt t i).loc (cOcc (occBase 1)) = 1)
    (hba : (envAt t i).loc (cEqBit (eqBase 3)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 3)) = 1)
    (hsurv : (envAt t i).loc cSurv = 0 ∨ (envAt t i).loc cSurv = 1) :
    ((envAt t i).loc cFtA = 0 ∨ (envAt t i).loc cFtA = 1)
      ∧ ((envAt t i).loc cFtA = 1 ↔
          ((envAt t i).loc (cEqBit (eqBase 2)) = 1 ∧ (envAt t i).loc cBnz = 0
            ∧ (envAt t i).loc cSurv = 1 ∧ (envAt t i).loc (cOcc (occBase 1)) = 0
            ∧ (envAt t i).loc (cEqBit (eqBase 3)) = 0)) :=
  ft_of_sat hsat hc i hi cNBnz cNOccb cNEqba cFa1 cFa2 cFa3 cFtA (cEqBit (eqBase 2)) cBnz
    (cOcc (occBase 1)) (cEqBit (eqBase 3)) cSurv
    (mem_flowThrough_idx 2 0 (by decide)) (mem_flowThrough_idx 2 1 (by decide))
    (mem_flowThrough_idx 2 2 (by decide)) (mem_flowThrough_idx 2 3 (by decide))
    (mem_flowThrough_idx 2 4 (by decide)) (mem_flowThrough_idx 2 5 (by decide))
    (mem_flowThrough_idx 2 6 (by decide)) hab hbnz hocc hba hsurv

theorem ftB_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hba : (envAt t i).loc (cEqBit (eqBase 3)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 3)) = 1)
    (hanz : (envAt t i).loc cAnz = 0 ∨ (envAt t i).loc cAnz = 1)
    (hocc : (envAt t i).loc (cOcc (occBase 0)) = 0 ∨ (envAt t i).loc (cOcc (occBase 0)) = 1)
    (hab : (envAt t i).loc (cEqBit (eqBase 2)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 2)) = 1)
    (hsurv : (envAt t i).loc cSurv = 0 ∨ (envAt t i).loc cSurv = 1) :
    ((envAt t i).loc cFtB = 0 ∨ (envAt t i).loc cFtB = 1)
      ∧ ((envAt t i).loc cFtB = 1 ↔
          ((envAt t i).loc (cEqBit (eqBase 3)) = 1 ∧ (envAt t i).loc cAnz = 0
            ∧ (envAt t i).loc cSurv = 1 ∧ (envAt t i).loc (cOcc (occBase 0)) = 0
            ∧ (envAt t i).loc (cEqBit (eqBase 2)) = 0)) :=
  ft_of_sat hsat hc i hi cNAnz cNOcca cNEqab cFb1 cFb2 cFb3 cFtB (cEqBit (eqBase 3)) cAnz
    (cOcc (occBase 0)) (cEqBit (eqBase 2)) cSurv
    (mem_flowThrough_idx 2 7 (by decide)) (mem_flowThrough_idx 2 8 (by decide))
    (mem_flowThrough_idx 2 9 (by decide)) (mem_flowThrough_idx 2 10 (by decide))
    (mem_flowThrough_idx 2 11 (by decide)) (mem_flowThrough_idx 2 12 (by decide))
    (mem_flowThrough_idx 2 13 (by decide)) hba hanz hocc hab hsurv

/-! ## §5.8 — (2) R6: the `write_mid_witnessed` endpoints and the per-cell rewrite gate.

Leg 7 is two families: `one_hot_rowcol` on each endpoint of each piece (source pinned to the move's
own `(fx, fy)`, destination pinned to the INTERPOLATED `destHead`), and the `k` per-cell equalities
`mid[c] == keep[c]·old[c] + Σ_i carry_i·dst_i[c]·particle_i` with the swap-restore term. The source
one-hots are ordinary `Builder::one_hot`s (`oneHot_of_sat` applies verbatim — the emitted gate
polynomial is literally the same expression); the destination one-hots need their own extractor
because the index is a HEAD, not a bare column. -/

/-- **The DESTINATION one-hot extractor.** The selector pair is pinned to the interpolated landing
coordinate `own + ft·(other − own)`: on `ft = 0` the piece's own destination, on `ft = 1` the chain
endpoint. No prover freedom — the one-hot cannot name a square the `ft` bit did not select. -/
theorem dstOneHot_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (sel0 sel1 own other ft : Nat)
    (h0 : cg (gBin sel0) ∈ automataflResolveDesc.constraints)
    (h1 : cg (gBin sel1) ∈ automataflResolveDesc.constraints)
    (hs : cgH (((Head.c (-1)).addLin 1 sel0).addLin 1 sel1) ∈ automataflResolveDesc.constraints)
    (hx : cgH (((Head.lin 0 sel0).addLin 1 sel1).append ((destHead own other ft).scale (-1)))
            ∈ automataflResolveDesc.constraints)
    (hown : (envAt t i).loc own = 0 ∨ (envAt t i).loc own = 1)
    (hoth : (envAt t i).loc other = 0 ∨ (envAt t i).loc other = 1)
    (hft : (envAt t i).loc ft = 0 ∨ (envAt t i).loc ft = 1) :
    ((envAt t i).loc sel1
        = (envAt t i).loc own
          + (envAt t i).loc ft * ((envAt t i).loc other - (envAt t i).loc own))
      ∧ (envAt t i).loc sel0 = 1 - (envAt t i).loc sel1
      ∧ ((envAt t i).loc sel1 = 0 ∨ (envAt t i).loc sel1 = 1) := by
  set e := envAt t i with he
  have b0 : e.loc sel0 = 0 ∨ e.loc sel0 = 1 :=
    bin_of_gate (rgate hsat i hi h0) (canon_loc hc i _)
  have b1 : e.loc sel1 = 0 ∨ e.loc sel1 = 1 :=
    bin_of_gate (rgate hsat i hi h1) (canon_loc hc i _)
  have hsum : e.loc sel0 + e.loc sel1 = 1 := by
    have hg := rgateH hsat i hi hs
    have hE : (headToExpr (((Head.c (-1)).addLin 1 sel0).addLin 1 sel1)).eval e.loc
        = e.loc sel0 + e.loc sel1 + (-1) := rfl
    rw [hE] at hg
    have := (gate_modEq_iff (x := e.loc sel0 + e.loc sel1 + -1)
      (a := e.loc sel0 + e.loc sel1) (b := 1) (by ring)).mp hg
    rcases b0 with h | h <;> rcases b1 with h' | h' <;>
      exact eq_of_modEq_small (by rw [h, h']; norm_num) (by norm_num) this
  have hval : e.loc sel1 = e.loc own + e.loc ft * (e.loc other - e.loc own) := by
    have hg := rgateH hsat i hi hx
    have hE : (headToExpr (((Head.lin 0 sel0).addLin 1 sel1).append
        ((destHead own other ft).scale (-1)))).eval e.loc
        = e.loc sel1 + (-1) * e.loc own + (-1) * (e.loc ft * e.loc other)
          + e.loc ft * e.loc own := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hown with a | a <;> rcases hoth with b | b <;> rcases hft with c | c <;>
      rw [a, b, c] <;> exact ⟨by norm_num, by norm_num⟩
  exact ⟨hval, by omega, b1⟩

/-- **The PER-CELL REWRITE GATE, as an extracted field equation.** `write_mid_witnessed`'s cell
gate, rearranged: the MID cell is the OLD cell KEPT (unless it is a cleared source or a landing
target), plus each landing piece's particle. Stated mod `p` — the raw polynomial can leave the
canonical window on a witness the alphabet gates then reject, and that rejection is exactly how the
double-count configurations are ruled out downstream. `Sa`/`Da` are the row×column one-hot products
of piece A's source and (interpolated) destination at this cell; likewise `Sb`/`Db`. -/
theorem writeCell_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) (c y x : Nat)
    (hmem : cgH (writeCellHead c) ∈ automataflResolveDesc.constraints)
    (hshape : (headToExpr (writeCellHead c)).eval (envAt t i).loc
        = (envAt t i).loc (mid c) + (-1) * (envAt t i).loc (old c)
          + (envAt t i).loc (carryCol 0) * (envAt t i).loc (wSrcRow 0 y)
              * (envAt t i).loc (wSrcCol 0 x) * (envAt t i).loc (old c)
          + (envAt t i).loc (carryCol 0) * (envAt t i).loc (wDstRow 0 y)
              * (envAt t i).loc (wDstCol 0 x) * (envAt t i).loc (old c)
          + (-1) * ((envAt t i).loc (carryCol 0) * (envAt t i).loc (wDstRow 0 y)
              * (envAt t i).loc (wDstCol 0 x) * (envAt t i).loc (particleCol 0))
          + (envAt t i).loc (carryCol 1) * (envAt t i).loc (wSrcRow 1 y)
              * (envAt t i).loc (wSrcCol 1 x) * (envAt t i).loc (old c)
          + (envAt t i).loc (carryCol 1) * (envAt t i).loc (wDstRow 1 y)
              * (envAt t i).loc (wDstCol 1 x) * (envAt t i).loc (old c)
          + (-1) * ((envAt t i).loc (carryCol 1) * (envAt t i).loc (wDstRow 1 y)
              * (envAt t i).loc (wDstCol 1 x) * (envAt t i).loc (particleCol 1))
          + (-1) * ((envAt t i).loc (carryCol 0) * (envAt t i).loc (wSrcRow 0 y)
              * (envAt t i).loc (wSrcCol 0 x) * (envAt t i).loc (carryCol 1)
              * (envAt t i).loc (wDstRow 1 y) * (envAt t i).loc (wDstCol 1 x)
              * (envAt t i).loc (old c))
          + (-1) * ((envAt t i).loc (carryCol 1) * (envAt t i).loc (wSrcRow 1 y)
              * (envAt t i).loc (wSrcCol 1 x) * (envAt t i).loc (carryCol 0)
              * (envAt t i).loc (wDstRow 0 y) * (envAt t i).loc (wDstCol 0 x)
              * (envAt t i).loc (old c))
          + (-1) * ((envAt t i).loc (carryCol 0) * (envAt t i).loc (wSrcRow 0 y)
              * (envAt t i).loc (wSrcCol 0 x) * (envAt t i).loc (carryCol 1)
              * (envAt t i).loc (wSrcRow 1 y) * (envAt t i).loc (wSrcCol 1 x)
              * (envAt t i).loc (old c))
          + (-1) * ((envAt t i).loc (carryCol 0) * (envAt t i).loc (wDstRow 0 y)
              * (envAt t i).loc (wDstCol 0 x) * (envAt t i).loc (carryCol 1)
              * (envAt t i).loc (wDstRow 1 y) * (envAt t i).loc (wDstCol 1 x)
              * (envAt t i).loc (old c))
          + (envAt t i).loc (carryCol 0) * (envAt t i).loc (wDstRow 0 y)
              * (envAt t i).loc (wDstCol 0 x) * (envAt t i).loc (carryCol 1)
              * (envAt t i).loc (wDstRow 1 y) * (envAt t i).loc (wDstCol 1 x)
              * (envAt t i).loc (particleCol 1)) :
    (envAt t i).loc (mid c)
      ≡ (1 - (envAt t i).loc (carryCol 0) * ((envAt t i).loc (wSrcRow 0 y)
                * (envAt t i).loc (wSrcCol 0 x))
           - (envAt t i).loc (carryCol 0) * ((envAt t i).loc (wDstRow 0 y)
                * (envAt t i).loc (wDstCol 0 x))
           - (envAt t i).loc (carryCol 1) * ((envAt t i).loc (wSrcRow 1 y)
                * (envAt t i).loc (wSrcCol 1 x))
           - (envAt t i).loc (carryCol 1) * ((envAt t i).loc (wDstRow 1 y)
                * (envAt t i).loc (wDstCol 1 x))
           + (envAt t i).loc (carryCol 0) * ((envAt t i).loc (wSrcRow 0 y)
                * (envAt t i).loc (wSrcCol 0 x)) * ((envAt t i).loc (carryCol 1)
                * ((envAt t i).loc (wDstRow 1 y) * (envAt t i).loc (wDstCol 1 x)))
           + (envAt t i).loc (carryCol 1) * ((envAt t i).loc (wSrcRow 1 y)
                * (envAt t i).loc (wSrcCol 1 x)) * ((envAt t i).loc (carryCol 0)
                * ((envAt t i).loc (wDstRow 0 y) * (envAt t i).loc (wDstCol 0 x)))
           + (envAt t i).loc (carryCol 0) * ((envAt t i).loc (wSrcRow 0 y)
                * (envAt t i).loc (wSrcCol 0 x)) * ((envAt t i).loc (carryCol 1)
                * ((envAt t i).loc (wSrcRow 1 y) * (envAt t i).loc (wSrcCol 1 x)))
           + (envAt t i).loc (carryCol 0) * ((envAt t i).loc (wDstRow 0 y)
                * (envAt t i).loc (wDstCol 0 x)) * ((envAt t i).loc (carryCol 1)
                * ((envAt t i).loc (wDstRow 1 y) * (envAt t i).loc (wDstCol 1 x))))
          * (envAt t i).loc (old c)
        + (envAt t i).loc (carryCol 0) * ((envAt t i).loc (wDstRow 0 y)
            * (envAt t i).loc (wDstCol 0 x)) * (envAt t i).loc (particleCol 0)
        + (envAt t i).loc (carryCol 1) * ((envAt t i).loc (wDstRow 1 y)
            * (envAt t i).loc (wDstCol 1 x)) * (envAt t i).loc (particleCol 1)
        - (envAt t i).loc (carryCol 0) * ((envAt t i).loc (wDstRow 0 y)
            * (envAt t i).loc (wDstCol 0 x)) * ((envAt t i).loc (carryCol 1)
            * ((envAt t i).loc (wDstRow 1 y) * (envAt t i).loc (wDstCol 1 x)))
            * (envAt t i).loc (particleCol 1)
        [ZMOD 2013265921] := by
  have hg := rgateH hsat i hi hmem
  rw [hshape] at hg
  exact (gate_modEq_iff (by ring)).mp hg

/-- The four cells' instances — each `(c, y, x)` triple's membership `decide`d against the
byte-pinned list and its polynomial SHAPE discharged by `rfl` on the emitted head. -/
example (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) : True := by
  have _h0 := writeCell_of_sat hsat i hi 0 0 0 (mem_resolve_of_mem_writeMid (wm_writeCell 2 0 (by decide))) rfl
  have _h1 := writeCell_of_sat hsat i hi 1 0 1 (mem_resolve_of_mem_writeMid (wm_writeCell 2 1 (by decide))) rfl
  have _h2 := writeCell_of_sat hsat i hi 2 1 0 (mem_resolve_of_mem_writeMid (wm_writeCell 2 2 (by decide))) rfl
  have _h3 := writeCell_of_sat hsat i hi 3 1 1 (mem_resolve_of_mem_writeMid (wm_writeCell 2 3 (by decide))) rfl
  trivial

end Selection

/-! ### §5.8.1 — The FIELD ALGEBRA of the per-cell gate, discharged once for all cells.

`writeCell_of_sat` delivers a congruence mod `p`; these two lemmas turn it into the reference's
per-cell VALUE. Both are pure integer statements over the four indicator products
`A = carry_a·src_a[c]`, `B = carry_a·dst_a[c]`, `C = carry_b·src_b[c]`, `D = carry_b·dst_b[c]`, so
they hold for every cell and every board without further case analysis upstream. -/

/-- **THE SHARED-SOURCE CASE — DEFECT #5, NOW FIXED (the canary polarity is FLIPPED).**

BEFORE: if BOTH pieces carried and BOTH cleared the SAME cell (`frm_a = frm_b`, the "two players
propose the identical move" turn, which the reference explicitly does NOT treat as a conflict —
`Automatafl.conflictResolve`'s doc: "Identical `(src,dst)` moves are NOT a conflict"), the emitted
cell gate subtracted the old particle TWICE, forcing `mid ≡ −old`; with both cells range-checked
into the particle alphabet that pinned `old = 0`, contradicting the carry — the leaf had NO
satisfying witness on a legal turn (a COMPLETENESS defect; soundness was never at risk).

AFTER: `AutomataflResolveEmit.writeCellHead` carries the inclusion–exclusion overlap terms
`A·C·old` and `B·D·(old − particle_b)`, so a shared source is vacated EXACTLY ONCE. This lemma is
that fact: on the shared-source configuration the gate now pins `mid = 0`, which IS in the particle
alphabet — the turn is SATISFIABLE, and no `old = 0` is forced. It is the shared-source
specialization of `cellAlgebra`, which no longer needs `A·C = 0` or `B·D = 0` as hypotheses. -/
theorem sharedSourceVacatesOnce {oldc midc : ℤ} (hold : 0 ≤ oldc ∧ oldc ≤ 3)
    (hmid : 0 ≤ midc ∧ midc ≤ 3)
    (hmod : midc ≡ (1 - 1 - 0 - 1 - 0 + 1 * 0 + 1 * 0 + 1 * 1 + 0 * 0) * oldc + 0 * oldc + 0 * oldc
              [ZMOD 2013265921]) : midc = 0 := by
  norm_num at hmod
  exact eq_of_modEq_canon ⟨hmid.1, by omega⟩ canon_zero hmod

/-- **(2) THE PER-CELL REWRITE, RESOLVED.** With the ONLY remaining structural exclusion (a cell is
never both a cleared source and a landing of the SAME piece: `A·B = C·D = 0`), the emitted cell
polynomial evaluates to exactly the reference `applyMoves` rewrite of that cell: a landing piece's
particle, else vacuum on a cleared source, else the old cell kept. Eleven live cases out of sixteen;
the other five are the same-piece exclusions.

DEFECT #5's fix is visible right here: the SHARED-SOURCE case `A = C = 1` and the SHARED-LANDING
case `B = D = 1` are now LIVE cases with a satisfying `midc` (`0` and `pa` respectively), where
before they were hypotheses (`hAC`, `hBD`) ruling the configurations out as unsatisfiable. -/
theorem cellAlgebra {oldc midc pa pb A B C D : ℤ}
    (hA : A = 0 ∨ A = 1) (hB : B = 0 ∨ B = 1) (hC : C = 0 ∨ C = 1) (hD : D = 0 ∨ D = 1)
    (hAB : A * B = 0) (hCD : C * D = 0)
    (hold : 0 ≤ oldc ∧ oldc ≤ 3) (hmid : Canon midc)
    (hpa : 0 ≤ pa ∧ pa ≤ 3) (hpb : 0 ≤ pb ∧ pb ≤ 3)
    (hmod : midc ≡ (1 - A - B - C - D + A * D + C * B + A * C + B * D) * oldc
              + B * pa + D * pb - B * D * pb [ZMOD 2013265921]) :
    midc = if B = 1 then pa else if D = 1 then pb else if A = 1 ∨ C = 1 then 0 else oldc := by
  have hcan : ∀ z : ℤ, 0 ≤ z → z ≤ 3 → Canon z := fun z h1 h2 => ⟨h1, by omega⟩
  rcases hA with a | a <;> rcases hB with b | b <;> rcases hC with c | c <;> rcases hD with d | d <;>
    subst a <;> subst b <;> subst c <;> subst d <;>
    first
      | (exfalso; simp only [mul_one, one_mul, mul_zero, zero_mul] at hAB hCD; omega)
      | (norm_num at hmod ⊢;
         refine eq_of_modEq_canon hmid ?_ hmod;
         first
           | exact hcan _ hold.1 hold.2
           | exact hcan _ hpa.1 hpa.2
           | exact hcan _ hpb.1 hpb.2
           | exact canon_zero)


/-! ### §5.8.2 — THE INDICATOR GLUE (residual (i), CLOSED).

`cellAlgebra` is phrased over the four indicator products `A, B, C, D`; the reference rewrite is
phrased over the decidable `Coord` predicates `⟨x,y⟩ = ma.frm` / `⟨x,y⟩ = dest_a`. These three
lemmas identify them, by per-cell unfolding of the one-hot VALUES at literal `(x, y)` plus the
`Int.toNat` bridge from the witnessed coordinate columns to `moveDecode`'s `Coord` fields. -/

/-- THE INDICATOR CORE: a pair of two-selector one-hots pinned to `(vx, vy)` multiplies to the
`Coord` equality indicator at every literal cell of the 2×2 board. -/
theorem oneHotPair_indicator {r0 r1 c0 c1 vx vy : ℤ}
    (hr1 : r1 = vy) (hr0 : r0 = 1 - vy) (hvy : vy = 0 ∨ vy = 1)
    (hc1 : c1 = vx) (hc0 : c0 = 1 - vx) (hvx : vx = 0 ∨ vx = 1)
    (x y : Nat) (hx : x < 2) (hy : y < 2) :
    (if y = 0 then r0 else r1) * (if x = 0 then c0 else c1)
      = if (⟨x, y⟩ : Coord) = (⟨vx.toNat, vy.toNat⟩ : Coord) then 1 else 0 := by
  interval_cases x <;> interval_cases y <;>
    rcases hvx with hvx | hvx <;> rcases hvy with hvy | hvy <;>
    subst hr0 <;> subst hr1 <;> subst hc0 <;> subst hc1 <;> rw [hvx, hvy] <;> decide

section IndicatorGlue
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- THE SOURCE-INDICATOR GLUE: piece `k`'s emitted source one-hot product at cell `(x,y)` IS the
decidable `Coord` predicate `⟨x,y⟩ = ma.frm` that the reference rewrite is phrased in — the
`Int.toNat` bridge between the witnessed coordinate columns and `moveDecode`'s `Coord` fields. -/
theorem srcIndicator_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (k x y : Nat)
    (hx : x < 2) (hy : y < 2)
    (hr0 : cg (gBin (wSrcRow k 0)) ∈ automataflResolveDesc.constraints)
    (hr1 : cg (gBin (wSrcRow k 1)) ∈ automataflResolveDesc.constraints)
    (hrs : cgH (((Head.c (-1)).addLin 1 (wSrcRow k 0)).addLin 1 (wSrcRow k 1))
            ∈ automataflResolveDesc.constraints)
    (hrx : cgH ((Head.lin 1 (wSrcRow k 1)).addLin (-1) (cFy (mvBase k)))
            ∈ automataflResolveDesc.constraints)
    (hc0 : cg (gBin (wSrcCol k 0)) ∈ automataflResolveDesc.constraints)
    (hc1 : cg (gBin (wSrcCol k 1)) ∈ automataflResolveDesc.constraints)
    (hcs : cgH (((Head.c (-1)).addLin 1 (wSrcCol k 0)).addLin 1 (wSrcCol k 1))
            ∈ automataflResolveDesc.constraints)
    (hcx : cgH ((Head.lin 1 (wSrcCol k 1)).addLin (-1) (cFx (mvBase k)))
            ∈ automataflResolveDesc.constraints) :
    (envAt t i).loc (wSrcRow k y) * (envAt t i).loc (wSrcCol k x)
      = if (⟨x, y⟩ : Coord)
           = (⟨((envAt t i).loc (cFx (mvBase k))).toNat,
              ((envAt t i).loc (cFy (mvBase k))).toNat⟩ : Coord) then 1 else 0 := by
  obtain ⟨hvy, hs1, hs0⟩ := oneHot_of_sat hsat hc i hi (wSrcRow k 0) (wSrcRow k 1)
    (cFy (mvBase k)) hr0 hr1 hrs hrx
  obtain ⟨hvx, ht1, ht0⟩ := oneHot_of_sat hsat hc i hi (wSrcCol k 0) (wSrcCol k 1)
    (cFx (mvBase k)) hc0 hc1 hcs hcx
  have hrow : (envAt t i).loc (wSrcRow k y)
      = if y = 0 then (envAt t i).loc (wSrcRow k 0) else (envAt t i).loc (wSrcRow k 1) := by
    interval_cases y <;> simp
  have hcol : (envAt t i).loc (wSrcCol k x)
      = if x = 0 then (envAt t i).loc (wSrcCol k 0) else (envAt t i).loc (wSrcCol k 1) := by
    interval_cases x <;> simp
  rw [hrow, hcol]
  exact oneHotPair_indicator hs1 hs0 hvy ht1 ht0 hvx x y hx hy

/-- THE DESTINATION-INDICATOR GLUE: piece `k`'s emitted landing one-hot product at cell `(x,y)` IS
the decidable `Coord` predicate `⟨x,y⟩ = dest_k`, where `dest_k` is the INTERPOLATED destination
`to_own + ft·(to_other − to_own)` the `ft` bit selects (`chainDest_a`/`chainDest_b`'s value). -/
theorem dstIndicator_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (k x y : Nat)
    (hx : x < 2) (hy : y < 2) (ownx othx owny othy ft : Nat)
    (hr0 : cg (gBin (wDstRow k 0)) ∈ automataflResolveDesc.constraints)
    (hr1 : cg (gBin (wDstRow k 1)) ∈ automataflResolveDesc.constraints)
    (hrs : cgH (((Head.c (-1)).addLin 1 (wDstRow k 0)).addLin 1 (wDstRow k 1))
            ∈ automataflResolveDesc.constraints)
    (hrx : cgH (((Head.lin 0 (wDstRow k 0)).addLin 1 (wDstRow k 1)).append
              ((destHead owny othy ft).scale (-1))) ∈ automataflResolveDesc.constraints)
    (hc0 : cg (gBin (wDstCol k 0)) ∈ automataflResolveDesc.constraints)
    (hc1 : cg (gBin (wDstCol k 1)) ∈ automataflResolveDesc.constraints)
    (hcs : cgH (((Head.c (-1)).addLin 1 (wDstCol k 0)).addLin 1 (wDstCol k 1))
            ∈ automataflResolveDesc.constraints)
    (hcx : cgH (((Head.lin 0 (wDstCol k 0)).addLin 1 (wDstCol k 1)).append
              ((destHead ownx othx ft).scale (-1))) ∈ automataflResolveDesc.constraints)
    (hox : (envAt t i).loc ownx = 0 ∨ (envAt t i).loc ownx = 1)
    (htx : (envAt t i).loc othx = 0 ∨ (envAt t i).loc othx = 1)
    (hoy : (envAt t i).loc owny = 0 ∨ (envAt t i).loc owny = 1)
    (hty : (envAt t i).loc othy = 0 ∨ (envAt t i).loc othy = 1)
    (hf : (envAt t i).loc ft = 0 ∨ (envAt t i).loc ft = 1) :
    (envAt t i).loc (wDstRow k y) * (envAt t i).loc (wDstCol k x)
      = if (⟨x, y⟩ : Coord)
           = (⟨((envAt t i).loc ownx
                 + (envAt t i).loc ft
                     * ((envAt t i).loc othx - (envAt t i).loc ownx)).toNat,
              ((envAt t i).loc owny
                 + (envAt t i).loc ft
                     * ((envAt t i).loc othy - (envAt t i).loc owny)).toNat⟩ : Coord)
        then 1 else 0 := by
  obtain ⟨hs1, hs0, hvy⟩ := dstOneHot_of_sat hsat hc i hi (wDstRow k 0) (wDstRow k 1)
    owny othy ft hr0 hr1 hrs hrx hoy hty hf
  obtain ⟨ht1, ht0, hvx⟩ := dstOneHot_of_sat hsat hc i hi (wDstCol k 0) (wDstCol k 1)
    ownx othx ft hc0 hc1 hcs hcx hox htx hf
  have hrow : (envAt t i).loc (wDstRow k y)
      = if y = 0 then (envAt t i).loc (wDstRow k 0) else (envAt t i).loc (wDstRow k 1) := by
    interval_cases y <;> simp
  have hcol : (envAt t i).loc (wDstCol k x)
      = if x = 0 then (envAt t i).loc (wDstCol k 0) else (envAt t i).loc (wDstCol k 1) := by
    interval_cases x <;> simp
  rw [hrow, hcol]
  exact oneHotPair_indicator hs1 (by rw [hs0, hs1]) (hs1 ▸ hvy)
    ht1 (by rw [ht0, ht1]) (ht1 ▸ hvx) x y hx hy

end IndicatorGlue

/-! ## §6 — The remaining gate bundles, discharged by `decide` against the byte-pinned list. -/

theorem eqGates_ff : EqCoordsGates (cFx (mvBase 0)) (cFy (mvBase 0)) (cFx (mvBase 1))
    (cFy (mvBase 1)) (eqBase 0) :=
  ⟨mem_patternBit_idx 2 0 (by decide),
   ⟨mem_patternBit_idx 2 1 (by decide), mem_patternBit_idx 2 2 (by decide), mem_patternBit_idx 2 3 (by decide), mem_patternBit_idx 2 4 (by decide), mem_patternBit_idx 2 5 (by decide), mem_patternBit_idx 2 6 (by decide), mem_patternBit_idx 2 7 (by decide), mem_patternBit_idx 2 8 (by decide), mem_patternBit_idx 2 9 (by decide), mem_patternBit_idx 2 10 (by decide), mem_patternBit_idx 2 11 (by decide)⟩,
   ⟨mem_patternBit_idx 2 12 (by decide)⟩⟩
theorem eqGates_tt : EqCoordsGates (cTx (mvBase 0)) (cTy (mvBase 0)) (cTx (mvBase 1))
    (cTy (mvBase 1)) (eqBase 1) :=
  ⟨mem_patternBit_idx 2 13 (by decide),
   ⟨mem_patternBit_idx 2 14 (by decide), mem_patternBit_idx 2 15 (by decide), mem_patternBit_idx 2 16 (by decide), mem_patternBit_idx 2 17 (by decide), mem_patternBit_idx 2 18 (by decide), mem_patternBit_idx 2 19 (by decide), mem_patternBit_idx 2 20 (by decide), mem_patternBit_idx 2 21 (by decide), mem_patternBit_idx 2 22 (by decide), mem_patternBit_idx 2 23 (by decide), mem_patternBit_idx 2 24 (by decide)⟩,
   ⟨mem_patternBit_idx 2 25 (by decide)⟩⟩
theorem eqGates_ab : EqCoordsGates (cTx (mvBase 0)) (cTy (mvBase 0)) (cFx (mvBase 1))
    (cFy (mvBase 1)) (eqBase 2) :=
  ⟨mem_patternBit_idx 2 26 (by decide),
   ⟨mem_patternBit_idx 2 27 (by decide), mem_patternBit_idx 2 28 (by decide), mem_patternBit_idx 2 29 (by decide), mem_patternBit_idx 2 30 (by decide), mem_patternBit_idx 2 31 (by decide), mem_patternBit_idx 2 32 (by decide), mem_patternBit_idx 2 33 (by decide), mem_patternBit_idx 2 34 (by decide), mem_patternBit_idx 2 35 (by decide), mem_patternBit_idx 2 36 (by decide), mem_patternBit_idx 2 37 (by decide)⟩,
   ⟨mem_patternBit_idx 2 38 (by decide)⟩⟩
theorem eqGates_ba : EqCoordsGates (cTx (mvBase 1)) (cTy (mvBase 1)) (cFx (mvBase 0))
    (cFy (mvBase 0)) (eqBase 3) :=
  ⟨mem_patternBit_idx 2 39 (by decide),
   ⟨mem_patternBit_idx 2 40 (by decide), mem_patternBit_idx 2 41 (by decide), mem_patternBit_idx 2 42 (by decide), mem_patternBit_idx 2 43 (by decide), mem_patternBit_idx 2 44 (by decide), mem_patternBit_idx 2 45 (by decide), mem_patternBit_idx 2 46 (by decide), mem_patternBit_idx 2 47 (by decide), mem_patternBit_idx 2 48 (by decide), mem_patternBit_idx 2 49 (by decide), mem_patternBit_idx 2 50 (by decide)⟩,
   ⟨mem_patternBit_idx 2 51 (by decide)⟩⟩

theorem anzGates : Ge0Gates5 (cFp (mvBase 0)) cAnz (anzBit 0) :=
  ⟨mem_srcNonVac_idx 2 0 (by decide), mem_srcNonVac_idx 2 1 (by decide),
   mem_srcNonVac_idx 2 2 (by decide), mem_srcNonVac_idx 2 3 (by decide),
   mem_srcNonVac_idx 2 4 (by decide), mem_srcNonVac_idx 2 5 (by decide),
   mem_srcNonVac_idx 2 6 (by decide)⟩
theorem bnzGates : Ge0Gates5 (cFp (mvBase 1)) cBnz (bnzBit 0) :=
  ⟨mem_srcNonVac_idx 2 7 (by decide), mem_srcNonVac_idx 2 8 (by decide),
   mem_srcNonVac_idx 2 9 (by decide), mem_srcNonVac_idx 2 10 (by decide),
   mem_srcNonVac_idx 2 11 (by decide), mem_srcNonVac_idx 2 12 (by decide),
   mem_srcNonVac_idx 2 13 (by decide)⟩

/-! ## §6.5 — THE ASSEMBLY (residual (iii), CLOSED): Leg R's capstone and THE WHOLE TURN. -/

open Dregg2.Games.Automatafl (resolveMid nextOf followChain applyTurn applyTurn_factors
  automatonStep automatonStep_congr applyMoves_size applyMoves_cell_TT applyMoves_cell_TF
  applyMoves_cell_FT applyMoves_cell_FF mkBoard)

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ## §A — small reference/bridge lemmas. -/

/-- The empty move list leaves every in-bounds cell alone. -/
theorem applyMoves_cell_nil (bd : Board) (c : Coord) (hx : c.x < bd.size) (hy : c.y < bd.size) :
    (applyMoves bd []).cellAt c = bd.cellAt c := by
  rw [Board.cellAt, applyMoves_size, if_pos ⟨hx, hy⟩]
  simp [applyMoves, Board.cellAt, hx, hy]

/-- On the `{0,1}` window `Int.toNat` is injective, so a decoded `Coord` equality IS the pair of
column equalities. -/
theorem toNat_inj01 {a b : ℤ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a.toNat = b.toNat) ↔ a = b := by
  rcases ha with h | h <;> rcases hb with h' | h' <;> subst h <;> subst h' <;> decide

/-- A carried indicator gate selects exactly its `Coord` predicate. -/
theorem ite_one {α : Type} (P : Prop) [Decidable P] (a b : α) :
    (if (1:ℤ) * (if P then 1 else 0) = 1 then a else b) = if P then a else b := by
  by_cases h : P <;> simp [h]

theorem ite_or_11 {α : Type} (P Q : Prop) [Decidable P] [Decidable Q] (a b : α) :
    (if ((1:ℤ) * (if P then 1 else 0) = 1 ∨ (1:ℤ) * (if Q then 1 else 0) = 1) then a else b)
      = if P ∨ Q then a else b := by
  by_cases h : P <;> by_cases h' : Q <;> simp [h, h']

/-! ## §B — the derived per-row semantic facts, bundled. -/

/-- Every semantic fact the per-cell assembly needs, derived ONCE from a satisfying canonical row.
Each field is a THEOREM about the emitted descriptor (see `resolveFacts_of_sat`); nothing here is
assumed. -/
structure ResolveFacts (e : VmRowEnv) : Prop where
  validA : MoveValid (boardDecodeOld e) (moveDecode e 0)
  validB : MoveValid (boardDecodeOld e) (moveDecode e 1)
  alphaOld : ∀ c, c < KK →
    (e.loc (old c) = 0 ∨ e.loc (old c) = 1 ∨ e.loc (old c) = 2 ∨ e.loc (old c) = 3)
  alphaMid : ∀ c, c < KK →
    (e.loc (mid c) = 0 ∨ e.loc (mid c) = 1 ∨ e.loc (mid c) = 2 ∨ e.loc (mid c) = 3)
  paVal : (boardDecodeOld e).cellAt (moveDecode e 0).frm = codeToParticle (e.loc (particleCol 0))
  pbVal : (boardDecodeOld e).cellAt (moveDecode e 1).frm = codeToParticle (e.loc (particleCol 1))
  paAlpha : e.loc (particleCol 0) = 0 ∨ e.loc (particleCol 0) = 1
    ∨ e.loc (particleCol 0) = 2 ∨ e.loc (particleCol 0) = 3
  pbAlpha : e.loc (particleCol 1) = 0 ∨ e.loc (particleCol 1) = 1
    ∨ e.loc (particleCol 1) = 2 ∨ e.loc (particleCol 1) = 3
  survB : e.loc cSurv = 0 ∨ e.loc cSurv = 1
  anzB : e.loc cAnz = 0 ∨ e.loc cAnz = 1
  bnzB : e.loc cBnz = 0 ∨ e.loc cBnz = 1
  anzIff : e.loc cAnz = 1 ↔
    ((boardDecodeOld e).cellAt (moveDecode e 0).frm).isVacuum = false
  bnzIff : e.loc cBnz = 1 ↔
    ((boardDecodeOld e).cellAt (moveDecode e 1).frm).isVacuum = false
  survIff : e.loc cSurv = 1 ↔
    ¬ (((moveDecode e 0).frm = (moveDecode e 1).frm ∧ (moveDecode e 0).to ≠ (moveDecode e 1).to)
       ∨ ((moveDecode e 0).to = (moveDecode e 1).to ∧ (moveDecode e 0).frm ≠ (moveDecode e 1).frm
          ∧ ((boardDecodeOld e).cellAt (moveDecode e 0).frm).isVacuum = false
          ∧ ((boardDecodeOld e).cellAt (moveDecode e 1).frm).isVacuum = false))
  carryAB : e.loc cCarryA = 0 ∨ e.loc cCarryA = 1
  carryBB : e.loc cCarryB = 0 ∨ e.loc cCarryB = 1
  carryAIff : e.loc cCarryA = 1 ↔ (e.loc cSurv = 1 ∧ e.loc cAnz = 1)
  carryBIff : e.loc cCarryB = 1 ↔ (e.loc cSurv = 1 ∧ e.loc cBnz = 1)
  ftAB : e.loc cFtA = 0 ∨ e.loc cFtA = 1
  ftBB : e.loc cFtB = 0 ∨ e.loc cFtB = 1
  ftAIff : e.loc cFtA = 1 ↔
    ((moveDecode e 0).to = (moveDecode e 1).frm ∧ e.loc cBnz = 0 ∧ e.loc cSurv = 1
      ∧ (moveDecode e 1).to ≠ (moveDecode e 0).frm)
  ftBIff : e.loc cFtB = 1 ↔
    ((moveDecode e 1).to = (moveDecode e 0).frm ∧ e.loc cAnz = 0 ∧ e.loc cSurv = 1
      ∧ (moveDecode e 0).to ≠ (moveDecode e 1).frm)
  srcIndA : ∀ x y : Nat, x < 2 → y < 2 →
    e.loc (wSrcRow 0 y) * e.loc (wSrcCol 0 x)
      = if (⟨x, y⟩ : Coord) = (moveDecode e 0).frm then 1 else 0
  srcIndB : ∀ x y : Nat, x < 2 → y < 2 →
    e.loc (wSrcRow 1 y) * e.loc (wSrcCol 1 x)
      = if (⟨x, y⟩ : Coord) = (moveDecode e 1).frm then 1 else 0
  dstIndA : ∀ x y : Nat, x < 2 → y < 2 →
    e.loc (wDstRow 0 y) * e.loc (wDstCol 0 x)
      = if (⟨x, y⟩ : Coord)
           = (if e.loc cFtA = 1 then (moveDecode e 1).to else (moveDecode e 0).to) then 1 else 0
  dstIndB : ∀ x y : Nat, x < 2 → y < 2 →
    e.loc (wDstRow 1 y) * e.loc (wDstCol 1 x)
      = if (⟨x, y⟩ : Coord)
           = (if e.loc cFtB = 1 then (moveDecode e 0).to else (moveDecode e 1).to) then 1 else 0

section Facts
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The `fork` and `collide` columns are BOOLEAN (`selection_of_sat` pins their meaning but not
their range; the range is what turns "not surviving" into a genuine conflict verdict). Extracted
from the same byte-pinned gates. -/
theorem forkCollide_bool_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hff : (envAt t i).loc (cEqBit (eqBase 0)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 0)) = 1)
    (htt : (envAt t i).loc (cEqBit (eqBase 1)) = 0 ∨ (envAt t i).loc (cEqBit (eqBase 1)) = 1)
    (hanz : (envAt t i).loc cAnz = 0 ∨ (envAt t i).loc cAnz = 1)
    (hbnz : (envAt t i).loc cBnz = 0 ∨ (envAt t i).loc cBnz = 1) :
    ((envAt t i).loc cFork = 0 ∨ (envAt t i).loc cFork = 1)
      ∧ ((envAt t i).loc cCollide = 0 ∨ (envAt t i).loc cCollide = 1) := by
  set e := envAt t i with he
  have hforkv : e.loc cFork
      = e.loc (cEqBit (eqBase 0)) - e.loc (cEqBit (eqBase 0)) * e.loc (cEqBit (eqBase 1)) := by
    have hg := rgateH hsat i hi
      (h := ((Head.lin 1 cFork).addLin (-1) (cEqBit (eqBase 0))).addProd 1
              [cEqBit (eqBase 0), cEqBit (eqBase 1)]) (mem_selection_idx 2 0 (by decide))
    have hE : (headToExpr (((Head.lin 1 cFork).addLin (-1) (cEqBit (eqBase 0))).addProd 1
          [cEqBit (eqBase 0), cEqBit (eqBase 1)])).eval e.loc
        = e.loc cFork + (-1) * e.loc (cEqBit (eqBase 0))
          + e.loc (cEqBit (eqBase 0)) * e.loc (cEqBit (eqBase 1)) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rcases htt with b | b <;> rw [a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hnff : e.loc cNeqFf = 1 - e.loc (cEqBit (eqBase 0)) := by
    have hg := rgateH hsat i hi
      (h := ((Head.lin 1 cNeqFf).addLin 1 (cEqBit (eqBase 0))).addConst (-1)) (mem_selection_idx 2 1 (by decide))
    have hE : (headToExpr (((Head.lin 1 cNeqFf).addLin 1 (cEqBit (eqBase 0))).addConst (-1))).eval
        e.loc = e.loc cNeqFf + e.loc (cEqBit (eqBase 0)) + (-1) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rw [a] <;> exact ⟨by norm_num, by norm_num⟩
  have hcol1 : e.loc cCol1 = e.loc (cEqBit (eqBase 1)) * e.loc cNeqFf := by
    have hg := rgateH hsat i hi (h := (Head.lin (-1) cCol1).addProd 1 [cEqBit (eqBase 1), cNeqFf]) (mem_selection_idx 2 2 (by decide))
    have hE : (headToExpr ((Head.lin (-1) cCol1).addProd 1
        [cEqBit (eqBase 1), cNeqFf])).eval e.loc
        = (-1) * e.loc cCol1 + e.loc (cEqBit (eqBase 1)) * e.loc cNeqFf := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rw [hnff, a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hcol2 : e.loc cCol2 = e.loc cCol1 * e.loc cAnz := by
    have hg := rgateH hsat i hi (h := (Head.lin (-1) cCol2).addProd 1 [cCol1, cAnz]) (mem_selection_idx 2 3 (by decide))
    have hE : (headToExpr ((Head.lin (-1) cCol2).addProd 1 [cCol1, cAnz])).eval e.loc
        = (-1) * e.loc cCol2 + e.loc cCol1 * e.loc cAnz := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rw [hcol1, hnff, a, b, c] <;> exact ⟨by norm_num, by norm_num⟩
  have hcollv : e.loc cCollide = e.loc cCol2 * e.loc cBnz := by
    have hg := rgateH hsat i hi (h := (Head.lin (-1) cCollide).addProd 1 [cCol2, cBnz]) (mem_selection_idx 2 4 (by decide))
    have hE : (headToExpr ((Head.lin (-1) cCollide).addProd 1 [cCol2, cBnz])).eval e.loc
        = (-1) * e.loc cCollide + e.loc cCol2 * e.loc cBnz := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rcases hbnz with d | d <;> rw [hcol2, hcol1, hnff, a, b, c, d] <;>
      exact ⟨by norm_num, by norm_num⟩
  constructor
  · rcases hff with a | a <;> rcases htt with b | b <;> rw [hforkv, a, b] <;> norm_num
  · rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rcases hbnz with d | d <;> rw [hcollv, hcol2, hcol1, hnff, a, b, c, d] <;> norm_num

/-- The witnessed source particle column IS the decoded OLD cell at the move's source. -/
theorem srcParticle_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat)
    (mg : MoveGates (mvBase which)) :
    (boardDecodeOld (envAt t i)).cellAt (moveDecode (envAt t i) which).frm
      = codeToParticle ((envAt t i).loc (cFp (mvBase which)))
    ∧ ((envAt t i).loc (cFp (mvBase which)) = 0 ∨ (envAt t i).loc (cFp (mvBase which)) = 1
        ∨ (envAt t i).loc (cFp (mvBase which)) = 2
        ∨ (envAt t i).loc (cFp (mvBase which)) = 3) := by
  have halpha : BoardAlphabet (envAt t i) := boardvalid_of_sat hsat hc i hi
  set e := envAt t i with he
  obtain ⟨X, Y, hX, hY, hfx, hfy, hfp⟩ := sourceRead_of_sat hsat hc i hi (mvBase which) mg
  rw [← he] at hfx hfy hfp
  have hXY : Y * NN + X < KK := by
    have h1 : X < 2 := by simpa [NN] using hX
    have h2 : Y < 2 := by simpa [NN] using hY
    simp only [KK, NN]; omega
  obtain ⟨hcellAlpha, _⟩ := halpha (Y * NN + X) hXY
  refine ⟨?_, by rw [hfp]; exact hcellAlpha⟩
  have hxn : (e.loc (cFx (mvBase which))).toNat = X := by rw [hfx]; simp
  have hyn : (e.loc (cFy (mvBase which))).toNat = Y := by rw [hfy]; simp
  simp only [Board.cellAt, boardDecodeOld, moveDecode]
  rw [hxn, hyn, if_pos ⟨by simpa [NN] using hX, by simpa [NN] using hY⟩, hfp]

/-- **THE FACT BUNDLE.** Every field is extracted from the byte-pinned constraint list. -/
theorem resolveFacts_of_sat (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ResolveFacts (envAt t i) := by
  -- coordinate booleanity for all eight witnessed coordinate columns
  have hfxa : (envAt t i).loc (cFx (mvBase 0)) = 0 ∨ (envAt t i).loc (cFx (mvBase 0)) = 1 :=
    coord01_of_sat hsat hc i hi _ _ moveGates_a.fxBin moveGates_a.fxPin
  have hfya : (envAt t i).loc (cFy (mvBase 0)) = 0 ∨ (envAt t i).loc (cFy (mvBase 0)) = 1 :=
    coord01_of_sat hsat hc i hi _ _ moveGates_a.fyBin moveGates_a.fyPin
  have htxa : (envAt t i).loc (cTx (mvBase 0)) = 0 ∨ (envAt t i).loc (cTx (mvBase 0)) = 1 :=
    coord01_of_sat hsat hc i hi _ _ moveGates_a.txBin moveGates_a.txPin
  have htya : (envAt t i).loc (cTy (mvBase 0)) = 0 ∨ (envAt t i).loc (cTy (mvBase 0)) = 1 :=
    coord01_of_sat hsat hc i hi _ _ moveGates_a.tyBin moveGates_a.tyPin
  have hfxb : (envAt t i).loc (cFx (mvBase 1)) = 0 ∨ (envAt t i).loc (cFx (mvBase 1)) = 1 :=
    coord01_of_sat hsat hc i hi _ _ moveGates_b.fxBin moveGates_b.fxPin
  have hfyb : (envAt t i).loc (cFy (mvBase 1)) = 0 ∨ (envAt t i).loc (cFy (mvBase 1)) = 1 :=
    coord01_of_sat hsat hc i hi _ _ moveGates_b.fyBin moveGates_b.fyPin
  have htxb : (envAt t i).loc (cTx (mvBase 1)) = 0 ∨ (envAt t i).loc (cTx (mvBase 1)) = 1 :=
    coord01_of_sat hsat hc i hi _ _ moveGates_b.txBin moveGates_b.txPin
  have htyb : (envAt t i).loc (cTy (mvBase 1)) = 0 ∨ (envAt t i).loc (cTy (mvBase 1)) = 1 :=
    coord01_of_sat hsat hc i hi _ _ moveGates_b.tyBin moveGates_b.tyPin
  -- occlusion bits are FORCED to zero
  have hocca : (envAt t i).loc (cOcc (occBase 0)) = 0 := occ_of_sat hsat hc i hi _ occGates_a
  have hoccb : (envAt t i).loc (cOcc (occBase 1)) = 0 := occ_of_sat hsat hc i hi _ occGates_b
  -- the four pattern bits
  obtain ⟨hffB, hffI⟩ := eqCoords_of_sat hsat hc i hi _ _ _ _ _ eqGates_ff hfxa hfya hfxb hfyb
  obtain ⟨httB, httI⟩ := eqCoords_of_sat hsat hc i hi _ _ _ _ _ eqGates_tt htxa htya htxb htyb
  obtain ⟨habB, habI⟩ := eqCoords_of_sat hsat hc i hi _ _ _ _ _ eqGates_ab htxa htya hfxb hfyb
  obtain ⟨hbaB, hbaI⟩ := eqCoords_of_sat hsat hc i hi _ _ _ _ _ eqGates_ba htxb htyb hfxa hfya
  -- the non-vacuum bits
  obtain ⟨hanzB, hanzI⟩ := srcNonVac_of_sat hsat hc i hi 0 cAnz (anzBit 0) moveGates_a anzGates
  obtain ⟨hbnzB, hbnzI⟩ := srcNonVac_of_sat hsat hc i hi 1 cBnz (bnzBit 0) moveGates_b bnzGates
  -- the selection truth table
  obtain ⟨hforkI, hcollI, hsurvB, hsurvI⟩ :=
    selection_of_sat hsat hc i hi hffB httB hanzB hbnzB
  -- carries and flow-through bits
  obtain ⟨hcaB, hcaI⟩ := carryA_of_sat hsat hc i hi hsurvB hanzB (Or.inl hocca)
  obtain ⟨hcbB, hcbI⟩ := carryB_of_sat hsat hc i hi hsurvB hbnzB (Or.inl hoccb)
  obtain ⟨hftaB, hftaI⟩ := ftA_of_sat hsat hc i hi habB hbnzB (Or.inl hoccb) hbaB hsurvB
  obtain ⟨hftbB, hftbI⟩ := ftB_of_sat hsat hc i hi hbaB hanzB (Or.inl hocca) habB hsurvB
  -- the Coord-level readings of the four pattern bits
  have hffC : (envAt t i).loc (cEqBit (eqBase 0)) = 1
      ↔ (moveDecode (envAt t i) 0).frm = (moveDecode (envAt t i) 1).frm := by
    rw [hffI]
    simp only [moveDecode, Coord.mk.injEq]
    rw [toNat_inj01 hfxa hfxb, toNat_inj01 hfya hfyb]
  have httC : (envAt t i).loc (cEqBit (eqBase 1)) = 1
      ↔ (moveDecode (envAt t i) 0).to = (moveDecode (envAt t i) 1).to := by
    rw [httI]
    simp only [moveDecode, Coord.mk.injEq]
    rw [toNat_inj01 htxa htxb, toNat_inj01 htya htyb]
  have habC : (envAt t i).loc (cEqBit (eqBase 2)) = 1
      ↔ (moveDecode (envAt t i) 0).to = (moveDecode (envAt t i) 1).frm := by
    rw [habI]
    simp only [moveDecode, Coord.mk.injEq]
    rw [toNat_inj01 htxa hfxb, toNat_inj01 htya hfyb]
  have hbaC : (envAt t i).loc (cEqBit (eqBase 3)) = 1
      ↔ (moveDecode (envAt t i) 1).to = (moveDecode (envAt t i) 0).frm := by
    rw [hbaI]
    simp only [moveDecode, Coord.mk.injEq]
    rw [toNat_inj01 htxb hfxa, toNat_inj01 htyb hfya]
  obtain ⟨hpaV, hpaA⟩ := srcParticle_of_sat hsat hc i hi 0 moveGates_a
  obtain ⟨hpbV, hpbA⟩ := srcParticle_of_sat hsat hc i hi 1 moveGates_b
  refine
    { validA := validMove_of_sat hsat hc i hi 0 (mvBase 0) rfl moveGates_a
      validB := validMove_of_sat hsat hc i hi 1 (mvBase 1) rfl moveGates_b
      alphaOld := fun c hcK => (boardvalid_of_sat hsat hc i hi c hcK).1
      alphaMid := fun c hcK => (boardvalid_of_sat hsat hc i hi c hcK).2
      paVal := hpaV
      pbVal := hpbV
      paAlpha := hpaA
      pbAlpha := hpbA
      survB := hsurvB
      anzB := hanzB
      bnzB := hbnzB
      anzIff := hanzI
      bnzIff := hbnzI
      carryAB := hcaB
      carryBB := hcbB
      ftAB := hftaB
      ftBB := hftbB
      survIff := ?_
      carryAIff := ?_
      carryBIff := ?_
      ftAIff := ?_
      ftBIff := ?_
      srcIndA := ?_
      srcIndB := ?_
      dstIndA := ?_
      dstIndB := ?_ }
  · -- survIff
    obtain ⟨hforkB, hcollB⟩ := forkCollide_bool_of_sat hsat hc i hi hffB httB hanzB hbnzB
    rw [hsurvI]
    constructor
    · rintro ⟨hf0, hc0⟩ hPQ
      rcases hPQ with h | h
      · have httz : (envAt t i).loc (cEqBit (eqBase 1)) = 0 := by
          rcases httB with hz | ho
          · exact hz
          · exact absurd (httC.mp ho) h.2
        have : (envAt t i).loc cFork = 1 := hforkI.mpr ⟨hffC.mpr h.1, httz⟩
        omega
      · have hffz : (envAt t i).loc (cEqBit (eqBase 0)) = 0 := by
          rcases hffB with hz | ho
          · exact hz
          · exact absurd (hffC.mp ho) h.2.1
        have : (envAt t i).loc cCollide = 1 :=
          hcollI.mpr ⟨httC.mpr h.1, hffz, hanzI.mpr h.2.2.1, hbnzI.mpr h.2.2.2⟩
        omega
    · intro hno
      refine ⟨?_, ?_⟩
      · rcases hforkB with hz | ho
        · exact hz
        · obtain ⟨h1, h2⟩ := hforkI.mp ho
          refine absurd (Or.inl ⟨hffC.mp h1, ?_⟩) hno
          intro hEq
          have := httC.mpr hEq
          omega
      · rcases hcollB with hz | ho
        · exact hz
        · obtain ⟨h1, h2, h3, h4⟩ := hcollI.mp ho
          refine absurd (Or.inr ⟨httC.mp h1, ?_, hanzI.mp h3, hbnzI.mp h4⟩) hno
          intro hEq
          have := hffC.mpr hEq
          omega
  · rw [hcaI]; constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hocca⟩
  · rw [hcbI]; constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hoccb⟩
  · rw [hftaI]; constructor
    · rintro ⟨h1, h2, h3, _, h5⟩
      exact ⟨habC.mp h1, h2, h3, fun hEq => by have := hbaC.mpr hEq; omega⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨habC.mpr h1, h2, h3, hoccb, ?_⟩
      rcases hbaB with hz | ho
      · exact hz
      · exact absurd (hbaC.mp ho) h4
  · rw [hftbI]; constructor
    · rintro ⟨h1, h2, h3, _, h5⟩
      exact ⟨hbaC.mp h1, h2, h3, fun hEq => by have := habC.mpr hEq; omega⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨hbaC.mpr h1, h2, h3, hocca, ?_⟩
      rcases habB with hz | ho
      · exact hz
      · exact absurd (habC.mp ho) h4
  · intro x y hx hy
    have h := srcIndicator_of_sat hsat hc i hi 0 x y hx hy
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcRow_sel 2 0 0 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcRow_sel 2 0 1 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcRow_sum 2 0 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcRow_idx 2 0 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcCol_sel 2 0 0 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcCol_sel 2 0 1 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcCol_sum 2 0 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcCol_idx 2 0 (by decide))))
    rw [h]; rfl
  · intro x y hx hy
    have h := srcIndicator_of_sat hsat hc i hi 1 x y hx hy
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcRow_sel 2 1 0 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcRow_sel 2 1 1 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcRow_sum 2 1 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcRow_idx 2 1 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcCol_sel 2 1 0 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcCol_sel 2 1 1 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcCol_sum 2 1 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcCol_idx 2 1 (by decide))))
    rw [h]; rfl
  · intro x y hx hy
    have h := dstIndicator_of_sat hsat hc i hi 0 x y hx hy (cTx (mvBase 0)) (cTx (mvBase 1))
      (cTy (mvBase 0)) (cTy (mvBase 1)) cFtA
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstRow_sel 2 0 0 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstRow_sel 2 0 1 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstRow_sum 2 0 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstRow_idx 2 0 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstCol_sel 2 0 0 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstCol_sel 2 0 1 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstCol_sum 2 0 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstCol_idx 2 0 (by decide))))
      htxa htxb htya htyb hftaB
    have hdest : (⟨((envAt t i).loc (cTx (mvBase 0))
                     + (envAt t i).loc cFtA * ((envAt t i).loc (cTx (mvBase 1)) - (envAt t i).loc (cTx (mvBase 0)))).toNat,
                   ((envAt t i).loc (cTy (mvBase 0))
                     + (envAt t i).loc cFtA * ((envAt t i).loc (cTy (mvBase 1)) - (envAt t i).loc (cTy (mvBase 0)))).toNat⟩
                  : Coord)
        = if (envAt t i).loc cFtA = 1 then (moveDecode (envAt t i) 1).to else (moveDecode (envAt t i) 0).to := by
      rcases hftaB with hz | ho
      · rw [hz, if_neg (by norm_num : ¬ (0 : ℤ) = 1)]
        simp only [zero_mul, add_zero]; rfl
      · rw [ho, if_pos rfl]
        simp only [show ∀ a b : ℤ, a + 1 * (b - a) = b from fun a b => by ring]; rfl
    rw [h, hdest]
  · intro x y hx hy
    have h := dstIndicator_of_sat hsat hc i hi 1 x y hx hy (cTx (mvBase 1)) (cTx (mvBase 0))
      (cTy (mvBase 1)) (cTy (mvBase 0)) cFtB
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstRow_sel 2 1 0 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstRow_sel 2 1 1 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstRow_sum 2 1 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstRow_idx 2 1 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstCol_sel 2 1 0 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstCol_sel 2 1 1 (by decide) (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstCol_sum 2 1 (by decide))))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstCol_idx 2 1 (by decide))))
      htxb htxa htyb htya hftbB
    have hdest : (⟨((envAt t i).loc (cTx (mvBase 1))
                     + (envAt t i).loc cFtB * ((envAt t i).loc (cTx (mvBase 0)) - (envAt t i).loc (cTx (mvBase 1)))).toNat,
                   ((envAt t i).loc (cTy (mvBase 1))
                     + (envAt t i).loc cFtB * ((envAt t i).loc (cTy (mvBase 0)) - (envAt t i).loc (cTy (mvBase 1)))).toNat⟩
                  : Coord)
        = if (envAt t i).loc cFtB = 1 then (moveDecode (envAt t i) 0).to else (moveDecode (envAt t i) 1).to := by
      rcases hftbB with hz | ho
      · rw [hz, if_neg (by norm_num : ¬ (0 : ℤ) = 1)]
        simp only [zero_mul, add_zero]; rfl
      · rw [ho, if_pos rfl]
        simp only [show ∀ a b : ℤ, a + 1 * (b - a) = b from fun a b => by ring]; rfl
    rw [h, hdest]

end Facts

/-! ## §C — the per-cell assembly: the emitted cell value IS the reference `resolveMid` cell. -/

section Cell
variable {e : VmRowEnv}

/-- **THE PER-CELL ASSEMBLY.** Given the derived facts and the emitted cell gate (in the shape
`writeCell_of_sat` delivers), the decoded MID cell IS the reference `resolveMid` cell. -/
theorem midCell_of_facts (F : ResolveFacts e) (x y c : Nat)
    (hx : x < 2) (hy : y < 2) (hcxy : c = y * NN + x)
    (hmid : e.loc (mid c)
      ≡ (1 - e.loc (carryCol 0) * (e.loc (wSrcRow 0 y) * e.loc (wSrcCol 0 x))
           - e.loc (carryCol 0) * (e.loc (wDstRow 0 y) * e.loc (wDstCol 0 x))
           - e.loc (carryCol 1) * (e.loc (wSrcRow 1 y) * e.loc (wSrcCol 1 x))
           - e.loc (carryCol 1) * (e.loc (wDstRow 1 y) * e.loc (wDstCol 1 x))
           + e.loc (carryCol 0) * (e.loc (wSrcRow 0 y) * e.loc (wSrcCol 0 x))
               * (e.loc (carryCol 1) * (e.loc (wDstRow 1 y) * e.loc (wDstCol 1 x)))
           + e.loc (carryCol 1) * (e.loc (wSrcRow 1 y) * e.loc (wSrcCol 1 x))
               * (e.loc (carryCol 0) * (e.loc (wDstRow 0 y) * e.loc (wDstCol 0 x)))
           + e.loc (carryCol 0) * (e.loc (wSrcRow 0 y) * e.loc (wSrcCol 0 x))
               * (e.loc (carryCol 1) * (e.loc (wSrcRow 1 y) * e.loc (wSrcCol 1 x)))
           + e.loc (carryCol 0) * (e.loc (wDstRow 0 y) * e.loc (wDstCol 0 x))
               * (e.loc (carryCol 1) * (e.loc (wDstRow 1 y) * e.loc (wDstCol 1 x))))
          * e.loc (old c)
        + e.loc (carryCol 0) * (e.loc (wDstRow 0 y) * e.loc (wDstCol 0 x)) * e.loc (particleCol 0)
        + e.loc (carryCol 1) * (e.loc (wDstRow 1 y) * e.loc (wDstCol 1 x)) * e.loc (particleCol 1)
        - e.loc (carryCol 0) * (e.loc (wDstRow 0 y) * e.loc (wDstCol 0 x))
            * (e.loc (carryCol 1) * (e.loc (wDstRow 1 y) * e.loc (wDstCol 1 x)))
            * e.loc (particleCol 1)
        [ZMOD 2013265921]) :
    codeToParticle (e.loc (mid c))
      = (resolveMid (boardDecodeOld e) [moveDecode e 0, moveDecode e 1]).cellAt ⟨x, y⟩ := by
  -- abbreviations
  have hkK : c < KK := by simp only [hcxy, KK, NN]; omega
  set bd := boardDecodeOld e with hbd
  set ma := moveDecode e 0 with hma
  set mb := moveDecode e 1 with hmb
  -- geometry from `MoveValid`
  obtain ⟨hdA, -, ⟨hfAx, hfAy⟩, ⟨htAx, htAy⟩, -, -, -, -⟩ := F.validA
  obtain ⟨hdB, -, ⟨hfBx, hfBy⟩, ⟨htBx, htBy⟩, -, -, -, -⟩ := F.validB
  have gA1 : ma.frm.x < 2 ∧ ma.frm.y < 2 := ⟨hfAx, hfAy⟩
  have gA2 : ma.to.x < 2 ∧ ma.to.y < 2 := ⟨htAx, htAy⟩
  have gB1 : mb.frm.x < 2 ∧ mb.frm.y < 2 := ⟨hfBx, hfBy⟩
  have gB2 : mb.to.x < 2 ∧ mb.to.y < 2 := ⟨htBx, htBy⟩
  -- the old cell, decoded
  have hbdcell : bd.cellAt (⟨x, y⟩ : Coord) = codeToParticle (e.loc (old c)) := by
    simp only [hbd, Board.cellAt, boardDecodeOld, hcxy]
    rw [if_pos (⟨by simpa [NN] using hx, by simpa [NN] using hy⟩ :
      (⟨x, y⟩ : Coord).x < NN ∧ (⟨x, y⟩ : Coord).y < NN)]
  -- the indicator readings
  have hsa := F.srcIndA x y hx hy
  have hsb := F.srcIndB x y hx hy
  have hda := F.dstIndA x y hx hy
  have hdb := F.dstIndB x y hx hy
  have hc0 : carryCol 0 = cCarryA := rfl
  have hc1 : carryCol 1 = cCarryB := rfl
  rw [hc0, hc1, hsa, hsb, hda, hdb] at hmid
  -- the two landing squares the `ft` bits select
  set destA : Coord := if e.loc cFtA = 1 then mb.to else ma.to with hdestA
  set destB : Coord := if e.loc cFtB = 1 then ma.to else mb.to with hdestB
  -- a landing square is never the SAME piece's source
  have hAneA : destA ≠ ma.frm := by
    rcases F.ftAB with hz | ho
    · rw [hdestA, if_neg (by rw [hz]; norm_num)]; exact fun h => hdA h.symm
    · rw [hdestA, if_pos ho]; exact (F.ftAIff.mp ho).2.2.2
  have nA1 : ¬ (ma.frm = destA) := fun h => hAneA h.symm
  have hBneB : destB ≠ mb.frm := by
    rcases F.ftBB with hz | ho
    · rw [hdestB, if_neg (by rw [hz]; norm_num)]; exact fun h => hdB h.symm
    · rw [hdestB, if_pos ho]; exact (F.ftBIff.mp ho).2.2.2
  have nB1 : ¬ (mb.frm = destB) := fun h => hBneB h.symm
  have nAA : ¬ (ma.to = ma.frm) := fun h => hdA h.symm
  have nBB : ¬ (mb.to = mb.frm) := fun h => hdB h.symm
  -- the four indicator products are booleans with the two same-piece exclusions
  have bA : e.loc cCarryA * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 0
      ∨ e.loc cCarryA * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0) = 1 := by
    rcases F.carryAB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = ma.frm <;>
      simp [h, q]
  have bB : e.loc cCarryA * (if (⟨x, y⟩ : Coord) = destA then (1:ℤ) else 0) = 0
      ∨ e.loc cCarryA * (if (⟨x, y⟩ : Coord) = destA then (1:ℤ) else 0) = 1 := by
    rcases F.carryAB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = destA <;>
      simp [h, q]
  have bC : e.loc cCarryB * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 0
      ∨ e.loc cCarryB * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0) = 1 := by
    rcases F.carryBB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = mb.frm <;>
      simp [h, q]
  have bD : e.loc cCarryB * (if (⟨x, y⟩ : Coord) = destB then (1:ℤ) else 0) = 0
      ∨ e.loc cCarryB * (if (⟨x, y⟩ : Coord) = destB then (1:ℤ) else 0) = 1 := by
    rcases F.carryBB with h | h <;> by_cases q : (⟨x, y⟩ : Coord) = destB <;>
      simp [h, q]
  have eAB : (e.loc cCarryA * (if (⟨x, y⟩ : Coord) = ma.frm then (1:ℤ) else 0))
      * (e.loc cCarryA * (if (⟨x, y⟩ : Coord) = destA then (1:ℤ) else 0)) = 0 := by
    by_cases q : (⟨x, y⟩ : Coord) = ma.frm
    · by_cases r : (⟨x, y⟩ : Coord) = destA
      · exact absurd (r.symm.trans q) hAneA
      · simp [r]
    · simp [q]
  have eCD : (e.loc cCarryB * (if (⟨x, y⟩ : Coord) = mb.frm then (1:ℤ) else 0))
      * (e.loc cCarryB * (if (⟨x, y⟩ : Coord) = destB then (1:ℤ) else 0)) = 0 := by
    by_cases q : (⟨x, y⟩ : Coord) = mb.frm
    · by_cases r : (⟨x, y⟩ : Coord) = destB
      · exact absurd (r.symm.trans q) hBneB
      · simp [r]
    · simp [q]
  have holdA : 0 ≤ e.loc (old c) ∧ e.loc (old c) ≤ 3 := by
    rcases F.alphaOld c hkK with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  have hmidA : Canon (e.loc (mid c)) := by
    rcases F.alphaMid c hkK with h | h | h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩
  have hpaA : 0 ≤ e.loc (particleCol 0) ∧ e.loc (particleCol 0) ≤ 3 := by
    rcases F.paAlpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  have hpbA : 0 ≤ e.loc (particleCol 1) ∧ e.loc (particleCol 1) ≤ 3 := by
    rcases F.pbAlpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  have halg := cellAlgebra bA bB bC bD eAB eCD holdA hmidA hpaA hpbA hmid
  -- the reference: the validity filter is the identity on the pair
  have hva : moveValidB bd ma = true :=
    (Dregg2.Games.Automatafl.moveValidB_iff bd ma).mpr F.validA
  have hvb : moveValidB bd mb = true :=
    (Dregg2.Games.Automatafl.moveValidB_iff bd mb).mpr F.validB
  have hfilter : List.filter (moveValidB bd) [ma, mb] = [ma, mb] := by
    simp [List.filter, hva, hvb]
  have hres : resolveMid bd [ma, mb] = applyMoves bd (conflictResolve bd [ma, mb]) := by
    show applyMoves bd (conflictResolve bd (List.filter (moveValidB bd) [ma, mb])) = _
    rw [hfilter]
  rw [hres, conflictResolve_pair bd ma mb]
  rw [halg]
  have hxb : (⟨x, y⟩ : Coord).x < bd.size := by simpa [hbd, boardDecodeOld, NN] using hx
  have hyb : (⟨x, y⟩ : Coord).y < bd.size := by simpa [hbd, boardDecodeOld, NN] using hy
  rcases F.survB with hs0 | hs1
  · -- THE TURN IS ADJUDICATED AWAY: the reference drops both moves, the circuit carries neither.
    have hCOND : ((ma.frm = mb.frm ∧ ma.to ≠ mb.to)
        ∨ (ma.to = mb.to ∧ ma.frm ≠ mb.frm
            ∧ (bd.cellAt ma.frm).isVacuum = false ∧ (bd.cellAt mb.frm).isVacuum = false)) := by
      by_contra hno
      exact absurd (F.survIff.mpr hno) (by rw [hs0]; norm_num)
    have hca : e.loc cCarryA = 0 := by
      rcases F.carryAB with h | h
      · exact h
      · exact absurd (F.carryAIff.mp h).1 (by rw [hs0]; norm_num)
    have hcb : e.loc cCarryB = 0 := by
      rcases F.carryBB with h | h
      · exact h
      · exact absurd (F.carryBIff.mp h).1 (by rw [hs0]; norm_num)
    rw [if_pos hCOND, applyMoves_cell_nil bd ⟨x, y⟩ hxb hyb, hbdcell, hca, hcb]
    norm_num
  · -- THE TURN SURVIVES: both moves are applied, and the shape depends on which sources carry.
    have hnc := F.survIff.mp hs1
    rw [if_neg hnc]
    rcases F.anzB with ha0 | ha1 <;> rcases F.bnzB with hb0 | hb1
    · -- FF: neither source carries
      have hvA : (bd.cellAt ma.frm).isVacuum = true := by
        cases h : (bd.cellAt ma.frm).isVacuum
        · exact absurd (F.anzIff.mpr h) (by rw [ha0]; norm_num)
        · rfl
      have hvB : (bd.cellAt mb.frm).isVacuum = true := by
        cases h : (bd.cellAt mb.frm).isVacuum
        · exact absurd (F.bnzIff.mpr h) (by rw [hb0]; norm_num)
        · rfl
      have hca : e.loc cCarryA = 0 := by
        rcases F.carryAB with h | h
        · exact h
        · exact absurd (F.carryAIff.mp h).2 (by rw [ha0]; norm_num)
      have hcb : e.loc cCarryB = 0 := by
        rcases F.carryBB with h | h
        · exact h
        · exact absurd (F.carryBIff.mp h).2 (by rw [hb0]; norm_num)
      rw [applyMoves_cell_FF bd ma mb ⟨x, y⟩ hxb hyb hvA hvB, hbdcell, hca, hcb]
      norm_num
    · -- FT: only B carries
      have hvA : (bd.cellAt ma.frm).isVacuum = true := by
        cases h : (bd.cellAt ma.frm).isVacuum
        · exact absurd (F.anzIff.mpr h) (by rw [ha0]; norm_num)
        · rfl
      have hvB : (bd.cellAt mb.frm).isVacuum = false := F.bnzIff.mp hb1
      have hne : ma.frm ≠ mb.frm := by
        intro h; rw [h, hvB] at hvA; exact absurd hvA (by norm_num)
      have hca : e.loc cCarryA = 0 := by
        rcases F.carryAB with h | h
        · exact h
        · exact absurd (F.carryAIff.mp h).2 (by rw [ha0]; norm_num)
      have hcb : e.loc cCarryB = 1 := F.carryBIff.mpr ⟨hs1, hb1⟩
      have hcont : ([mb.frm] : List Coord).contains ma.frm = false := by
        simp [hne]
      have hchain := Dregg2.Circuit.Emit.AutomataflResolveRefine.chainDest_b bd ma mb [mb.frm]
        gA1 gA2 gB1 gB2 hne hdA hdB (by intro _ _ h3; simp [h3]) 1
      have hfc : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [mb.frm] mb.frm [] 3
          = destB := by
        -- defect #8's STAY branch is empty here: `to_b` is never `frm_b`.
        have hmid : ¬ (([mb.frm] : List Coord).contains mb.to = true ∧ mb.to ≠ ma.frm) := by
          rintro ⟨h, -⟩; simp at h; first | exact hdB h | exact hdB h.symm
        rw [show (3 : Nat) = 1 + 1 + 1 from rfl, hchain, hcont, if_neg hmid, hdestB]
        by_cases hf : e.loc cFtB = 1
        · obtain ⟨h1, -, -, h4⟩ := F.ftBIff.mp hf
          rw [if_pos hf, if_pos ⟨h1, rfl, h4⟩]
        · rw [if_neg hf, if_neg ?_]
          rintro ⟨h1, -, h3⟩
          exact hf (F.ftBIff.mpr ⟨h1, ha0, hs1, h3⟩)
      rw [applyMoves_cell_FT bd ma mb ⟨x, y⟩ hxb hyb hvA hvB, hfc, hca, hcb, F.pbVal, hbdcell]
      by_cases q1 : (⟨x, y⟩ : Coord) = destB <;> by_cases q2 : (⟨x, y⟩ : Coord) = mb.frm <;>
        simp [q1, q2, eq_comm, apply_ite codeToParticle, codeToParticle, nA1, nB1, hAneA, hBneB, hdA, hdB, nAA, nBB]
    · -- TF: only A carries
      have hvA : (bd.cellAt ma.frm).isVacuum = false := F.anzIff.mp ha1
      have hvB : (bd.cellAt mb.frm).isVacuum = true := by
        cases h : (bd.cellAt mb.frm).isVacuum
        · exact absurd (F.bnzIff.mpr h) (by rw [hb0]; norm_num)
        · rfl
      have hca : e.loc cCarryA = 1 := F.carryAIff.mpr ⟨hs1, ha1⟩
      have hcb : e.loc cCarryB = 0 := by
        rcases F.carryBB with h | h
        · exact h
        · exact absurd (F.carryBIff.mp h).2 (by rw [hb0]; norm_num)
      have hchain := Dregg2.Circuit.Emit.AutomataflResolveRefine.chainDest_a bd ma mb [ma.frm]
        gA1 gA2 gB1 gB2 hdA hdB (by intro _ _ h3; simp [h3]) 1
      have hfc : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm] ma.frm [] 3
          = destA := by
        -- defect #8's STAY branch is empty here: `to_a` is never `frm_a`.
        have hmid : ¬ (([ma.frm] : List Coord).contains ma.to = true ∧ ma.to ≠ mb.frm) := by
          rintro ⟨h, -⟩; simp at h; first | exact hdA h | exact hdA h.symm
        rw [show (3 : Nat) = 1 + 1 + 1 from rfl, hchain, if_neg hmid, hdestA]
        by_cases hf : e.loc cFtA = 1
        · obtain ⟨h1, -, -, h4⟩ := F.ftAIff.mp hf
          have hcont : ([ma.frm] : List Coord).contains mb.frm = false := by
            simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_eq_false_iff_ne,
              ne_eq]
            intro h; exact hdA (h1.trans h).symm
          rw [if_pos hf, if_pos ⟨h1, hcont, h4⟩]
        · rw [if_neg hf, if_neg ?_]
          rintro ⟨h1, -, h3⟩
          exact hf (F.ftAIff.mpr ⟨h1, hb0, hs1, h3⟩)
      rw [applyMoves_cell_TF bd ma mb ⟨x, y⟩ hxb hyb hvA hvB, hfc, hca, hcb, F.paVal, hbdcell]
      by_cases q1 : (⟨x, y⟩ : Coord) = destA <;> by_cases q2 : (⟨x, y⟩ : Coord) = ma.frm <;>
        simp [q1, q2, eq_comm, apply_ite codeToParticle, codeToParticle, nA1, nB1, hAneA, hBneB, hdA, hdB, nAA, nBB]
    · -- TT: both sources carry
      have hvA : (bd.cellAt ma.frm).isVacuum = false := F.anzIff.mp ha1
      have hvB : (bd.cellAt mb.frm).isVacuum = false := F.bnzIff.mp hb1
      have hca : e.loc cCarryA = 1 := F.carryAIff.mpr ⟨hs1, ha1⟩
      have hcb : e.loc cCarryB = 1 := F.carryBIff.mpr ⟨hs1, hb1⟩
      have hfA0 : e.loc cFtA = 0 := by
        rcases F.ftAB with h | h
        · exact h
        · exact absurd (F.ftAIff.mp h).2.1 (by rw [hb1]; norm_num)
      have hfB0 : e.loc cFtB = 0 := by
        rcases F.ftBB with h | h
        · exact h
        · exact absurd (F.ftBIff.mp h).2.1 (by rw [ha1]; norm_num)
      have hdA' : destA = ma.to := by rw [hdestA, if_neg (by rw [hfA0]; norm_num)]
      have hdB' : destB = mb.to := by rw [hdestB, if_neg (by rw [hfB0]; norm_num)]
      have hchainA := Dregg2.Circuit.Emit.AutomataflResolveRefine.chainDest_a bd ma mb
        [ma.frm, mb.frm] gA1 gA2 gB1 gB2 hdA hdB (by intro _ h2 _; simp at h2) 1
      have hfcA : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] ma.frm [] 3
          = ma.to := by
        -- defect #8's STAY branch is empty here: `to_a ∈ {frm_a, frm_b}` is refuted either by
        -- `frm_a ≠ to_a` or by the branch's own `to_a ≠ frm_b`.
        have hmid : ¬ (([ma.frm, mb.frm] : List Coord).contains ma.to = true ∧ ma.to ≠ mb.frm) := by
          rintro ⟨h, h2⟩
          simp at h
          rcases h with h | h
          · first | exact hdA h | exact hdA h.symm
          · first | exact h2 h | exact h2 h.symm
        rw [show (3 : Nat) = 1 + 1 + 1 from rfl, hchainA,
          if_neg (by rintro ⟨-, h2, -⟩; simp at h2), if_neg hmid]
      have hfcB : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] mb.frm [] 3
          = mb.to := by
        by_cases hne : ma.frm = mb.frm
        · have hto : ma.to = mb.to := by
            by_contra hno
            exact hnc (Or.inl ⟨hne, hno⟩)
          have hswap : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm]
              ma.frm [] 3
              = followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] mb.frm [] 3 := by
            rw [hne]
          rw [← hswap, hfcA, hto]
        · have hchainB := Dregg2.Circuit.Emit.AutomataflResolveRefine.chainDest_b bd ma mb
            [ma.frm, mb.frm] gA1 gA2 gB1 gB2 hne hdA hdB (by intro _ h2 _; simp at h2) 1
          have hmid : ¬ (([ma.frm, mb.frm] : List Coord).contains mb.to = true
              ∧ mb.to ≠ ma.frm) := by
            rintro ⟨h, h2⟩
            simp at h
            rcases h with h | h
            · first | exact h2 h | exact h2 h.symm
            · first | exact hdB h | exact hdB h.symm
          rw [show (3 : Nat) = 1 + 1 + 1 from rfl, hchainB,
            if_neg (by rintro ⟨-, h2, -⟩; simp at h2), if_neg hmid]
      have oA : (ma.to = (⟨x, y⟩ : Coord)) = ((⟨x, y⟩ : Coord) = ma.to) :=
        propext ⟨Eq.symm, Eq.symm⟩
      have oB : (mb.to = (⟨x, y⟩ : Coord)) = ((⟨x, y⟩ : Coord) = mb.to) :=
        propext ⟨Eq.symm, Eq.symm⟩
      rw [applyMoves_cell_TT bd ma mb ⟨x, y⟩ hxb hyb hvA hvB, hfcA, hfcB, hca, hcb, hdA', hdB',
        F.paVal, F.pbVal, hbdcell, ite_one, ite_one, ite_or_11, apply_ite codeToParticle,
        apply_ite codeToParticle, apply_ite codeToParticle]
      simp only [oA, oB, show codeToParticle 0 = Particle.vacuum from by decide]

end Cell

/-! ## §D — LEG R'S CAPSTONE, and THE WHOLE TURN. -/

/-- The decoded MID board reads a cell as the felt-decode of its `mid` column. -/
theorem boardDecodeMid_cell (e : VmRowEnv) (x y : Nat) (hx : x < NN) (hy : y < NN) :
    (boardDecodeMid e).cellAt ⟨x, y⟩ = codeToParticle (e.loc (mid (y * NN + x))) := by
  simp only [Board.cellAt, boardDecodeMid]
  rw [if_pos (⟨hx, hy⟩ : (⟨x, y⟩ : Coord).x < NN ∧ (⟨x, y⟩ : Coord).y < NN)]

section Capstone
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **LEG R'S CAPSTONE — `resolve_sat_imp_resolveMid`, UNCONDITIONAL.**

On ANY satisfying, canonical trace of the byte-pinned `automataflResolveDesc`, the decoded MID board
IS the reference `old → mid` half of the automatafl turn applied to the decoded OLD board and the
two decoded moves — cell-wise, over every in-bounds cell, with NO assumed alphabet envelope, NO
assumed arithmetization hypothesis and NO side condition on the witness. The validity filter, the
conflict adjudication (fork / collide / survive), the caterpillar chain-follow and the per-cell
rewrite are all DERIVED from constraints proved members of the emitted list. -/
theorem resolve_sat_imp_resolveMid
    (hsat : Satisfied2 hash automataflResolveDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ∀ x y : Nat, x < NN → y < NN →
      codeToParticle ((envAt t i).loc (mid (y * NN + x)))
        = (resolveMid (boardDecodeOld (envAt t i))
            [moveDecode (envAt t i) 0, moveDecode (envAt t i) 1]).cellAt ⟨x, y⟩ := by
  have F := resolveFacts_of_sat hsat hc i hi
  intro x y hx hy
  have hx2 : x < 2 := by simpa [NN] using hx
  have hy2 : y < 2 := by simpa [NN] using hy
  interval_cases x <;> interval_cases y
  · exact midCell_of_facts F 0 0 0 (by norm_num) (by norm_num) rfl
      (writeCell_of_sat hsat i hi 0 0 0 (mem_resolve_of_mem_writeMid (wm_writeCell 2 0 (by decide))) rfl)
  · exact midCell_of_facts F 0 1 2 (by norm_num) (by norm_num) rfl
      (writeCell_of_sat hsat i hi 2 1 0 (mem_resolve_of_mem_writeMid (wm_writeCell 2 2 (by decide))) rfl)
  · exact midCell_of_facts F 1 0 1 (by norm_num) (by norm_num) rfl
      (writeCell_of_sat hsat i hi 1 0 1 (mem_resolve_of_mem_writeMid (wm_writeCell 2 1 (by decide))) rfl)
  · exact midCell_of_facts F 1 1 3 (by norm_num) (by norm_num) rfl
      (writeCell_of_sat hsat i hi 3 1 1 (mem_resolve_of_mem_writeMid (wm_writeCell 2 3 (by decide))) rfl)

end Capstone

/-! ## §D.5 — LEG R's PACKED COMMITMENT TRANSPORT (the seam ingredient).

Leg R adopted the packed base-4 commitment (`NGen.commitBoardsConstraints`), so its published PIs
are the packed felts of the OLD board (`[16, 16+fc)`), the packed felts of the MID board
(`[16+fc, 16+2fc)`) and the automaton coordinate. These lemmas are the Leg-R mirror of
`AutomataflCommitRefine`'s Leg-A instances, and they are what turns the whole-turn seam from a
hypothesis about BOARDS into a hypothesis about PUBLIC INPUTS. All `n`-generic; no chip lookup, no
hash, no soundness assumption. -/

section RCommit
open Dregg2.Circuit.Emit.AutomataflCommit
open Dregg2.Circuit.Emit.AutomataflCommitRefine
  (gate_of_mem piFirst_of_mem pack_pi_of_mem boardDecodeCommitAt seam_of_pack_congr)

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {n : Nat}

/-- The OLD board cells of a satisfying Leg-R trace are in the particle alphabet, `n`-generically. -/
theorem rcommit_oldAlpha (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (c : Nat) (hcK : c < n * n) :
    ((envAt t 0).loc (NGen.old n c) = 0 ∨ (envAt t 0).loc (NGen.old n c) = 1
      ∨ (envAt t 0).loc (NGen.old n c) = 2 ∨ (envAt t 0).loc (NGen.old n c) = 3) :=
  AutomataflStepRefine.mem4_of_gate
    (gate_of_mem hsat 0 (by omega) (mem_resolve_of_mem_boardRange (br_old n c hcK)))
    (canon_loc hc 0 _)

/-- The COMMITTED FINAL board cells `cMidV4` likewise — off the NEW `assert_member(cMidV4, {0,1,2,3})`
range gate. This is the `{0,1,2,3}` precondition the packed-`cMidV4` commitment transport needs. -/
theorem rcommit_cMidV4Alpha (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (c : Nat) (hcK : c < n * n) :
    ((envAt t 0).loc (NGen.cMidV4 n c) = 0 ∨ (envAt t 0).loc (NGen.cMidV4 n c) = 1
      ∨ (envAt t 0).loc (NGen.cMidV4 n c) = 2 ∨ (envAt t 0).loc (NGen.cMidV4 n c) = 3) :=
  AutomataflStepRefine.mem4_of_gate
    (gate_of_mem hsat 0 (by omega) (mem_resolve_of_mem_boardRange (br_cMidV4 n c hcK)))
    (canon_loc hc 0 _)

theorem rcommit_oldPack_mem (j : Nat) (hj : j < feltCount n) :
    linGate (packTermsAt n j (NGen.old n) (NGen.packOldFelt n)) 0
      ∈ (automataflResolveDescN n).constraints := by
  refine mem_resolve_of_mem_commit ?_
  unfold NGen.commitBoardsConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))

theorem rcommit_midPack_mem (j : Nat) (hj : j < feltCount n) :
    linGate (packTermsAt n j (NGen.cMidV4 n) (NGen.packMidFelt n)) 0
      ∈ (automataflResolveDescN n).constraints := by
  refine mem_resolve_of_mem_commit ?_
  unfold NGen.commitBoardsConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))

theorem rcommit_oldPi_mem (j : Nat) (hj : j < feltCount n) :
    (.base (.piBinding VmRow.first (NGen.packOldFelt n j) (16 + j)) : VmConstraint2)
      ∈ (automataflResolveDescN n).constraints := by
  refine mem_resolve_of_mem_commit ?_
  unfold NGen.commitBoardsConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))

theorem rcommit_midPi_mem (j : Nat) (hj : j < feltCount n) :
    (.base (.piBinding VmRow.first (NGen.packMidFelt n j) (16 + NGen.RFC n + j)) : VmConstraint2)
      ∈ (automataflResolveDescN n).constraints := by
  refine mem_resolve_of_mem_commit ?_
  unfold NGen.commitBoardsConstraints
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))

theorem rcommit_autoX_mem :
    (.base (.piBinding VmRow.first (NGen.AX_C n) (NGen.AUTO_PI_BASE n)) : VmConstraint2)
      ∈ (automataflResolveDescN n).constraints := by
  refine mem_resolve_of_mem_commit ?_
  unfold NGen.commitBoardsConstraints
  exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))

theorem rcommit_autoY_mem :
    (.base (.piBinding VmRow.first (NGen.AY_C n) (NGen.AUTO_PI_BASE n + 1)) : VmConstraint2)
      ∈ (automataflResolveDescN n).constraints := by
  refine mem_resolve_of_mem_commit ?_
  unfold NGen.commitBoardsConstraints
  exact List.mem_append_right _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))

/-- **`resolve_oldPack_pi_of_sat`** — `PI[16+j]` IS the `j`-th packed felt of Leg R's OLD board. -/
theorem resolve_oldPack_pi_of_sat
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    t.pub (16 + j)
      ≡ packCell (boardCode (boardDecodeCommitAt n (NGen.old n) (envAt t 0)) n) j
        [ZMOD 2013265921] :=
  pack_pi_of_mem hsat hlen (NGen.old n) (NGen.packOldFelt n) 16 j
    (fun idx hidx => rcommit_oldAlpha hsat hc hlen idx hidx)
    (rcommit_oldPack_mem j hj) (rcommit_oldPi_mem j hj)

/-- **`resolve_midPack_pi_of_sat` — THE SEAM SIDE, now over the FINAL corrected board `cMidV4`.**
`PI[16+fc+j]` IS the `j`-th packed felt of Leg R's `cMidV4` board — the THIRD-wound-fixed FINAL board
that `AutomataflResolveMovesCapstone.resolve_sat_imp_roundBoardN` pins to the `AutomataflRules.
roundStep` resolve board (`old` on a clash, the VALIDATED `resolveMoves` cell otherwise). The
commitment window packs `cMidV4` (not the V2 `mid`), so this is an EMITTED transport off the pack
gate + the `.piBinding` + the NEW `cMidV4` alphabet range gate — no hash, no chip-soundness
hypothesis. This is exactly the `hRmidPack` ingredient the whole-turn cell seam
(`AutomataflTurnCapstone.turn_sat_imp_roundStep_pi`) needs, so that seam is now fully
emitted-crypto-free (it takes only the fold PI-equalities). -/
theorem resolve_midPack_pi_of_sat
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    t.pub (16 + NGen.RFC n + j)
      ≡ packCell (boardCode (boardDecodeCommitAt n (NGen.cMidV4 n) (envAt t 0)) n) j
        [ZMOD 2013265921] :=
  pack_pi_of_mem hsat hlen (NGen.cMidV4 n) (NGen.packMidFelt n) (16 + NGen.RFC n) j
    (fun idx hidx => rcommit_cMidV4Alpha hsat hc hlen idx hidx)
    (rcommit_midPack_mem j hj) (rcommit_midPi_mem j hj)

theorem resolve_autoX_pi_of_sat
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hlen : 1 < t.rows.length) :
    (envAt t 0).loc (NGen.AX_C n) ≡ t.pub (NGen.AUTO_PI_BASE n) [ZMOD 2013265921] :=
  piFirst_of_mem hsat hlen _ _ rcommit_autoX_mem

theorem resolve_autoY_pi_of_sat
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hlen : 1 < t.rows.length) :
    (envAt t 0).loc (NGen.AY_C n) ≡ t.pub (NGen.AUTO_PI_BASE n + 1) [ZMOD 2013265921] :=
  piFirst_of_mem hsat hlen _ _ rcommit_autoY_mem

/-- **`resolve_forge_rejected`** — the Leg-R transport BITES: no satisfying canonical witness can
publish a MID commitment that is not the genuine pack of the FINAL corrected board `cMidV4` the
roundStep-faithful rewrite proved over. -/
theorem resolve_forge_rejected
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n)
    (hforge : ¬ (t.pub (16 + NGen.RFC n + j)
      ≡ packCell (boardCode (boardDecodeCommitAt n (NGen.cMidV4 n) (envAt t 0)) n) j
        [ZMOD 2013265921])) : False :=
  hforge (resolve_midPack_pi_of_sat hsat hc hlen j hj)

end RCommit

/-! ## §D.6b — THE V2 WHOLE-TURN THEOREM `resolve_step_sat_imp_applyTurn` IS RETIRED.

It proved `new = applyTurn(old, moves)` at `NN = 2` by discharging the cell seam from Leg R's MID
commitment pack transport. The commitment now packs the FINAL corrected board `cMidV4` (not the V2
`mid`), so that crypto-free seam over the `mid` columns no longer exists — and its `applyTurn =
automatonStep ∘ resolveMid` conclusion is the SUPERSEDED V2 spec (the buggy board the occlusion /
2-cycle corrections were built to fix). The correct whole turn is
`AutomataflTurnCapstone.turn_sat_imp_roundStep_pi` at the deployed `n = 11`, over `roundStep` /
`resolveMoves` / `cMidV4`, with the cell seam now a fully EMITTED-crypto-free consequence of
`resolve_midPack_pi_of_sat` (this file, re-pointed to `cMidV4`). -/

#print axioms resolveFacts_of_sat
#print axioms midCell_of_facts
#print axioms resolve_sat_imp_resolveMid
-- LEG R's PACKED COMMITMENT TRANSPORT (the seam ingredients).
#print axioms rcommit_oldAlpha
#print axioms rcommit_cMidV4Alpha
#print axioms resolve_oldPack_pi_of_sat
#print axioms resolve_midPack_pi_of_sat
#print axioms resolve_autoX_pi_of_sat
#print axioms resolve_autoY_pi_of_sat
#print axioms resolve_forge_rejected

/-! ## §D.7 — THE OCCLUSION-INDEPENDENT ADJUDICATION CORE, AT ARBITRARY BOARD SIZE `n`.

Everything above is keyed at the frozen `NN = 2` (`automataflResolveDesc`). This section re-proves the
part of Leg R's argument that is *occlusion-independent and coordinate-independent* — the
`fork`/`collide`/`survive` selection truth-table (Leg 4), the carries (Leg 5) and the flow-through
bits (Leg 6) — as ARGUMENTS OVER AN ARBITRARY `n`, off `Satisfied2 (automataflResolveDescN n)`.

WHY THESE AND NOT THE WHOLE CAPSTONE. Legs 4/5/6 compute booleans out of the pattern bits and the
non-vacuum bits by PURE GATE ALGEBRA — no coordinate window, no board enumeration, no occlusion. So
their proofs port verbatim from the `NN = 2` originals with only the descriptor swapped
(`automataflResolveDescN n`) and the membership drawn from the already-`n`-generic
`AutomataflResolveMembership` (`mem_selection_idx` / `mem_carry_idx` / `mem_flowThrough_idx`, whose
families are fixed-length lists whose positions do NOT move with `n`). `selectionConstraints n`,
`carryConstraints n` and `flowThroughConstraints n` are literally the same 6 / 4 / 14 gates as the
frozen ones, so every polynomial-shape `rfl` and every `norm_num` closes unchanged.

WHAT THE COORDINATE FAMILY NOW REACHES (§D.8, off the `AutomataflCoord` foundation). The
COORDINATE-DEPENDENT extractions that needed the `[0, n)` window are now closed at ARBITRARY `n`:
`sourceReadN_of_sat` (the witnessed source read, off `oneHotN_of_sat` + `dot_oneHot2`),
`validMoveN_of_sat` (`validate_move` ⇒ the reference `MoveValid`, off `coordN_of_sat` +
`autoPinN_of_sat` + `sqdistN_pure`), `ivN_of_sat` (the witnessed `is_vertical`), `eqCoordsN_of_sat`
(the four pattern bits) and `srcNonVacN_of_sat` (the source-non-vacuum bit). The `{0,1}` reasoning
(`coord01_of_sat` / `interval_cases` / `sqdist_pure` / the 4-cell split) is replaced by the
foundation's `coordN_of_sat` UPPER-edge decode and the generalised `sqdistN_pure`/`sq1dN_pure` under
EXPLICIT board-size windows (`2·(n−1)² < p`, `2^(rbits+1) ≤ p`, and for the 9-bit `is_vertical` /
`eq_coords` distance sites the honest cap `dist ≤ 999` that the FIXED `RBITS = 9` decomposition
imposes). All five are `#print axioms`-clean and non-vacuous at `n = 3`.

WHAT IS STILL NOT HERE, AND WHY (the honest residual). The CAPSTONE `resolve_sat_imp_resolveMid` is
NOT yet reached at `n > 2`; three ingredients remain at `NN = 2`:
  • a NON-VACUOUS OCCLUSION discharge. The generic occlusion MATH exists
    (`AutomataflOcclusionGeneric.occ_eq_occluded_vert/horiz`), but its `Satisfied2` discharge
    `occ_iff_occluded_of_sat` (in `AutomataflOcclusionBridge`) is still stated at `NN = 2` (built on
    `coord01_of_sat` + `NN = 2`); the capstone's occlusion leg here still routes through `occ_of_sat`
    / `occluded_false_n2` VACUITY;
  • the per-cell `write_mid` assembly (`writeCell_of_sat` / `midCell_of_facts`), still enumerated over
    the 4-cell `{0,1}²` board;
  • the caterpillar coordinate bounds (`nextOf_pair` / `followChain_*` / `chainDest_*`), still stated
    with `.x < 2 ∧ .y < 2`.
So `resolve_sat_imp_resolveMid` remains at `NN = 2`; it is NOT restated at an `n` its proof cannot
reach. The `n`-generic coordinate extractions above are the assembled-capstone's inputs, landed but
not yet composed. -/

section AdjudicationCoreN
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {n : Nat}

/-- `rgate`, n-generically: a per-row gate of `automataflResolveDescN n` forces its body to vanish
mod `p` on a non-last row. The proof is n-independent — identical to the frozen `rgate` with the
descriptor a variable. -/
theorem rgateN (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {g : EmittedExpr}
    (hg : cg g ∈ (automataflResolveDescN n).constraints) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have h : i + 1 ≠ t.rows.length := by omega
    simpa using h
  simpa only [cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- The `Head` form of `rgateN`. -/
theorem rgateHN (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {h : Head}
    (hg : cgH h ∈ (automataflResolveDescN n).constraints) :
    (headToExpr h).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] :=
  rgateN hsat i hi hg

/-- `Builder::alloc_prod`, n-generically. -/
theorem prodN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (out a b : Nat)
    (hg : cgH ((Head.lin (-1) out).addProd 1 [a, b]) ∈ (automataflResolveDescN n).constraints)
    (ha : (envAt t i).loc a = 0 ∨ (envAt t i).loc a = 1)
    (hb : (envAt t i).loc b = 0 ∨ (envAt t i).loc b = 1) :
    (envAt t i).loc out = (envAt t i).loc a * (envAt t i).loc b := by
  set e := envAt t i with he
  have hgg := rgateHN hsat i hi hg
  have hE : (headToExpr ((Head.lin (-1) out).addProd 1 [a, b])).eval e.loc
      = (-1) * e.loc out + e.loc a * e.loc b := rfl
  rw [hE] at hgg
  refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hgg)).symm
  rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;>
    exact ⟨by norm_num, by norm_num⟩

/-- `not_bit`, n-generically. -/
theorem notBitN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (out col : Nat)
    (hg : notBitPin out col ∈ (automataflResolveDescN n).constraints)
    (hb : (envAt t i).loc col = 0 ∨ (envAt t i).loc col = 1) :
    (envAt t i).loc out = 1 - (envAt t i).loc col := by
  set e := envAt t i with he
  have hgg := rgateHN hsat i hi hg
  have hE : (headToExpr (((Head.lin 1 out).addLin 1 col).addConst (-1))).eval e.loc
      = e.loc out + e.loc col + (-1) := rfl
  rw [hE] at hgg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hgg)
  rcases hb with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩

/-- **Leg 4 — `selectionN_of_sat`: THE SELECTION TRUTH TABLE, AT ARBITRARY `n`.** The `n`-generic
twin of `selection_of_sat`: the emitted `fork`, `collide` and `surv` columns are booleans, each
EXACTLY its reference condition as a function of the four pattern bits and the two non-vacuum bits.
Pure gate algebra over columns already known boolean — occlusion- and coordinate-independent. -/
theorem selectionN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hff : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1)
    (htt : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1)
    (hanz : (envAt t i).loc (NGen.cAnz n) = 0 ∨ (envAt t i).loc (NGen.cAnz n) = 1)
    (hbnz : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1) :
    ((envAt t i).loc (NGen.cFork n) = 1 ↔
        ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1
          ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0))
    ∧ ((envAt t i).loc (NGen.cCollide n) = 1 ↔
        ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1
          ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0
          ∧ (envAt t i).loc (NGen.cAnz n) = 1 ∧ (envAt t i).loc (NGen.cBnz n) = 1))
    ∧ ((envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1)
    ∧ ((envAt t i).loc (NGen.cSurv n) = 1 ↔
        ((envAt t i).loc (NGen.cFork n) = 0 ∧ (envAt t i).loc (NGen.cCollide n) = 0)) := by
  set e := envAt t i with he
  have hforkv : e.loc (NGen.cFork n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 0))
        - e.loc (NGen.cEqBit n (NGen.eqBase n 0)) * e.loc (NGen.cEqBit n (NGen.eqBase n 1)) := by
    have hg := rgateHN hsat i hi
      (h := ((Head.lin 1 (NGen.cFork n)).addLin (-1) (NGen.cEqBit n (NGen.eqBase n 0))).addProd 1
              [NGen.cEqBit n (NGen.eqBase n 0), NGen.cEqBit n (NGen.eqBase n 1)])
      (mem_selection_idx n 0 (show (0:Nat) < 6 by decide))
    have hE : (headToExpr (((Head.lin 1 (NGen.cFork n)).addLin (-1)
          (NGen.cEqBit n (NGen.eqBase n 0))).addProd 1
          [NGen.cEqBit n (NGen.eqBase n 0), NGen.cEqBit n (NGen.eqBase n 1)])).eval e.loc
        = e.loc (NGen.cFork n) + (-1) * e.loc (NGen.cEqBit n (NGen.eqBase n 0))
          + e.loc (NGen.cEqBit n (NGen.eqBase n 0)) * e.loc (NGen.cEqBit n (NGen.eqBase n 1)) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rcases htt with b | b <;> rw [a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hnff : e.loc (NGen.cNeqFf n) = 1 - e.loc (NGen.cEqBit n (NGen.eqBase n 0)) := by
    have hg := rgateHN hsat i hi
      (h := ((Head.lin 1 (NGen.cNeqFf n)).addLin 1 (NGen.cEqBit n (NGen.eqBase n 0))).addConst (-1))
      (mem_selection_idx n 1 (show (1:Nat) < 6 by decide))
    have hE : (headToExpr (((Head.lin 1 (NGen.cNeqFf n)).addLin 1
        (NGen.cEqBit n (NGen.eqBase n 0))).addConst (-1))).eval e.loc
        = e.loc (NGen.cNeqFf n) + e.loc (NGen.cEqBit n (NGen.eqBase n 0)) + (-1) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rw [a] <;> exact ⟨by norm_num, by norm_num⟩
  have hcol1 : e.loc (NGen.cCol1 n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 1)) * e.loc (NGen.cNeqFf n) := by
    have hg := rgateHN hsat i hi
      (h := (Head.lin (-1) (NGen.cCol1 n)).addProd 1 [NGen.cEqBit n (NGen.eqBase n 1), NGen.cNeqFf n])
      (mem_selection_idx n 2 (show (2:Nat) < 6 by decide))
    have hE : (headToExpr ((Head.lin (-1) (NGen.cCol1 n)).addProd 1
        [NGen.cEqBit n (NGen.eqBase n 1), NGen.cNeqFf n])).eval e.loc
        = (-1) * e.loc (NGen.cCol1 n)
          + e.loc (NGen.cEqBit n (NGen.eqBase n 1)) * e.loc (NGen.cNeqFf n) := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rw [hnff, a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hcol2 : e.loc (NGen.cCol2 n) = e.loc (NGen.cCol1 n) * e.loc (NGen.cAnz n) := by
    have hg := rgateHN hsat i hi
      (h := (Head.lin (-1) (NGen.cCol2 n)).addProd 1 [NGen.cCol1 n, NGen.cAnz n])
      (mem_selection_idx n 3 (show (3:Nat) < 6 by decide))
    have hE : (headToExpr ((Head.lin (-1) (NGen.cCol2 n)).addProd 1
        [NGen.cCol1 n, NGen.cAnz n])).eval e.loc
        = (-1) * e.loc (NGen.cCol2 n) + e.loc (NGen.cCol1 n) * e.loc (NGen.cAnz n) := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rw [hcol1, hnff, a, b, c] <;> exact ⟨by norm_num, by norm_num⟩
  have hcollv : e.loc (NGen.cCollide n) = e.loc (NGen.cCol2 n) * e.loc (NGen.cBnz n) := by
    have hg := rgateHN hsat i hi
      (h := (Head.lin (-1) (NGen.cCollide n)).addProd 1 [NGen.cCol2 n, NGen.cBnz n])
      (mem_selection_idx n 4 (show (4:Nat) < 6 by decide))
    have hE : (headToExpr ((Head.lin (-1) (NGen.cCollide n)).addProd 1
        [NGen.cCol2 n, NGen.cBnz n])).eval e.loc
        = (-1) * e.loc (NGen.cCollide n) + e.loc (NGen.cCol2 n) * e.loc (NGen.cBnz n) := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rcases hbnz with d | d <;> rw [hcol2, hcol1, hnff, a, b, c, d] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hsurvv : e.loc (NGen.cSurv n)
      = 1 - e.loc (NGen.cFork n) - e.loc (NGen.cCollide n)
        + e.loc (NGen.cFork n) * e.loc (NGen.cCollide n) := by
    have hg := rgateHN hsat i hi
      (h := ((((Head.lin 1 (NGen.cSurv n)).addConst (-1)).addLin 1 (NGen.cFork n)).addLin 1
              (NGen.cCollide n)).addProd (-1) [NGen.cFork n, NGen.cCollide n])
      (mem_selection_idx n 5 (show (5:Nat) < 6 by decide))
    have hE : (headToExpr (((((Head.lin 1 (NGen.cSurv n)).addConst (-1)).addLin 1
        (NGen.cFork n)).addLin 1 (NGen.cCollide n)).addProd (-1)
        [NGen.cFork n, NGen.cCollide n])).eval e.loc
        = e.loc (NGen.cSurv n) + e.loc (NGen.cFork n) + e.loc (NGen.cCollide n)
          + (-1) * (e.loc (NGen.cFork n) * e.loc (NGen.cCollide n)) + (-1) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rcases hbnz with d | d <;> rw [hforkv, hcollv, hcol2, hcol1, hnff, a, b, c, d] <;>
      exact ⟨by norm_num, by norm_num⟩
  rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
    rcases hbnz with d | d <;>
    rw [hcollv, hcol2, hcol1, hnff] at hsurvv ⊢ <;> rw [hforkv] at hsurvv ⊢ <;>
    rw [a, b, c, d] at hsurvv ⊢ <;> norm_num at hsurvv ⊢ <;>
    simp_all

/-- **Leg 5 — `carryN_of_sat`, AT ARBITRARY `n`.** The `n`-generic twin of `carry_of_sat`: the carry
column is EXACTLY `surv ∧ nz ∧ ¬occ`. Column-parametric; the proof is the frozen one with the
descriptor a variable and `prod_of_sat`/`rgateH` replaced by their `n`-generic twins. -/
theorem carryN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (sa1 carry surv nz occ : Nat)
    (hp : cgH ((Head.lin (-1) sa1).addProd 1 [surv, nz]) ∈ (automataflResolveDescN n).constraints)
    (hq : cgH (((Head.lin 1 carry).addProd (-1) [sa1]).addProd 1 [sa1, occ])
            ∈ (automataflResolveDescN n).constraints)
    (hsurv : (envAt t i).loc surv = 0 ∨ (envAt t i).loc surv = 1)
    (hnz : (envAt t i).loc nz = 0 ∨ (envAt t i).loc nz = 1)
    (hocc : (envAt t i).loc occ = 0 ∨ (envAt t i).loc occ = 1) :
    ((envAt t i).loc carry = 0 ∨ (envAt t i).loc carry = 1)
      ∧ ((envAt t i).loc carry = 1 ↔
          ((envAt t i).loc surv = 1 ∧ (envAt t i).loc nz = 1 ∧ (envAt t i).loc occ = 0)) := by
  set e := envAt t i with he
  have hsa : e.loc sa1 = e.loc surv * e.loc nz :=
    prodN_of_sat hsat hc i hi sa1 surv nz hp hsurv hnz
  have hcv : e.loc carry = e.loc sa1 - e.loc sa1 * e.loc occ := by
    have hgg := rgateHN hsat i hi hq
    have hE : (headToExpr (((Head.lin 1 carry).addProd (-1) [sa1]).addProd 1 [sa1, occ])).eval e.loc
        = e.loc carry + (-1) * e.loc sa1 + e.loc sa1 * e.loc occ := rfl
    rw [hE] at hgg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hgg)
    rcases hsurv with a | a <;> rcases hnz with b | b <;> rcases hocc with c | c <;>
      rw [hsa, a, b, c] <;> exact ⟨by norm_num, by norm_num⟩
  rcases hsurv with a | a <;> rcases hnz with b | b <;> rcases hocc with c | c <;>
    rw [hsa, a, b, c] at hcv <;> norm_num at hcv <;> rw [hcv, a, b, c] <;> norm_num

/-- **Leg 6 — `ftN_of_sat`, AT ARBITRARY `n`.** The `n`-generic twin of `ft_of_sat`: the
flow-through bit is EXACTLY the five-way conjunction the emitted chain computes. Column-parametric;
proof identical modulo the `n`-generic descriptor and `prod`/`notBit`/`rgate` twins. -/
theorem ftN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (nB nO nE f1 f2 f3 ft eqAb bnz occB eqBa surv : Nat)
    (g1 : notBitPin nB bnz ∈ (automataflResolveDescN n).constraints)
    (g2 : notBitPin nO occB ∈ (automataflResolveDescN n).constraints)
    (g3 : notBitPin nE eqBa ∈ (automataflResolveDescN n).constraints)
    (g4 : cgH ((Head.lin (-1) f1).addProd 1 [eqAb, nB]) ∈ (automataflResolveDescN n).constraints)
    (g5 : cgH ((Head.lin (-1) f2).addProd 1 [f1, surv]) ∈ (automataflResolveDescN n).constraints)
    (g6 : cgH ((Head.lin (-1) f3).addProd 1 [f2, nO]) ∈ (automataflResolveDescN n).constraints)
    (g7 : cgH ((Head.lin (-1) ft).addProd 1 [f3, nE]) ∈ (automataflResolveDescN n).constraints)
    (hab : (envAt t i).loc eqAb = 0 ∨ (envAt t i).loc eqAb = 1)
    (hbnz : (envAt t i).loc bnz = 0 ∨ (envAt t i).loc bnz = 1)
    (hocc : (envAt t i).loc occB = 0 ∨ (envAt t i).loc occB = 1)
    (hba : (envAt t i).loc eqBa = 0 ∨ (envAt t i).loc eqBa = 1)
    (hsurv : (envAt t i).loc surv = 0 ∨ (envAt t i).loc surv = 1) :
    ((envAt t i).loc ft = 0 ∨ (envAt t i).loc ft = 1)
      ∧ ((envAt t i).loc ft = 1 ↔
          ((envAt t i).loc eqAb = 1 ∧ (envAt t i).loc bnz = 0 ∧ (envAt t i).loc surv = 1
            ∧ (envAt t i).loc occB = 0 ∧ (envAt t i).loc eqBa = 0)) := by
  set e := envAt t i with he
  have hnB : e.loc nB = 1 - e.loc bnz := notBitN_of_sat hsat hc i hi nB bnz g1 hbnz
  have hnO : e.loc nO = 1 - e.loc occB := notBitN_of_sat hsat hc i hi nO occB g2 hocc
  have hnE : e.loc nE = 1 - e.loc eqBa := notBitN_of_sat hsat hc i hi nE eqBa g3 hba
  have bnB : e.loc nB = 0 ∨ e.loc nB = 1 := by rcases hbnz with h | h <;> rw [hnB, h] <;> norm_num
  have bnO : e.loc nO = 0 ∨ e.loc nO = 1 := by rcases hocc with h | h <;> rw [hnO, h] <;> norm_num
  have bnE : e.loc nE = 0 ∨ e.loc nE = 1 := by rcases hba with h | h <;> rw [hnE, h] <;> norm_num
  have hf1 : e.loc f1 = e.loc eqAb * e.loc nB := prodN_of_sat hsat hc i hi f1 eqAb nB g4 hab bnB
  have bf1 : e.loc f1 = 0 ∨ e.loc f1 = 1 := by
    rcases hab with a | a <;> rcases bnB with b | b <;> rw [hf1, a, b] <;> norm_num
  have hf2 : e.loc f2 = e.loc f1 * e.loc surv := prodN_of_sat hsat hc i hi f2 f1 surv g5 bf1 hsurv
  have bf2 : e.loc f2 = 0 ∨ e.loc f2 = 1 := by
    rcases bf1 with a | a <;> rcases hsurv with b | b <;> rw [hf2, a, b] <;> norm_num
  have hf3 : e.loc f3 = e.loc f2 * e.loc nO := prodN_of_sat hsat hc i hi f3 f2 nO g6 bf2 bnO
  have bf3 : e.loc f3 = 0 ∨ e.loc f3 = 1 := by
    rcases bf2 with a | a <;> rcases bnO with b | b <;> rw [hf3, a, b] <;> norm_num
  have hft : e.loc ft = e.loc f3 * e.loc nE := prodN_of_sat hsat hc i hi ft f3 nE g7 bf3 bnE
  rcases hab with a | a <;> rcases hbnz with b | b <;> rcases hsurv with c | c <;>
    rcases hocc with d | d <;> rcases hba with f | f <;>
    rw [hft, hf3, hf2, hf1, hnB, hnO, hnE, a, b, c, d, f] <;> norm_num

/-- The Leg-5 carry INSTANCE for move A, at arbitrary `n` (`n`-generic twin of `carryA_of_sat`). -/
theorem carryAN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1)
    (hnz : (envAt t i).loc (NGen.cAnz n) = 0 ∨ (envAt t i).loc (NGen.cAnz n) = 1)
    (hocc : (envAt t i).loc (NGen.cOcc n (NGen.occBase n 0)) = 0
        ∨ (envAt t i).loc (NGen.cOcc n (NGen.occBase n 0)) = 1) :
    ((envAt t i).loc (NGen.cCarryA n) = 0 ∨ (envAt t i).loc (NGen.cCarryA n) = 1)
      ∧ ((envAt t i).loc (NGen.cCarryA n) = 1 ↔
          ((envAt t i).loc (NGen.cSurv n) = 1 ∧ (envAt t i).loc (NGen.cAnz n) = 1
            ∧ (envAt t i).loc (NGen.cOcc n (NGen.occBase n 0)) = 0)) :=
  carryN_of_sat hsat hc i hi (NGen.cSa1 n) (NGen.cCarryA n) (NGen.cSurv n) (NGen.cAnz n)
    (NGen.cOcc n (NGen.occBase n 0))
    (mem_carry_idx n 0 (show (0:Nat) < 4 by decide)) (mem_carry_idx n 1 (show (1:Nat) < 4 by decide)) hsurv hnz hocc

/-- The Leg-5 carry INSTANCE for move B, at arbitrary `n`. -/
theorem carryBN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1)
    (hnz : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1)
    (hocc : (envAt t i).loc (NGen.cOcc n (NGen.occBase n 1)) = 0
        ∨ (envAt t i).loc (NGen.cOcc n (NGen.occBase n 1)) = 1) :
    ((envAt t i).loc (NGen.cCarryB n) = 0 ∨ (envAt t i).loc (NGen.cCarryB n) = 1)
      ∧ ((envAt t i).loc (NGen.cCarryB n) = 1 ↔
          ((envAt t i).loc (NGen.cSurv n) = 1 ∧ (envAt t i).loc (NGen.cBnz n) = 1
            ∧ (envAt t i).loc (NGen.cOcc n (NGen.occBase n 1)) = 0)) :=
  carryN_of_sat hsat hc i hi (NGen.cSb1 n) (NGen.cCarryB n) (NGen.cSurv n) (NGen.cBnz n)
    (NGen.cOcc n (NGen.occBase n 1))
    (mem_carry_idx n 2 (show (2:Nat) < 4 by decide)) (mem_carry_idx n 3 (show (3:Nat) < 4 by decide)) hsurv hnz hocc

/-- The Leg-6 flow-through INSTANCE for move A, at arbitrary `n` (`n`-generic twin of `ftA_of_sat`). -/
theorem ftAN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hab : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1)
    (hbnz : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1)
    (hocc : (envAt t i).loc (NGen.cOcc n (NGen.occBase n 1)) = 0
        ∨ (envAt t i).loc (NGen.cOcc n (NGen.occBase n 1)) = 1)
    (hba : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1) :
    ((envAt t i).loc (NGen.cFtA n) = 0 ∨ (envAt t i).loc (NGen.cFtA n) = 1)
      ∧ ((envAt t i).loc (NGen.cFtA n) = 1 ↔
          ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1 ∧ (envAt t i).loc (NGen.cBnz n) = 0
            ∧ (envAt t i).loc (NGen.cSurv n) = 1
            ∧ (envAt t i).loc (NGen.cOcc n (NGen.occBase n 1)) = 0
            ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0)) :=
  ftN_of_sat hsat hc i hi (NGen.cNBnz n) (NGen.cNOccb n) (NGen.cNEqba n) (NGen.cFa1 n) (NGen.cFa2 n)
    (NGen.cFa3 n) (NGen.cFtA n) (NGen.cEqBit n (NGen.eqBase n 2)) (NGen.cBnz n)
    (NGen.cOcc n (NGen.occBase n 1)) (NGen.cEqBit n (NGen.eqBase n 3)) (NGen.cSurv n)
    (mem_flowThrough_idx n 0 (show (0:Nat) < 14 by decide)) (mem_flowThrough_idx n 1 (show (1:Nat) < 14 by decide))
    (mem_flowThrough_idx n 2 (show (2:Nat) < 14 by decide)) (mem_flowThrough_idx n 3 (show (3:Nat) < 14 by decide))
    (mem_flowThrough_idx n 4 (show (4:Nat) < 14 by decide)) (mem_flowThrough_idx n 5 (show (5:Nat) < 14 by decide))
    (mem_flowThrough_idx n 6 (show (6:Nat) < 14 by decide)) hab hbnz hocc hba hsurv

/-- The Leg-6 flow-through INSTANCE for move B, at arbitrary `n`. -/
theorem ftBN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hba : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1)
    (hanz : (envAt t i).loc (NGen.cAnz n) = 0 ∨ (envAt t i).loc (NGen.cAnz n) = 1)
    (hocc : (envAt t i).loc (NGen.cOcc n (NGen.occBase n 0)) = 0
        ∨ (envAt t i).loc (NGen.cOcc n (NGen.occBase n 0)) = 1)
    (hab : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1) :
    ((envAt t i).loc (NGen.cFtB n) = 0 ∨ (envAt t i).loc (NGen.cFtB n) = 1)
      ∧ ((envAt t i).loc (NGen.cFtB n) = 1 ↔
          ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1 ∧ (envAt t i).loc (NGen.cAnz n) = 0
            ∧ (envAt t i).loc (NGen.cSurv n) = 1
            ∧ (envAt t i).loc (NGen.cOcc n (NGen.occBase n 0)) = 0
            ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0)) :=
  ftN_of_sat hsat hc i hi (NGen.cNAnz n) (NGen.cNOcca n) (NGen.cNEqab n) (NGen.cFb1 n) (NGen.cFb2 n)
    (NGen.cFb3 n) (NGen.cFtB n) (NGen.cEqBit n (NGen.eqBase n 3)) (NGen.cAnz n)
    (NGen.cOcc n (NGen.occBase n 0)) (NGen.cEqBit n (NGen.eqBase n 2)) (NGen.cSurv n)
    (mem_flowThrough_idx n 7 (show (7:Nat) < 14 by decide)) (mem_flowThrough_idx n 8 (show (8:Nat) < 14 by decide))
    (mem_flowThrough_idx n 9 (show (9:Nat) < 14 by decide)) (mem_flowThrough_idx n 10 (show (10:Nat) < 14 by decide))
    (mem_flowThrough_idx n 11 (show (11:Nat) < 14 by decide)) (mem_flowThrough_idx n 12 (show (12:Nat) < 14 by decide))
    (mem_flowThrough_idx n 13 (show (13:Nat) < 14 by decide)) hba hanz hocc hab hsurv

end AdjudicationCoreN

#print axioms rgateN
#print axioms selectionN_of_sat
#print axioms carryN_of_sat
#print axioms ftN_of_sat
#print axioms carryAN_of_sat
#print axioms carryBN_of_sat
#print axioms ftAN_of_sat
#print axioms ftBN_of_sat

/-! ## §D.8 — THE COORDINATE-DEPENDENT EXTRACTIONS, AT ARBITRARY BOARD SIZE `n`.

This section closes the FIRST family of the honest residual §D.7 named: the extractions whose frozen
proofs pinned coordinates to `{0,1}` (`coord01_of_sat` / `interval_cases` / `sqdist_pure` / the 4-cell
board enumeration). Each is re-proved off `Satisfied2 (automataflResolveDescN n)` at ARBITRARY `n`,
using the just-landed `AutomataflCoord` foundation (`coordN_of_sat`, `oneHotN_of_sat`, `dot_oneHot2`)
in place of the `{0,1}` reasoning, and the already-`n`-generic `AutomataflResolveMembership` injectors.

The window facts (`(n:ℤ) < p`, `2·(n−1)² < p`, `2^(rbits+1) ≤ p`) are EXPLICIT, discharged-at-call
inequalities on the board size — trivially true at every realistic `n` and non-vacuous at `n = 3` —
not assumed circuit facts. -/

section CoordExtractN
open Dregg2.Circuit.Emit.AutomataflCoord
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (OneHotAt)
open Dregg2.Circuit.Emit.AutomataflResolveMembership
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {n : Nat}

/-! ### §D.8.0 — Descriptor-generic reusable extractors (the `n`-generic twins of §0.2 / §3). -/

/-- The `one` pin, n-generically (`one_of_sat`'s twin). -/
theorem oneN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (NGen.ONE n) = 1 := by
  have hg := rgateHN hsat i hi (h := (Head.lin 1 (NGen.ONE n)).addConst (-1)) (mem_resolve_onePin n)
  have hE : (headToExpr ((Head.lin 1 (NGen.ONE n)).addConst (-1))).eval (envAt t i).loc
      = (envAt t i).loc (NGen.ONE n) + (-1) := rfl
  rw [hE] at hg
  exact eq_of_modEq_canon (canon_loc hc i _) canon_one ((gate_modEq_iff (by ring)).mp hg)

/-- The `cond_nonzero` extractor, n-generically (`condNonzero_of_sat`'s twin). -/
theorem condNonzeroN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (v inv : Nat)
    (hg : cg (gCondNonzero (NGen.ONE n) v inv) ∈ (automataflResolveDescN n).constraints) :
    ¬ ((envAt t i).loc v ≡ 0 [ZMOD 2013265921]) := by
  set e := envAt t i with he
  have hone := oneN_of_sat hsat hc i hi
  rw [← he] at hone
  have h := rgateN hsat i hi hg
  simp only [gCondNonzero, EmittedExpr.eval] at h
  rw [hone, one_mul] at h
  intro hz
  have : (e.loc v * e.loc inv + -1) ≡ (0 * e.loc inv + -1) [ZMOD 2013265921] :=
    Int.ModEq.add (Int.ModEq.mul hz (Int.ModEq.refl _)) (Int.ModEq.refl _)
  have h2 : (0 : ℤ) ≡ -1 [ZMOD 2013265921] := by
    calc (0 : ℤ) ≡ e.loc v * e.loc inv + -1 [ZMOD 2013265921] := h.symm
    _ ≡ 0 * e.loc inv + -1 [ZMOD 2013265921] := this
    _ = -1 := by ring
  exact absurd (eq_of_modEq_small (by norm_num) (by norm_num) h2) (by norm_num)

/-- The `eq == 1 − neq` pin, n-generically (`eqPin_of_sat`'s twin). -/
theorem eqPinN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (eqCol neqCol : Nat)
    (gp : cgH (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1))
            ∈ (automataflResolveDescN n).constraints)
    (hneq : (envAt t i).loc neqCol = 0 ∨ (envAt t i).loc neqCol = 1) :
    (envAt t i).loc eqCol = 1 - (envAt t i).loc neqCol := by
  set e := envAt t i with he
  have hg := rgateHN hsat i hi gp
  have hE : (headToExpr (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1))).eval e.loc
      = e.loc eqCol + e.loc neqCol + (-1) := rfl
  rw [hE] at hg
  have hmod := (gate_modEq_iff (x := e.loc eqCol + e.loc neqCol + -1)
    (a := e.loc eqCol) (b := 1 - e.loc neqCol) (by ring)).mp hg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ hmod
  rcases hneq with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩

/-- The 9-bit `forced_ge0` site extractor, n-generically (`ge0_9_of_sat`'s twin, membership args
raw). The recomposition head is a FIXED structure (independent of `n`), so its `eval` is still `rfl`;
`forcedGe0_wide` is pure; only the descriptor and the memberships are `n`-parametric. -/
theorem ge0_9N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (val ib bit0 : Nat)
    (hib : cg (gBin ib) ∈ (automataflResolveDescN n).constraints)
    (hbit : ∀ k, k < 9 → cg (gBin (bit0 + k)) ∈ (automataflResolveDescN n).constraints)
    (hrec : cgH ((List.range 9).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
                 (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))
             ∈ (automataflResolveDescN n).constraints)
    (hlo : -999 ≤ (envAt t i).loc val) (hhi : (envAt t i).loc val ≤ 999) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 → 1 ≤ (envAt t i).loc val)
      ∧ ((envAt t i).loc ib = 0 → (envAt t i).loc val ≤ 0) := by
  set e := envAt t i with he
  have hibv : e.loc ib = 0 ∨ e.loc ib = 1 :=
    bin_of_gate (rgateN hsat i hi hib) (canon_loc hc i _)
  have B : ∀ k : Nat, k < 9 → (0 ≤ e.loc (bit0 + k) ∧ e.loc (bit0 + k) ≤ 1) := by
    intro k hk
    have hb : e.loc (bit0 + k) = 0 ∨ e.loc (bit0 + k) = 1 :=
      bin_of_gate (rgateN hsat i hi (hbit k hk)) (canon_loc hc i _)
    rcases hb with h | h <;> omega
  have h0 := B 0 (by norm_num); have h1 := B 1 (by norm_num); have h2 := B 2 (by norm_num)
  have h3 := B 3 (by norm_num); have h4 := B 4 (by norm_num); have h5 := B 5 (by norm_num)
  have h6 := B 6 (by norm_num); have h7 := B 7 (by norm_num); have h8 := B 8 (by norm_num)
  set S : ℤ := e.loc (bit0 + 0) + 2 * e.loc (bit0 + 1) + 4 * e.loc (bit0 + 2)
    + 8 * e.loc (bit0 + 3) + 16 * e.loc (bit0 + 4) + 32 * e.loc (bit0 + 5)
    + 64 * e.loc (bit0 + 6) + 128 * e.loc (bit0 + 7) + 256 * e.loc (bit0 + 8) with hS
  have hS0 : 0 ≤ S := by rw [hS]; omega
  have hS1 : S ≤ 511 := by rw [hS]; omega
  have hg := rgateHN hsat i hi hrec
  have hE : (headToExpr ((List.range 9).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
        (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))).eval e.loc
      = 2 * (e.loc ib * e.loc val) + (-2) * e.loc ib + e.loc ib + (-1) * e.loc val
        + (-1) * e.loc (bit0 + 0) + (-2) * e.loc (bit0 + 1) + (-4) * e.loc (bit0 + 2)
        + (-8) * e.loc (bit0 + 3) + (-16) * e.loc (bit0 + 4) + (-32) * e.loc (bit0 + 5)
        + (-64) * e.loc (bit0 + 6) + (-128) * e.loc (bit0 + 7)
        + (-256) * e.loc (bit0 + 8) := by rfl
  rw [hE] at hg
  have hmod : (2 * e.loc ib * (e.loc val - 1) + e.loc ib - (e.loc val - 1) - 1)
      ≡ S [ZMOD 2013265921] := by
    refine (gate_modEq_iff ?_).mp hg
    rw [hS]; ring
  obtain ⟨hp, hn⟩ := forcedGe0_wide hibv hS0 hS1 hmod (by omega) (by omega)
  exact ⟨hibv, fun h => by have := hp h; omega, fun h => by have := hn h; omega⟩

/-- The 5-bit `forced_ge0` site extractor, n-generically (`ge0_5_of_sat`'s twin). -/
theorem ge0_5N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (val ib bit0 : Nat)
    (hib : cg (gBin ib) ∈ (automataflResolveDescN n).constraints)
    (hbit : ∀ k, k < 5 → cg (gBin (bit0 + k)) ∈ (automataflResolveDescN n).constraints)
    (hrec : cgH ((List.range 5).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
                 (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))
             ∈ (automataflResolveDescN n).constraints)
    (hlo : -99 ≤ (envAt t i).loc val) (hhi : (envAt t i).loc val ≤ 99) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 → 1 ≤ (envAt t i).loc val)
      ∧ ((envAt t i).loc ib = 0 → (envAt t i).loc val ≤ 0) := by
  set e := envAt t i with he
  have hibv : e.loc ib = 0 ∨ e.loc ib = 1 :=
    bin_of_gate (rgateN hsat i hi hib) (canon_loc hc i _)
  have B : ∀ k : Nat, k < 5 → (0 ≤ e.loc (bit0 + k) ∧ e.loc (bit0 + k) ≤ 1) := by
    intro k hk
    have hb : e.loc (bit0 + k) = 0 ∨ e.loc (bit0 + k) = 1 :=
      bin_of_gate (rgateN hsat i hi (hbit k hk)) (canon_loc hc i _)
    rcases hb with h | h <;> omega
  have h0 := B 0 (by norm_num); have h1 := B 1 (by norm_num); have h2 := B 2 (by norm_num)
  have h3 := B 3 (by norm_num); have h4 := B 4 (by norm_num)
  set S : ℤ := e.loc (bit0 + 0) + 2 * e.loc (bit0 + 1) + 4 * e.loc (bit0 + 2)
    + 8 * e.loc (bit0 + 3) + 16 * e.loc (bit0 + 4) with hS
  have hS0 : 0 ≤ S := by rw [hS]; omega
  have hS1 : S ≤ 31 := by rw [hS]; omega
  have hg := rgateHN hsat i hi hrec
  have hE : (headToExpr ((List.range 5).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
        (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))).eval e.loc
      = 2 * (e.loc ib * e.loc val) + (-2) * e.loc ib + e.loc ib + (-1) * e.loc val
        + (-1) * e.loc (bit0 + 0) + (-2) * e.loc (bit0 + 1) + (-4) * e.loc (bit0 + 2)
        + (-8) * e.loc (bit0 + 3) + (-16) * e.loc (bit0 + 4) := by rfl
  rw [hE] at hg
  have hmod : (2 * e.loc ib * (e.loc val - 1) + e.loc ib - (e.loc val - 1) - 1)
      ≡ S [ZMOD 2013265921] := by
    refine (gate_modEq_iff ?_).mp hg
    rw [hS]; ring
  obtain ⟨hp, hn⟩ := forcedGe0_core hibv hS0 hS1 hmod (by omega) (by omega)
  exact ⟨hibv, fun h => by have := hp h; omega, fun h => by have := hn h; omega⟩

/-! ### §D.8.1 — Generalised squared-distance purity: coordinates in `[0, n)`, no `{0,1}` split. -/

/-- **`sqdistN_pure`** (`sqdist_pure`'s twin). A witnessed 2-D squared-distance column over four
coordinates each in `[0, M]` is exactly the integer squared distance, provided the no-wrap window
`2·M² < p` holds. `sqdist_pure` was this at `M = 1` with a `{0,1}⁴` enumeration; here the window is
an explicit inequality on the board size. -/
theorem sqdistN_pure {d x1 x2 y1 y2 M : ℤ} (hd : Canon d)
    (bx1 : 0 ≤ x1 ∧ x1 ≤ M) (bx2 : 0 ≤ x2 ∧ x2 ≤ M)
    (by1 : 0 ≤ y1 ∧ y1 ≤ M) (by2 : 0 ≤ y2 ∧ y2 ≤ M)
    (hwin : 2 * M * M < 2013265921)
    (h : d + (-1) * (x1 * x1) + 2 * (x1 * x2) + (-1) * (x2 * x2)
          + (-1) * (y1 * y1) + 2 * (y1 * y2) + (-1) * (y2 * y2) ≡ 0 [ZMOD 2013265921]) :
    d = (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2) := by
  have hdx : (x1 - x2) * (x1 - x2) ≤ M * M :=
    by nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ M - (x1 - x2)) (by linarith : (0:ℤ) ≤ M + (x1 - x2))]
  have hdy : (y1 - y2) * (y1 - y2) ≤ M * M :=
    by nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ M - (y1 - y2)) (by linarith : (0:ℤ) ≤ M + (y1 - y2))]
  have hval : Canon ((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)) :=
    ⟨by nlinarith [mul_self_nonneg (x1 - x2), mul_self_nonneg (y1 - y2)],
     by nlinarith [hdx, hdy, hwin]⟩
  exact eq_of_modEq_canon hd hval ((gate_modEq_iff (by ring)).mp h)

/-- **`sq1dN_pure`** (`sq1d_pure`'s twin). The 1-D `eq_scalar` squared-distance over two coordinates
in `[0, M]`, under `M² < p`. -/
theorem sq1dN_pure {d a c M : ℤ} (hd : Canon d)
    (ba : 0 ≤ a ∧ a ≤ M) (bc : 0 ≤ c ∧ c ≤ M) (hwin : M * M < 2013265921)
    (h : d + (-1) * (a * a) + 2 * (a * c) + (-1) * (c * c) ≡ 0 [ZMOD 2013265921]) :
    d = (a - c) * (a - c) := by
  have hval : Canon ((a - c) * (a - c)) :=
    ⟨mul_self_nonneg _,
     by nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ M - (a - c)) (by linarith : (0:ℤ) ≤ M + (a - c)), hwin]⟩
  exact eq_of_modEq_canon hd hval ((gate_modEq_iff (by ring)).mp h)

/-! ### §D.8.2 — `sourceReadN_of_sat`: the witnessed source particle IS the OLD board cell.

The `n`-generic twin of `sourceRead_of_sat` (§2), off `oneHotN_of_sat` (the two source one-hots) and
`dot_oneHot2` (the row×column collapse), in place of the frozen 4-cell `rcases`. -/

/-- The clean semantic value of `sourceReadHead`: `fp − Σ_y Σ_x selRow[y]·selCol[x]·old[y·n+x]`,
written so the double sum is EXACTLY the shape `dot_oneHot2` collapses (the `−1` absorbed into the
cell payload). The variable-length `foldl` does not `rfl`-reduce, so this is proved via the `evalH`
combinators — the twin of the foundation's `evalH_autoPinHead`. -/
theorem evalH_sourceReadHead (a : Nat → ℤ) (m b : Nat) :
    evalH (NGen.sourceReadHead m b) a
      = a (NGen.cFp m b)
        + ((List.range m).map (fun y => ((List.range m).map (fun x =>
            a (NGen.cSelRow m b y) * a (NGen.cSelCol m b x)
              * (- a (NGen.old m (y * m + x))))).sum)).sum := by
  have hinner : ∀ (h : Head) (y : Nat),
      evalH ((List.range m).foldl (fun h2 x =>
          h2.addProd (-1) [NGen.cSelRow m b y, NGen.cSelCol m b x, NGen.old m (y * m + x)]) h) a
        = evalH h a
          + ((List.range m).map (fun x =>
              a (NGen.cSelRow m b y) * a (NGen.cSelCol m b x)
                * (- a (NGen.old m (y * m + x))))).sum := by
    intro h y
    exact evalH_foldl_step a h (List.range m)
      (fun h2 x => h2.addProd (-1) [NGen.cSelRow m b y, NGen.cSelCol m b x, NGen.old m (y * m + x)])
      (fun x => a (NGen.cSelRow m b y) * a (NGen.cSelCol m b x) * (- a (NGen.old m (y * m + x))))
      (by intro h2 x; rw [evalH_addProd]; simp only [varsVal, List.foldl_cons, List.foldl_nil]; ring)
  rw [NGen.sourceReadHead,
    evalH_foldl_step a (Head.lin 1 (NGen.cFp m b)) (List.range m)
      (fun h y => (List.range m).foldl (fun h2 x =>
          h2.addProd (-1) [NGen.cSelRow m b y, NGen.cSelCol m b x, NGen.old m (y * m + x)]) h)
      (fun y => ((List.range m).map (fun x =>
          a (NGen.cSelRow m b y) * a (NGen.cSelCol m b x) * (- a (NGen.old m (y * m + x))))).sum)
      hinner,
    evalH_lin]
  ring

/-- **`sourceReadN_of_sat`.** On a satisfying, canonical trace of `automataflResolveDescN n`, the
witnessed source particle `fp` IS the OLD board cell `old[n·fy + fx]`: the source row/column one-hots
collapse `Σ selRow·selCol·old` to the single cell at `(fx, fy)`, `n`-generically. The membership of
the whole `validate_move` block is supplied by `hmv` (instantiated with
`mem_resolve_of_mem_validateMove0/1` at the two move bases). -/
theorem sourceReadN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b : Nat)
    (hn : (n : ℤ) < 2013265921)
    (hmv : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n b
            → g ∈ (automataflResolveDescN n).constraints) :
    ∃ X Y : Nat, X < n ∧ Y < n
      ∧ (envAt t i).loc (NGen.cFx n b) = (X : ℤ) ∧ (envAt t i).loc (NGen.cFy n b) = (Y : ℤ)
      ∧ (envAt t i).loc (NGen.cFp n b) = (envAt t i).loc (NGen.old n (Y * n + X)) := by
  set e := envAt t i with he
  obtain ⟨ay, hayLt, hfyEq, hrow⟩ :=
    oneHotN_of_sat hsat hc i hi n hn (NGen.cSelRow n b) (NGen.cFy n b)
      (fun j hj => hmv (vm_selRow n b j hj)) (hmv (vm_srRs n b)) (hmv (vm_srRi n b))
  obtain ⟨ax, haxLt, hfxEq, hcol⟩ :=
    oneHotN_of_sat hsat hc i hi n hn (NGen.cSelCol n b) (NGen.cFx n b)
      (fun j hj => hmv (vm_selCol n b j hj)) (hmv (vm_srCs n b)) (hmv (vm_srCi n b))
  rw [← he] at hfyEq hfxEq
  have hg := rgateHN hsat i hi (hmv (vm_srcRd n b))
  rw [headToExpr_eval, evalH_sourceReadHead,
    dot_oneHot2 hrow hcol (fun y x => - e.loc (NGen.old n (y * n + x)))] at hg
  -- hg : e.loc (cFp n b) + (- e.loc (old n (ay*n+ax))) ≡ 0
  have hmod : e.loc (NGen.cFp n b) ≡ e.loc (NGen.old n (ay * n + ax)) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hg
  exact ⟨ax, ay, haxLt, hayLt, hfxEq, hfyEq,
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) hmod⟩

/-! ### §D.8.3 — `ivN_of_sat`: the witnessed direction bit IS the real geometry, at arbitrary `n`.

The `n`-generic twin of `iv_of_sat` (§4). The squared-distance definition is a FIXED head (`rfl`
eval); `sq1dN_pure` replaces the `{0,1}` `sq1d_pure`; the 9-bit `forced_ge0` decides the bit provided
the (pinned) squared distance fits, which is the honest window `M² ≤ 999` on the board size
(`M = n − 1`). NON-VACUOUS at `n = 3` (`M = 2`, `M² = 4 ≤ 999`). -/
theorem ivN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat) (M : ℤ)
    (hwin : M * M ≤ 999)
    (hfx : 0 ≤ (envAt t i).loc (NGen.cFx n b) ∧ (envAt t i).loc (NGen.cFx n b) ≤ M)
    (htx : 0 ≤ (envAt t i).loc (NGen.cTx n b) ∧ (envAt t i).loc (NGen.cTx n b) ≤ M)
    (hvo : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
            → g ∈ (automataflResolveDescN n).constraints) :
    ((envAt t i).loc (NGen.cIv n o) = 0 ∨ (envAt t i).loc (NGen.cIv n o) = 1)
      ∧ ((envAt t i).loc (NGen.cIv n o) = 1 ↔
          (envAt t i).loc (NGen.cFx n b) = (envAt t i).loc (NGen.cTx n b)) := by
  set e := envAt t i with he
  have hdsq : e.loc (NGen.cIvDsq n o)
      = (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) * (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) := by
    have hg := rgateHN hsat i hi (hvo (vo_iv_dsq n b o ob))
    have hE : (headToExpr ((((Head.lin 1 (NGen.cIvDsq n o)).addProd (-1) [NGen.cFx n b, NGen.cFx n b]).addProd 2
          [NGen.cFx n b, NGen.cTx n b]).addProd (-1) [NGen.cTx n b, NGen.cTx n b])).eval e.loc
        = e.loc (NGen.cIvDsq n o) + (-1) * (e.loc (NGen.cFx n b) * e.loc (NGen.cFx n b))
          + 2 * (e.loc (NGen.cFx n b) * e.loc (NGen.cTx n b))
          + (-1) * (e.loc (NGen.cTx n b) * e.loc (NGen.cTx n b)) := rfl
    rw [hE] at hg
    exact sq1dN_pure (canon_loc hc i _) hfx htx (by nlinarith [hwin]) hg
  have hbnd : -999 ≤ e.loc (NGen.cIvDsq n o) ∧ e.loc (NGen.cIvDsq n o) ≤ 999 := by
    rw [hdsq]
    refine ⟨by nlinarith [mul_self_nonneg (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b))], ?_⟩
    nlinarith [mul_nonneg (by linarith [hfx.1, hfx.2, htx.1, htx.2] :
        (0:ℤ) ≤ M - (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)))
      (by linarith [hfx.1, hfx.2, htx.1, htx.2] :
        (0:ℤ) ≤ M + (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b))), hwin]
  obtain ⟨hnb, hn1, hn0⟩ :=
    ge0_9N_of_sat hsat hc i hi (NGen.cIvDsq n o) (NGen.cIvNeq n o) (NGen.ivNeqBit n o 0)
      (hvo (vo_iv_neqIb n b o ob)) (fun k hk => hvo (vo_iv_neqBit n b o ob k hk))
      (hvo (vo_iv_neqHead n b o ob)) hbnd.1 hbnd.2
  rw [← he] at hnb hn1 hn0
  have hiv : e.loc (NGen.cIv n o) = 1 - e.loc (NGen.cIvNeq n o) := by
    have := eqPinN_of_sat hsat hc i hi (NGen.cIv n o) (NGen.cIvNeq n o) (hvo (vo_iv_eqPin n b o ob)) hnb
    rwa [← he] at this
  refine ⟨by rcases hnb with h | h <;> rw [hiv, h] <;> norm_num, ?_⟩
  constructor
  · intro h1
    have hn : e.loc (NGen.cIvNeq n o) = 0 := by omega
    have hle := hn0 hn
    rw [hdsq] at hle
    have hsq0 : (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b))
        * (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) = 0 :=
      le_antisymm hle (mul_self_nonneg _)
    have := mul_self_eq_zero.mp hsq0; linarith
  · intro heq
    have hz : e.loc (NGen.cIvDsq n o) = 0 := by rw [hdsq, heq]; ring
    have : e.loc (NGen.cIvNeq n o) = 0 := by
      rcases hnb with h | h
      · exact h
      · have := hn1 h; omega
    omega

/-! ### §D.8.4 — `eqCoordsN_of_sat`: an `eq_coords` pattern bit IS the coordinate-pair equality.

The `n`-generic twin of `eqCoords_of_sat` (§5). `sqdistN_pure` replaces the `{0,1}⁴` `sqdist_pure`;
the two sum-of-squares terms are split by non-negativity instead of enumeration. The 9-bit
`forced_ge0` window is `2·M² ≤ 999` (the 2-D squared distance). NON-VACUOUS at `n = 3`. -/
theorem eqCoordsN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (xa ya xb yb ec : Nat) (M : ℤ)
    (hwin : 2 * M * M ≤ 999)
    (bxa : 0 ≤ (envAt t i).loc xa ∧ (envAt t i).loc xa ≤ M)
    (bya : 0 ≤ (envAt t i).loc ya ∧ (envAt t i).loc ya ≤ M)
    (bxb : 0 ≤ (envAt t i).loc xb ∧ (envAt t i).loc xb ≤ M)
    (byb : 0 ≤ (envAt t i).loc yb ∧ (envAt t i).loc yb ≤ M)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.eqCoordsConstraints n xa ya xb yb ec
            → g ∈ (automataflResolveDescN n).constraints) :
    ((envAt t i).loc (NGen.cEqBit n ec) = 0 ∨ (envAt t i).loc (NGen.cEqBit n ec) = 1)
      ∧ ((envAt t i).loc (NGen.cEqBit n ec) = 1 ↔
          ((envAt t i).loc xa = (envAt t i).loc xb ∧ (envAt t i).loc ya = (envAt t i).loc yb)) := by
  set e := envAt t i with he
  have hdsq : e.loc (NGen.cEqDsq n ec)
      = (e.loc xa - e.loc xb) * (e.loc xa - e.loc xb)
        + (e.loc ya - e.loc yb) * (e.loc ya - e.loc yb) := by
    have hgm : cgH ((((((Head.lin 1 (NGen.cEqDsq n ec)).addProd (-1) [xa, xa]).addProd 2 [xa, xb]).addProd (-1)
          [xb, xb]).addProd (-1) [ya, ya]).addProd 2 [ya, yb] |>.addProd (-1) [yb, yb])
          ∈ (automataflResolveDescN n).constraints := by
      apply hlift; rw [NGen.eqCoordsConstraints]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton.mpr rfl))
    have hg := rgateHN hsat i hi hgm
    have hE : (headToExpr ((((((Head.lin 1 (NGen.cEqDsq n ec)).addProd (-1) [xa, xa]).addProd 2
          [xa, xb]).addProd (-1) [xb, xb]).addProd (-1) [ya, ya]).addProd 2 [ya, yb]
          |>.addProd (-1) [yb, yb])).eval e.loc
        = e.loc (NGen.cEqDsq n ec) + (-1) * (e.loc xa * e.loc xa) + 2 * (e.loc xa * e.loc xb)
          + (-1) * (e.loc xb * e.loc xb) + (-1) * (e.loc ya * e.loc ya)
          + 2 * (e.loc ya * e.loc yb) + (-1) * (e.loc yb * e.loc yb) := rfl
    rw [hE] at hg
    exact sqdistN_pure (canon_loc hc i _) bxa bxb bya byb (by nlinarith [hwin]) hg
  have hbnd : -999 ≤ e.loc (NGen.cEqDsq n ec) ∧ e.loc (NGen.cEqDsq n ec) ≤ 999 := by
    rw [hdsq]
    refine ⟨by nlinarith [mul_self_nonneg (e.loc xa - e.loc xb),
        mul_self_nonneg (e.loc ya - e.loc yb)], ?_⟩
    nlinarith [mul_nonneg (by linarith [bxa.1, bxa.2, bxb.1, bxb.2] :
        (0:ℤ) ≤ M - (e.loc xa - e.loc xb)) (by linarith [bxa.1, bxa.2, bxb.1, bxb.2] :
        (0:ℤ) ≤ M + (e.loc xa - e.loc xb)),
      mul_nonneg (by linarith [bya.1, bya.2, byb.1, byb.2] :
        (0:ℤ) ≤ M - (e.loc ya - e.loc yb)) (by linarith [bya.1, bya.2, byb.1, byb.2] :
        (0:ℤ) ≤ M + (e.loc ya - e.loc yb)), hwin]
  have gib : cg (gBin (NGen.cEqNeq n ec)) ∈ (automataflResolveDescN n).constraints := by
    apply hlift; rw [NGen.eqCoordsConstraints]
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_forcedGe0N_ib ((Head.lin 1 (NGen.cEqDsq n ec)).addConst (-1)) (NGen.cEqNeq n ec)
        (NGen.eqBitAt n ec 0) RBITS))
  have gbit : ∀ k, k < 9 → cg (gBin (NGen.eqBitAt n ec 0 + k)) ∈ (automataflResolveDescN n).constraints := by
    intro k hk
    apply hlift; rw [NGen.eqCoordsConstraints]
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_forcedGe0N_bit ((Head.lin 1 (NGen.cEqDsq n ec)).addConst (-1)) (NGen.cEqNeq n ec)
        (NGen.eqBitAt n ec 0) RBITS k hk))
  have ghead : cgH ((List.range 9).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (NGen.eqBitAt n ec 0 + k))
      (forcedGe0Term ((Head.lin 1 (NGen.cEqDsq n ec)).addConst (-1)) (NGen.cEqNeq n ec)))
      ∈ (automataflResolveDescN n).constraints := by
    apply hlift; rw [NGen.eqCoordsConstraints]
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_forcedGe0N_head ((Head.lin 1 (NGen.cEqDsq n ec)).addConst (-1)) (NGen.cEqNeq n ec)
        (NGen.eqBitAt n ec 0) RBITS))
  obtain ⟨hnb, hn1, hn0⟩ :=
    ge0_9N_of_sat hsat hc i hi (NGen.cEqDsq n ec) (NGen.cEqNeq n ec) (NGen.eqBitAt n ec 0)
      gib gbit ghead hbnd.1 hbnd.2
  rw [← he] at hnb hn1 hn0
  have hbit : e.loc (NGen.cEqBit n ec) = 1 - e.loc (NGen.cEqNeq n ec) := by
    have hep : cgH (((Head.lin 1 (NGen.cEqBit n ec)).addLin 1 (NGen.cEqNeq n ec)).addConst (-1))
        ∈ (automataflResolveDescN n).constraints := by
      apply hlift; rw [NGen.eqCoordsConstraints]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have := eqPinN_of_sat hsat hc i hi (NGen.cEqBit n ec) (NGen.cEqNeq n ec) hep hnb
    rwa [← he] at this
  refine ⟨by rcases hnb with h | h <;> rw [hbit, h] <;> norm_num, ?_⟩
  constructor
  · intro hone
    have hn : e.loc (NGen.cEqNeq n ec) = 0 := by omega
    have hle := hn0 hn
    rw [hdsq] at hle
    have hx0 : (e.loc xa - e.loc xb) * (e.loc xa - e.loc xb) = 0 :=
      le_antisymm (by nlinarith [mul_self_nonneg (e.loc ya - e.loc yb)]) (mul_self_nonneg _)
    have hy0 : (e.loc ya - e.loc yb) * (e.loc ya - e.loc yb) = 0 :=
      le_antisymm (by nlinarith [mul_self_nonneg (e.loc xa - e.loc xb)]) (mul_self_nonneg _)
    exact ⟨by have := mul_self_eq_zero.mp hx0; linarith,
           by have := mul_self_eq_zero.mp hy0; linarith⟩
  · rintro ⟨e1, e2⟩
    have hz : e.loc (NGen.cEqDsq n ec) = 0 := by rw [hdsq, e1, e2]; ring
    have : e.loc (NGen.cEqNeq n ec) = 0 := by
      rcases hnb with h | h
      · exact h
      · have := hn1 h; omega
    omega

/-! ### §D.8.5 — `validMoveN_of_sat`: `validate_move` ⇒ the reference `MoveValid`, at arbitrary `n`.

The flagship `n`-generic twin of `validMove_of_sat` (§2). `coordN_of_sat` pins the four move
coordinates into `[0, n)` (replacing `coord01_of_sat` / `interval_cases`), `autoPinN_of_sat` pins the
auto cell, `sqdistN_pure` replaces the `{0,1}⁴` `sqdist_pure`, and the rook-alignment product is
resolved through `eq_of_modEq_win`. Windows: `M ≤ 1000` (via `M² ≤ 1000000`, for the rook product and
the squared-distance no-wrap) and `2^(COORD_RBITS n + 1) ≤ p` (for the coordinate decode) — explicit
board-size inequalities, non-vacuous at `n = 3` (`M = 2`). -/

/-- The OLD board decoded at arbitrary size `n` (the `n`-generic `boardDecodeOld`). -/
def boardDecodeOldN (n : Nat) (e : VmRowEnv) : Board where
  size          := n
  automaton     := ⟨(e.loc (NGen.AX_C n)).toNat, (e.loc (NGen.AY_C n)).toNat⟩
  cells         := fun c => codeToParticle (e.loc (NGen.old n (c.y * n + c.x)))
  useColumnRule := true

/-- A move decoded at arbitrary size `n` (the `n`-generic `moveDecode`). -/
def moveDecodeN (n : Nat) (e : VmRowEnv) (which : Nat) : Move :=
  Move.mk 0
    ⟨(e.loc (NGen.cFx n (NGen.mvBase n which))).toNat, (e.loc (NGen.cFy n (NGen.mvBase n which))).toNat⟩
    ⟨(e.loc (NGen.cTx n (NGen.mvBase n which))).toNat, (e.loc (NGen.cTy n (NGen.mvBase n which))).toNat⟩

theorem validMoveN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (M : ℤ)
    (hn1 : 1 ≤ n) (hnlt : (n : ℤ) < 2013265921) (hM : M = (n : ℤ) - 1) (hwin : M * M ≤ 1000000)
    (hcw : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921)
    (hmv : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n (NGen.mvBase n which)
            → g ∈ (automataflResolveDescN n).constraints) :
    MoveValid (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) which) := by
  set e := envAt t i with he
  set b := NGen.mvBase n which with hbdef
  -- block embeds of the four coordinate `decompose_coord_le` blocks into `validate_move`
  have embFx : ∀ {g : VmConstraint2},
      g ∈ NGen.decomposeConstraints n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b)
        → g ∈ (automataflResolveDescN n).constraints := by
    intro g hg; apply hmv; rw [NGen.validateMove]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (hg)))))))))))))
  have embFy : ∀ {g : VmConstraint2},
      g ∈ NGen.decomposeConstraints n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b)
        → g ∈ (automataflResolveDescN n).constraints := by
    intro g hg; apply hmv; rw [NGen.validateMove]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hg)))))))))))))
  have embTx : ∀ {g : VmConstraint2},
      g ∈ NGen.decomposeConstraints n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b)
        → g ∈ (automataflResolveDescN n).constraints := by
    intro g hg; apply hmv; rw [NGen.validateMove]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hg))))))))))))
  have embTy : ∀ {g : VmConstraint2},
      g ∈ NGen.decomposeConstraints n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b)
        → g ∈ (automataflResolveDescN n).constraints := by
    intro g hg; apply hmv; rw [NGen.validateMove]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hg)))))))))))
  obtain ⟨X, hXlt, hfxE⟩ :=
    coordN_of_sat hsat hc i hi n (NGen.COORD_RBITS n) (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b)
      hn1 hnlt hcw
      (fun k hk => embFx (mem_decompose_loBit n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b) k hk))
      (embFx (mem_decompose_loHead n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b)))
      (fun k hk => embFx (mem_decompose_hiBit n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b) k hk))
      (embFx (mem_decompose_hiHead n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b)))
  obtain ⟨Y, hYlt, hfyE⟩ :=
    coordN_of_sat hsat hc i hi n (NGen.COORD_RBITS n) (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b)
      hn1 hnlt hcw
      (fun k hk => embFy (mem_decompose_loBit n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b) k hk))
      (embFy (mem_decompose_loHead n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b)))
      (fun k hk => embFy (mem_decompose_hiBit n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b) k hk))
      (embFy (mem_decompose_hiHead n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b)))
  obtain ⟨TX, hTXlt, htxE⟩ :=
    coordN_of_sat hsat hc i hi n (NGen.COORD_RBITS n) (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b)
      hn1 hnlt hcw
      (fun k hk => embTx (mem_decompose_loBit n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b) k hk))
      (embTx (mem_decompose_loHead n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b)))
      (fun k hk => embTx (mem_decompose_hiBit n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b) k hk))
      (embTx (mem_decompose_hiHead n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b)))
  obtain ⟨TY, hTYlt, htyE⟩ :=
    coordN_of_sat hsat hc i hi n (NGen.COORD_RBITS n) (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b)
      hn1 hnlt hcw
      (fun k hk => embTy (mem_decompose_loBit n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b) k hk))
      (embTy (mem_decompose_loHead n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b)))
      (fun k hk => embTy (mem_decompose_hiBit n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b) k hk))
      (embTy (mem_decompose_hiHead n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b)))
  obtain ⟨AX, AY, hAXlt, hAYlt, hAXe, hAYe, _⟩ := autoPinN_of_sat n hnlt hsat hc i hi
  rw [← he] at hfxE hfyE htxE htyE hAXe hAYe
  -- coordinate bounds in `[0, M]`
  have bfx : 0 ≤ e.loc (NGen.cFx n b) ∧ e.loc (NGen.cFx n b) ≤ M := by rw [hfxE, hM]; omega
  have bfy : 0 ≤ e.loc (NGen.cFy n b) ∧ e.loc (NGen.cFy n b) ≤ M := by rw [hfyE, hM]; omega
  have btx : 0 ≤ e.loc (NGen.cTx n b) ∧ e.loc (NGen.cTx n b) ≤ M := by rw [htxE, hM]; omega
  have bty : 0 ≤ e.loc (NGen.cTy n b) ∧ e.loc (NGen.cTy n b) ≤ M := by rw [htyE, hM]; omega
  have bax : 0 ≤ e.loc (NGen.AX_C n) ∧ e.loc (NGen.AX_C n) ≤ M := by rw [hAXe, hM]; omega
  have bay : 0 ≤ e.loc (NGen.AY_C n) ∧ e.loc (NGen.AY_C n) ≤ M := by rw [hAYe, hM]; omega
  -- toNat facts
  have hxn : (e.loc (NGen.cFx n b)).toNat = X := by rw [hfxE]; simp
  have hyn : (e.loc (NGen.cFy n b)).toNat = Y := by rw [hfyE]; simp
  have htxn : (e.loc (NGen.cTx n b)).toNat = TX := by rw [htxE]; simp
  have htyn : (e.loc (NGen.cTy n b)).toNat = TY := by rw [htyE]; simp
  -- rook alignment: (fx − tx)·(fy − ty) = 0
  have hd1sq : (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) * (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) ≤ M * M :=
    by nlinarith [mul_nonneg (by linarith [bfx.1, bfx.2, btx.1, btx.2] : (0:ℤ) ≤ M - (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b))) (by linarith [bfx.1, bfx.2, btx.1, btx.2] : (0:ℤ) ≤ M + (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)))]
  have hd2sq : (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)) * (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)) ≤ M * M :=
    by nlinarith [mul_nonneg (by linarith [bfy.1, bfy.2, bty.1, bty.2] : (0:ℤ) ≤ M - (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b))) (by linarith [bfy.1, bfy.2, bty.1, bty.2] : (0:ℤ) ≤ M + (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)))]
  have hrook : (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) * (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)) = 0 := by
    have hg := rgateHN hsat i hi (hmv (vm_rook n b))
    have hE : (headToExpr (NGen.rookAlignHead n b)).eval e.loc
        = e.loc (NGen.cFx n b) * e.loc (NGen.cFy n b) + (-1) * (e.loc (NGen.cFx n b) * e.loc (NGen.cTy n b))
          + (-1) * (e.loc (NGen.cTx n b) * e.loc (NGen.cFy n b)) + e.loc (NGen.cTx n b) * e.loc (NGen.cTy n b) := rfl
    rw [hE] at hg
    have hmod : (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) * (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b))
        ≡ 0 [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hg
    refine eq_of_modEq_win ⟨?_, ?_⟩ ⟨by norm_num, by norm_num⟩ hmod
    · nlinarith [hd1sq, hd2sq, hwin, mul_self_nonneg (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b) + (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)))]
    · nlinarith [hd1sq, hd2sq, hwin, mul_self_nonneg (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b) - (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)))]
  -- distinctness: dsq ≠ 0 ⇒ ¬(frm = to)
  have hdsqDef : e.loc (NGen.cDsq n b)
      = (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) * (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b))
        + (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)) * (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)) := by
    have hg := rgateHN hsat i hi (hmv (vm_dsqDef n b))
    have hE : (headToExpr (NGen.dsqHead n b)).eval e.loc
        = e.loc (NGen.cDsq n b) + (-1) * (e.loc (NGen.cFx n b) * e.loc (NGen.cFx n b))
          + 2 * (e.loc (NGen.cFx n b) * e.loc (NGen.cTx n b)) + (-1) * (e.loc (NGen.cTx n b) * e.loc (NGen.cTx n b))
          + (-1) * (e.loc (NGen.cFy n b) * e.loc (NGen.cFy n b)) + 2 * (e.loc (NGen.cFy n b) * e.loc (NGen.cTy n b))
          + (-1) * (e.loc (NGen.cTy n b) * e.loc (NGen.cTy n b)) := rfl
    rw [hE] at hg
    exact sqdistN_pure (canon_loc hc i _) bfx btx bfy bty (by nlinarith [hwin]) hg
  have hdnz : ¬ ((e.loc (NGen.cDsq n b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzeroN_of_sat hsat hc i hi (NGen.cDsq n b) (NGen.cDistinctInv n b) (hmv (vm_dsqNz n b))
    rwa [← he] at this
  have hdistinct : ¬ (e.loc (NGen.cFx n b) = e.loc (NGen.cTx n b) ∧ e.loc (NGen.cFy n b) = e.loc (NGen.cTy n b)) := by
    rintro ⟨h1, h2⟩; exact hdnz (by rw [hdsqDef, h1, h2]; simp [Int.ModEq])
  -- frm ≠ auto
  have hfaDef : e.loc (NGen.cFa n b)
      = (e.loc (NGen.cFx n b) - e.loc (NGen.AX_C n)) * (e.loc (NGen.cFx n b) - e.loc (NGen.AX_C n))
        + (e.loc (NGen.cFy n b) - e.loc (NGen.AY_C n)) * (e.loc (NGen.cFy n b) - e.loc (NGen.AY_C n)) := by
    have hg := rgateHN hsat i hi (hmv (vm_faDef n b))
    have hE : (headToExpr (NGen.autoDistHead n (NGen.cFa n b) (NGen.cFx n b) (NGen.cFy n b))).eval e.loc
        = e.loc (NGen.cFa n b) + (-1) * (e.loc (NGen.cFx n b) * e.loc (NGen.cFx n b))
          + 2 * (e.loc (NGen.cFx n b) * e.loc (NGen.AX_C n)) + (-1) * (e.loc (NGen.AX_C n) * e.loc (NGen.AX_C n))
          + (-1) * (e.loc (NGen.cFy n b) * e.loc (NGen.cFy n b)) + 2 * (e.loc (NGen.cFy n b) * e.loc (NGen.AY_C n))
          + (-1) * (e.loc (NGen.AY_C n) * e.loc (NGen.AY_C n)) := rfl
    rw [hE] at hg
    exact sqdistN_pure (canon_loc hc i _) bfx bax bfy bay (by nlinarith [hwin]) hg
  have hfanz : ¬ ((e.loc (NGen.cFa n b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzeroN_of_sat hsat hc i hi (NGen.cFa n b) (NGen.cFnaInv n b) (hmv (vm_faNz n b))
    rwa [← he] at this
  have hfnotauto : ¬ (e.loc (NGen.cFx n b) = e.loc (NGen.AX_C n) ∧ e.loc (NGen.cFy n b) = e.loc (NGen.AY_C n)) := by
    rintro ⟨h1, h2⟩; exact hfanz (by rw [hfaDef, h1, h2]; simp [Int.ModEq])
  -- to ≠ auto
  have htaDef : e.loc (NGen.cTa n b)
      = (e.loc (NGen.cTx n b) - e.loc (NGen.AX_C n)) * (e.loc (NGen.cTx n b) - e.loc (NGen.AX_C n))
        + (e.loc (NGen.cTy n b) - e.loc (NGen.AY_C n)) * (e.loc (NGen.cTy n b) - e.loc (NGen.AY_C n)) := by
    have hg := rgateHN hsat i hi (hmv (vm_taDef n b))
    have hE : (headToExpr (NGen.autoDistHead n (NGen.cTa n b) (NGen.cTx n b) (NGen.cTy n b))).eval e.loc
        = e.loc (NGen.cTa n b) + (-1) * (e.loc (NGen.cTx n b) * e.loc (NGen.cTx n b))
          + 2 * (e.loc (NGen.cTx n b) * e.loc (NGen.AX_C n)) + (-1) * (e.loc (NGen.AX_C n) * e.loc (NGen.AX_C n))
          + (-1) * (e.loc (NGen.cTy n b) * e.loc (NGen.cTy n b)) + 2 * (e.loc (NGen.cTy n b) * e.loc (NGen.AY_C n))
          + (-1) * (e.loc (NGen.AY_C n) * e.loc (NGen.AY_C n)) := rfl
    rw [hE] at hg
    exact sqdistN_pure (canon_loc hc i _) btx bax bty bay (by nlinarith [hwin]) hg
  have htanz : ¬ ((e.loc (NGen.cTa n b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzeroN_of_sat hsat hc i hi (NGen.cTa n b) (NGen.cTnaInv n b) (hmv (vm_taNz n b))
    rwa [← he] at this
  have htnotauto : ¬ (e.loc (NGen.cTx n b) = e.loc (NGen.AX_C n) ∧ e.loc (NGen.cTy n b) = e.loc (NGen.AY_C n)) := by
    rintro ⟨h1, h2⟩; exact htanz (by rw [htaDef, h1, h2]; simp [Int.ModEq])
  -- assemble `MoveValid`
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro hEq
    simp only [moveDecodeN, ← hbdef, Coord.mk.injEq] at hEq
    obtain ⟨q1, q2⟩ := hEq
    exact hdistinct ⟨by omega, by omega⟩
  · rcases mul_eq_zero.mp hrook with h | h
    · left; simp only [moveDecodeN, ← hbdef]; omega
    · right; simp only [moveDecodeN, ← hbdef]; omega
  · show (moveDecodeN n e which).frm.x < (boardDecodeOldN n e).size
    simp only [moveDecodeN, ← hbdef, boardDecodeOldN]; rw [hxn]; exact hXlt
  · show (moveDecodeN n e which).frm.y < (boardDecodeOldN n e).size
    simp only [moveDecodeN, ← hbdef, boardDecodeOldN]; rw [hyn]; exact hYlt
  · show (moveDecodeN n e which).to.x < (boardDecodeOldN n e).size
    simp only [moveDecodeN, ← hbdef, boardDecodeOldN]; rw [htxn]; exact hTXlt
  · show (moveDecodeN n e which).to.y < (boardDecodeOldN n e).size
    simp only [moveDecodeN, ← hbdef, boardDecodeOldN]; rw [htyn]; exact hTYlt
  · intro hEq
    simp only [Board.isAutomaton, boardDecodeOldN, moveDecodeN, ← hbdef, Coord.mk.injEq] at hEq
    obtain ⟨q1, q2⟩ := hEq
    exact hfnotauto ⟨by omega, by omega⟩
  · intro hEq
    simp only [Board.isAutomaton, boardDecodeOldN, moveDecodeN, ← hbdef, Coord.mk.injEq] at hEq
    obtain ⟨q1, q2⟩ := hEq
    exact htnotauto ⟨by omega, by omega⟩
  · simp [Board.isConflict, boardDecodeOldN]
  · simp [Board.isConflict, boardDecodeOldN]

/-! ### §D.8.5b — LEGALITY re-pointed to the VALIDATED spec (`AutomataflRules.MoveLegal`).

The migration re-targets move-legality from the OLD `Automatafl.MoveValid` to
`AutomataflRules.MoveLegal`. Two clauses change (design Δ2):

* **the automaton square is banned as a SOURCE ONLY.** `MoveLegal` drops the `¬ isAutomaton to`
  gate — naming the automaton as a DESTINATION is legal to propose and simply fails to execute (the
  occupied square blocks the inclusive path, §5b). The emitted `validate_move` still PROVES
  `¬ isAutomaton to` today, so `MoveLegal` follows as a WEAKENING of `MoveValid` on that clause; the
  gate-drop itself is a later descriptor re-emit.
* **marks-membership.** `MoveValid`'s `¬ isConflict frm ∧ ¬ isConflict to` (which read
  `Board.conflictAt`, never set in the OLD tree) becomes `frm ∉ marks ∧ to ∉ marks` against the
  round's committed marker set. The current descriptor has NO marks columns, so this is supplied as
  a HYPOTHESIS (`hfrm`/`hto`) — the labelled round-composition seam Phase 3 discharges from the marks
  PI commitment. On the opening round `marks = []`, so it is vacuous and `moveLegalN_of_sat`
  discharges it outright.

Fork/collide (`AutomataflRules.forkAt`/`collideAt`) are the SAME predicates as the old
`frmConflict`/`toConflict` — already proven equal to the `d3` selection truth table in
`AutomataflAir.conflictResolve_pair` — so the conflict-detection leg re-points by rename, not
re-proof. -/

/-- **`validate_move` ⇒ `AutomataflRules.MoveLegal`, general marker set.** Everything but
marks-membership comes from the emitted `validate_move` (via `validMoveN_of_sat`); the
`frm ∉ marks`/`to ∉ marks` clauses are the Phase-3 round-composition seam, supplied here as
hypotheses. -/
theorem moveLegalN_of_sat_marks (marks : List Coord)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (M : ℤ)
    (hn1 : 1 ≤ n) (hnlt : (n : ℤ) < 2013265921) (hM : M = (n : ℤ) - 1) (hwin : M * M ≤ 1000000)
    (hcw : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921)
    (hmv : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n (NGen.mvBase n which)
            → g ∈ (automataflResolveDescN n).constraints)
    (hfrm : (moveDecodeN n (envAt t i) which).frm ∉ marks)
    (hto : (moveDecodeN n (envAt t i) which).to ∉ marks) :
    Dregg2.Games.AutomataflRules.MoveLegal (boardDecodeOldN n (envAt t i)) marks
      (moveDecodeN n (envAt t i) which) := by
  obtain ⟨hne, hrook, hinF, hinT, hautoF, _hautoT, _hcfF, _hcfT⟩ :=
    validMoveN_of_sat hsat hc i hi which M hn1 hnlt hM hwin hcw hmv
  exact ⟨hne, hrook, hinF, hinT, hautoF, hfrm, hto⟩

/-- **`validate_move` ⇒ `AutomataflRules.MoveLegal` on the OPENING round** (`marks = []`), where the
marks clause is vacuous. This is the round-1 legality the migrated Leg S/C consumes directly. -/
theorem moveLegalN_of_sat
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (M : ℤ)
    (hn1 : 1 ≤ n) (hnlt : (n : ℤ) < 2013265921) (hM : M = (n : ℤ) - 1) (hwin : M * M ≤ 1000000)
    (hcw : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921)
    (hmv : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n (NGen.mvBase n which)
            → g ∈ (automataflResolveDescN n).constraints) :
    Dregg2.Games.AutomataflRules.MoveLegal (boardDecodeOldN n (envAt t i)) []
      (moveDecodeN n (envAt t i) which) :=
  moveLegalN_of_sat_marks [] hsat hc i hi which M hn1 hnlt hM hwin hcw hmv
    (by simp) (by simp)

/-! ### §D.8.6 — `srcNonVacN_of_sat`: the source-non-vacuum bit IS the reference predicate.

The `n`-generic twin of `srcNonVac_of_sat` (§5), off `sourceReadN_of_sat` (the witnessed source read)
and `ge0_5N_of_sat` (the 5-bit non-vacuum threshold), with the particle-alphabet envelope re-derived
`n`-generically at the read cell from the emitted `assert_member` gate (DEFECT #4's fix, `n`-generic
via `br_old`). The `anz` gate memberships are supplied raw (as in `ge0_5N`), anchored to
`automataflResolveDescN n`. No board-size window needed — the source felt is alphabet-bounded. -/
theorem srcNonVacN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which ib bit0 : Nat)
    (hnlt : (n : ℤ) < 2013265921)
    (hmv : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n (NGen.mvBase n which)
            → g ∈ (automataflResolveDescN n).constraints)
    (hib : cg (gBin ib) ∈ (automataflResolveDescN n).constraints)
    (hbit : ∀ k, k < 5 → cg (gBin (bit0 + k)) ∈ (automataflResolveDescN n).constraints)
    (hrec : cgH ((List.range 5).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
                 (forcedGe0Term ((Head.lin 1 (NGen.cFp n (NGen.mvBase n which))).addConst (-1)) ib))
             ∈ (automataflResolveDescN n).constraints) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 ↔
          ((boardDecodeOldN n (envAt t i)).cellAt (moveDecodeN n (envAt t i) which).frm).isVacuum
            = false) := by
  set e := envAt t i with he
  set b := NGen.mvBase n which with hbdef
  obtain ⟨X, Y, hX, hY, hfxE, hfyE, hfp⟩ := sourceReadN_of_sat hsat hc i hi b hnlt hmv
  rw [← he] at hfxE hfyE hfp
  have hXY : Y * n + X < NGen.KK n := by
    simp only [NGen.KK]
    have hle : (Y + 1) * n ≤ n * n := mul_le_mul_right' (by omega : Y + 1 ≤ n) n
    have hexp : (Y + 1) * n = Y * n + n := by ring
    omega
  have hcellAlpha : e.loc (NGen.old n (Y * n + X)) = 0 ∨ e.loc (NGen.old n (Y * n + X)) = 1
      ∨ e.loc (NGen.old n (Y * n + X)) = 2 ∨ e.loc (NGen.old n (Y * n + X)) = 3 :=
    AutomataflStepRefine.mem4_of_gate
      (rgateN hsat i hi (mem_resolve_of_mem_boardRange (br_old n (Y * n + X) hXY)))
      (canon_loc hc i _)
  have hfpv : e.loc (NGen.cFp n b) = 0 ∨ e.loc (NGen.cFp n b) = 1
      ∨ e.loc (NGen.cFp n b) = 2 ∨ e.loc (NGen.cFp n b) = 3 := by rw [hfp]; exact hcellAlpha
  have hbnd : -99 ≤ e.loc (NGen.cFp n b) ∧ e.loc (NGen.cFp n b) ≤ 99 := by
    rcases hfpv with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  obtain ⟨hb, h1, h0⟩ :=
    ge0_5N_of_sat hsat hc i hi (NGen.cFp n b) ib bit0 hib hbit hrec hbnd.1 hbnd.2
  rw [← he] at hb h1 h0
  have hcell : (boardDecodeOldN n e).cellAt (moveDecodeN n e which).frm
      = codeToParticle (e.loc (NGen.cFp n b)) := by
    have hxn : (e.loc (NGen.cFx n b)).toNat = X := by rw [hfxE]; simp
    have hyn : (e.loc (NGen.cFy n b)).toNat = Y := by rw [hfyE]; simp
    simp only [Board.cellAt, boardDecodeOldN, moveDecodeN, ← hbdef]
    rw [hxn, hyn, if_pos ⟨hX, hY⟩, hfp]
  rw [hcell]
  refine ⟨hb, ?_⟩
  rcases hfpv with hv | hv | hv | hv <;> rw [hv] at h1 h0 ⊢ <;>
    norm_num [codeToParticle, Particle.isVacuum] <;>
    (first
      | (intro hone; have := h1 hone; omega)
      | (rcases hb with hz | ho
         · exact absurd (h0 hz) (by norm_num)
         · exact ho))

#print axioms oneN_of_sat
#print axioms condNonzeroN_of_sat
#print axioms eqPinN_of_sat
#print axioms ge0_9N_of_sat
#print axioms ge0_5N_of_sat
#print axioms sqdistN_pure
#print axioms sq1dN_pure
#print axioms sourceReadN_of_sat
#print axioms ivN_of_sat
#print axioms eqCoordsN_of_sat
#print axioms validMoveN_of_sat
#print axioms moveLegalN_of_sat_marks
#print axioms moveLegalN_of_sat
#print axioms srcNonVacN_of_sat

end CoordExtractN

/-! ## §E — TWO-SIDED CANARIES for the assembly's reference side (`resolveMid` at `n = 2`).

Each verdict the capstone routes through is exercised in BOTH polarities on a concrete 2×2 board
(automaton parked off-board so no endpoint is the auto cell), so none of the four `applyMoves_cell_*`
shapes nor the fork/collide/survive branch is vacuously reachable. -/

open Dregg2.Games.Automatafl (mkBoard) in
/-- A 2×2 board with an attractor at `(0,0)`, everything else vacuum. -/
def canonBoardA : Board := mkBoard 2 [(⟨0, 0⟩, Particle.attractor)] ⟨9, 9⟩

open Dregg2.Games.Automatafl (mkBoard) in
/-- The same, plus a repulsor at `(1,1)`. -/
def canonBoardAB : Board :=
  mkBoard 2 [(⟨0, 0⟩, Particle.attractor), (⟨1, 1⟩, Particle.repulsor)] ⟨9, 9⟩

def cmA : Move := Move.mk 0 ⟨0, 0⟩ ⟨0, 1⟩   -- the carrying move
def cmB : Move := Move.mk 1 ⟨1, 0⟩ ⟨1, 1⟩   -- a vacuum-source move
def cmFork : Move := Move.mk 1 ⟨0, 0⟩ ⟨1, 0⟩ -- SAME source, other dest
def cmColl : Move := Move.mk 1 ⟨1, 1⟩ ⟨0, 1⟩ -- SAME dest as `cmA`
def cmChain : Move := Move.mk 1 ⟨0, 1⟩ ⟨1, 1⟩ -- the caterpillar edge

-- SURVIVE (distinct sources, distinct destinations): the piece really moves…
#guard (resolveMid canonBoardA [cmA, cmB]).cellAt ⟨0, 1⟩ = Particle.attractor
#guard (resolveMid canonBoardA [cmA, cmB]).cellAt ⟨0, 0⟩ = Particle.vacuum
-- …and the FORK verdict (same source, two destinations) drops BOTH moves: the piece stays.
#guard (resolveMid canonBoardA [cmA, cmFork]).cellAt ⟨0, 0⟩ = Particle.attractor
#guard (resolveMid canonBoardA [cmA, cmFork]).cellAt ⟨0, 1⟩ = Particle.vacuum

-- COLLIDE (same destination, two CARRYING sources): both dropped, both pieces stay…
#guard (resolveMid canonBoardAB [cmA, cmColl]).cellAt ⟨0, 0⟩ = Particle.attractor
#guard (resolveMid canonBoardAB [cmA, cmColl]).cellAt ⟨1, 1⟩ = Particle.repulsor
#guard (resolveMid canonBoardAB [cmA, cmColl]).cellAt ⟨0, 1⟩ = Particle.vacuum
-- …but with the SECOND source vacuum it is NOT a collision, and A lands.
#guard (resolveMid canonBoardA [cmA, cmColl]).cellAt ⟨0, 1⟩ = Particle.attractor
#guard (resolveMid canonBoardA [cmA, cmColl]).cellAt ⟨0, 0⟩ = Particle.vacuum

-- CATERPILLAR: the vacating square is ridden THROUGH to `(1,1)`…
#guard (resolveMid canonBoardA [cmA, cmChain]).cellAt ⟨1, 1⟩ = Particle.attractor
#guard (resolveMid canonBoardA [cmA, cmChain]).cellAt ⟨0, 1⟩ = Particle.vacuum
-- …whereas when `(0,1)` itself CARRIES a piece the chain STOPS there (no flow-through).
#guard (resolveMid canonBoardAB [cmA, cmColl]).cellAt ⟨0, 1⟩ = Particle.vacuum

/-! ## §7 — NON-VACUITY canaries: the gates BITE.

Each canary evaluates the ACTUAL emitted gate polynomial on a good assignment (`== 0`, satisfied)
and on a forged one (`!= 0`, rejected). Two-sided, so none of the above is a vacuous implication. -/

/-- The auto pin: a board that does NOT hold AUTO at the witnessed one-hot index has no witness. -/
def canonAutoGood : Assignment := fun c =>
  if c = old 0 then 3 else if c = selAutoRow 0 ∨ c = selAutoCol 0 then 1 else 0
def canonAutoForge : Assignment := fun c =>
  if c = selAutoRow 0 ∨ c = selAutoCol 0 then 1 else 0

#guard (headToExpr autoPinHead).eval canonAutoGood == 0    -- AUTO really at (0,0): gate holds
#guard (headToExpr autoPinHead).eval canonAutoForge != 0   -- forged empty cell: gate FAILS

/-- The distinctness `cond_nonzero`: a move with `frm == to` (so `dsq = 0`) has NO inverse witness,
whatever the prover picks for `distinct_inv`. -/
def canonDistinctExpr : EmittedExpr := gCondNonzero ONE (cDsq (mvBase 0)) (cDistinctInv (mvBase 0))
def canonDistGood : Assignment := fun c =>
  if c = ONE ∨ c = cDsq (mvBase 0) ∨ c = cDistinctInv (mvBase 0) then 1 else 0
def canonDistForge : Assignment := fun c =>
  if c = ONE ∨ c = cDistinctInv (mvBase 0) then 1 else 0   -- dsq = 0: the degenerate "move"

#guard canonDistinctExpr.eval canonDistGood == 0     -- dsq = 1, inv = 1: satisfied
#guard canonDistinctExpr.eval canonDistForge != 0    -- dsq = 0 (frm == to): NO witness, REJECTED

/-- The `write_mid_witnessed` cell gate: a forged MID cell (a "dropped move" lie, or any rewrite
that does not match `resolve_mid`) fails the per-cell equality. Here both carries are `0`, so the
gate degenerates to `mid[0] == old[0]`: the board must be UNCHANGED when nothing journeys. -/
def canonMidExpr : EmittedExpr := headToExpr (writeCellHead 0)
def canonMidGood : Assignment := fun c => if c = old 0 ∨ c = mid 0 then 2 else 0
def canonMidForge : Assignment := fun c => if c = old 0 then 2 else 0  -- mid[0] forged to VACUUM

#guard canonMidExpr.eval canonMidGood == 0     -- no carry: mid == old, gate holds
#guard canonMidExpr.eval canonMidForge != 0    -- forged mid (piece silently deleted): REJECTED

/-- The `surv` inclusion–exclusion gate: claiming SURVIVAL while a fork is detected fails. -/
def canonSurvExpr : EmittedExpr :=
  headToExpr (((((Head.lin 1 cSurv).addConst (-1)).addLin 1 cFork).addLin 1 cCollide).addProd (-1)
    [cFork, cCollide])
def canonSurvGood : Assignment := fun c => if c = cSurv then 1 else 0
def canonSurvForge : Assignment := fun c => if c = cSurv ∨ c = cFork then 1 else 0

#guard canonSurvExpr.eval canonSurvGood == 0    -- no fork, no collide, surv = 1: consistent
#guard canonSurvExpr.eval canonSurvForge != 0   -- fork = 1 but surv = 1 claimed: REJECTED

/-- The occlusion `seg` gate at `n = 2`: the strictly-between mask is FORCED to zero, so a prover
cannot manufacture an interior blocker to fake an occlusion. -/
def canonSegExpr : EmittedExpr := headToExpr (segHead (occBase 0) 0)
def canonSegGood : Assignment := fun _ => 0
def canonSegForge : Assignment := fun c => if c = cSeg (occBase 0) 0 then 1 else 0

#guard canonSegExpr.eval canonSegGood == 0     -- seg = 0: the only satisfying value
#guard canonSegExpr.eval canonSegForge != 0    -- forged interior cell: REJECTED

/-- **THE DEFECT-#4 CANARY.** The newly emitted board-cell alphabet gate REJECTS exactly the witness
that broke the capstone: `old[0] = 4`, which the circuit's `anz = forced_ge0(fp − 1, 5)` would have
read as "carries a piece" while `codeToParticle 4 = .vacuum` reads it as empty. Two-sided: an
in-alphabet cell passes, the out-of-alphabet cell that made the refinement FALSE does not. -/
def canonAlphaExpr : EmittedExpr := memberExpr (old 0) [0, 1, 2, 3]
def canonAlphaGood : Assignment := fun c => if c = old 0 then 2 else 0   -- ATTRACTOR: legal
def canonAlphaForge : Assignment := fun c => if c = old 0 then 4 else 0  -- the DEFECT witness

#guard canonAlphaExpr.eval canonAlphaGood == 0    -- in-alphabet cell: ACCEPTED
#guard canonAlphaExpr.eval canonAlphaForge != 0   -- `old[0] = 4`: REJECTED (was accepted before)
#guard (memberExpr (mid 0) [0, 1, 2, 3]).eval (fun c => if c = mid 0 then 4 else 0) != 0
#guard cg (memberExpr (old 0) [0,1,2,3]) ∈ automataflResolveDesc.constraints
#guard cg (memberExpr (mid 3) [0,1,2,3]) ∈ automataflResolveDesc.constraints

/-- **THE CARRY CANARY.** The carry gate `carry == sa1·(1 − occ)` REJECTS a prover who claims the
piece journeyed while its line was occluded: with `sa1 = 1` and `occ = 1` the only satisfying carry
is `0`, so the forged `carry = 1` fails. -/
def canonCarryExpr : EmittedExpr :=
  headToExpr (((Head.lin 1 cCarryA).addProd (-1) [cSa1]).addProd 1 [cSa1, cOcc (occBase 0)])
def canonCarryGood : Assignment := fun c => if c = cSa1 ∨ c = cCarryA then 1 else 0
def canonCarryForge : Assignment := fun c =>
  if c = cSa1 ∨ c = cCarryA ∨ c = cOcc (occBase 0) then 1 else 0

#guard canonCarryExpr.eval canonCarryGood == 0     -- clear line, source carries: carry = 1 holds
#guard canonCarryExpr.eval canonCarryForge != 0    -- occluded but carry claimed: REJECTED

/-- **THE FLOW-THROUGH CANARY.** `ft` rides `not_bit(bnz)`: a prover who wants the chain bonus must
claim the square ahead is VACATING. Claiming `¬bnz` while `bnz = 1` fails the pin, so a piece can
never flow through a square that still holds a piece. -/
def canonFtExpr : EmittedExpr := headToExpr (((Head.lin 1 cNBnz).addLin 1 cBnz).addConst (-1))
def canonFtGood : Assignment := fun c => if c = cNBnz then 1 else 0
def canonFtForge : Assignment := fun c => if c = cNBnz ∨ c = cBnz then 1 else 0

#guard canonFtExpr.eval canonFtGood == 0     -- bnz = 0, nBnz = 1: the honest vacating square
#guard canonFtExpr.eval canonFtForge != 0    -- bnz = 1 with nBnz = 1 claimed: REJECTED

/-- **THE DESTINATION-ONE-HOT CANARY.** The landing selector is pinned to the INTERPOLATED
destination `to_own + ft·(to_other − to_own)`. With `ft = 0` and `ty_a = 1` the only satisfying
selector is `1`: a prover cannot land the piece on a square the `ft` bit did not select. -/
def canonDstExpr : EmittedExpr :=
  headToExpr (((Head.lin 0 (wDstRow 0 0)).addLin 1 (wDstRow 0 1)).append
    ((destHead (cTy (mvBase 0)) (cTy (mvBase 1)) cFtA).scale (-1)))
def canonDstGood : Assignment := fun c =>
  if c = wDstRow 0 1 ∨ c = cTy (mvBase 0) then 1 else 0
def canonDstForge : Assignment := fun c => if c = cTy (mvBase 0) then 1 else 0

#guard canonDstExpr.eval canonDstGood == 0     -- ft = 0: the piece lands on its OWN `to`
#guard canonDstExpr.eval canonDstForge != 0    -- landing square forged away from `to`: REJECTED

/-- **THE DEFECT-#5 CANARY, POLARITY FLIPPED (the completeness fix, witnessed).** On the
identical-move turn (`frm_a = frm_b`, both carrying) the emitted cell gate USED TO subtract the
source particle twice, so the only satisfying `mid` at the shared source was `−old` — out of the
particle alphabet for every non-vacuum source, i.e. NO witness on a legal turn.

With the inclusion–exclusion overlap terms the shared source vacates ONCE: the honest `mid = 0`
now satisfies BOTH the cell gate and the alphabet gate. Two-sided, in both directions:

* GOOD — `mid[0] = 0` (vacated once): cell gate `== 0` AND alphabet gate `== 0`. The turn the
  descriptor previously could not prove is now PROVABLE.
* FORGE (i) — the OLD forced value `mid[0] = −1` is now REJECTED by the cell gate (so the fix did
  not merely widen the gate: it MOVED the pinned value).
* FORGE (ii) — `mid[0] = 1` (the source not vacated at all) is REJECTED: soundness intact, the
  cell is still pinned to exactly one value. -/
def canonDoubleBase : Assignment := fun c =>
  if c = old 0 ∨ c = particleCol 0 ∨ c = particleCol 1 then 1
  else if c = carryCol 0 ∨ c = carryCol 1 ∨ c = wSrcRow 0 0 ∨ c = wSrcCol 0 0
       ∨ c = wSrcRow 1 0 ∨ c = wSrcCol 1 0 then 1
  else 0
def canonDoubleGood : Assignment := fun c => if c = mid 0 then 0 else canonDoubleBase c
def canonDoubleForgeNeg : Assignment := fun c => if c = mid 0 then -1 else canonDoubleBase c
def canonDoubleForgeKeep : Assignment := fun c => if c = mid 0 then 1 else canonDoubleBase c

#guard (headToExpr (writeCellHead 0)).eval canonDoubleGood == 0       -- vacated ONCE: SATISFIED
#guard (memberExpr (mid 0) [0, 1, 2, 3]).eval canonDoubleGood == 0    -- and 0 IS a particle code
#guard (headToExpr (writeCellHead 0)).eval canonDoubleForgeNeg != 0   -- the OLD forced −old: GONE
#guard (headToExpr (writeCellHead 0)).eval canonDoubleForgeKeep != 0  -- source not vacated: REJECTED

/-- **THE SHARED-LANDING CANARY.** The other half of the inclusion–exclusion: both pieces landing on
the SAME square (the identical move's destination) deposits exactly ONE particle, not two. -/
def canonLandBase : Assignment := fun c =>
  if c = particleCol 0 ∨ c = particleCol 1 then 2
  else if c = carryCol 0 ∨ c = carryCol 1 ∨ c = wDstRow 0 0 ∨ c = wDstCol 0 0
       ∨ c = wDstRow 1 0 ∨ c = wDstCol 1 0 then 1
  else 0
def canonLandGood : Assignment := fun c => if c = mid 0 then 2 else canonLandBase c
def canonLandForge : Assignment := fun c => if c = mid 0 then 4 else canonLandBase c

#guard (headToExpr (writeCellHead 0)).eval canonLandGood == 0    -- ONE particle lands: SATISFIED
#guard (headToExpr (writeCellHead 0)).eval canonLandForge != 0   -- doubled deposit: REJECTED

/-! ## §8 — Axiom hygiene. Every exported theorem, kernel-clean. -/

#print axioms rgate
#print axioms rgateH
#print axioms oneHot_of_sat
#print axioms one_of_sat
#print axioms condNonzero_of_sat
#print axioms autoPinR_of_sat
#print axioms decodedOld_auto_holds_automaton
#print axioms moveGates_a
#print axioms moveGates_b
#print axioms coord01_of_sat
#print axioms sqdist_pure
#print axioms validMove_of_sat
#print axioms sourceRead_of_sat
#print axioms forcedGe0_wide
#print axioms ge0_9_of_sat
#print axioms eqPin_of_sat
#print axioms sq1d_pure
#print axioms ivGates_a
#print axioms ivGates_b
#print axioms occGates_a
#print axioms occGates_b
#print axioms iv_of_sat
#print axioms occ_of_sat
#print axioms interior_nil_n2
#print axioms occluded_false_n2
#print axioms ge0_5_of_sat
#print axioms eqCoords_of_sat
#print axioms selection_of_sat
#print axioms srcNonVac_of_sat
#print axioms eqGates_ff
#print axioms eqGates_tt
#print axioms eqGates_ab
#print axioms eqGates_ba
#print axioms anzGates
#print axioms bnzGates
#print axioms boardvalid_of_sat
#print axioms frmConflict_pair
#print axioms toConflict_pair
#print axioms conflictResolve_pair
#print axioms nextOf_pair
#print axioms followChain_own
#print axioms followChain_own_landing
#print axioms followChain_flowThrough
#print axioms followChain_twoCycle
#print axioms chainDest_a
#print axioms followChain_ownB
#print axioms followChain_own_landingB
#print axioms followChain_flowThroughB
#print axioms followChain_twoCycleB
#print axioms chainDest_b
#print axioms prod_of_sat
#print axioms notBit_of_sat
#print axioms carry_of_sat
#print axioms ft_of_sat
#print axioms carryA_of_sat
#print axioms carryB_of_sat
#print axioms ftA_of_sat
#print axioms ftB_of_sat
#print axioms dstOneHot_of_sat
#print axioms writeCell_of_sat
#print axioms sharedSourceVacatesOnce
#print axioms cellAlgebra
#print axioms oneHotPair_indicator
#print axioms srcIndicator_of_sat
#print axioms dstIndicator_of_sat

end Dregg2.Circuit.Emit.AutomataflResolveRefine
