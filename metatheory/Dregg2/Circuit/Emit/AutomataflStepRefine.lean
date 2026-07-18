/-
# Dregg2.Circuit.Emit.AutomataflStepRefine — STAGE 2: the SAT⇒SEM refinement of the
byte-pinned automaton-step descriptor (`AutomataflStepEmit.automataflStepDesc`,
`dregg-automatafl-step-d1-n2`) against the pure reference transition
(`Dregg2.Games.Automatafl.automatonStep`).

## What this file IS (and what it deliberately is NOT — the honest partial)

`AutomataflStepEmit.lean` closed Law #1 (the descriptor is authored in Lean and byte-pinned by an
`emitVmJson2` `#guard`); `Automatafl.lean` STATED the refinement obligation
(`automatafl_air_refines_applyTurn`) against an ABSTRACT `BoardTransitionAIR`. This file replaces the
abstract obligation with a REAL theorem over the EMITTED object: a satisfying witness to the emitted
constraints, canonical over BabyBear, is shown to force the reference machine's reads. It is keyed on
`Satisfied2 hash automataflStepDesc` — the deployed acceptance predicate — exactly as
`DyckStackRefine.dyck_sat_imp_row_valid` is keyed on the byte-pinned `dyckParseDesc`.

The single automaton-step gate set is enormous (410 constraints: the front-end ray-scan, the
`decide_axis` truth table ×2, `choose_offset`, the step + board-update, the two `board_root8`
lookups). The full composition `boardDecode(new) = automatonStep(boardDecode(old))` decomposes into
the five design sub-lemmas (`Automatafl.lean` §3):

  (1) auto one-hot + dot-product pin   ⇒ the decoded auto position holds the AUTO particle;
  (2) the ray-scan gates              ⇒ each ray's `(dist,what)` is the true `raycastFuel`;
  (3) the `decide_axis` 9-case gates  ⇒ per-axis `Decision = evaluateAxis`;
  (4) the `choose_offset` gates       ⇒ the chosen offset `= chooseOffset`;
  (5) the step + board-update gates   ⇒ `new = old` with the auto moved by that offset.

**This file lands sub-lemma (1) IN FULL, plus the two "envelope" facts (2)-(4) rest on** — the
in-bounds decode of the auto coordinate (`coord_of_sat`) and the cardinal-offset membership
(`offset_of_sat`, the circuit-side analogue of `automatonOffset_bounded`) — all DERIVED from the
constraints, none assumed. The heavier soundness legs (2), (3), (5) are the NAMED residual (§7): they
require modelling `raycastFuel`/`evaluateAxis`/the board-update fold against the ray/decide/step
columns, a multi-file effort. Nothing here assumes them, and nothing is a vacuous `P → P`: the
top-level composition is NOT stated as a proven theorem — only the sub-lemmas that close are.

## The field denotation (mod-`p`, `p = 2013265921`) and the single-row model

The descriptor is a SINGLE-ROW AIR (per-row gates, no window constraints). As in
`NoteSpendingLeafRefine`, `Satisfied2`'s `.gate` denotation is vacuous on the LAST row (the
`when_transition` guard), so the extraction runs on row `i` with `i + 1 < t.rows.length` (row 0 with a
padding successor) where `isLast = false` binds every gate to its body congruence. Gates vanish
`≡ 0 [ZMOD p]`; the ℤ conclusions are recovered from the deployed range-check canonicality
(`StepCanon`), inhabited concretely by the §6 witness.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Membership into the fold-generated
constraint list is discharged by `decide` over LOCALLY-derived `DecidableEq` instances (computable, no
axioms). NEW file; imports read-only save the `Dregg2.lean` root add.
-/
import Dregg2.Circuit.Emit.AutomataflStepEmit
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Games.Automatafl

namespace Dregg2.Circuit.Emit.AutomataflStepRefine

open Dregg2.Circuit.Emit.AutomataflStepEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Games.Automatafl (Board Coord Particle)

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §0 — `DecidableEq` for the constraint carriers (membership by `decide`).

The constraint list is FOLD-generated (`frontEndConstraints ++ backEndConstraints`), so the literal
head/tail walk used for `DyckStackRefine`'s hand-written list does not apply. Instead we derive the
structural `DecidableEq` and let `decide` reduce the concrete list and short-circuit at the match.
These instances are computable — they add no axioms to the proofs that consume them. -/

deriving instance DecidableEq for EmittedExpr
deriving instance DecidableEq for Lookup
deriving instance DecidableEq for MemOp
deriving instance DecidableEq for MapOp
deriving instance DecidableEq for UMemOp
deriving instance DecidableEq for ProofBind
deriving instance DecidableEq for VmConstraint
deriving instance DecidableEq for WindowExpr
deriving instance DecidableEq for WindowConstraint
deriving instance DecidableEq for VmConstraint2

/-! ## §1 — Field-denotation glue (identical in shape to `DyckStackRefine` §0). -/

/-- The deployed range-check invariant on a stored field cell: it is the canonical residue. -/
def Canon (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

theorem canon_zero : Canon 0 := ⟨le_refl 0, by norm_num⟩
theorem canon_three : Canon 3 := ⟨by norm_num, by norm_num⟩

/-- Two canonical field cells congruent mod `p` are EQUAL over ℤ. -/
theorem eq_of_modEq_canon {a b : ℤ} (ha : Canon a) (hb : Canon b)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

/-- Two SMALL integers (`|·| ≤ 16`) congruent mod `p` are equal — `p` dwarfs the gap. -/
theorem eq_of_modEq_small {a b : ℤ} (ha : -16 ≤ a ∧ a ≤ 16) (hb : -16 ≤ b ∧ b ≤ 16)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

/-- Booleanity from a `gBin` gate under the field denotation: a CANONICAL cell whose booleanity
gate vanishes mod `p` IS `0` or `1` over ℤ (primality splits `p ∣ x(x−1)`). -/
theorem bin_of_gate {a : Assignment} {c : Nat}
    (h : (gBin c).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) : a c = 0 ∨ a c = 1 := by
  simp only [gBin, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ a c * (a c + (-1)) := Int.modEq_zero_iff_dvd.mp h
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-! ## §2 — The canonicality envelope + the single-row gate extraction. -/

/-- **The step envelope**: every cell of every row is the canonical residue — the deployed
range-check invariant. Carried EXPLICITLY because the field denotation only pins gates mod `p`.
Inhabited concretely by the §6 witness, so it is never a vacuous antecedent. -/
structure StepCanon (t : VmTrace) : Prop where
  cells : ∀ i c, Canon (t.rows.getD i zeroAsg c)

theorem canon_loc {t : VmTrace} (h : StepCanon t) (i c : Nat) : Canon ((envAt t i).loc c) :=
  h.cells i c

/-- A per-row gate `cg g` forces its body to vanish mod `p` on a NON-LAST row (`i + 1 < length`),
where the deployed `when_transition` lowering binds. Keyed on the byte-pinned `automataflStepDesc`. -/
theorem astep_gate {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace} (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {g : EmittedExpr} (hg : cg g ∈ automataflStepDesc.constraints) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have h : i + 1 ≠ t.rows.length := by omega
    simpa using h
  simpa only [cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-! ## §3 — The board decode + sub-lemma (1): the auto one-hot pins the AUTO cell.

`codeToParticle`/`boardDecode` read a satisfying row back into the reference `Board`
(`Automatafl.lean`): particle felt codes `{VAC=0, REP=1, ATT=2, AUTO=3}`, the auto coordinate off
`AX`/`AY`, and the `old` cells off columns `0..k`. -/

/-- The particle felt-code decode (`reference.rs`: `VAC=0, REP=1, ATT=2, AUTO=3`). -/
def codeToParticle (z : ℤ) : Particle :=
  if z = 3 then .automaton else if z = 2 then .attractor else if z = 1 then .repulsor
  else .vacuum

/-- Decode a satisfying row's OLD-board columns into the reference `Board`: size `n`, the auto at
`(AX, AY)`, cell `(x,y)` the felt-decode of `old[y·n+x]`. -/
def boardDecode (e : VmRowEnv) : Board where
  size          := NN
  automaton     := ⟨(e.loc AX).toNat, (e.loc AY).toNat⟩
  cells         := fun c => codeToParticle (e.loc (old (c.y * NN + c.x)))
  useColumnRule := true

section AutoPin
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`coord_of_sat` — the decoded auto coordinate is IN BOUNDS.** The `decompose_coord_le` gates
force `AX = axLoBit` and `AY = ayLoBit`, each a boolean, so both coordinates lie in `{0,1} = [0,n)`.
Derived from the circuit, not assumed. -/
theorem coord_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc AX = 0 ∨ (envAt t i).loc AX = 1)
      ∧ ((envAt t i).loc AY = 0 ∨ (envAt t i).loc AY = 1) := by
  set e := envAt t i with he
  -- AX = axLoBit, AY = ayLoBit (the recomposition gates), each boolean.
  have hxeq : e.loc AX = e.loc axLoBit := by
    have hg := astep_gate hsat i hi (g := .add (.var AX) (.mul (.const (-1)) (.var axLoBit)))
      (by decide)
    simp only [EmittedExpr.eval] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hyeq : e.loc AY = e.loc ayLoBit := by
    have hg := astep_gate hsat i hi (g := .add (.var AY) (.mul (.const (-1)) (.var ayLoBit)))
      (by decide)
    simp only [EmittedExpr.eval] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hxb : e.loc axLoBit = 0 ∨ e.loc axLoBit = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin axLoBit) (by decide)) (canon_loc hc i _)
  have hyb : e.loc ayLoBit = 0 ∨ e.loc ayLoBit = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin ayLoBit) (by decide)) (canon_loc hc i _)
  exact ⟨hxeq ▸ hxb, hyeq ▸ hyb⟩

/-- **`autoPin_of_sat` — SUB-LEMMA (1): the auto one-hot + dot-product pin the AUTO cell.** On a
satisfying, canonical trace, the witnessed `(AX, AY)` are legal board coordinates `(X, Y)` and the
OLD board genuinely holds the AUTO particle there: `old[Y·n+X] = AUTO`. This is derived — the auto
row/column one-hots (`Σ sel = 1`, boolean, index-pinned to `AY`/`AX`) collapse the dot product
`Σ selRow·selCol·old` to the single selected cell, which the pin forces to `AUTO`. -/
theorem autoPin_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ∃ X Y : Nat, X < NN ∧ Y < NN
      ∧ (envAt t i).loc AX = (X : ℤ) ∧ (envAt t i).loc AY = (Y : ℤ)
      ∧ (envAt t i).loc (old (Y * NN + X)) = AUTO := by
  set e := envAt t i with he
  -- boolean one-hot selectors
  have bR0 : e.loc (selRow 0) = 0 ∨ e.loc (selRow 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 0)) (by decide)) (canon_loc hc i _)
  have bR1 : e.loc (selRow 1) = 0 ∨ e.loc (selRow 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 1)) (by decide)) (canon_loc hc i _)
  have bC0 : e.loc (selCol 0) = 0 ∨ e.loc (selCol 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 0)) (by decide)) (canon_loc hc i _)
  have bC1 : e.loc (selCol 1) = 0 ∨ e.loc (selCol 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 1)) (by decide)) (canon_loc hc i _)
  -- Σ sel = 1 (row + col). eval = (a+b) − 1 ≡ 0, both bool ⇒ a+b = 1.
  have sumR : e.loc (selRow 0) + e.loc (selRow 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selRow 0)) (.var (selRow 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selRow 0) + e.loc (selRow 1) + -1)
      (a := e.loc (selRow 0) + e.loc (selRow 1)) (b := 1) (by ring)).mp hg
    rcases bR0 with h0 | h0 <;> rcases bR1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have sumC : e.loc (selCol 0) + e.loc (selCol 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selCol 0)) (.var (selCol 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selCol 0) + e.loc (selCol 1) + -1)
      (a := e.loc (selCol 0) + e.loc (selCol 1)) (b := 1) (by ring)).mp hg
    rcases bC0 with h0 | h0 <;> rcases bC1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  -- index pins: AY = selRow 1, AX = selCol 1 (the j=0 term drops at n=2).
  have idxR : e.loc AY = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selRow 1)) (.mul (.const (-1)) (.var AY))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have idxC : e.loc AX = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selCol 1)) (.mul (.const (-1)) (.var AX))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  -- selectors as functions of the coordinates: selRow1 = AY, selRow0 = 1 − AY (and cols).
  have r1eq : e.loc (selRow 1) = e.loc AY := idxR.symm
  have c1eq : e.loc (selCol 1) = e.loc AX := idxC.symm
  have r0eq : e.loc (selRow 0) = 1 - e.loc AY := by rw [← r1eq]; omega
  have c0eq : e.loc (selCol 0) = 1 - e.loc AX := by rw [← c1eq]; omega
  -- AY, AX ∈ {0,1}.
  have hay : e.loc AY = 0 ∨ e.loc AY = 1 := r1eq ▸ bR1
  have hax : e.loc AX = 0 ∨ e.loc AX = 1 := c1eq ▸ bC1
  -- the dot-product pin, in closed form (the fold reduces definitionally at n = 2).
  have hEval : (headToExpr autoPinHead).eval e.loc
      = e.loc (selRow 0) * e.loc (selCol 0) * e.loc (old 0)
        + e.loc (selRow 0) * e.loc (selCol 1) * e.loc (old 1)
        + e.loc (selRow 1) * e.loc (selCol 0) * e.loc (old 2)
        + e.loc (selRow 1) * e.loc (selCol 1) * e.loc (old 3) + (-3) := rfl
  have hAuto := astep_gate hsat i hi (g := headToExpr autoPinHead) (by decide)
  rw [hEval, r0eq, r1eq, c0eq, c1eq] at hAuto
  -- 4 coordinate cases; the one-hot collapses the sum to the selected cell, pinned to AUTO = 3.
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

/-- **`decoded_auto_holds_automaton` — sub-lemma (1) in `Board` terms.** The decoded OLD board
genuinely carries the AUTO particle at the decoded automaton coordinate. This is the fact
`automatonStep` reads when it steps `b.automaton`: the descriptor forces the witnessed `(AX,AY)` to
BE the automaton's cell, not merely a claimed coordinate. -/
theorem decoded_auto_holds_automaton
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (boardDecode (envAt t i)).cellAt (boardDecode (envAt t i)).automaton = Particle.automaton := by
  obtain ⟨X, Y, hX, hY, hAX, hAY, hcell⟩ := autoPin_of_sat hsat hc i hi
  have hxn : ((envAt t i).loc AX).toNat = X := by rw [hAX]; simp
  have hyn : ((envAt t i).loc AY).toNat = Y := by rw [hAY]; simp
  simp only [Board.cellAt, boardDecode]
  rw [hxn, hyn, hcell, if_pos ⟨hX, hY⟩]
  simp [codeToParticle, AUTO]

end AutoPin

/-! ## §4 — sub-lemma (4), partial: the offset columns are a CARDINAL step (field `{−1,0,1}`).

The circuit-side analogue of `Automatafl.automatonOffset_bounded`: the `choose_offset` membership
gates force `OX`/`OY` into `{−1, 0, 1}` as FIELD elements (`−1 ≡ p−1`). The full sub-lemma (4)
(`offset = chooseOffset`) additionally needs the score-compare soundness (§7 residual); this is the
value-range half, derived from the deployed member gate. -/

/-- A canonical cell whose `{−1,0,1}` membership gate `(x+1)·x·(x−1)` vanishes mod `p` is `0`, `1`,
or `p−1` (`≡ −1`). Same primality argument as `bin_of_gate`, one factor wider. -/
theorem tri_of_gate {a : Assignment} {c : Nat}
    (h : (memberExpr c [-1, 0, 1]).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) :
    a c = 0 ∨ a c = 1 ∨ a c = 2013265920 := by
  simp only [memberExpr, List.foldl, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ (a c + -(-1)) * (a c + -0) * (a c + -1) :=
    Int.modEq_zero_iff_dvd.mp (by simpa using h)
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with h1 | h1
  · rcases pPrimeInt.dvd_mul.mp h1 with h2 | h2
    · obtain ⟨k, hk⟩ := h2; right; right; omega
    · obtain ⟨k, hk⟩ := h2; left; omega
  · obtain ⟨k, hk⟩ := h1; right; left; omega

section Offset
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`offset_of_sat`** — the witnessed offset columns are a cardinal step in field terms. -/
theorem offset_of_sat (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc OX_C = 0 ∨ (envAt t i).loc OX_C = 1 ∨ (envAt t i).loc OX_C = 2013265920)
      ∧ ((envAt t i).loc OY_C = 0 ∨ (envAt t i).loc OY_C = 1
          ∨ (envAt t i).loc OY_C = 2013265920) := by
  refine ⟨tri_of_gate (astep_gate hsat i hi (g := memberExpr OX_C [-1, 0, 1]) (by decide))
      (canon_loc hc i _),
    tri_of_gate (astep_gate hsat i hi (g := memberExpr OY_C [-1, 0, 1]) (by decide))
      (canon_loc hc i _)⟩

end Offset

/-! ## §5 — NON-VACUITY: the auto-pin gate is a two-sided discriminator (`#guard`).

A full satisfying trace for all 410 constraints (ray/decide/step witness columns + the two Poseidon2
`board_root8` lookups) is out of scope; but the SEMANTIC tooth this file proves is non-vacuous, shown
concretely on the auto-pin gate: it ACCEPTS the correct board (auto at (0,0) holding `AUTO=3`) and
REJECTS a wrong one (that cell holding `VAC=0`). A vacuous or always-true gate could not do both. -/

/-- Row picking cell (0,0): `selRow0 = selCol0 = 1`, that cell holds `AUTO = 3`. -/
def goodAsg : Assignment := fun c => if c = 0 then 3 else if c = selRow 0 ∨ c = selCol 0 then 1 else 0
/-- Same selectors, but cell (0,0) holds `VAC = 0` — a wrong board. -/
def badAsg : Assignment := fun c => if c = selRow 0 ∨ c = selCol 0 then 1 else 0

#guard (headToExpr autoPinHead).eval goodAsg == 0       -- correct board: gate holds
#guard (headToExpr autoPinHead).eval badAsg != 0        -- wrong board: gate FAILS (≠ 0)

/-! ## §6 — Axiom hygiene. -/

#print axioms autoPin_of_sat
#print axioms decoded_auto_holds_automaton
#print axioms offset_of_sat

/-! ## §7 — THE NAMED RESIDUAL (what remains for the full composition).

Proven here, keyed on the byte-pinned `automataflStepDesc`, canonical over BabyBear, none assumed:
  * `astep_gate` — the single-row gate extraction;
  * `coord_of_sat` — the decoded auto coordinate is in bounds (`decompose_coord_le` soundness);
  * `autoPin_of_sat` / `decoded_auto_holds_automaton` — SUB-LEMMA (1) in full;
  * `offset_of_sat` — the value-range half of sub-lemma (4).

REMAINING (the heavier soundness legs, each a multi-file effort; NOT assumed, NOT stubbed):
  (2) `raycastFuel` refinement — the four ray blocks (prefix-sum in-bounds bit, gated shifted read,
      hit one-hot, dist/what recomposition, occlusion) force `(rDist d, rWhat d) = Board.raycast`;
  (3) `evaluateAxis` refinement — the `decide_axis` 9×4 truth table + `forced_ge0` range gadgets
      force `Decision = evaluateAxis` (watch the field-congruence trap on the `ge0` bits);
  (4) `chooseOffset` — the score-compare (`sgt/slt`, 20-bit) soundness closing offset = `chooseOffset`;
  (5) the step + board-update fold ⇒ `boardDecode(new) = automatonStep(boardDecode(old))`.
The top-level composition is deliberately NOT stated as a proven theorem until (2)-(5) close. -/

end Dregg2.Circuit.Emit.AutomataflStepRefine
