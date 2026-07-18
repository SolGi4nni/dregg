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

**This file lands sub-lemma (1) IN FULL, sub-lemma (2) for the XP ray IN FULL, plus the two
"envelope" facts (2)-(4) rest on** — the in-bounds decode of the auto coordinate (`coord_of_sat`) and
the cardinal-offset membership (`offset_of_sat`, the circuit-side analogue of
`automatonOffset_bounded`) — all DERIVED from the constraints, none assumed. Sub-lemma (2) closes as
`raycast_xp_of_sat`: on a satisfying canonical trace the decoded `(rDist 0, rWhat 0)` IS the reference
`Board.raycast (boardDecode e) auto .xp` — the hit one-hot, the vacuum-before / in-bounds-before
occlusion gates, and the `cond_nonzero` in-bounds-hit witness force the true first-non-vacuum cell. The
remaining legs — the OTHER THREE rays `XN`/`YP`/`YN` (a mechanical replay of XP, §7 (2')), and (3),
(5) — are the NAMED residual (§7): they require modelling `evaluateAxis`/the board-update fold against
the decide/step columns, a multi-file effort. Nothing here assumes them, and nothing is a vacuous
`P → P`: the top-level composition is NOT stated as a proven theorem — only the sub-lemmas that close.

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
open Dregg2.Games.Automatafl (Board Coord Particle Dir raycastFuel Decision Raycast evaluateAxis)

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
theorem canon_one : Canon 1 := ⟨by norm_num, by norm_num⟩
theorem canon_two : Canon 2 := ⟨by norm_num, by norm_num⟩
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

/-- A canonical cell whose `{0,1,2}` particle-code membership gate `x(x−1)(x−2)` vanishes mod `p` is
`0`, `1`, or `2` — the ray's `what` is a vacuum/repulsor/attractor felt code (never `AUTO`). Same
primality argument as `tri_of_gate`. -/
theorem mem3_of_gate {a : Assignment} {c : Nat}
    (h : (memberExpr c [0, 1, 2]).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) :
    a c = 0 ∨ a c = 1 ∨ a c = 2 := by
  simp only [memberExpr, List.foldl, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ a c * (a c + -1) * (a c + -2) :=
    Int.modEq_zero_iff_dvd.mp (by simpa using h)
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with h1 | h1
  · rcases pPrimeInt.dvd_mul.mp h1 with h2 | h2
    · obtain ⟨k, hk⟩ := h2; left; omega
    · obtain ⟨k, hk⟩ := h2; right; left; omega
  · obtain ⟨k, hk⟩ := h1; right; right; omega

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

/-! ## §4.5 — sub-lemma (2), the XP ray: the ray gates FORCE the true `Board.raycast`.

The four ray-scan blocks each witness a `(dist, what)`; this section closes the XP block IN FULL —
the decoded `(rDist 0, rWhat 0)` is provably the reference `Board.raycast (boardDecode e) auto .xp`.
The hit one-hot pins WHICH step is the hit; the occlusion (vacuum-before / in-bounds-before) gates +
the `cond_nonzero` in-bounds-hit witness force every strictly-earlier cell to be vacuum and the read
cell to be genuinely non-vacuum; the gated shifted read ties `what` to that cell's felt code. Derived
from the constraints, none assumed; `n = 2` is handled concretely (the rays are two steps long). -/

/-- The `Board.raycast … .xp` reduction at `n = 2`: from `(X, Y)` the ray reads cell `(1, Y)` when
`X = 0` (dist 1 on a hit, else dist 2 at the wall) and hits the wall immediately (dist 1, vacuum)
when `X = 1`. A pure `Board` fact — the semantic target the circuit must match. -/
theorem raycast_xp_reduce (b : Board) (hs : b.size = 2) (X Y : Nat) (hX : X < 2) (hY : Y < 2) :
    Board.raycast b ⟨X, Y⟩ Dir.xp
      = (if X = 0 then
           (if (b.cellAt ⟨1, Y⟩).isVacuum then { what := .vacuum, dist := 2 }
            else { what := b.cellAt ⟨1, Y⟩, dist := 1 })
         else { what := .vacuum, dist := 1 }) := by
  have h3 : (b.size + 1) = 3 := by omega
  have hY1 : (Y : Int) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hY
  rcases (by omega : X = 0 ∨ X = 1) with rfl | rfl
  · rw [if_pos rfl]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]
    norm_num [hY1]
    by_cases hv : (b.cellAt ⟨1, Y⟩).isVacuum = true
    · rw [if_pos hv, if_pos hv, raycastFuel, hs]; norm_num
    · rw [if_neg hv, if_neg hv]
  · rw [if_neg (by norm_num)]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]; norm_num

section RayXP
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`raycast_xp_of_sat` — SUB-LEMMA (2) for the XP ray, in full.** On a satisfying, canonical
trace, the decoded `(rDist 0, rWhat 0)` of the XP ray block equals the reference
`Board.raycast (boardDecode e) (auto) .xp`: the witnessed distance and particle ARE the genuine
first-non-vacuum hit along `+x` (or the wall-vacuum sentinel). Derived from the hit one-hot, the
occlusion gates, and the `cond_nonzero` witness — none assumed. -/
theorem raycast_xp_of_sat
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecode (envAt t i)) (boardDecode (envAt t i)).automaton Dir.xp
      = { what := codeToParticle ((envAt t i).loc (rWhat 0)),
          dist := ((envAt t i).loc (rDist 0)).toNat } := by
  set e := envAt t i with he
  -- ============ selector / coordinate facts ============
  have bC0 : e.loc (selCol 0) = 0 ∨ e.loc (selCol 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 0)) (by decide)) (canon_loc hc i _)
  have bC1 : e.loc (selCol 1) = 0 ∨ e.loc (selCol 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 1)) (by decide)) (canon_loc hc i _)
  have sumC : e.loc (selCol 0) + e.loc (selCol 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selCol 0)) (.var (selCol 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selCol 0) + e.loc (selCol 1) + -1)
      (a := e.loc (selCol 0) + e.loc (selCol 1)) (b := 1) (by ring)).mp hg
    rcases bC0 with h0 | h0 <;> rcases bC1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxC : e.loc AX = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selCol 1)) (.mul (.const (-1)) (.var AX))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have bR0 : e.loc (selRow 0) = 0 ∨ e.loc (selRow 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 0)) (by decide)) (canon_loc hc i _)
  have bR1 : e.loc (selRow 1) = 0 ∨ e.loc (selRow 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 1)) (by decide)) (canon_loc hc i _)
  have sumR : e.loc (selRow 0) + e.loc (selRow 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selRow 0)) (.var (selRow 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selRow 0) + e.loc (selRow 1) + -1)
      (a := e.loc (selRow 0) + e.loc (selRow 1)) (b := 1) (by ring)).mp hg
    rcases bR0 with h0 | h0 <;> rcases bR1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxR : e.loc AY = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selRow 1)) (.mul (.const (-1)) (.var AY))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have hc0 : e.loc (selCol 0) = 1 - e.loc AX := by rw [idxC]; omega
  have hr0 : e.loc (selRow 0) = 1 - e.loc AY := by rw [idxR]; omega
  have hr1 : e.loc (selRow 1) = e.loc AY := idxR.symm
  have hax : e.loc AX = 0 ∨ e.loc AX = 1 := idxC ▸ bC1
  have hay : e.loc AY = 0 ∨ e.loc AY = 1 := idxR ▸ bR1
  -- ============ ray-XP gate extractions (d = 0, steps kk ∈ {1,2}) ============
  -- ib pins: rIb1 = selCol0 (in-window prefix sum at kk=1), rIb2 = 0 (kk=2 out of window).
  have hib1 : e.loc (rIb 0 1) = e.loc (selCol 0) := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 0 1 0 1)) (by decide)
    rw [show (headToExpr (ibEqHead 0 1 0 1)).eval e.loc
        = e.loc (rIb 0 1) + (-1) * e.loc (selCol 0) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hib2 : e.loc (rIb 0 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 0 1 0 2)) (by decide)
    rw [show (headToExpr (ibEqHead 0 1 0 2)).eval e.loc = e.loc (rIb 0 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hrc2 : e.loc (rRc 0 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (rcReadHead 0 1 0 2)) (by decide)
    rw [show (headToExpr (rcReadHead 0 1 0 2)).eval e.loc = e.loc (rRc 0 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  -- the hit one-hot: booleans + Σ = 1.
  have hb1 : e.loc (rHit 0 1) = 0 ∨ e.loc (rHit 0 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 0 1)) (by decide)) (canon_loc hc i _)
  have hb2 : e.loc (rHit 0 2) = 0 ∨ e.loc (rHit 0 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 0 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 0 1) + e.loc (rHit 0 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 0 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 0 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 0 1) + e.loc (rHit 0 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 0 1) + e.loc (rHit 0 2)) (b := 1) (by ring)).mp hg
    rcases hb1 with h0 | h0 <;> rcases hb2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  -- the recomposition / occlusion / read gates as raw mod-`p` congruences (reduced per case).
  have hDist := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 0 kk))
      (Head.lin (-1) (rDist 0)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 0 kk))
      (Head.lin (-1) (rDist 0)))).eval e.loc
      = (-1) * e.loc (rDist 0) + e.loc (rHit 0 1) + 2 * e.loc (rHit 0 2) from rfl] at hDist
  have hWhat := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 0 kk, rRc 0 kk])
      (Head.lin (-1) (rWhat 0)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 0 kk, rRc 0 kk])
      (Head.lin (-1) (rWhat 0)))).eval e.loc
      = (-1) * e.loc (rWhat 0) + e.loc (rHit 0 1) * e.loc (rRc 0 1)
        + e.loc (rHit 0 2) * e.loc (rRc 0 2) from rfl] at hWhat
  have hHib := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 0 kk, rIb 0 kk])
      (Head.lin (-1) (rHib 0)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 0 kk, rIb 0 kk])
      (Head.lin (-1) (rHib 0)))).eval e.loc
      = (-1) * e.loc (rHib 0) + e.loc (rHit 0 1) * e.loc (rIb 0 1)
        + e.loc (rHit 0 2) * e.loc (rIb 0 2) from rfl] at hHib
  have hRC1 := astep_gate hsat i hi (g := headToExpr (rcReadHead 0 1 0 1)) (by decide)
  rw [show (headToExpr (rcReadHead 0 1 0 1)).eval e.loc
      = e.loc (rRc 0 1)
        + (-1) * (e.loc (rIb 0 1) * e.loc (selRow 0) * e.loc (selCol 0) * e.loc (old 1))
        + (-1) * (e.loc (rIb 0 1) * e.loc (selRow 1) * e.loc (selCol 0) * e.loc (old 3)) from rfl]
    at hRC1
  have hVac := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [rHit 0 2, rRc 0 1])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [rHit 0 2, rRc 0 1])).eval e.loc
      = e.loc (rHit 0 2) * e.loc (rRc 0 1) from rfl] at hVac
  have hInb := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addLin 1 (rHit 0 2)).addProd (-1) [rHit 0 2, rIb 0 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addLin 1 (rHit 0 2)).addProd (-1) [rHit 0 2, rIb 0 1])).eval e.loc
      = e.loc (rHit 0 2) + (-1) * (e.loc (rHit 0 2) * e.loc (rIb 0 1)) from rfl] at hInb
  have hCond := astep_gate hsat i hi
    (g := .mul (.var (rHib 0)) (.add (.mul (.var (rWhat 0)) (.var (rInv 0))) (.const (-1)))) (by decide)
  simp only [EmittedExpr.eval] at hCond
  -- the ray's `what` is a {VAC,REP,ATT} felt code (never AUTO).
  have hMem : e.loc (rWhat 0) = 0 ∨ e.loc (rWhat 0) = 1 ∨ e.loc (rWhat 0) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 0) [0, 1, 2]) (by decide))
      (canon_loc hc i _)
  -- ============ reduce the reference raycast to the two-step n=2 scan ============
  have hXlt : (e.loc AX).toNat < 2 := by rcases hax with h | h <;> rw [h] <;> decide
  have hYlt : (e.loc AY).toNat < 2 := by rcases hay with h | h <;> rw [h] <;> decide
  rw [show (boardDecode e).automaton = ⟨(e.loc AX).toNat, (e.loc AY).toNat⟩ from rfl,
     raycast_xp_reduce (boardDecode e) (show (boardDecode e).size = 2 from rfl) _ _ hXlt hYlt]
  -- the hit one-hot resolves to exactly one hit step.
  have hone : (e.loc (rHit 0 1) = 1 ∧ e.loc (rHit 0 2) = 0)
            ∨ (e.loc (rHit 0 1) = 0 ∧ e.loc (rHit 0 2) = 1) := by
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
    · right; exact ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
  rcases hone with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
  · -- CASE hit = (1,0): dist = 1, what = rc1, hib = ib1.
    rw [hh1, hh2] at hDist hWhat hHib
    have hd : e.loc (rDist 0) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rDist 0)) (by ring)).mp hDist)).symm
    have hw : e.loc (rWhat 0) = e.loc (rRc 0 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := e.loc (rWhat 0)) (by ring)).mp hWhat)).symm
    have hh : e.loc (rHib 0) = e.loc (rIb 0 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rIb 0 1)) (b := e.loc (rHib 0)) (by ring)).mp hHib)).symm
    rcases hax with hAX | hAX
    · -- X = 0: ib1 = 1, the read cell is genuinely non-vacuum (cond_nonzero).
      have hib1v : e.loc (rIb 0 1) = 1 := by rw [hib1, hc0, hAX]; norm_num
      have hHib1 : e.loc (rHib 0) = 1 := by rw [hh, hib1v]
      rw [hHib1] at hCond
      have hwne : e.loc (rWhat 0) ≠ 0 := by
        intro h0
        rw [h0] at hCond
        have hneg : (1 : ℤ) * (0 * e.loc (rInv 0) + -1) = -1 := by ring
        rw [hneg] at hCond
        obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hCond
        omega
      have hw12 : e.loc (rWhat 0) = 1 ∨ e.loc (rWhat 0) = 2 := by
        rcases hMem with h | h | h
        · exact absurd h hwne
        · exact Or.inl h
        · exact Or.inr h
      have hX0 : (e.loc AX).toNat = 0 := by rw [hAX]; rfl
      rcases hay with hAY | hAY
      · -- Y = 0: cell = old 1.
        have hrc1 : e.loc (rRc 0 1) = e.loc (old 1) := by
          rw [hib1v, (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
              (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
              (show e.loc (selRow 1) = 0 by rw [hr1, hAY])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := e.loc (old 1)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨1, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 1)) := by
          rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hX0, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 0))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
      · -- Y = 1: cell = old 3.
        have hrc1 : e.loc (rRc 0 1) = e.loc (old 3) := by
          rw [hib1v, (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
              (show e.loc (selRow 0) = 0 by rw [hr0, hAY]; norm_num),
              (show e.loc (selRow 1) = 1 by rw [hr1, hAY])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := e.loc (old 3)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨1, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 3)) := by
          rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hX0, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 0))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
    · -- X = 1: ib1 = 0, the read is the wall — rc1 = 0, what = vacuum.
      have hib1v : e.loc (rIb 0 1) = 0 := by rw [hib1, hc0, hAX]; norm_num
      have hrc1 : e.loc (rRc 0 1) = 0 := by
        rw [hib1v] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) canon_zero
          ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := 0) (by ring)).mp hRC1)
      have hw0 : e.loc (rWhat 0) = 0 := by rw [hw, hrc1]
      have hX1 : ¬ ((e.loc AX).toNat = 0) := by rw [hAX]; decide
      rw [if_neg hX1, hw0, hd]
      rfl
  · -- CASE hit = (0,1): dist = 2, what = rc2 = 0 (wall past a vacuum before-cell); forces X = 0.
    rw [hh1, hh2] at hDist hWhat
    rw [hh2] at hVac hInb
    have hd : e.loc (rDist 0) = 2 :=
      (eq_of_modEq_canon canon_two (canon_loc hc i _)
        ((gate_modEq_iff (a := (2 : ℤ)) (b := e.loc (rDist 0)) (by ring)).mp hDist)).symm
    have hrc1z : e.loc (rRc 0 1) = 0 :=
      eq_of_modEq_canon (canon_loc hc i _) canon_zero
        ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := 0) (by ring)).mp hVac)
    have hib1v : e.loc (rIb 0 1) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rIb 0 1)) (by ring)).mp hInb)).symm
    have hAX : e.loc AX = 0 := by
      have : e.loc (selCol 0) = 1 := by rw [← hib1, hib1v]
      rw [hc0] at this; omega
    have hw0 : e.loc (rWhat 0) = 0 := by
      have := hWhat
      rw [hrc2] at this
      exact (eq_of_modEq_canon canon_zero (canon_loc hc i _)
        ((gate_modEq_iff (a := (0 : ℤ)) (b := e.loc (rWhat 0)) (by ring)).mp this)).symm
    rcases hay with hAY | hAY
    · -- Y = 0: cell = old 1 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 0 1) = e.loc (old 1) := by
        rw [hib1v, (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
            (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
            (show e.loc (selRow 1) = 0 by rw [hr1, hAY])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := e.loc (old 1)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨1, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 1)) := by
        rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
      have hX0 : (e.loc AX).toNat = 0 := by rw [hAX]; rfl
      rw [if_pos hX0, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl
    · -- Y = 1: cell = old 3 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 0 1) = e.loc (old 3) := by
        rw [hib1v, (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
            (show e.loc (selRow 0) = 0 by rw [hr0, hAY]; norm_num),
            (show e.loc (selRow 1) = 1 by rw [hr1, hAY])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 0 1)) (b := e.loc (old 3)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨1, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 3)) := by
        rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
      have hX0 : (e.loc AX).toNat = 0 := by rw [hAX]; rfl
      rw [if_pos hX0, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl

end RayXP

/-! ## §4.6 — sub-lemma (2), the XN ray (`Dir.xn`, ray block `d = 1`, shifts `−x`).

A mechanical replay of the XP leg (§4.5) with the along-axis direction flipped: the in-window bit at
`kk = 1` is `selCol 1` (`= AX`, in bounds iff `AX = 1`), the shifted read collapses to cell `(0, Y)`,
and the reference reduction reads `−x`. Same hit one-hot / occlusion / `cond_nonzero` machinery. -/

/-- The `Board.raycast … .xn` reduction at `n = 2`: from `(X, Y)` the ray reads cell `(0, Y)` when
`X = 1` (dist 1 on a hit, else dist 2 at the wall) and hits the wall immediately when `X = 0`. -/
theorem raycast_xn_reduce (b : Board) (hs : b.size = 2) (X Y : Nat) (hX : X < 2) (hY : Y < 2) :
    Board.raycast b ⟨X, Y⟩ Dir.xn
      = (if X = 1 then
           (if (b.cellAt ⟨0, Y⟩).isVacuum then { what := .vacuum, dist := 2 }
            else { what := b.cellAt ⟨0, Y⟩, dist := 1 })
         else { what := .vacuum, dist := 1 }) := by
  have h3 : (b.size + 1) = 3 := by omega
  have hY1 : (Y : Int) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hY
  rcases (by omega : X = 0 ∨ X = 1) with rfl | rfl
  · rw [if_neg (by norm_num)]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]; norm_num
  · rw [if_pos rfl]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]
    norm_num [hY1]
    by_cases hv : (b.cellAt ⟨0, Y⟩).isVacuum = true
    · rw [if_pos hv, if_pos hv, raycastFuel, hs]; norm_num
    · rw [if_neg hv, if_neg hv]

section RayXN
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`raycast_xn_of_sat` — SUB-LEMMA (2) for the XN ray, in full.** The decoded `(rDist 1, rWhat 1)`
of the XN ray block equals the reference `Board.raycast (boardDecode e) auto .xn`. -/
theorem raycast_xn_of_sat
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecode (envAt t i)) (boardDecode (envAt t i)).automaton Dir.xn
      = { what := codeToParticle ((envAt t i).loc (rWhat 1)),
          dist := ((envAt t i).loc (rDist 1)).toNat } := by
  set e := envAt t i with he
  -- ============ selector / coordinate facts (shared front-end auto one-hot) ============
  have bC0 : e.loc (selCol 0) = 0 ∨ e.loc (selCol 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 0)) (by decide)) (canon_loc hc i _)
  have bC1 : e.loc (selCol 1) = 0 ∨ e.loc (selCol 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 1)) (by decide)) (canon_loc hc i _)
  have sumC : e.loc (selCol 0) + e.loc (selCol 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selCol 0)) (.var (selCol 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selCol 0) + e.loc (selCol 1) + -1)
      (a := e.loc (selCol 0) + e.loc (selCol 1)) (b := 1) (by ring)).mp hg
    rcases bC0 with h0 | h0 <;> rcases bC1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxC : e.loc AX = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selCol 1)) (.mul (.const (-1)) (.var AX))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have bR0 : e.loc (selRow 0) = 0 ∨ e.loc (selRow 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 0)) (by decide)) (canon_loc hc i _)
  have bR1 : e.loc (selRow 1) = 0 ∨ e.loc (selRow 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 1)) (by decide)) (canon_loc hc i _)
  have sumR : e.loc (selRow 0) + e.loc (selRow 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selRow 0)) (.var (selRow 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selRow 0) + e.loc (selRow 1) + -1)
      (a := e.loc (selRow 0) + e.loc (selRow 1)) (b := 1) (by ring)).mp hg
    rcases bR0 with h0 | h0 <;> rcases bR1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxR : e.loc AY = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selRow 1)) (.mul (.const (-1)) (.var AY))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have hc0 : e.loc (selCol 0) = 1 - e.loc AX := by rw [idxC]; omega
  have hc1 : e.loc (selCol 1) = e.loc AX := idxC.symm
  have hr0 : e.loc (selRow 0) = 1 - e.loc AY := by rw [idxR]; omega
  have hr1 : e.loc (selRow 1) = e.loc AY := idxR.symm
  have hax : e.loc AX = 0 ∨ e.loc AX = 1 := idxC ▸ bC1
  have hay : e.loc AY = 0 ∨ e.loc AY = 1 := idxR ▸ bR1
  -- ============ ray-XN gate extractions (d = 1, steps kk ∈ {1,2}) ============
  have hib1 : e.loc (rIb 1 1) = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 1 (-1) 0 1)) (by decide)
    rw [show (headToExpr (ibEqHead 1 (-1) 0 1)).eval e.loc
        = e.loc (rIb 1 1) + (-1) * e.loc (selCol 1) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hib2 : e.loc (rIb 1 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 1 (-1) 0 2)) (by decide)
    rw [show (headToExpr (ibEqHead 1 (-1) 0 2)).eval e.loc = e.loc (rIb 1 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hrc2 : e.loc (rRc 1 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (rcReadHead 1 (-1) 0 2)) (by decide)
    rw [show (headToExpr (rcReadHead 1 (-1) 0 2)).eval e.loc = e.loc (rRc 1 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hb1 : e.loc (rHit 1 1) = 0 ∨ e.loc (rHit 1 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 1 1)) (by decide)) (canon_loc hc i _)
  have hb2 : e.loc (rHit 1 2) = 0 ∨ e.loc (rHit 1 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 1 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 1 1) + e.loc (rHit 1 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 1 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 1 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 1 1) + e.loc (rHit 1 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 1 1) + e.loc (rHit 1 2)) (b := 1) (by ring)).mp hg
    rcases hb1 with h0 | h0 <;> rcases hb2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hDist := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 1 kk))
      (Head.lin (-1) (rDist 1)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 1 kk))
      (Head.lin (-1) (rDist 1)))).eval e.loc
      = (-1) * e.loc (rDist 1) + e.loc (rHit 1 1) + 2 * e.loc (rHit 1 2) from rfl] at hDist
  have hWhat := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 1 kk, rRc 1 kk])
      (Head.lin (-1) (rWhat 1)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 1 kk, rRc 1 kk])
      (Head.lin (-1) (rWhat 1)))).eval e.loc
      = (-1) * e.loc (rWhat 1) + e.loc (rHit 1 1) * e.loc (rRc 1 1)
        + e.loc (rHit 1 2) * e.loc (rRc 1 2) from rfl] at hWhat
  have hHib := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 1 kk, rIb 1 kk])
      (Head.lin (-1) (rHib 1)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 1 kk, rIb 1 kk])
      (Head.lin (-1) (rHib 1)))).eval e.loc
      = (-1) * e.loc (rHib 1) + e.loc (rHit 1 1) * e.loc (rIb 1 1)
        + e.loc (rHit 1 2) * e.loc (rIb 1 2) from rfl] at hHib
  have hRC1 := astep_gate hsat i hi (g := headToExpr (rcReadHead 1 (-1) 0 1)) (by decide)
  rw [show (headToExpr (rcReadHead 1 (-1) 0 1)).eval e.loc
      = e.loc (rRc 1 1)
        + (-1) * (e.loc (rIb 1 1) * e.loc (selRow 0) * e.loc (selCol 1) * e.loc (old 0))
        + (-1) * (e.loc (rIb 1 1) * e.loc (selRow 1) * e.loc (selCol 1) * e.loc (old 2)) from rfl]
    at hRC1
  have hVac := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [rHit 1 2, rRc 1 1])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [rHit 1 2, rRc 1 1])).eval e.loc
      = e.loc (rHit 1 2) * e.loc (rRc 1 1) from rfl] at hVac
  have hInb := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addLin 1 (rHit 1 2)).addProd (-1) [rHit 1 2, rIb 1 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addLin 1 (rHit 1 2)).addProd (-1) [rHit 1 2, rIb 1 1])).eval e.loc
      = e.loc (rHit 1 2) + (-1) * (e.loc (rHit 1 2) * e.loc (rIb 1 1)) from rfl] at hInb
  have hCond := astep_gate hsat i hi
    (g := .mul (.var (rHib 1)) (.add (.mul (.var (rWhat 1)) (.var (rInv 1))) (.const (-1)))) (by decide)
  simp only [EmittedExpr.eval] at hCond
  have hMem : e.loc (rWhat 1) = 0 ∨ e.loc (rWhat 1) = 1 ∨ e.loc (rWhat 1) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 1) [0, 1, 2]) (by decide))
      (canon_loc hc i _)
  -- ============ reduce the reference raycast to the two-step n=2 scan ============
  have hXlt : (e.loc AX).toNat < 2 := by rcases hax with h | h <;> rw [h] <;> decide
  have hYlt : (e.loc AY).toNat < 2 := by rcases hay with h | h <;> rw [h] <;> decide
  rw [show (boardDecode e).automaton = ⟨(e.loc AX).toNat, (e.loc AY).toNat⟩ from rfl,
     raycast_xn_reduce (boardDecode e) (show (boardDecode e).size = 2 from rfl) _ _ hXlt hYlt]
  have hone : (e.loc (rHit 1 1) = 1 ∧ e.loc (rHit 1 2) = 0)
            ∨ (e.loc (rHit 1 1) = 0 ∧ e.loc (rHit 1 2) = 1) := by
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
    · right; exact ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
  rcases hone with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
  · -- CASE hit = (1,0): dist = 1, what = rc1, hib = ib1.
    rw [hh1, hh2] at hDist hWhat hHib
    have hd : e.loc (rDist 1) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rDist 1)) (by ring)).mp hDist)).symm
    have hw : e.loc (rWhat 1) = e.loc (rRc 1 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := e.loc (rWhat 1)) (by ring)).mp hWhat)).symm
    have hh : e.loc (rHib 1) = e.loc (rIb 1 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rIb 1 1)) (b := e.loc (rHib 1)) (by ring)).mp hHib)).symm
    rcases hax with hAX | hAX
    · -- X = 0: out of window (selCol 1 = AX = 0) → wall, dist 1 vacuum.
      have hib1v : e.loc (rIb 1 1) = 0 := by rw [hib1, hc1, hAX]
      have hrc1 : e.loc (rRc 1 1) = 0 := by
        rw [hib1v] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) canon_zero
          ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := 0) (by ring)).mp hRC1)
      have hw0 : e.loc (rWhat 1) = 0 := by rw [hw, hrc1]
      have hX0 : ¬ ((e.loc AX).toNat = 1) := by rw [hAX]; decide
      rw [if_neg hX0, hw0, hd]
      rfl
    · -- X = 1: in window → genuine hit, read cell (0, Y).
      have hib1v : e.loc (rIb 1 1) = 1 := by rw [hib1, hc1, hAX]
      have hHib1 : e.loc (rHib 1) = 1 := by rw [hh, hib1v]
      rw [hHib1] at hCond
      have hwne : e.loc (rWhat 1) ≠ 0 := by
        intro h0
        rw [h0] at hCond
        have hneg : (1 : ℤ) * (0 * e.loc (rInv 1) + -1) = -1 := by ring
        rw [hneg] at hCond
        obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hCond
        omega
      have hw12 : e.loc (rWhat 1) = 1 ∨ e.loc (rWhat 1) = 2 := by
        rcases hMem with h | h | h
        · exact absurd h hwne
        · exact Or.inl h
        · exact Or.inr h
      have hX1 : (e.loc AX).toNat = 1 := by rw [hAX]; rfl
      rcases hay with hAY | hAY
      · -- Y = 0: cell = old 0.
        have hrc1 : e.loc (rRc 1 1) = e.loc (old 0) := by
          rw [hib1v, (show e.loc (selCol 1) = 1 by rw [hc1, hAX]),
              (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
              (show e.loc (selRow 1) = 0 by rw [hr1, hAY])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := e.loc (old 0)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨0, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 0)) := by
          rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hX1, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 1))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
      · -- Y = 1: cell = old 2.
        have hrc1 : e.loc (rRc 1 1) = e.loc (old 2) := by
          rw [hib1v, (show e.loc (selCol 1) = 1 by rw [hc1, hAX]),
              (show e.loc (selRow 0) = 0 by rw [hr0, hAY]; norm_num),
              (show e.loc (selRow 1) = 1 by rw [hr1, hAY])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := e.loc (old 2)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨0, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 2)) := by
          rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hX1, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 1))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
  · -- CASE hit = (0,1): dist = 2, what = rc2 = 0; forces X = 1 (in window).
    rw [hh1, hh2] at hDist hWhat
    rw [hh2] at hVac hInb
    have hd : e.loc (rDist 1) = 2 :=
      (eq_of_modEq_canon canon_two (canon_loc hc i _)
        ((gate_modEq_iff (a := (2 : ℤ)) (b := e.loc (rDist 1)) (by ring)).mp hDist)).symm
    have hrc1z : e.loc (rRc 1 1) = 0 :=
      eq_of_modEq_canon (canon_loc hc i _) canon_zero
        ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := 0) (by ring)).mp hVac)
    have hib1v : e.loc (rIb 1 1) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rIb 1 1)) (by ring)).mp hInb)).symm
    have hAX : e.loc AX = 1 := by
      have hsc : e.loc (selCol 1) = 1 := by rw [← hib1, hib1v]
      rw [hc1] at hsc; exact hsc
    have hw0 : e.loc (rWhat 1) = 0 := by
      have := hWhat
      rw [hrc2] at this
      exact (eq_of_modEq_canon canon_zero (canon_loc hc i _)
        ((gate_modEq_iff (a := (0 : ℤ)) (b := e.loc (rWhat 1)) (by ring)).mp this)).symm
    have hX1 : (e.loc AX).toNat = 1 := by rw [hAX]; rfl
    rcases hay with hAY | hAY
    · -- Y = 0: cell = old 0 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 1 1) = e.loc (old 0) := by
        rw [hib1v, (show e.loc (selCol 1) = 1 by rw [hc1, hAX]),
            (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
            (show e.loc (selRow 1) = 0 by rw [hr1, hAY])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := e.loc (old 0)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨0, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 0)) := by
        rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hX1, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl
    · -- Y = 1: cell = old 2 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 1 1) = e.loc (old 2) := by
        rw [hib1v, (show e.loc (selCol 1) = 1 by rw [hc1, hAX]),
            (show e.loc (selRow 0) = 0 by rw [hr0, hAY]; norm_num),
            (show e.loc (selRow 1) = 1 by rw [hr1, hAY])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 1 1)) (b := e.loc (old 2)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨0, (e.loc AY).toNat⟩ = codeToParticle (e.loc (old 2)) := by
        rw [hAY]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hX1, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl

end RayXN

/-! ## §4.7 — sub-lemma (2), the YP ray (`Dir.yp`, ray block `d = 2`, scans ROWS via `selRow +y`).

The row analogue of the XP leg: the in-window bit at `kk = 1` is `selRow 0` (`= 1 − AY`, in bounds iff
`AY = 0`), the shifted read collapses to cell `(X, 1)` (column chosen by `selCol`), the reference
reduction reads `+y`. -/

/-- The `Board.raycast … .yp` reduction at `n = 2`: from `(X, Y)` the ray reads cell `(X, 1)` when
`Y = 0` (dist 1 on a hit, else dist 2 at the wall) and hits the wall immediately when `Y = 1`. -/
theorem raycast_yp_reduce (b : Board) (hs : b.size = 2) (X Y : Nat) (hX : X < 2) (hY : Y < 2) :
    Board.raycast b ⟨X, Y⟩ Dir.yp
      = (if Y = 0 then
           (if (b.cellAt ⟨X, 1⟩).isVacuum then { what := .vacuum, dist := 2 }
            else { what := b.cellAt ⟨X, 1⟩, dist := 1 })
         else { what := .vacuum, dist := 1 }) := by
  have h3 : (b.size + 1) = 3 := by omega
  have hX1 : (X : Int) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hX
  rcases (by omega : Y = 0 ∨ Y = 1) with rfl | rfl
  · rw [if_pos rfl]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]
    norm_num [hX1]
    by_cases hv : (b.cellAt ⟨X, 1⟩).isVacuum = true
    · rw [if_pos hv, if_pos hv, raycastFuel, hs]; norm_num
    · rw [if_neg hv, if_neg hv]
  · rw [if_neg (by norm_num)]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]; norm_num

section RayYP
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`raycast_yp_of_sat` — SUB-LEMMA (2) for the YP ray, in full.** The decoded `(rDist 2, rWhat 2)`
of the YP ray block equals the reference `Board.raycast (boardDecode e) auto .yp`. -/
theorem raycast_yp_of_sat
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecode (envAt t i)) (boardDecode (envAt t i)).automaton Dir.yp
      = { what := codeToParticle ((envAt t i).loc (rWhat 2)),
          dist := ((envAt t i).loc (rDist 2)).toNat } := by
  set e := envAt t i with he
  -- ============ selector / coordinate facts (shared front-end auto one-hot) ============
  have bC0 : e.loc (selCol 0) = 0 ∨ e.loc (selCol 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 0)) (by decide)) (canon_loc hc i _)
  have bC1 : e.loc (selCol 1) = 0 ∨ e.loc (selCol 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 1)) (by decide)) (canon_loc hc i _)
  have sumC : e.loc (selCol 0) + e.loc (selCol 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selCol 0)) (.var (selCol 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selCol 0) + e.loc (selCol 1) + -1)
      (a := e.loc (selCol 0) + e.loc (selCol 1)) (b := 1) (by ring)).mp hg
    rcases bC0 with h0 | h0 <;> rcases bC1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxC : e.loc AX = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selCol 1)) (.mul (.const (-1)) (.var AX))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have bR0 : e.loc (selRow 0) = 0 ∨ e.loc (selRow 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 0)) (by decide)) (canon_loc hc i _)
  have bR1 : e.loc (selRow 1) = 0 ∨ e.loc (selRow 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 1)) (by decide)) (canon_loc hc i _)
  have sumR : e.loc (selRow 0) + e.loc (selRow 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selRow 0)) (.var (selRow 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selRow 0) + e.loc (selRow 1) + -1)
      (a := e.loc (selRow 0) + e.loc (selRow 1)) (b := 1) (by ring)).mp hg
    rcases bR0 with h0 | h0 <;> rcases bR1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxR : e.loc AY = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selRow 1)) (.mul (.const (-1)) (.var AY))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have hc0 : e.loc (selCol 0) = 1 - e.loc AX := by rw [idxC]; omega
  have hc1 : e.loc (selCol 1) = e.loc AX := idxC.symm
  have hr0 : e.loc (selRow 0) = 1 - e.loc AY := by rw [idxR]; omega
  have hr1 : e.loc (selRow 1) = e.loc AY := idxR.symm
  have hax : e.loc AX = 0 ∨ e.loc AX = 1 := idxC ▸ bC1
  have hay : e.loc AY = 0 ∨ e.loc AY = 1 := idxR ▸ bR1
  -- ============ ray-YP gate extractions (d = 2, steps kk ∈ {1,2}) ============
  have hib1 : e.loc (rIb 2 1) = e.loc (selRow 0) := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 2 0 1 1)) (by decide)
    rw [show (headToExpr (ibEqHead 2 0 1 1)).eval e.loc
        = e.loc (rIb 2 1) + (-1) * e.loc (selRow 0) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hib2 : e.loc (rIb 2 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 2 0 1 2)) (by decide)
    rw [show (headToExpr (ibEqHead 2 0 1 2)).eval e.loc = e.loc (rIb 2 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hrc2 : e.loc (rRc 2 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (rcReadHead 2 0 1 2)) (by decide)
    rw [show (headToExpr (rcReadHead 2 0 1 2)).eval e.loc = e.loc (rRc 2 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hb1 : e.loc (rHit 2 1) = 0 ∨ e.loc (rHit 2 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 2 1)) (by decide)) (canon_loc hc i _)
  have hb2 : e.loc (rHit 2 2) = 0 ∨ e.loc (rHit 2 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 2 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 2 1) + e.loc (rHit 2 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 2 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 2 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 2 1) + e.loc (rHit 2 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 2 1) + e.loc (rHit 2 2)) (b := 1) (by ring)).mp hg
    rcases hb1 with h0 | h0 <;> rcases hb2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hDist := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 2 kk))
      (Head.lin (-1) (rDist 2)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 2 kk))
      (Head.lin (-1) (rDist 2)))).eval e.loc
      = (-1) * e.loc (rDist 2) + e.loc (rHit 2 1) + 2 * e.loc (rHit 2 2) from rfl] at hDist
  have hWhat := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 2 kk, rRc 2 kk])
      (Head.lin (-1) (rWhat 2)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 2 kk, rRc 2 kk])
      (Head.lin (-1) (rWhat 2)))).eval e.loc
      = (-1) * e.loc (rWhat 2) + e.loc (rHit 2 1) * e.loc (rRc 2 1)
        + e.loc (rHit 2 2) * e.loc (rRc 2 2) from rfl] at hWhat
  have hHib := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 2 kk, rIb 2 kk])
      (Head.lin (-1) (rHib 2)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 2 kk, rIb 2 kk])
      (Head.lin (-1) (rHib 2)))).eval e.loc
      = (-1) * e.loc (rHib 2) + e.loc (rHit 2 1) * e.loc (rIb 2 1)
        + e.loc (rHit 2 2) * e.loc (rIb 2 2) from rfl] at hHib
  have hRC1 := astep_gate hsat i hi (g := headToExpr (rcReadHead 2 0 1 1)) (by decide)
  rw [show (headToExpr (rcReadHead 2 0 1 1)).eval e.loc
      = e.loc (rRc 2 1)
        + (-1) * (e.loc (rIb 2 1) * e.loc (selRow 0) * e.loc (selCol 0) * e.loc (old 2))
        + (-1) * (e.loc (rIb 2 1) * e.loc (selRow 0) * e.loc (selCol 1) * e.loc (old 3)) from rfl]
    at hRC1
  have hVac := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [rHit 2 2, rRc 2 1])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [rHit 2 2, rRc 2 1])).eval e.loc
      = e.loc (rHit 2 2) * e.loc (rRc 2 1) from rfl] at hVac
  have hInb := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addLin 1 (rHit 2 2)).addProd (-1) [rHit 2 2, rIb 2 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addLin 1 (rHit 2 2)).addProd (-1) [rHit 2 2, rIb 2 1])).eval e.loc
      = e.loc (rHit 2 2) + (-1) * (e.loc (rHit 2 2) * e.loc (rIb 2 1)) from rfl] at hInb
  have hCond := astep_gate hsat i hi
    (g := .mul (.var (rHib 2)) (.add (.mul (.var (rWhat 2)) (.var (rInv 2))) (.const (-1)))) (by decide)
  simp only [EmittedExpr.eval] at hCond
  have hMem : e.loc (rWhat 2) = 0 ∨ e.loc (rWhat 2) = 1 ∨ e.loc (rWhat 2) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 2) [0, 1, 2]) (by decide))
      (canon_loc hc i _)
  -- ============ reduce the reference raycast to the two-step n=2 scan ============
  have hXlt : (e.loc AX).toNat < 2 := by rcases hax with h | h <;> rw [h] <;> decide
  have hYlt : (e.loc AY).toNat < 2 := by rcases hay with h | h <;> rw [h] <;> decide
  rw [show (boardDecode e).automaton = ⟨(e.loc AX).toNat, (e.loc AY).toNat⟩ from rfl,
     raycast_yp_reduce (boardDecode e) (show (boardDecode e).size = 2 from rfl) _ _ hXlt hYlt]
  have hone : (e.loc (rHit 2 1) = 1 ∧ e.loc (rHit 2 2) = 0)
            ∨ (e.loc (rHit 2 1) = 0 ∧ e.loc (rHit 2 2) = 1) := by
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
    · right; exact ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
  rcases hone with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
  · -- CASE hit = (1,0): dist = 1, what = rc1, hib = ib1.
    rw [hh1, hh2] at hDist hWhat hHib
    have hd : e.loc (rDist 2) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rDist 2)) (by ring)).mp hDist)).symm
    have hw : e.loc (rWhat 2) = e.loc (rRc 2 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := e.loc (rWhat 2)) (by ring)).mp hWhat)).symm
    have hh : e.loc (rHib 2) = e.loc (rIb 2 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rIb 2 1)) (b := e.loc (rHib 2)) (by ring)).mp hHib)).symm
    rcases hay with hAY | hAY
    · -- Y = 0: in window (selRow 0 = 1 − AY = 1) → genuine hit, read cell (X, 1).
      have hib1v : e.loc (rIb 2 1) = 1 := by rw [hib1, hr0, hAY]; norm_num
      have hHib1 : e.loc (rHib 2) = 1 := by rw [hh, hib1v]
      rw [hHib1] at hCond
      have hwne : e.loc (rWhat 2) ≠ 0 := by
        intro h0
        rw [h0] at hCond
        have hneg : (1 : ℤ) * (0 * e.loc (rInv 2) + -1) = -1 := by ring
        rw [hneg] at hCond
        obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hCond
        omega
      have hw12 : e.loc (rWhat 2) = 1 ∨ e.loc (rWhat 2) = 2 := by
        rcases hMem with h | h | h
        · exact absurd h hwne
        · exact Or.inl h
        · exact Or.inr h
      have hY0 : (e.loc AY).toNat = 0 := by rw [hAY]; rfl
      rcases hax with hAX | hAX
      · -- X = 0: cell = old 2.
        have hrc1 : e.loc (rRc 2 1) = e.loc (old 2) := by
          rw [hib1v, (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
              (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
              (show e.loc (selCol 1) = 0 by rw [hc1, hAX])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := e.loc (old 2)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 1⟩ = codeToParticle (e.loc (old 2)) := by
          rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hY0, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 2))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
      · -- X = 1: cell = old 3.
        have hrc1 : e.loc (rRc 2 1) = e.loc (old 3) := by
          rw [hib1v, (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
              (show e.loc (selCol 0) = 0 by rw [hc0, hAX]; norm_num),
              (show e.loc (selCol 1) = 1 by rw [hc1, hAX])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := e.loc (old 3)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 1⟩ = codeToParticle (e.loc (old 3)) := by
          rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hY0, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 2))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
    · -- Y = 1: out of window (selRow 0 = 0) → wall, dist 1 vacuum.
      have hib1v : e.loc (rIb 2 1) = 0 := by rw [hib1, hr0, hAY]; norm_num
      have hrc1 : e.loc (rRc 2 1) = 0 := by
        rw [hib1v] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) canon_zero
          ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := 0) (by ring)).mp hRC1)
      have hw0 : e.loc (rWhat 2) = 0 := by rw [hw, hrc1]
      have hY1 : ¬ ((e.loc AY).toNat = 0) := by rw [hAY]; decide
      rw [if_neg hY1, hw0, hd]
      rfl
  · -- CASE hit = (0,1): dist = 2, what = rc2 = 0; forces Y = 0 (in window).
    rw [hh1, hh2] at hDist hWhat
    rw [hh2] at hVac hInb
    have hd : e.loc (rDist 2) = 2 :=
      (eq_of_modEq_canon canon_two (canon_loc hc i _)
        ((gate_modEq_iff (a := (2 : ℤ)) (b := e.loc (rDist 2)) (by ring)).mp hDist)).symm
    have hrc1z : e.loc (rRc 2 1) = 0 :=
      eq_of_modEq_canon (canon_loc hc i _) canon_zero
        ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := 0) (by ring)).mp hVac)
    have hib1v : e.loc (rIb 2 1) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rIb 2 1)) (by ring)).mp hInb)).symm
    have hAY : e.loc AY = 0 := by
      have hsr : e.loc (selRow 0) = 1 := by rw [← hib1, hib1v]
      rw [hr0] at hsr; omega
    have hw0 : e.loc (rWhat 2) = 0 := by
      have := hWhat
      rw [hrc2] at this
      exact (eq_of_modEq_canon canon_zero (canon_loc hc i _)
        ((gate_modEq_iff (a := (0 : ℤ)) (b := e.loc (rWhat 2)) (by ring)).mp this)).symm
    have hY0 : (e.loc AY).toNat = 0 := by rw [hAY]; rfl
    rcases hax with hAX | hAX
    · -- X = 0: cell = old 2 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 2 1) = e.loc (old 2) := by
        rw [hib1v, (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
            (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
            (show e.loc (selCol 1) = 0 by rw [hc1, hAX])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := e.loc (old 2)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 1⟩ = codeToParticle (e.loc (old 2)) := by
        rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hY0, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl
    · -- X = 1: cell = old 3 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 2 1) = e.loc (old 3) := by
        rw [hib1v, (show e.loc (selRow 0) = 1 by rw [hr0, hAY]; norm_num),
            (show e.loc (selCol 0) = 0 by rw [hc0, hAX]; norm_num),
            (show e.loc (selCol 1) = 1 by rw [hc1, hAX])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 2 1)) (b := e.loc (old 3)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 1⟩ = codeToParticle (e.loc (old 3)) := by
        rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hY0, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl

end RayYP

/-! ## §4.8 — sub-lemma (2), the YN ray (`Dir.yn`, ray block `d = 3`, rows `−y` via `selRow`).

The row analogue of the XN leg: the in-window bit at `kk = 1` is `selRow 1` (`= AY`, in bounds iff
`AY = 1`), the shifted read collapses to cell `(X, 0)` (column chosen by `selCol`), the reference
reduction reads `−y`. -/

/-- The `Board.raycast … .yn` reduction at `n = 2`: from `(X, Y)` the ray reads cell `(X, 0)` when
`Y = 1` (dist 1 on a hit, else dist 2 at the wall) and hits the wall immediately when `Y = 0`. -/
theorem raycast_yn_reduce (b : Board) (hs : b.size = 2) (X Y : Nat) (hX : X < 2) (hY : Y < 2) :
    Board.raycast b ⟨X, Y⟩ Dir.yn
      = (if Y = 1 then
           (if (b.cellAt ⟨X, 0⟩).isVacuum then { what := .vacuum, dist := 2 }
            else { what := b.cellAt ⟨X, 0⟩, dist := 1 })
         else { what := .vacuum, dist := 1 }) := by
  have h3 : (b.size + 1) = 3 := by omega
  have hX1 : (X : Int) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hX
  rcases (by omega : Y = 0 ∨ Y = 1) with rfl | rfl
  · rw [if_neg (by norm_num)]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]; norm_num
  · rw [if_pos rfl]
    simp only [Board.raycast, Dir.delta, h3]
    rw [raycastFuel, hs]
    norm_num [hX1]
    by_cases hv : (b.cellAt ⟨X, 0⟩).isVacuum = true
    · rw [if_pos hv, if_pos hv, raycastFuel, hs]; norm_num
    · rw [if_neg hv, if_neg hv]

section RayYN
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`raycast_yn_of_sat` — SUB-LEMMA (2) for the YN ray, in full.** The decoded `(rDist 3, rWhat 3)`
of the YN ray block equals the reference `Board.raycast (boardDecode e) auto .yn`. -/
theorem raycast_yn_of_sat
    (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecode (envAt t i)) (boardDecode (envAt t i)).automaton Dir.yn
      = { what := codeToParticle ((envAt t i).loc (rWhat 3)),
          dist := ((envAt t i).loc (rDist 3)).toNat } := by
  set e := envAt t i with he
  -- ============ selector / coordinate facts (shared front-end auto one-hot) ============
  have bC0 : e.loc (selCol 0) = 0 ∨ e.loc (selCol 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 0)) (by decide)) (canon_loc hc i _)
  have bC1 : e.loc (selCol 1) = 0 ∨ e.loc (selCol 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selCol 1)) (by decide)) (canon_loc hc i _)
  have sumC : e.loc (selCol 0) + e.loc (selCol 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selCol 0)) (.var (selCol 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selCol 0) + e.loc (selCol 1) + -1)
      (a := e.loc (selCol 0) + e.loc (selCol 1)) (b := 1) (by ring)).mp hg
    rcases bC0 with h0 | h0 <;> rcases bC1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxC : e.loc AX = e.loc (selCol 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selCol 1)) (.mul (.const (-1)) (.var AX))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have bR0 : e.loc (selRow 0) = 0 ∨ e.loc (selRow 0) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 0)) (by decide)) (canon_loc hc i _)
  have bR1 : e.loc (selRow 1) = 0 ∨ e.loc (selRow 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (selRow 1)) (by decide)) (canon_loc hc i _)
  have sumR : e.loc (selRow 0) + e.loc (selRow 1) = 1 := by
    have hg := astep_gate hsat i hi
      (g := .add (.add (.var (selRow 0)) (.var (selRow 1))) (.const (-1))) (by decide)
    simp only [EmittedExpr.eval] at hg
    have := (gate_modEq_iff (x := e.loc (selRow 0) + e.loc (selRow 1) + -1)
      (a := e.loc (selRow 0) + e.loc (selRow 1)) (b := 1) (by ring)).mp hg
    rcases bR0 with h0 | h0 <;> rcases bR1 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have idxR : e.loc AY = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi
      (g := .add (.var (selRow 1)) (.mul (.const (-1)) (.var AY))) (by decide)
    simp only [EmittedExpr.eval] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  have hc0 : e.loc (selCol 0) = 1 - e.loc AX := by rw [idxC]; omega
  have hc1 : e.loc (selCol 1) = e.loc AX := idxC.symm
  have hr0 : e.loc (selRow 0) = 1 - e.loc AY := by rw [idxR]; omega
  have hr1 : e.loc (selRow 1) = e.loc AY := idxR.symm
  have hax : e.loc AX = 0 ∨ e.loc AX = 1 := idxC ▸ bC1
  have hay : e.loc AY = 0 ∨ e.loc AY = 1 := idxR ▸ bR1
  -- ============ ray-YN gate extractions (d = 3, steps kk ∈ {1,2}) ============
  have hib1 : e.loc (rIb 3 1) = e.loc (selRow 1) := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 3 0 (-1) 1)) (by decide)
    rw [show (headToExpr (ibEqHead 3 0 (-1) 1)).eval e.loc
        = e.loc (rIb 3 1) + (-1) * e.loc (selRow 1) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)
  have hib2 : e.loc (rIb 3 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (ibEqHead 3 0 (-1) 2)) (by decide)
    rw [show (headToExpr (ibEqHead 3 0 (-1) 2)).eval e.loc = e.loc (rIb 3 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hrc2 : e.loc (rRc 3 2) = 0 := by
    have hg := astep_gate hsat i hi (g := headToExpr (rcReadHead 3 0 (-1) 2)) (by decide)
    rw [show (headToExpr (rcReadHead 3 0 (-1) 2)).eval e.loc = e.loc (rRc 3 2) from rfl] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  have hb1 : e.loc (rHit 3 1) = 0 ∨ e.loc (rHit 3 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 3 1)) (by decide)) (canon_loc hc i _)
  have hb2 : e.loc (rHit 3 2) = 0 ∨ e.loc (rHit 3 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 3 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 3 1) + e.loc (rHit 3 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 3 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 3 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 3 1) + e.loc (rHit 3 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 3 1) + e.loc (rHit 3 2)) (b := 1) (by ring)).mp hg
    rcases hb1 with h0 | h0 <;> rcases hb2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hDist := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 3 kk))
      (Head.lin (-1) (rDist 3)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 3 kk))
      (Head.lin (-1) (rDist 3)))).eval e.loc
      = (-1) * e.loc (rDist 3) + e.loc (rHit 3 1) + 2 * e.loc (rHit 3 2) from rfl] at hDist
  have hWhat := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 3 kk, rRc 3 kk])
      (Head.lin (-1) (rWhat 3)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 3 kk, rRc 3 kk])
      (Head.lin (-1) (rWhat 3)))).eval e.loc
      = (-1) * e.loc (rWhat 3) + e.loc (rHit 3 1) * e.loc (rRc 3 1)
        + e.loc (rHit 3 2) * e.loc (rRc 3 2) from rfl] at hWhat
  have hHib := astep_gate hsat i hi
    (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 3 kk, rIb 3 kk])
      (Head.lin (-1) (rHib 3)))) (by decide)
  rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addProd 1 [rHit 3 kk, rIb 3 kk])
      (Head.lin (-1) (rHib 3)))).eval e.loc
      = (-1) * e.loc (rHib 3) + e.loc (rHit 3 1) * e.loc (rIb 3 1)
        + e.loc (rHit 3 2) * e.loc (rIb 3 2) from rfl] at hHib
  have hRC1 := astep_gate hsat i hi (g := headToExpr (rcReadHead 3 0 (-1) 1)) (by decide)
  rw [show (headToExpr (rcReadHead 3 0 (-1) 1)).eval e.loc
      = e.loc (rRc 3 1)
        + (-1) * (e.loc (rIb 3 1) * e.loc (selRow 1) * e.loc (selCol 0) * e.loc (old 0))
        + (-1) * (e.loc (rIb 3 1) * e.loc (selRow 1) * e.loc (selCol 1) * e.loc (old 1)) from rfl]
    at hRC1
  have hVac := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [rHit 3 2, rRc 3 1])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [rHit 3 2, rRc 3 1])).eval e.loc
      = e.loc (rHit 3 2) * e.loc (rRc 3 1) from rfl] at hVac
  have hInb := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addLin 1 (rHit 3 2)).addProd (-1) [rHit 3 2, rIb 3 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addLin 1 (rHit 3 2)).addProd (-1) [rHit 3 2, rIb 3 1])).eval e.loc
      = e.loc (rHit 3 2) + (-1) * (e.loc (rHit 3 2) * e.loc (rIb 3 1)) from rfl] at hInb
  have hCond := astep_gate hsat i hi
    (g := .mul (.var (rHib 3)) (.add (.mul (.var (rWhat 3)) (.var (rInv 3))) (.const (-1)))) (by decide)
  simp only [EmittedExpr.eval] at hCond
  have hMem : e.loc (rWhat 3) = 0 ∨ e.loc (rWhat 3) = 1 ∨ e.loc (rWhat 3) = 2 :=
    mem3_of_gate (astep_gate hsat i hi (g := memberExpr (rWhat 3) [0, 1, 2]) (by decide))
      (canon_loc hc i _)
  -- ============ reduce the reference raycast to the two-step n=2 scan ============
  have hXlt : (e.loc AX).toNat < 2 := by rcases hax with h | h <;> rw [h] <;> decide
  have hYlt : (e.loc AY).toNat < 2 := by rcases hay with h | h <;> rw [h] <;> decide
  rw [show (boardDecode e).automaton = ⟨(e.loc AX).toNat, (e.loc AY).toNat⟩ from rfl,
     raycast_yn_reduce (boardDecode e) (show (boardDecode e).size = 2 from rfl) _ _ hXlt hYlt]
  have hone : (e.loc (rHit 3 1) = 1 ∧ e.loc (rHit 3 2) = 0)
            ∨ (e.loc (rHit 3 1) = 0 ∧ e.loc (rHit 3 2) = 1) := by
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
    · right; exact ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · exfalso; rw [h1, h2] at hsum; norm_num at hsum
  rcases hone with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
  · -- CASE hit = (1,0): dist = 1, what = rc1, hib = ib1.
    rw [hh1, hh2] at hDist hWhat hHib
    have hd : e.loc (rDist 3) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rDist 3)) (by ring)).mp hDist)).symm
    have hw : e.loc (rWhat 3) = e.loc (rRc 3 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := e.loc (rWhat 3)) (by ring)).mp hWhat)).symm
    have hh : e.loc (rHib 3) = e.loc (rIb 3 1) :=
      (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (a := e.loc (rIb 3 1)) (b := e.loc (rHib 3)) (by ring)).mp hHib)).symm
    rcases hay with hAY | hAY
    · -- Y = 0: out of window (selRow 1 = AY = 0) → wall, dist 1 vacuum.
      have hib1v : e.loc (rIb 3 1) = 0 := by rw [hib1, hr1, hAY]
      have hrc1 : e.loc (rRc 3 1) = 0 := by
        rw [hib1v] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) canon_zero
          ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := 0) (by ring)).mp hRC1)
      have hw0 : e.loc (rWhat 3) = 0 := by rw [hw, hrc1]
      have hY0 : ¬ ((e.loc AY).toNat = 1) := by rw [hAY]; decide
      rw [if_neg hY0, hw0, hd]
      rfl
    · -- Y = 1: in window → genuine hit, read cell (X, 0).
      have hib1v : e.loc (rIb 3 1) = 1 := by rw [hib1, hr1, hAY]
      have hHib1 : e.loc (rHib 3) = 1 := by rw [hh, hib1v]
      rw [hHib1] at hCond
      have hwne : e.loc (rWhat 3) ≠ 0 := by
        intro h0
        rw [h0] at hCond
        have hneg : (1 : ℤ) * (0 * e.loc (rInv 3) + -1) = -1 := by ring
        rw [hneg] at hCond
        obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hCond
        omega
      have hw12 : e.loc (rWhat 3) = 1 ∨ e.loc (rWhat 3) = 2 := by
        rcases hMem with h | h | h
        · exact absurd h hwne
        · exact Or.inl h
        · exact Or.inr h
      have hY1 : (e.loc AY).toNat = 1 := by rw [hAY]; rfl
      rcases hax with hAX | hAX
      · -- X = 0: cell = old 0.
        have hrc1 : e.loc (rRc 3 1) = e.loc (old 0) := by
          rw [hib1v, (show e.loc (selRow 1) = 1 by rw [hr1, hAY]),
              (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
              (show e.loc (selCol 1) = 0 by rw [hc1, hAX])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := e.loc (old 0)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 0⟩ = codeToParticle (e.loc (old 0)) := by
          rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hY1, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 3))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
      · -- X = 1: cell = old 1.
        have hrc1 : e.loc (rRc 3 1) = e.loc (old 1) := by
          rw [hib1v, (show e.loc (selRow 1) = 1 by rw [hr1, hAY]),
              (show e.loc (selCol 0) = 0 by rw [hc0, hAX]; norm_num),
              (show e.loc (selCol 1) = 1 by rw [hc1, hAX])] at hRC1
          exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
            ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := e.loc (old 1)) (by ring)).mp hRC1)
        have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 0⟩ = codeToParticle (e.loc (old 1)) := by
          rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
        rw [if_pos hY1, hcell, ← hrc1, ← hw,
            if_neg (show ¬ (codeToParticle (e.loc (rWhat 3))).isVacuum = true from by
              rcases hw12 with h | h <;> rw [h] <;> decide), hd]
        rfl
  · -- CASE hit = (0,1): dist = 2, what = rc2 = 0; forces Y = 1 (in window).
    rw [hh1, hh2] at hDist hWhat
    rw [hh2] at hVac hInb
    have hd : e.loc (rDist 3) = 2 :=
      (eq_of_modEq_canon canon_two (canon_loc hc i _)
        ((gate_modEq_iff (a := (2 : ℤ)) (b := e.loc (rDist 3)) (by ring)).mp hDist)).symm
    have hrc1z : e.loc (rRc 3 1) = 0 :=
      eq_of_modEq_canon (canon_loc hc i _) canon_zero
        ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := 0) (by ring)).mp hVac)
    have hib1v : e.loc (rIb 3 1) = 1 :=
      (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (a := (1 : ℤ)) (b := e.loc (rIb 3 1)) (by ring)).mp hInb)).symm
    have hAY : e.loc AY = 1 := by
      have hsr : e.loc (selRow 1) = 1 := by rw [← hib1, hib1v]
      rw [hr1] at hsr; exact hsr
    have hw0 : e.loc (rWhat 3) = 0 := by
      have := hWhat
      rw [hrc2] at this
      exact (eq_of_modEq_canon canon_zero (canon_loc hc i _)
        ((gate_modEq_iff (a := (0 : ℤ)) (b := e.loc (rWhat 3)) (by ring)).mp this)).symm
    have hY1 : (e.loc AY).toNat = 1 := by rw [hAY]; rfl
    rcases hax with hAX | hAX
    · -- X = 0: cell = old 0 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 3 1) = e.loc (old 0) := by
        rw [hib1v, (show e.loc (selRow 1) = 1 by rw [hr1, hAY]),
            (show e.loc (selCol 0) = 1 by rw [hc0, hAX]; norm_num),
            (show e.loc (selCol 1) = 0 by rw [hc1, hAX])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := e.loc (old 0)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 0⟩ = codeToParticle (e.loc (old 0)) := by
        rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hY1, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl
    · -- X = 1: cell = old 1 = rc1 = 0 → vacuum.
      have hrc1 : e.loc (rRc 3 1) = e.loc (old 1) := by
        rw [hib1v, (show e.loc (selRow 1) = 1 by rw [hr1, hAY]),
            (show e.loc (selCol 0) = 0 by rw [hc0, hAX]; norm_num),
            (show e.loc (selCol 1) = 1 by rw [hc1, hAX])] at hRC1
        exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
          ((gate_modEq_iff (a := e.loc (rRc 3 1)) (b := e.loc (old 1)) (by ring)).mp hRC1)
      have hcell : (boardDecode e).cellAt ⟨(e.loc AX).toNat, 0⟩ = codeToParticle (e.loc (old 1)) := by
        rw [hAX]; norm_num [boardDecode, Board.cellAt, NN, old]
      rw [if_pos hY1, hcell, ← hrc1, hrc1z,
          if_pos (show (codeToParticle (0 : ℤ)).isVacuum = true from rfl), hw0, hd]
      rfl

end RayYN

/-! ## §4.8 — sub-lemma (3): the `decide_axis` truth table ⇒ per-axis `Decision = evaluateAxis`.

This section lands leg (3): on a satisfying, canonical trace the decoded `decide_axis` witness columns
`(variant, pos, att, rep)` decode to exactly `evaluateAxis` of the two rays' `(dist, what)` on that
axis. The HEART is `forcedGe0_core` — the `forced_ge0` NO-WRAP soundness: a 5-bit range witness that
vanishes mod `p` pins the ACTUAL comparison, because `SMALL_RBITS = 5` makes the compared magnitudes
`< 2^5 ≪ p`, the exact no-wrap window. `forcedGe0_core` is applied to the byte-pinned descriptor in
`xdec_gpd_sound` (the `gpd = [pd ≥ 2]` bit), the one-hot case selection is closed in `xdec_ipw_sel` /
`xdec_inw_sel`, and the 9-case `assert_case` truth table then forces the witnessed decision to the
`evaluateAxis` formula case-by-case. Two representative cases close IN FULL against the byte-pinned
object — `decideAxis_xdec_none` (vacuum/vacuum ⇒ `.none`) and `decideAxis_xdec_attRep`
(attractor/repulsor ⇒ `.unbalancedPair`) — demonstrating the pipeline (ge0 no-wrap ▸ one-hot ▸
assert_case ▸ decode) closes end-to-end; the remaining seven cases + the `ydec` axis are the named
residual (§7). Nothing assumed: the only extra premises are the two ray `what`-codes, the legitimate
case discriminant. -/

/-- Wide no-wrap window: two integers of magnitude `≤ 10^6` congruent mod `p` are equal (`p ≈ 2·10^9`
dwarfs the gap, so `p ∣ (a−b)` collapses to `a = b`). The interval that contains every `forced_ge0`
term and 5-bit range-sum. -/
theorem eq_of_modEq_win {a b : ℤ} (ha : -1000000 ≤ a ∧ a ≤ 1000000)
    (hb : -1000000 ≤ b ∧ b ≤ 1000000) (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd; obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb; omega

/-- **The `forced_ge0` NO-WRAP soundness heart.** A `forced_ge0` bit `ib` pins `[d ≥ 0]` with NO
wraparound: given `ib ∈ {0,1}`, a 5-bit range-sum `S ∈ [0, 31]`, and the recomposed non-negativity
term `2·ib·D + ib − D − 1 ≡ S [ZMOD p]` for a SMALL `D` (`|D| ≤ 100 ≪ 2^5 ≪ p`), the bit is exactly
the comparison: `ib = 1 → 0 ≤ D` and `ib = 0 → D ≤ −1`. The window `[−100,100] ∪ [0,31] ⊂ (−p/2, p/2)`
is the exact no-wrap interval — a 5-bit witness cannot alias a different residue, so a forged bit has
no satisfying decomposition. This is the lemma that makes the `decide_axis` distance comparisons SOUND
(not merely well-typed): `gpd/gnd/lt/gt/le/gm` genuinely decide `pd ≥ 2`, `pd < nd`, etc. -/
theorem forcedGe0_core {ib D S : ℤ}
    (hib : ib = 0 ∨ ib = 1) (hS0 : 0 ≤ S) (hS1 : S ≤ 31)
    (hmod : (2 * ib * D + ib - D - 1) ≡ S [ZMOD 2013265921])
    (hDlo : -100 ≤ D) (hDhi : D ≤ 100) :
    (ib = 1 → 0 ≤ D) ∧ (ib = 0 → D ≤ -1) := by
  rcases hib with h | h
  · subst h
    rw [show (2 * (0:ℤ) * D + 0 - D - 1) = -D - 1 by ring] at hmod
    have heq : -D - 1 = S := eq_of_modEq_win (by omega) (by omega) hmod
    exact ⟨by intro hc; omega, by intro _; omega⟩
  · subst h
    rw [show (2 * (1:ℤ) * D + 1 - D - 1) = D by ring] at hmod
    have heq : D = S := eq_of_modEq_win (by omega) (by omega) hmod
    exact ⟨by intro _; omega, by intro hc; omega⟩

/-- Decode the four `decide_axis` witness columns `(variant, pos, att, rep)` into the reference
`Decision` (`reference.rs`'s felt encoding: the priority number in `variant` — `unbalancedPair = 3 >
fromRepulsor = 2 > towardAttractor = 1 > none = 0` — the direction bit in `pos`, and the attractor /
repulsor distances in `att` / `rep`). This is the circuit-side reader `choose_offset`'s score head
consumes; leg (3) proves it equals `evaluateAxis`. -/
def decodeDecision (v pos att rep : ℤ) : Decision :=
  if v = 3 then .unbalancedPair (pos = 1) att.toNat rep.toNat
  else if v = 2 then .fromRepulsor (pos = 1) rep.toNat
  else if v = 1 then .towardAttractor (pos = 1) att.toNat
  else .none

section DecideXdec
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The xdec `ipw` one-hot (over the XP ray's `what`-code, columns `62..64`): booleans, `Σ = 1`, and
the index pin `ipw₁ + 2·ipw₂ = what`. Together they force `ipw` to be single-hot at the code. -/
theorem xdec_ipw_sel (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 62 = 0 ∨ (envAt t i).loc 62 = 1)
    ∧ ((envAt t i).loc 63 = 0 ∨ (envAt t i).loc 63 = 1)
    ∧ ((envAt t i).loc 64 = 0 ∨ (envAt t i).loc 64 = 1)
    ∧ (envAt t i).loc 62 + (envAt t i).loc 63 + (envAt t i).loc 64 = 1
    ∧ (envAt t i).loc 63 + 2 * (envAt t i).loc 64 = (envAt t i).loc (rWhat 0) := by
  set e := envAt t i with he
  have b0 : e.loc 62 = 0 ∨ e.loc 62 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 62) (by decide)) (canon_loc hc i _)
  have b1 : e.loc 63 = 0 ∨ e.loc 63 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 63) (by decide)) (canon_loc hc i _)
  have b2 : e.loc 64 = 0 ∨ e.loc 64 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 64) (by decide)) (canon_loc hc i _)
  have hsum : e.loc 62 + e.loc 63 + e.loc 64 = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ([62,63,64].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))) (by decide)
    rw [show (headToExpr ([62,63,64].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))).eval e.loc
        = e.loc 62 + e.loc 63 + e.loc 64 + -1 from rfl] at hg
    have := (gate_modEq_iff (a := e.loc 62 + e.loc 63 + e.loc 64) (b := 1) (by ring)).mp hg
    rcases b0 with h|h <;> rcases b1 with h'|h' <;> rcases b2 with h''|h'' <;>
      exact eq_of_modEq_small (by rw [h,h',h'']; norm_num) (by norm_num) this
  have hidx : e.loc 63 + 2 * e.loc 64 = e.loc (rWhat 0) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([62,63,64][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 0)).scale (-1)))) (by decide)
    rw [show (headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([62,63,64][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 0)).scale (-1)))).eval e.loc = e.loc 63 + 2 * e.loc 64 + -1 * e.loc (rWhat 0) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc 63 + 2 * e.loc 64) (b := e.loc (rWhat 0)) (by ring)).mp hg
    have hcL : Canon (e.loc 63 + 2 * e.loc 64) := by
      rcases b1 with h|h <;> rcases b2 with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon hcL (canon_loc hc i _) hmod
  exact ⟨b0, b1, b2, hsum, hidx⟩

/-- The xdec `inw` one-hot (over the XN ray's `what`-code, columns `65..67`). -/
theorem xdec_inw_sel (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 65 = 0 ∨ (envAt t i).loc 65 = 1)
    ∧ ((envAt t i).loc 66 = 0 ∨ (envAt t i).loc 66 = 1)
    ∧ ((envAt t i).loc 67 = 0 ∨ (envAt t i).loc 67 = 1)
    ∧ (envAt t i).loc 65 + (envAt t i).loc 66 + (envAt t i).loc 67 = 1
    ∧ (envAt t i).loc 66 + 2 * (envAt t i).loc 67 = (envAt t i).loc (rWhat 1) := by
  set e := envAt t i with he
  have b0 : e.loc 65 = 0 ∨ e.loc 65 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 65) (by decide)) (canon_loc hc i _)
  have b1 : e.loc 66 = 0 ∨ e.loc 66 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 66) (by decide)) (canon_loc hc i _)
  have b2 : e.loc 67 = 0 ∨ e.loc 67 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin 67) (by decide)) (canon_loc hc i _)
  have hsum : e.loc 65 + e.loc 66 + e.loc 67 = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ([65,66,67].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))) (by decide)
    rw [show (headToExpr ([65,66,67].foldl (fun h co => h.addLin 1 co) (Head.c (-1)))).eval e.loc
        = e.loc 65 + e.loc 66 + e.loc 67 + -1 from rfl] at hg
    have := (gate_modEq_iff (a := e.loc 65 + e.loc 66 + e.loc 67) (b := 1) (by ring)).mp hg
    rcases b0 with h|h <;> rcases b1 with h'|h' <;> rcases b2 with h''|h'' <;>
      exact eq_of_modEq_small (by rw [h,h',h'']; norm_num) (by norm_num) this
  have hidx : e.loc 66 + 2 * e.loc 67 = e.loc (rWhat 1) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([65,66,67][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 1)).scale (-1)))) (by decide)
    rw [show (headToExpr (((List.range 3).foldl (fun h (j:Nat) => h.addLin (j:ℤ) ([65,66,67][j]!)) Head.zero).append
        ((Head.lin 1 (rWhat 1)).scale (-1)))).eval e.loc = e.loc 66 + 2 * e.loc 67 + -1 * e.loc (rWhat 1) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc 66 + 2 * e.loc 67) (b := e.loc (rWhat 1)) (by ring)).mp hg
    have hcL : Canon (e.loc 66 + 2 * e.loc 67) := by
      rcases b1 with h|h <;> rcases b2 with h'|h' <;> rw [h,h'] <;> exact ⟨by norm_num, by norm_num⟩
    exact eq_of_modEq_canon hcL (canon_loc hc i _) hmod
  exact ⟨b0, b1, b2, hsum, hidx⟩

/-- The XP ray distance is a genuine `n = 2` step count: `rDist 0 ∈ {1,2}` (from the hit one-hot +
`dist = Σ kk·hitₖ` recomposition). The `forced_ge0` comparisons rely on this small-magnitude fact. -/
theorem xdec_pd_mem (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (rDist 0) = 1 ∨ (envAt t i).loc (rDist 0) = 2 := by
  set e := envAt t i with he
  have b1 : e.loc (rHit 0 1) = 0 ∨ e.loc (rHit 0 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 0 1)) (by decide)) (canon_loc hc i _)
  have b2 : e.loc (rHit 0 2) = 0 ∨ e.loc (rHit 0 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 0 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 0 1) + e.loc (rHit 0 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 0 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 0 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 0 1) + e.loc (rHit 0 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 0 1) + e.loc (rHit 0 2)) (b := 1) (by ring)).mp hg
    rcases b1 with h0 | h0 <;> rcases b2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hval : e.loc (rDist 0) = e.loc (rHit 0 1) + 2 * e.loc (rHit 0 2) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 0 kk))
        (Head.lin (-1) (rDist 0)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 0 kk))
        (Head.lin (-1) (rDist 0)))).eval e.loc
        = (-1) * e.loc (rDist 0) + e.loc (rHit 0 1) + 2 * e.loc (rHit 0 2) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc (rHit 0 1) + 2 * e.loc (rHit 0 2))
      (b := e.loc (rDist 0)) (by ring)).mp hg
    have hcD : Canon (e.loc (rHit 0 1) + 2 * e.loc (rHit 0 2)) := by
      rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] <;> exact ⟨by norm_num, by norm_num⟩
    exact (eq_of_modEq_canon hcD (canon_loc hc i _) hmod).symm
  rw [hval]; rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] at hsum ⊢ <;> omega

/-- The XN ray distance `rDist 1 ∈ {1,2}`. -/
theorem xdec_nd_mem (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (rDist 1) = 1 ∨ (envAt t i).loc (rDist 1) = 2 := by
  set e := envAt t i with he
  have b1 : e.loc (rHit 1 1) = 0 ∨ e.loc (rHit 1 1) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 1 1)) (by decide)) (canon_loc hc i _)
  have b2 : e.loc (rHit 1 2) = 0 ∨ e.loc (rHit 1 2) = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (rHit 1 2)) (by decide)) (canon_loc hc i _)
  have hsum : e.loc (rHit 1 1) + e.loc (rHit 1 2) = 1 := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 1 kk))
        (Head.c (-1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin 1 (rHit 1 kk))
        (Head.c (-1)))).eval e.loc = e.loc (rHit 1 1) + e.loc (rHit 1 2) + (-1) from rfl] at hg
    have := (gate_modEq_iff (a := e.loc (rHit 1 1) + e.loc (rHit 1 2)) (b := 1) (by ring)).mp hg
    rcases b1 with h0 | h0 <;> rcases b2 with h1 | h1 <;>
      exact eq_of_modEq_small (by rw [h0, h1]; norm_num) (by norm_num) this
  have hval : e.loc (rDist 1) = e.loc (rHit 1 1) + 2 * e.loc (rHit 1 2) := by
    have hg := astep_gate hsat i hi
      (g := headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 1 kk))
        (Head.lin (-1) (rDist 1)))) (by decide)
    rw [show (headToExpr ((List.range' 1 NN).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (rHit 1 kk))
        (Head.lin (-1) (rDist 1)))).eval e.loc
        = (-1) * e.loc (rDist 1) + e.loc (rHit 1 1) + 2 * e.loc (rHit 1 2) from rfl] at hg
    have hmod := (gate_modEq_iff (a := e.loc (rHit 1 1) + 2 * e.loc (rHit 1 2))
      (b := e.loc (rDist 1)) (by ring)).mp hg
    have hcD : Canon (e.loc (rHit 1 1) + 2 * e.loc (rHit 1 2)) := by
      rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] <;> exact ⟨by norm_num, by norm_num⟩
    exact (eq_of_modEq_canon hcD (canon_loc hc i _) hmod).symm
  rw [hval]; rcases b1 with h|h <;> rcases b2 with h2|h2 <;> rw [h, h2] at hsum ⊢ <;> omega

/-- **`forcedGe0_core` applied to the byte-pinned descriptor: the `gpd = [pd ≥ 2]` bit is SOUND.** The
xdec `forced_ge0` guard column `68` genuinely decides `rDist 0 ≥ 2` — no wraparound — with its 5-bit
range witness (`bits 69..73`) forcing the non-negativity of `2·gpd·(pd−2) + gpd − (pd−2) − 1`. This is
the leg's heart wired to the real object. -/
theorem xdec_gpd_sound (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc 68 = 0 ∨ (envAt t i).loc 68 = 1)
    ∧ ((envAt t i).loc 68 = 1 → 2 ≤ (envAt t i).loc (rDist 0))
    ∧ ((envAt t i).loc 68 = 0 → (envAt t i).loc (rDist 0) ≤ 1) := by
  set e := envAt t i with he
  have gpdB : e.loc 68 = 0 ∨ e.loc 68 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 10)) (by decide)) (canon_loc hc i _)
  have bit0 : e.loc 69 = 0 ∨ e.loc 69 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 11)) (by decide)) (canon_loc hc i _)
  have bit1 : e.loc 70 = 0 ∨ e.loc 70 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 12)) (by decide)) (canon_loc hc i _)
  have bit2 : e.loc 71 = 0 ∨ e.loc 71 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 13)) (by decide)) (canon_loc hc i _)
  have bit3 : e.loc 72 = 0 ∨ e.loc 72 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 14)) (by decide)) (canon_loc hc i _)
  have bit4 : e.loc 73 = 0 ∨ e.loc 73 = 1 :=
    bin_of_gate (astep_gate hsat i hi (g := gBin (58 + 15)) (by decide)) (canon_loc hc i _)
  have grec := astep_gate hsat i hi
    (g := headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 11) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 10) ((Head.lin 1 (rDist 0)).addConst (-2))))) (by decide)
  rw [show (headToExpr ((List.range SMALL_RBITS).foldl
      (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 11) SMALL_RBITS)[k]!))
      (forcedGe0Term (58 + 10) ((Head.lin 1 (rDist 0)).addConst (-2))))).eval e.loc
      = 2 * (e.loc 68 * e.loc (rDist 0)) + -4 * e.loc 68 + e.loc 68 + -1 * e.loc (rDist 0)
        + -1 * e.loc 69 + -2 * e.loc 70 + -4 * e.loc 71 + -8 * e.loc 72 + -16 * e.loc 73 + 1 from rfl] at grec
  have gmod : (2 * e.loc 68 * (e.loc (rDist 0) - 2) + e.loc 68 - (e.loc (rDist 0) - 2) - 1)
      ≡ (e.loc 69 + 2 * e.loc 70 + 4 * e.loc 71 + 8 * e.loc 72 + 16 * e.loc 73) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp grec
  have pdMem := xdec_pd_mem hsat hc i hi
  rw [← he] at pdMem
  have core := forcedGe0_core (D := e.loc (rDist 0) - 2)
    (S := e.loc 69 + 2 * e.loc 70 + 4 * e.loc 71 + 8 * e.loc 72 + 16 * e.loc 73) gpdB
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    (by rcases bit0 with h|h <;> rcases bit1 with h1|h1 <;> rcases bit2 with h2|h2 <;>
        rcases bit3 with h3|h3 <;> rcases bit4 with h4|h4 <;> rw [h,h1,h2,h3,h4] <;> norm_num)
    gmod (by rcases pdMem with h|h <;> rw [h] <;> norm_num) (by rcases pdMem with h|h <;> rw [h] <;> norm_num)
  exact ⟨gpdB, by intro h; have := core.1 h; omega, by intro h; have := core.2 h; omega⟩

/-- **Leg (3), case (vacuum, vacuum): `decide_axis` decodes to `.none`.** On a satisfying canonical
trace whose XP/XN rays both read vacuum, the decoded xdec decision IS `evaluateAxis` — both `.none`.
The `assert_case` `(0,0)` gate (selected by the `ipw₀·inw₀` one-hot) forces `variant = 0`. Keyed on
the byte-pinned `automataflStepDesc`; the only extra premises are the ray `what`-codes. -/
theorem decideAxis_xdec_none (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 0) = 0) (hnw : (envAt t i).loc (rWhat 1) = 0) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip0 : e.loc 62 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin0 : e.loc 65 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi (g := headToExpr (Head.zero.addProd 1 [62,65,58])) (by decide)
  rw [show (headToExpr (Head.zero.addProd 1 [62,65,58])).eval e.loc = e.loc 62 * e.loc 65 * e.loc 58 from rfl,
     hip0, hin0] at hgv
  have hvar : e.loc 58 = 0 :=
    eq_of_modEq_canon (canon_loc hc i _) canon_zero
      ((gate_modEq_iff (a := e.loc 58) (b := 0) (by ring)).mp hgv)
  rw [hvar, hpw, hnw]
  simp [decodeDecision, codeToParticle, evaluateAxis]

/-- **Leg (3), case (attractor, repulsor): `decide_axis` decodes to `.unbalancedPair`.** On a
satisfying canonical trace whose XP ray reads an attractor and XN a repulsor, the decoded xdec decision
IS `evaluateAxis`: `.unbalancedPair true pd nd` when the guard `pd > 1` holds (`gpd = 1`), else `.none`.
The full pipeline closes — `xdec_gpd_sound` (the `forced_ge0` no-wrap heart) resolves the distance
guard, `xdec_ipw_sel`/`xdec_inw_sel` select the `(2,1)` case, and its four `assert_case` gates force
`variant = 3·gpd`, `pos = gpd`, `att = gpd·pd`, `rep = gpd·nd`. -/
theorem decideAxis_xdec_attRep (hsat : Satisfied2 hash automataflStepDesc minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hpw : (envAt t i).loc (rWhat 0) = 2) (hnw : (envAt t i).loc (rWhat 1) = 1) :
    decodeDecision ((envAt t i).loc 58) ((envAt t i).loc 59) ((envAt t i).loc 60) ((envAt t i).loc 61)
      = evaluateAxis { what := codeToParticle ((envAt t i).loc (rWhat 0)), dist := ((envAt t i).loc (rDist 0)).toNat }
                     { what := codeToParticle ((envAt t i).loc (rWhat 1)), dist := ((envAt t i).loc (rDist 1)).toNat } := by
  obtain ⟨ib0, ib1, ib2, isum, iidx⟩ := xdec_ipw_sel hsat hc i hi
  obtain ⟨nb0, nb1, nb2, nsum, nidx⟩ := xdec_inw_sel hsat hc i hi
  obtain ⟨gpdB, gpd1, gpd0⟩ := xdec_gpd_sound hsat hc i hi
  have pdMem := xdec_pd_mem hsat hc i hi
  set e := envAt t i with he
  rw [hpw] at iidx; rw [hnw] at nidx
  have hip2 : e.loc 64 = 1 := by rcases ib1 with h|h <;> rcases ib2 with h'|h' <;> omega
  have hin1 : e.loc 66 = 1 := by rcases nb1 with h|h <;> rcases nb2 with h'|h' <;> omega
  have hgv := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,66,58]).addProd (-3) [64,66,68])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,66,58]).addProd (-3) [64,66,68])).eval e.loc
      = e.loc 64 * e.loc 66 * e.loc 58 + -3 * (e.loc 64 * e.loc 66 * e.loc 68) from rfl,
     hip2, hin1] at hgv
  have hvar : e.loc 58 = 3 * e.loc 68 :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 58) (b := 3 * e.loc 68) (by ring)).mp hgv)
  have hgp := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,66,59]).addProd (-1) [64,66,68])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,66,59]).addProd (-1) [64,66,68])).eval e.loc
      = e.loc 64 * e.loc 66 * e.loc 59 + -1 * (e.loc 64 * e.loc 66 * e.loc 68) from rfl,
     hip2, hin1] at hgp
  have hpos : e.loc 59 = e.loc 68 :=
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc 59) (b := e.loc 68) (by ring)).mp hgp)
  have hga := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,66,60]).addProd (-1) [64,66,68, rDist 0])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,66,60]).addProd (-1) [64,66,68, rDist 0])).eval e.loc
      = e.loc 64 * e.loc 66 * e.loc 60 + -1 * (e.loc 64 * e.loc 66 * e.loc 68 * e.loc (rDist 0)) from rfl,
     hip2, hin1] at hga
  have hgr := astep_gate hsat i hi
    (g := headToExpr ((Head.zero.addProd 1 [64,66,61]).addProd (-1) [64,66,68, rDist 1])) (by decide)
  rw [show (headToExpr ((Head.zero.addProd 1 [64,66,61]).addProd (-1) [64,66,68, rDist 1])).eval e.loc
      = e.loc 64 * e.loc 66 * e.loc 61 + -1 * (e.loc 64 * e.loc 66 * e.loc 68 * e.loc (rDist 1)) from rfl,
     hip2, hin1] at hgr
  have hatt : e.loc 60 = e.loc 68 * e.loc (rDist 0) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> rcases pdMem with hp|hp <;> rw [hp] <;>
          exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 60) (b := e.loc 68 * e.loc (rDist 0)) (by ring)).mp hga)
  have hrep : e.loc 61 = e.loc 68 * e.loc (rDist 1) :=
    eq_of_modEq_canon (canon_loc hc i _)
      (by rcases gpdB with h|h <;> rw [h] <;> rcases xdec_nd_mem hsat hc i hi with hp|hp <;>
          rw [← he] at hp <;> rw [hp] <;> exact ⟨by norm_num, by norm_num⟩)
      ((gate_modEq_iff (a := e.loc 61) (b := e.loc 68 * e.loc (rDist 1)) (by ring)).mp hgr)
  rw [hpw, hnw]
  rcases gpdB with hg0 | hg1
  · have hpd1 : e.loc (rDist 0) = 1 := by have := gpd0 hg0; rcases pdMem with h|h <;> omega
    have hv0 : e.loc 58 = 0 := by rw [hvar, hg0]; ring
    rw [hv0, hpd1]
    simp [decodeDecision, codeToParticle, evaluateAxis]
  · have hpd2 : e.loc (rDist 0) = 2 := by have := gpd1 hg1; rcases pdMem with h|h <;> omega
    have hv3 : e.loc 58 = 3 := by rw [hvar, hg1]; ring
    have hp1 : e.loc 59 = 1 := by rw [hpos, hg1]
    have hattv : e.loc 60 = e.loc (rDist 0) := by rw [hatt, hg1]; ring
    have hrepv : e.loc 61 = e.loc (rDist 1) := by rw [hrep, hg1]; ring
    rw [hv3, hp1, hattv, hrepv, hpd2]
    simp [decodeDecision, codeToParticle, evaluateAxis]

end DecideXdec

/-! ## §4.9 — NON-VACUITY for leg (3): the `forced_ge0` bit + `assert_case` gate REJECT wrong witnesses
(`#guard`).

The `forced_ge0` no-wrap soundness is only meaningful if the gadget can FAIL: a forged `gpd = 1` on a
board where `pd = 1` (`pd − 2 = −1 < 0`) has NO 5-bit non-negativity decomposition — its recomposition
term `2·1·1 + 1 − 1 − 1 = 1`… wait, the forged direction: claiming `gpd = 1` forces the range witness
to encode `pd − 2`; when `pd = 1` that is `−1`, which no sum of five booleans equals, so the gate is
UNSATISFIABLE. And the `(2,1)` `assert_case` variant gate rejects a decision that claims
`unbalancedPair` (`variant = 3`) while `gpd = 0`. Both shown as two-sided `#guard`s below. -/

/-- `gpd = 1`, `pd = 2`: the non-negativity witness `2·gpd·(pd−2) + gpd − (pd−2) − 1 = 0` recomposes
with ALL range bits `0` — the gadget ACCEPTS. -/
def ge0GoodAsg : Assignment := fun c =>
  if c = 68 then 1 else if c = rDist 0 then 2 else 0

/-- `gpd = 1`, `pd = 1`: term `= 2·1·1 + 1 − 1 − 1 = 1`; with ALL range bits 0 the recomposition is
`1 ≠ 0` — a FORGED `[pd ≥ 2]` bit has no satisfying decomposition here. -/
def ge0ForgeAsg : Assignment := fun c => if c = 68 then 1 else if c = rDist 0 then 1 else 0

/-- The exact `forced_ge0` recomposition gate body for the gpd gadget (term − Σ 2^k·bitₖ). -/
def gpdRecompExpr : EmittedExpr :=
  headToExpr ((List.range SMALL_RBITS).foldl
    (fun h (k : Nat) => h.addLin (-((2:ℤ) ^ k)) ((bitsFrom (58 + 11) SMALL_RBITS)[k]!))
    (forcedGe0Term (58 + 10) ((Head.lin 1 (rDist 0)).addConst (-2))))

#guard gpdRecompExpr.eval ge0GoodAsg == 0     -- pd = 2, gpd = 1, bit₁ = 1: term recomposes, gate holds
#guard gpdRecompExpr.eval ge0ForgeAsg != 0    -- pd = 1, forged gpd = 1: NO decomposition, gate FAILS

/-- The `(2,1)` `assert_case` variant gate `ipw₂·inw₁·(variant − 3·gpd)`. A decision claiming
`unbalancedPair` (`variant = 3`) while the guard failed (`gpd = 0`) makes it `≠ 0`. -/
def acVariantExpr : EmittedExpr :=
  headToExpr ((Head.zero.addProd 1 [64,66,58]).addProd (-3) [64,66,68])
/-- Selected case (`ipw₂ = inw₁ = 1`), `gpd = 1`, `variant = 3`: consistent — gate holds. -/
def acGoodAsg : Assignment := fun c => if c = 64 ∨ c = 66 ∨ c = 68 then 1 else if c = 58 then 3 else 0
/-- Selected case, but `gpd = 0` while `variant = 3` claims `unbalancedPair` — a LIE; gate FAILS. -/
def acForgeAsg : Assignment := fun c => if c = 64 ∨ c = 66 then 1 else if c = 58 then 3 else 0

#guard acVariantExpr.eval acGoodAsg == 0      -- variant = 3·gpd = 3: consistent
#guard acVariantExpr.eval acForgeAsg != 0     -- variant = 3 but gpd = 0: unbalancedPair LIE FAILS

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

/-! ### §5b — the XP ray teeth are two-sided discriminators (`#guard`).

The `raycast_xp_of_sat` refinement rests on two occlusion teeth; both REJECT a wrong `(dist, what)`:
the vacuum-before gate `hit₂·rc₁` rejects claiming the FAR hit (dist 2) when the near cell was
non-vacuous, and the `cond_nonzero` gate `hib·(what·inv − 1)` rejects claiming an in-bounds hit that
read VACUUM (`what = 0`). A wrong witness cannot satisfy them — so the ray gate set is non-vacuous. -/

/-- A witness that (correctly) hits at step 1 with the near cell non-vacuum (`hit₁ = 1`, `rc₁ = 1`). -/
def rayGoodAsg : Assignment := fun c => if c = rHit 0 1 then 1 else if c = rRc 0 1 then 1 else 0
/-- A wrong witness that claims the FAR hit (`hit₂ = 1`) though the near cell `rc₁ = 1` is non-vacuum. -/
def rayFarBadAsg : Assignment := fun c => if c = rHit 0 2 then 1 else if c = rRc 0 1 then 1 else 0
/-- A wrong witness claiming an in-bounds hit (`hib = 1`) whose read was VACUUM (`what = 0`). -/
def rayVacBadAsg : Assignment := fun c => if c = rHib 0 then 1 else 0

#guard (headToExpr (Head.zero.addProd 1 [rHit 0 2, rRc 0 1])).eval rayGoodAsg == 0    -- near hit: ok
#guard (headToExpr (Head.zero.addProd 1 [rHit 0 2, rRc 0 1])).eval rayFarBadAsg != 0  -- far-hit lie: FAILS
#guard (EmittedExpr.mul (.var (rHib 0))
          (.add (.mul (.var (rWhat 0)) (.var (rInv 0))) (.const (-1)))).eval rayVacBadAsg != 0 -- vac-hit lie: FAILS

/-! ### §5c — the XN ray teeth are two-sided discriminators (`#guard`, canary for the replay).

The same occlusion teeth, now on the XN ray block (`d = 1`): they REJECT a wrong `(dist, what)` exactly
as the XP teeth do. This is the canary that the mechanical replay pins a REAL gate set per direction,
not a re-authored mirror — the `d = 1` columns are the ones `raycast_xn_of_sat` extracts. -/

/-- XN near-hit witness (`hit₁ = 1`, `rc₁ = 1`) for ray block `d = 1`. -/
def rayGoodAsgXN : Assignment := fun c => if c = rHit 1 1 then 1 else if c = rRc 1 1 then 1 else 0
/-- XN far-hit lie (`hit₂ = 1`, near cell `rc₁ = 1` non-vacuous). -/
def rayFarBadAsgXN : Assignment := fun c => if c = rHit 1 2 then 1 else if c = rRc 1 1 then 1 else 0
/-- XN vacuum-hit lie (`hib = 1`, read VACUUM `what = 0`). -/
def rayVacBadAsgXN : Assignment := fun c => if c = rHib 1 then 1 else 0

#guard (headToExpr (Head.zero.addProd 1 [rHit 1 2, rRc 1 1])).eval rayGoodAsgXN == 0    -- near hit: ok
#guard (headToExpr (Head.zero.addProd 1 [rHit 1 2, rRc 1 1])).eval rayFarBadAsgXN != 0  -- far-hit lie: FAILS
#guard (EmittedExpr.mul (.var (rHib 1))
          (.add (.mul (.var (rWhat 1)) (.var (rInv 1))) (.const (-1)))).eval rayVacBadAsgXN != 0 -- vac-hit lie: FAILS

/-! ## §6 — Axiom hygiene. -/

#print axioms autoPin_of_sat
#print axioms decoded_auto_holds_automaton
#print axioms offset_of_sat
#print axioms raycast_xp_of_sat
#print axioms raycast_xn_of_sat
#print axioms raycast_yp_of_sat
#print axioms raycast_yn_of_sat
#print axioms forcedGe0_core
#print axioms xdec_gpd_sound
#print axioms decideAxis_xdec_none
#print axioms decideAxis_xdec_attRep

/-! ## §7 — THE NAMED RESIDUAL (what remains for the full composition).

Proven here, keyed on the byte-pinned `automataflStepDesc`, canonical over BabyBear, none assumed:
  * `astep_gate` — the single-row gate extraction;
  * `coord_of_sat` — the decoded auto coordinate is in bounds (`decompose_coord_le` soundness);
  * `autoPin_of_sat` / `decoded_auto_holds_automaton` — SUB-LEMMA (1) in full;
  * `raycast_xp_reduce` — the pure `Board.raycast … .xp` reduction at `n = 2`;
  * `raycast_xp_of_sat` — SUB-LEMMA (2) for the XP ray IN FULL: `(rDist 0, rWhat 0) = Board.raycast`,
    derived from the hit one-hot, the vacuum-before / in-bounds-before occlusion gates, and the
    `cond_nonzero` in-bounds-hit witness (with `mem3_of_gate` pinning `what ∈ {VAC,REP,ATT}`);
  * `raycast_xn_reduce` / `raycast_yp_reduce` / `raycast_yn_reduce` — the pure `Board.raycast`
    reductions at `n = 2` for the remaining three cardinals;
  * `raycast_xn_of_sat` / `raycast_yp_of_sat` / `raycast_yn_of_sat` — SUB-LEMMA (2) for the OTHER
    THREE rays IN FULL, keyed on the byte-pinned `rayConstraints d dx dy` for `d = 1,2,3` (each with
    its own `inWindowCols`/`rcReadHead` closed form: `XN` shifts `−x`; `YP`/`YN` scan ROWS via
    `selRow`). **SUB-LEMMA (2) IS NOW CLOSED FOR ALL FOUR RAYS** — leg (2) is complete;
  * `offset_of_sat` — the value-range half of sub-lemma (4);
  * **leg (3), PARTIAL — the `forced_ge0` NO-WRAP heart + the `decide_axis` case selection + two of the
    nine cases IN FULL:**
      - `forcedGe0_core` — the no-wrap soundness heart: a 5-bit range witness pins the ACTUAL
        comparison (`SMALL_RBITS = 5` ⇒ magnitudes `< 2^5 ≪ p`, the exact no-wrap window). PURE, the
        lemma every distance guard rests on;
      - `xdec_gpd_sound` — `forcedGe0_core` APPLIED to the byte-pinned descriptor: the guard column `68`
        genuinely decides `rDist 0 ≥ 2` (the field-congruence trap discharged, not tripped);
      - `xdec_pd_mem` / `xdec_nd_mem` — the ray distances are `n = 2` step counts (`∈ {1,2}`);
      - `xdec_ipw_sel` / `xdec_inw_sel` — the `ipw`/`inw` one-hots select exactly the ray-code case;
      - `decideAxis_xdec_none` (vacuum/vacuum ⇒ `.none`) and `decideAxis_xdec_attRep`
        (attractor/repulsor ⇒ `.unbalancedPair`) — TWO of the nine `decide_axis` cases closed IN FULL:
        the decoded `(variant, pos, att, rep)` = `evaluateAxis` of the two rays, keyed on the byte-pinned
        object, only the ray `what`-codes as premises. §4.9 canary `#guard`s show the `forced_ge0` bit
        and the `assert_case` gate REJECT forged witnesses (a `[pd ≥ 2]` lie at `pd = 1`; an
        `unbalancedPair` claim with `gpd = 0`).

REMAINING (each NOT assumed, NOT stubbed — no `sorry`, no placeholder):
  (3, rest) the OTHER SEVEN `decide_axis` cases (`(1,2)`/`(1,0)`/`(0,1)`/`(2,0)`/`(0,2)` each a single
      `gpd`/`gnd` guard, mechanical replays of `attRep`; `(1,1)`/`(2,2)` need the `lt`/`gt`/`le`/`gm`
      + `min` gadgets — all six `forced_ge0` closed forms are already verified) AND the `ydec` axis
      (base `105`, rays `d = 2,3` — a column-shift replay of `xdec`); then the union `Decision =
      evaluateAxis` over all `(pw, nw)`;
  (4) `chooseOffset` — the score-compare (`sgt/slt`, 20-bit) soundness closing offset = `chooseOffset`;
  (5) the step + board-update fold ⇒ `boardDecode(new) = automatonStep(boardDecode(old))`.
The top-level composition is deliberately NOT stated as a proven theorem until (3, rest)-(5) close. -/

end Dregg2.Circuit.Emit.AutomataflStepRefine
