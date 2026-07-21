/-
# Dregg2.Circuit.Emit.AccumulatorNonRevocationComplete — the COMPLETENESS leg (SEM ⟹ SAT) of the
alpha-batch NON-REVOCATION **accumulator** whole-descriptor bridge, composed with the committed
soundness leg (`AccumulatorNonRevocationRefine`) into a two-direction accept-set characterization.

## What the committed soundness bridge gave us and what this file adds

`AccumulatorNonRevocationRefine.lean` proves SOUNDNESS: a trace SATISFYING `accumulatorNonRevDesc`
(`Satisfied2`) genuinely CERTIFIES non-membership of each active row's ancestor against the public
accumulator — `Satisfied2 ⟹ NonMemberCertified`, with the remainder nonzero IN THE FIELD. That is
SAT ⟹ SEM.

This file proves the COMPLEMENTARY half — COMPLETENESS (SEM ⟹ SAT): from a genuine non-membership
certificate carrying the prover's inverse witness (`NonMemberWitness alpha acc h`: the quotient `w`,
the remainder `v`, and its field inverse `vinv` with `acc = w⊗(alpha⊖h)⊕v` and `v⊗vinv = 1`), a
witness trace GENUINELY SATISFYING the deployed `Satisfied2` EXISTS — every gate discharged, the
carriers (the empty mem/map legs) BUILT AND PROVEN, not assumed. The construction is PARAMETRIC over
`(alpha, acc, h, w, v, vinv)` — not one hard-coded witness (the committed file already carries one
concrete inhabitant `accSat`; this generalizes it to every certified instance).

## The witness relation vs. Refine's `NonMemberCertified` (the honest ⟺ shape)

The deployed `check` gate binds `check = v·vinv` AND `check = (1,0,0,0)` — the AIR genuinely REQUIRES
an inverse witness `vinv` for `v`. So the completeness input is `NonMemberWitness` (which CARRIES
`vinv`), the prover's full witness. It is strictly informative over Refine's `NonMemberCertified`
(`∃ w v, … ∧ v ≠ 0`): `witness_implies_certified` forgets `vinv` and recovers `v ≠ 0` from the unit
gate (`unit_not_modEq_ezero`, no primality). The converse — bare `v ≠ 0 ⟹ ∃ vinv` — is the deployed
`BabyBear^4 = F_p[X]/(X⁴−11)` FIELD invertibility (`X⁴−11` irreducible over BabyBear); it is a TRUE
property of the deployment, NOT a refuted floor, and it is NOT needed here: the accept-set ⟺ closes
WITHOUT it because a satisfying trace already CARRIES `vinv` in its `V_INV` column
(`sat_implies_witness_public` reads it back, via the emit file's `check` = `v·vinv` = `1` gates).

## The accept-set ⟺ (the honest, per-relation two-direction result)

A literal per-trace `Satisfied2 ↔ NonMemberWitness` degenerates (a trace and a relation are different
objects). The honest ⟺ is on the ACCEPT-SET (`Accepts`):

    Accepts alpha acc h  ↔  NonMemberWitness alpha acc h        (`accepts_iff`)

  * ⟸ COMPLETENESS (`witness_implies_accepts`): from the certificate BUILD a satisfying trace whose
    public accumulator/challenge are `acc`/`alpha` and whose active row reads `h`.
  * ⟹ SOUNDNESS-to-witness (`sat_implies_witness_public`): from ANY satisfying trace + active row,
    read back the FULL witness (quotient `QUOTIENT`, remainder `REMAINDER`, inverse `V_INV`) — the
    inverse recovered from the trace, no abstract field invertibility.

`accumNonRev_roundtrip` runs BOTH legs end-to-end: from a certificate it builds a trace, then feeds
it into Refine's SOUNDNESS bridge to recover the literal `NonMemberCertified alpha acc h`.

## Non-vacuity + the sweep finding (the anti-scar)
  * `certSat` CONSTRUCTS a satisfying trace parametrically (every gate proven, not a rubber stamp);
    `witness_demo` / `roundtrip_demo` discharge a concrete inhabited instance (`7 = 2·(10−7)+1`,
    `v = 1 ≠ 0`).
  * `member_not_witnessed` — a genuine MEMBER (`h = alpha`, `acc = 0`) is NOT certified: the recovered
    relation is two-valued (via Refine's `member_not_certified`).
  * `certTamper_check_fails` — a certified instance mutated to `check = 0` (a member's vanishing
    remainder) FAILS `Satisfied2` (the `check` gate bites), mirroring Refine's `badTrace_rejected` /
    the sweep's `sem_fail` canary.
  * SWEEP FINDING: the accumulator SOUNDNESS (and this completeness) rest on NO hash floor — the AIR
    uses no Poseidon2 chip / no range lookup (`tables = []`, `hashSites = []`), so neither
    `Poseidon2SpongeCR` nor `compressNInjective` (both FALSE at BabyBear params) enters. The
    non-membership content is the polynomial-division certificate + the unit `check` gate; NON-VACUOUS,
    NOT resting on a refuted floor.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`/`axiom`/`native_decide`; the
carriers are constructed (the empty mem/map legs), never assumed. NEW file; it rides ON TOP of the
co-tenant felt-width restructure (`AccumulatorNonRevocationRefine`/`Emit`), read-only over both.
-/
import Dregg2.Circuit.Emit.AccumulatorNonRevocationRefine

namespace Dregg2.Circuit.Emit.AccumulatorNonRevocationComplete

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowConstraint WindowExpr Satisfied2 VmTrace envAt
   memLog mapLog memOpsOf mapOpsOf memCheck_nil)
open Dregg2.Circuit.Emit.AccumulatorNonRevocationEmit
open Dregg2.Circuit.Emit.AccumulatorNonRevocationRefine
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff eqToModEq)

set_option autoImplicit false

/-! ## §1 — the completeness input: the certificate WITH its inverse witness (what the AIR needs). -/

/-- **`NonMemberWitness alpha acc h`** — the FULL prover certificate the `check` gate requires: a
quotient `w`, a remainder `v`, and `v`'s field inverse `vinv`, with `acc = w⊗(alpha⊖h)⊕v` (AS FIELD
elements) and `v⊗vinv = 1` (so `v` is a UNIT, hence nonzero). Strictly informative over Refine's
`NonMemberCertified` (which only asserts `v ≠ 0` existentially); `witness_implies_certified` forgets
`vinv`. -/
def NonMemberWitness (alpha acc h : Ext) : Prop :=
  ∃ w v vinv : Ext,
    ExtModEq acc (eadd (emul w (esub alpha h)) v) ∧ ExtModEq (emul v vinv) eone

/-- The witness relation implies Refine's `NonMemberCertified` — drop `vinv`, recover `v ≠ 0` from
the unit gate (`unit_not_modEq_ezero`, no primality). So the completeness result composes with the
soundness bridge stated over `NonMemberCertified`. -/
theorem witness_implies_certified {alpha acc h : Ext} (hw : NonMemberWitness alpha acc h) :
    NonMemberCertified alpha acc h := by
  obtain ⟨w, v, vinv, hacc, hchk⟩ := hw
  exact ⟨w, v, hacc, unit_not_modEq_ezero v vinv hchk⟩

/-- `NonMemberWitness` respects the field congruence in ALL THREE slots (the ring ops are `ExtModEq`
congruences), so the row-local certificate transfers to congruent public values. -/
theorem nonmemberWitness_congr {alpha alpha' acc acc' hsh hsh' : Ext}
    (ha : ExtModEq alpha alpha') (hc : ExtModEq acc acc') (hh : ExtModEq hsh hsh')
    (hn : NonMemberWitness alpha acc hsh) : NonMemberWitness alpha' acc' hsh' := by
  obtain ⟨w, v, vinv, heq, hchk⟩ := hn
  exact ⟨w, v, vinv,
    hc.symm.trans (heq.trans (eadd_congr
      (emul_congr (ExtModEq.refl _) (esub_congr ha hh)) (ExtModEq.refl _))), hchk⟩

/-! ## §2 — SOUNDNESS-to-witness: a satisfying trace CARRIES the full witness (inverse from V_INV). -/

section SoundnessWitness

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable (hsat : Satisfied2 hash accumulatorNonRevDesc minit mfin maddrs t)
include hsat

/-- On any active row, the FULL witness is read out of the trace: `w = QUOTIENT`, `v = REMAINDER`,
`vinv = V_INV`, with the accumulator chain (C1..C3 + `sum==acc`) and the unit equation
(`check = v·vinv` ⊗ `check = 1`) — the inverse comes FROM the trace, no abstract field invertibility. -/
theorem sat_implies_witness_aux (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length) :
    NonMemberWitness (col4 (envAt t i).loc ALPHA_AUX) (col4 (envAt t i).loc ACC_AUX)
      (col4 (envAt t i).loc HASH) := by
  refine ⟨col4 (envAt t i).loc QUOTIENT, col4 (envAt t i).loc REMAINDER,
    col4 (envAt t i).loc V_INV, ?_, ?_⟩
  · exact (col_accEq hsat i hi hlast).symm.trans
      ((col_sum hsat i hi hlast).trans
        (eadd_congr
          ((col_prod hsat i hi hlast).trans
            (emul_congr (ExtModEq.refl _) (col_diff hsat i hi hlast)))
          (ExtModEq.refl _)))
  · exact (col_check hsat i hi hlast).symm.trans (col_check1 hsat i hi hlast)

/-- **SOUNDNESS-to-witness (SAT ⟹ the FULL witness, tied to the PUBLIC inputs).** For every active
row, the ancestor is `NonMemberWitness` against the PUBLIC accumulator `(col4 pub PI_ACC)` and
challenge `(col4 pub PI_ALPHA)` — the ⟹ leg of the accept-set ⟺. -/
theorem sat_implies_witness_public (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length) :
    NonMemberWitness (col4 t.pub PI_ALPHA) (col4 t.pub PI_ACC) (col4 (envAt t i).loc HASH) :=
  nonmemberWitness_congr (pub_alpha hsat i hi) (pub_acc hsat i hi) (ExtModEq.refl _)
    (sat_implies_witness_aux hsat i hi hlast)

end SoundnessWitness

/-! ## §3 — the PARAMETRIC completeness construction (row, pub, trace). -/

/-- The single active main-row assignment for the certificate `(alpha, acc, h, w, v, vinv)`. Fills
every declared column with its honest value: the ancestor `h`, quotient `w`, remainder `v`, the
difference `alpha−h`, the product `w·(alpha−h)`, the sum `prod+v` (pinned to `Acc`), the inverse
`vinv`, the constant `check = (1,0,0,0)`, and the two aux copies `alpha`/`acc`. -/
def certRow (alpha acc h w v vinv : Ext) : Assignment := fun n =>
  -- HASH 0..3
  if n = 0 then h.c0 else if n = 1 then h.c1 else if n = 2 then h.c2 else if n = 3 then h.c3
  -- QUOTIENT 4..7
  else if n = 4 then w.c0 else if n = 5 then w.c1 else if n = 6 then w.c2 else if n = 7 then w.c3
  -- REMAINDER 8..11
  else if n = 8 then v.c0 else if n = 9 then v.c1 else if n = 10 then v.c2 else if n = 11 then v.c3
  -- DIFF 12..15  (alpha − h)
  else if n = 12 then alpha.c0 - h.c0 else if n = 13 then alpha.c1 - h.c1
  else if n = 14 then alpha.c2 - h.c2 else if n = 15 then alpha.c3 - h.c3
  -- PRODUCT 16..19  (w · (alpha − h))
  else if n = 16 then (emul w (esub alpha h)).c0 else if n = 17 then (emul w (esub alpha h)).c1
  else if n = 18 then (emul w (esub alpha h)).c2 else if n = 19 then (emul w (esub alpha h)).c3
  -- SUM 20..23  (prod + v)
  else if n = 20 then (emul w (esub alpha h)).c0 + v.c0 else if n = 21 then (emul w (esub alpha h)).c1 + v.c1
  else if n = 22 then (emul w (esub alpha h)).c2 + v.c2 else if n = 23 then (emul w (esub alpha h)).c3 + v.c3
  -- V_INV 24..27
  else if n = 24 then vinv.c0 else if n = 25 then vinv.c1 else if n = 26 then vinv.c2 else if n = 27 then vinv.c3
  -- CHECK 28..31  (= (1,0,0,0))
  else if n = 28 then 1 else if n = 29 then 0 else if n = 30 then 0 else if n = 31 then 0
  -- ALPHA_AUX 32..35
  else if n = 32 then alpha.c0 else if n = 33 then alpha.c1 else if n = 34 then alpha.c2 else if n = 35 then alpha.c3
  -- ACC_AUX 36..39
  else if n = 36 then acc.c0 else if n = 37 then acc.c1 else if n = 38 then acc.c2 else if n = 39 then acc.c3
  else 0

/-- The public inputs: `Acc` at `PI_ACC = 0..3`, `alpha` at `PI_ALPHA = 4..7`. -/
def certPub (alpha acc : Ext) : Assignment := fun k =>
  if k = 0 then acc.c0 else if k = 1 then acc.c1 else if k = 2 then acc.c2 else if k = 3 then acc.c3
  else if k = 4 then alpha.c0 else if k = 5 then alpha.c1 else if k = 6 then alpha.c2 else if k = 7 then alpha.c3
  else 0

/-- The concrete 2-row certificate trace. Row 0 is a GENUINE ACTIVE row (`0+1 ≠ 2`); row 1 is the
wrap row (identical, so the `.boundary .last` twins fire on it). -/
def certTrace (alpha acc h w v vinv : Ext) : VmTrace :=
  { rows := [certRow alpha acc h w v vinv, certRow alpha acc h w v vinv]
  , pub  := certPub alpha acc
  , tf   := fun _ => [] }

theorem certTrace_len (alpha acc h w v vinv : Ext) :
    (certTrace alpha acc h w v vinv).rows.length = 2 := rfl

/-! ## §4 — the per-gate evaluations on the parametric row (the arithmetic core). -/

theorem certRow_c1 (alpha acc h w v vinv : Ext) (j : Nat) (hj : j < 4) :
    (c1Body j).eval (certRow alpha acc h w v vinv) = 0 := by
  interval_cases j <;>
    · simp only [c1Body, coeffVar, EmittedExpr.eval, HASH, DIFF, ALPHA_AUX]
      norm_num [certRow]; ring

theorem certRow_c2 (alpha acc h w v vinv : Ext) (j : Nat) (hj : j < 4) :
    (extMulLane PRODUCT QUOTIENT DIFF j).eval (certRow alpha acc h w v vinv) = 0 := by
  interval_cases j <;>
    · simp only [extMulLane, coeffVar, coeffMul, EmittedExpr.eval, W, PRODUCT, QUOTIENT, DIFF]
      norm_num [certRow, emul, esub]; ring

theorem certRow_c3 (alpha acc h w v vinv : Ext) (j : Nat) (hj : j < 4) :
    (c3Body j).eval (certRow alpha acc h w v vinv) = 0 := by
  interval_cases j <;>
    · simp only [c3Body, coeffVar, EmittedExpr.eval, SUM, PRODUCT, REMAINDER]
      norm_num [certRow]

theorem certRow_checkOne (alpha acc h w v vinv : Ext) (j : Nat) (hj : j < 4) :
    (checkOneBody j).eval (certRow alpha acc h w v vinv) = 0 := by
  interval_cases j <;>
    · norm_num [checkOneBody, coeffVar, EmittedExpr.eval, CHECK, certRow]

/-- The C4 (`check = v·vinv`) gate holds mod `p` — from the unit hypothesis `v⊗vinv ≡ (1,0,0,0)`. -/
theorem certRow_c4 (alpha acc h w v vinv : Ext) (hchk : ExtModEq (emul v vinv) eone)
    (j : Nat) (hj : j < 4) :
    (extMulLane CHECK REMAINDER V_INV j).eval (certRow alpha acc h w v vinv) ≡ 0 [ZMOD 2013265921] := by
  interval_cases j
  · refine (gate_modEq_iff (a := eone.c0) (b := (emul v vinv).c0) ?_).mpr hchk.1.symm
    simp only [extMulLane, coeffVar, coeffMul, EmittedExpr.eval, W, CHECK, REMAINDER, V_INV]
    norm_num [certRow, emul, eone]; ring
  · refine (gate_modEq_iff (a := eone.c1) (b := (emul v vinv).c1) ?_).mpr hchk.2.1.symm
    simp only [extMulLane, coeffVar, coeffMul, EmittedExpr.eval, W, CHECK, REMAINDER, V_INV]
    norm_num [certRow, emul, eone]; ring
  · refine (gate_modEq_iff (a := eone.c2) (b := (emul v vinv).c2) ?_).mpr hchk.2.2.1.symm
    simp only [extMulLane, coeffVar, coeffMul, EmittedExpr.eval, W, CHECK, REMAINDER, V_INV]
    norm_num [certRow, emul, eone]; ring
  · refine (gate_modEq_iff (a := eone.c3) (b := (emul v vinv).c3) ?_).mpr hchk.2.2.2.symm
    simp only [extMulLane, coeffVar, coeffMul, EmittedExpr.eval, CHECK, REMAINDER, V_INV]
    norm_num [certRow, emul, eone]; ring

/-- The `sum == acc_aux` binding holds mod `p` — from `acc ≡ w⊗(alpha⊖h)⊕v`. -/
theorem certRow_sumAcc (alpha acc h w v vinv : Ext)
    (hacc : ExtModEq acc (eadd (emul w (esub alpha h)) v)) (j : Nat) (hj : j < 4) :
    (sumAccBody j).eval (certRow alpha acc h w v vinv) ≡ 0 [ZMOD 2013265921] := by
  interval_cases j
  · refine (gate_modEq_iff (a := (eadd (emul w (esub alpha h)) v).c0) (b := acc.c0) ?_).mpr hacc.1.symm
    simp only [sumAccBody, coeffVar, EmittedExpr.eval, SUM, ACC_AUX]
    norm_num [certRow, eadd]; ring
  · refine (gate_modEq_iff (a := (eadd (emul w (esub alpha h)) v).c1) (b := acc.c1) ?_).mpr hacc.2.1.symm
    simp only [sumAccBody, coeffVar, EmittedExpr.eval, SUM, ACC_AUX]
    norm_num [certRow, eadd]; ring
  · refine (gate_modEq_iff (a := (eadd (emul w (esub alpha h)) v).c2) (b := acc.c2) ?_).mpr hacc.2.2.1.symm
    simp only [sumAccBody, coeffVar, EmittedExpr.eval, SUM, ACC_AUX]
    norm_num [certRow, eadd]; ring
  · refine (gate_modEq_iff (a := (eadd (emul w (esub alpha h)) v).c3) (b := acc.c3) ?_).mpr hacc.2.2.2.symm
    simp only [sumAccBody, coeffVar, EmittedExpr.eval, SUM, ACC_AUX]
    norm_num [certRow, eadd]; ring

/-- The aux-constancy window body vanishes: both rows are identical, so `next[c] − loc[c] = 0`. -/
theorem certRow_const (alpha acc h w v vinv : Ext) (c : Nat) :
    (constBody c).eval (envAt (certTrace alpha acc h w v vinv) 0) = 0 := by
  simp only [constBody, WindowExpr.eval, envAt, certTrace, List.getD_cons_zero,
    List.getD_cons_succ]
  ring

/-! ## §5 — the completeness core: the deployed `Satisfied2` is genuinely inhabited, parametrically. -/

theorem memLogC_nil (alpha acc h w v vinv : Ext) :
    memLog accumulatorNonRevDesc (certTrace alpha acc h w v vinv) = [] := memLog_nil _

theorem mapLogC_nil (alpha acc h w v vinv : Ext) :
    mapLog accumulatorNonRevDesc (certTrace alpha acc h w v vinv) = [] := mapLog_nil _

set_option maxHeartbeats 4000000 in
/-- **`certSat` — THE COMPLETENESS CORE (SEM ⟹ SAT), PARAMETRIC.** For every certificate
`(alpha, acc, h, w, v, vinv)` with `acc ≡ w⊗(alpha⊖h)⊕v` and `v⊗vinv ≡ (1,0,0,0)`, the constructed
two-row trace GENUINELY SATISFIES the deployed whole-trace denotation `Satisfied2` of
`accumulatorNonRevDesc`: C1..C4 / sum / check / pins / constancy fire on the active row 0, the
`.boundary .last` twins fire on the wrap row 1, and the empty mem/map legs close. So the soundness
bridge's `Satisfied2` hypothesis is inhabited PARAMETRICALLY, not by one example. -/
theorem certSat (alpha acc h w v vinv : Ext)
    (hacc : ExtModEq acc (eadd (emul w (esub alpha h)) v)) (hchk : ExtModEq (emul v vinv) eone) :
    Satisfied2 (fun _ => 0) accumulatorNonRevDesc (fun _ => 0) (fun _ => (0, 0)) []
      (certTrace alpha acc h w v vinv) where
  rowConstraints := by
    intro i hi
    rw [certTrace_len] at hi
    interval_cases i
    · -- row 0: active (isFirst = true, isLast = false).  Each constraint reduces DEFINITIONALLY.
      simp only [accumulatorNonRevDesc, List.forall_mem_append, and_assoc]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact eqToModEq (certRow_c1 alpha acc h w v vinv _ (by decide))
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact eqToModEq (certRow_c2 alpha acc h w v vinv _ (by decide))
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact eqToModEq (certRow_c3 alpha acc h w v vinv _ (by decide))
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact certRow_c4 alpha acc h w v vinv hchk _ (by decide)
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact certRow_sumAcc alpha acc h w v vinv hacc _ (by decide)
      · -- sumAccLast: vacuous on the active row 0
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> (intro hb; rw [certTrace_len] at hb; exact absurd hb (by decide))
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact eqToModEq (certRow_checkOne alpha acc h w v vinv _ (by decide))
      · -- checkOneLast: vacuous on row 0
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> (intro hb; rw [certTrace_len] at hb; exact absurd hb (by decide))
      · -- alphaPins: reflexive on row 0
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact fun _ => eqToModEq rfl
      · -- accPins: reflexive on row 0
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact fun _ => eqToModEq rfl
      · -- alphaConst: constancy = 0 on row 0
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact fun _ => eqToModEq (certRow_const alpha acc h w v vinv _)
      · -- accConst: constancy = 0 on row 0
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact fun _ => eqToModEq (certRow_const alpha acc h w v vinv _)
    · -- row 1: wrap (isFirst = false, isLast = true).
      simp only [accumulatorNonRevDesc, List.forall_mem_append, and_assoc]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact trivial
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact trivial
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact trivial
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact trivial
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact trivial
      · -- sumAccLast: FIRES on the wrap row 1 (mod p via hacc)
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact fun _ => certRow_sumAcc alpha acc h w v vinv hacc _ (by decide)
      · intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact trivial
      · -- checkOneLast: FIRES on row 1 (exact)
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact fun _ => eqToModEq (certRow_checkOne alpha acc h w v vinv _ (by decide))
      · -- alphaPins: vacuous on row 1 (isFirst = false)
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact fun hb => absurd hb (by decide)
      · -- accPins: vacuous on row 1
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> exact fun hb => absurd hb (by decide)
      · -- alphaConst: vacuous on the wrap row 1 (isLast = true)
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> (intro hb; rw [certTrace_len] at hb; exact absurd hb (by decide))
      · -- accConst: vacuous on row 1
        intro c hc; obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc; have hj := List.mem_range.mp hjm
        interval_cases j <;> (intro hb; rw [certTrace_len] at hb; exact absurd hb (by decide))
  rowHashes := by intro i hi; exact trivial
  rowRanges := by intro i hi r hr; simp [accumulatorNonRevDesc] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLogC_nil] at hop; simp at hop
  memDisciplined := by rw [memLogC_nil]; trivial
  memBalanced := by rw [memLogC_nil]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLogC_nil]; rfl
  mapTableFaithful := by rw [mapLogC_nil]; rfl

/-! ## §6 — the packaged completeness statement + the accept-set ⟺ + the round-trip. -/

/-- **`accumNonRev_sem_implies_sat` — existential completeness.** For every certificate there EXISTS
a trace that (a) genuinely satisfies the deployed `Satisfied2`, and (b) reads back the intended
public `alpha`/`acc` and active-row `h`. The complement of Refine's `Satisfied2 ⟹ NonMemberCertified`. -/
theorem accumNonRev_sem_implies_sat (alpha acc h w v vinv : Ext)
    (hacc : ExtModEq acc (eadd (emul w (esub alpha h)) v)) (hchk : ExtModEq (emul v vinv) eone) :
    ∃ t : VmTrace,
      Satisfied2 (fun _ => 0) accumulatorNonRevDesc (fun _ => 0) (fun _ => (0, 0)) [] t
      ∧ 0 < t.rows.length ∧ 0 + 1 ≠ t.rows.length
      ∧ ExtModEq (col4 t.pub PI_ALPHA) alpha ∧ ExtModEq (col4 t.pub PI_ACC) acc
      ∧ ExtModEq (col4 (envAt t 0).loc HASH) h :=
  ⟨certTrace alpha acc h w v vinv, certSat alpha acc h w v vinv hacc hchk,
   by have h2 := certTrace_len alpha acc h w v vinv; omega,
   by have h2 := certTrace_len alpha acc h w v vinv; omega,
   ExtModEq.refl _, ExtModEq.refl _, ExtModEq.refl _⟩

/-- **The accept-set predicate.** `alpha acc h` is ACCEPTED iff some satisfying trace has public
accumulator/challenge congruent to `acc`/`alpha` and a genuine active row reading `h`. -/
def Accepts (alpha acc h : Ext) : Prop :=
  ∃ (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (i : Nat),
    Satisfied2 hash accumulatorNonRevDesc minit mfin maddrs t
    ∧ i < t.rows.length ∧ i + 1 ≠ t.rows.length
    ∧ ExtModEq (col4 t.pub PI_ALPHA) alpha ∧ ExtModEq (col4 t.pub PI_ACC) acc
    ∧ ExtModEq (col4 (envAt t i).loc HASH) h

/-- Completeness ⟹ acceptance: a certificate BUILDS an accepting trace. -/
theorem witness_implies_accepts {alpha acc h : Ext} (hw : NonMemberWitness alpha acc h) :
    Accepts alpha acc h := by
  obtain ⟨w, v, vinv, hacc, hchk⟩ := hw
  refine ⟨fun _ => 0, fun _ => 0, fun _ => (0, 0), [], certTrace alpha acc h w v vinv, 0,
    certSat alpha acc h w v vinv hacc hchk, ?_, ?_, ExtModEq.refl _, ExtModEq.refl _, ExtModEq.refl _⟩
  · have h2 := certTrace_len alpha acc h w v vinv; omega
  · have h2 := certTrace_len alpha acc h w v vinv; omega

/-- Acceptance ⟹ certificate: an accepting trace CARRIES the full witness (inverse from `V_INV`). -/
theorem accepts_implies_witness {alpha acc h : Ext} (ha : Accepts alpha acc h) :
    NonMemberWitness alpha acc h := by
  obtain ⟨hash, minit, mfin, maddrs, t, i, hsat, hi, hlast, hpa, hpc, hph⟩ := ha
  exact nonmemberWitness_congr hpa hpc hph (sat_implies_witness_public hsat i hi hlast)

/-- **`accepts_iff` — THE ACCEPT-SET ⟺.** The descriptor's accept-set IS exactly the non-membership
certificate relation, in BOTH directions: soundness (a trace's public data is a certificate) and
completeness (a certificate is realized by a trace). The honest two-direction result the byte-pinned
emit could not, on its own, establish. -/
theorem accepts_iff (alpha acc h : Ext) :
    Accepts alpha acc h ↔ NonMemberWitness alpha acc h :=
  ⟨accepts_implies_witness, witness_implies_accepts⟩

/-- **`accumNonRev_roundtrip` — THE TWO-DIRECTION COMPOSITION.** From any certificate, BUILD a
satisfying trace (this file's completeness), then FEED it back through Refine's SOUNDNESS bridge
(`sat_implies_nonmember_public`) to recover the literal `NonMemberCertified alpha acc h` on the public
accumulator/challenge. Descriptor accepts the built witness AND its acceptance re-derives the semantic
non-membership — accept-set and spec agree in both directions. -/
theorem accumNonRev_roundtrip (alpha acc h w v vinv : Ext)
    (hacc : ExtModEq acc (eadd (emul w (esub alpha h)) v)) (hchk : ExtModEq (emul v vinv) eone) :
    NonMemberCertified alpha acc h :=
  -- `col4 (certPub alpha acc) PI_ALPHA = alpha`, `… PI_ACC = acc`, `col4 (row 0) HASH = h` (all rfl).
  sat_implies_nonmember_public (certSat alpha acc h w v vinv hacc hchk) 0
    (by have h2 := certTrace_len alpha acc h w v vinv; omega)
    (by have h2 := certTrace_len alpha acc h w v vinv; omega)

/-! ## §7 — non-vacuity + the two-valued canary (the anti-scar). -/

/-- The certificate hypotheses are jointly SATISFIABLE — `alpha=(10,·)`, `acc=(7,·)`, `h=(7,·)`,
`w=(2,·)`, `v=(1,·)`, `vinv=(1,·)`: `7 = 2·(10−7)+1`, `1·1 = 1`. So completeness is not vacuously
quantified. -/
theorem witness_demo :
    NonMemberWitness ⟨10, 0, 0, 0⟩ ⟨7, 0, 0, 0⟩ ⟨7, 0, 0, 0⟩ :=
  ⟨⟨2, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩,
    ⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩⟩

/-- **The round-trip on the inhabited instance is a genuine non-membership certificate** (`h=(7,·)`
absent from the accumulator `(7,·)` at challenge `(10,·)`), BUILT from a satisfying trace, not
asserted — the anti-vacuity capstone matching Refine's `accTrace_nonmember`. -/
theorem roundtrip_demo :
    NonMemberCertified ⟨10, 0, 0, 0⟩ ⟨7, 0, 0, 0⟩ ⟨7, 0, 0, 0⟩ :=
  accumNonRev_roundtrip ⟨10, 0, 0, 0⟩ ⟨7, 0, 0, 0⟩ ⟨7, 0, 0, 0⟩ ⟨2, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩

/-- **Witness FALSE — the recovered relation CONSTRAINS.** A genuine MEMBER (`h = alpha`, `acc = 0`)
is NOT witnessed — the accept-set is two-valued (via Refine's `member_not_certified`), so a `True` /
`P → P` bridge could not separate this. -/
theorem member_not_witnessed (alpha : Ext) : ¬ NonMemberWitness alpha ezero alpha :=
  fun hw => member_not_certified alpha (witness_implies_certified hw)

/-- The certificate trace mutated so `check = 0` (a member's vanishing remainder) instead of
`(1,0,0,0)`. -/
def certTraceTampered (alpha acc h w v vinv : Ext) : VmTrace :=
  { certTrace alpha acc h w v vinv with
    rows := [ fun n => if n = CHECK then 0 else certRow alpha acc h w v vinv n
            , fun n => if n = CHECK then 0 else certRow alpha acc h w v vinv n ] }

/-- **A certified instance mutated to `check = 0` FAILS `Satisfied2` (the `check` gate BITES),
PARAMETRICALLY.** The lane-0 `check == 1` gate residual is `0 − 1 = −1 ≢ 0 [ZMOD p]` on the active
row, so no satisfying trace has `check = 0`. Together with `certSat` (a genuine inhabitant) this shows
the deployed denotation is TWO-VALUED — a tamper canary mirroring Refine's `badTrace_rejected` and the
sweep's `sem_fail`. -/
theorem certTamper_check_fails (alpha acc h w v vinv : Ext) :
    ¬ Satisfied2 (fun _ => 0) accumulatorNonRevDesc (fun _ => 0) (fun _ => (0, 0)) []
        (certTraceTampered alpha acc h w v vinv) := by
  intro hsat
  have hlen : (certTraceTampered alpha acc h w v vinv).rows.length = 2 := rfl
  have hg := gate_of_active hsat 0 (by omega) (by omega) _ (mem_checkOne 0 (by decide))
  rw [show checkOneBody 0 = .add (coeffVar 1 (CHECK + 0)) (.const (-1)) from rfl] at hg
  simp only [coeffVar, EmittedExpr.eval] at hg
  have hz : (envAt (certTraceTampered alpha acc h w v vinv) 0).loc (CHECK + 0) = 0 := by
    simp only [certTraceTampered, envAt, List.getD_cons_zero]
    norm_num [CHECK]
  have hval : (1 : ℤ) * (envAt (certTraceTampered alpha acc h w v vinv) 0).loc (CHECK + 0) + -1 = -1 := by
    rw [hz]; norm_num
  rw [hval] at hg
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hg
  omega

/-! ## §8 — axiom hygiene. -/

#assert_axioms certSat
#assert_axioms accumNonRev_sem_implies_sat
#assert_axioms sat_implies_witness_public
#assert_axioms accepts_iff
#assert_axioms accumNonRev_roundtrip
#assert_axioms witness_demo
#assert_axioms roundtrip_demo
#assert_axioms member_not_witnessed
#assert_axioms certTamper_check_fails

end Dregg2.Circuit.Emit.AccumulatorNonRevocationComplete
