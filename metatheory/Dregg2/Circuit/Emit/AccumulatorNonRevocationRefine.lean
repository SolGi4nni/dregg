/-
# Dregg2.Circuit.Emit.AccumulatorNonRevocationRefine — the WHOLE-DESCRIPTOR functional-correctness
bridge for the alpha-batch NON-REVOCATION accumulator (Rung 1).

## What Rung 0 gave, and what this file adds

`AccumulatorNonRevocationEmit.lean` byte-pins the emitted descriptor `accumulatorNonRevDesc` and proves
per-GATE lemmas (each constraint poly = 0 ↔ its LOCAL relation: `alpha_constancy_zero_iff`,
`accum_row_binding`, `check0_forces_one`). Those are gate-local. This file proves the WHOLE-DESCRIPTOR
bridge: a trace SATISFYING the descriptor (`DescriptorIR2.Satisfied2`) genuinely CERTIFIES NON-MEMBERSHIP
of each active row's ancestor hash against the public accumulator — the functional spec the AIR computes.

## The NO_LEAN case: authoring the missing functional spec

The census dossier flags `accumulator` as NO_LEAN for THIS descriptor: the pre-existing accumulator model
(`AccumulatorOpenEmit` / `AccumulatorInsertEmit`) models a CATEGORICALLY DIFFERENT object — a
sorted-Poseidon2 Merkle SET-INSERT — not this rational-function non-revocation batch AIR. So there is no
model to weld to; we FIRST author the semantic relation, THEN prove the refinement.

### The semantic relation (`NonMemberCertified`)

The revocation set `{h_j}` is committed by the public accumulator `Acc = P(alpha)`, `P(X) = ∏(X − h_j)`,
evaluated at the public challenge `alpha`, both living in the extension field `BabyBear^4 =
BabyBear[X]/(X^4 − 11)` (modelled here as the ring `ℤ[X]/(X^4 − 11)` over ℤ; the AIR's gates ARE integer
polynomial identities, and the ext-mul lanes ARE this ring's convolution). Polynomial division writes
`P(X) = Q(X)·(X − h) + P(h)`, so at `alpha`: `Acc = Q(alpha)·(alpha − h) + P(h)`. The remainder `P(h) =
∏(h − h_j)` is NONZERO exactly when `h ∉ {h_j}`. Hence the division certificate with a NONZERO remainder
IS the non-membership statement:

    NonMemberCertified alpha acc h  :=  ∃ w v, acc = w ⊗ (alpha ⊖ h) ⊕ v  ∧  v ≠ 0

with `⊗`/`⊕`/`⊖` the `BabyBear^4` operations. `w` is the quotient witness `Q(alpha)`, `v` the nonzero
remainder `P(h)`. This is the KZG/polynomial-commitment non-membership relation.

### The refinement (the bridge, SAT ⟹ SEM)

`sat_implies_nonmember_public`: for EVERY active (non-last) row of a `Satisfied2` trace, the ancestor
`(col4 loc HASH)` is `NonMemberCertified` against the PUBLIC accumulator/challenge `(col4 pub PI_ACC)` /
`(col4 pub PI_ALPHA)`. The whole descriptor is composed:
  * C1..C3 chain the columns: `acc_aux = w ⊗ (alpha_aux ⊖ h) ⊕ v`;
  * the `sum == acc_aux` gate binds `sum` to the accumulator;
  * C4 + the `check == (1,0,0,0)` gate force `v ⊗ v_inv = 1`, i.e. `v` is a UNIT, hence `v ≠ 0`
    (the genuine non-membership content — the remainder does not vanish);
  * the row-0 PI pins + the constancy `.windowGate`s (the emit file's soundness strengthening) transfer
    `alpha_aux`/`acc_aux` to the TRUE public inputs on every active row.

## Non-vacuity (the anti-scar)

`accSat` CONSTRUCTS a concrete non-empty `Satisfied2` witness — a 2-row honest trace whose row 0 is a
GENUINE ACTIVE row where C1..C4 / sum / check FIRE (not the vacuous empty trace). `accTrace_nonmember`
runs the bridge on it end-to-end, yielding `NonMemberCertified (10,0,0,0) (7,0,0,0) (7,0,0,0)` with a
NONZERO remainder `v = (1,0,0,0)`. `badTrace_rejected` exhibits a concrete "member" trace (`v = 0`) that
FAILS `Satisfied2` — the `check` gate bites. `member_not_certified` shows the SEMANTIC relation itself is
two-sided: a genuine member (`h = alpha`, `acc = 0`) is NOT certified. So the bridge hypothesis is
inhabited-and-constraining, and the conclusion is a real predicate, not a tautology.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No Poseidon2 carrier enters (this AIR uses no
chip). NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.AccumulatorNonRevocationEmit

namespace Dregg2.Circuit.Emit.AccumulatorNonRevocationRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowConstraint WindowExpr Satisfied2 VmTrace envAt
   memLog mapLog memOpsOf mapOpsOf memCheck_nil)
open Dregg2.Circuit.Emit.AccumulatorNonRevocationEmit

set_option autoImplicit false

/-! ## §1 — the `BabyBear^4 = ℤ[X]/(X^4 − 11)` extension-field arithmetic (mirrors the AIR's ext-mul
lanes byte-for-byte) + the column extractor. Represented as `Fin 4 → ℤ`; each op reduces LANE-wise to a
`base + k` column read so `linear_combination` against the gate bodies closes exactly. -/

/-- An extension-field element: four base limbs (`c0 + c1·X + c2·X² + c3·X³`). -/
structure Ext where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
deriving DecidableEq

/-- Additive identity. -/
def ezero : Ext := ⟨0, 0, 0, 0⟩
/-- Multiplicative identity `(1,0,0,0)`. -/
def eone : Ext := ⟨1, 0, 0, 0⟩
/-- Lane-wise addition. -/
def eadd (a b : Ext) : Ext := ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩
/-- Lane-wise subtraction. -/
def esub (a b : Ext) : Ext := ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3⟩
/-- Multiplication in `ℤ[X]/(X^4 − 11)` — the SAME convolution the AIR's `extMulLane` witnesses
(the reduction `X^4 = 11`), limb-for-limb. -/
def emul (a b : Ext) : Ext :=
  ⟨a.c0 * b.c0 + 11 * (a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1),
   a.c0 * b.c1 + a.c1 * b.c0 + 11 * (a.c2 * b.c3 + a.c3 * b.c2),
   a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + 11 * (a.c3 * b.c3),
   a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0⟩

/-- Read a 4-limb ext value out of an assignment starting at `base` (`a (base + k)`) — matching the
gate bodies' column reads exactly. -/
def col4 (a : Assignment) (base : Nat) : Ext := ⟨a (base + 0), a (base + 1), a (base + 2), a (base + 3)⟩

theorem emul_ezero_left (b : Ext) : emul ezero b = ezero := by
  simp only [emul, ezero, Ext.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem emul_ezero_right (a : Ext) : emul a ezero = ezero := by
  simp only [emul, ezero, Ext.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem eone_ne_ezero : eone ≠ ezero := by
  intro heq; have h0 := congrArg Ext.c0 heq; simp [eone, ezero] at h0

/-- A unit is nonzero: if `v ⊗ v_inv = 1` then `v ≠ 0`. This is where the circuit's `check` gate
becomes the genuine "remainder does not vanish" content. -/
theorem unit_ne_ezero (v vinv : Ext) (huv : emul v vinv = eone) : v ≠ ezero := by
  intro hz
  rw [hz, emul_ezero_left] at huv
  exact eone_ne_ezero huv.symm

/-! ## §2 — the semantic relation this circuit computes: witnessed polynomial-division non-membership. -/

/-- **`NonMemberCertified alpha acc h`** — the FUNCTIONAL SPEC. `h` is certified NOT in the revocation set
committed by `acc = P(alpha)`: the accumulator decomposes as `w ⊗ (alpha ⊖ h) ⊕ v` with a NONZERO
remainder `v` (`= P(h) = ∏(h − h_j) ≠ 0 ⟺ h ∉ {h_j}`). The quotient `w` and remainder `v` are the
prover's witnesses. -/
def NonMemberCertified (alpha acc h : Ext) : Prop :=
  ∃ w v : Ext, acc = eadd (emul w (esub alpha h)) v ∧ v ≠ ezero

/-- **The relation is genuinely two-sided (a member is NOT certified).** If `h = alpha` (so `alpha ⊖ h =
0`) and `acc = 0` (the accumulator vanishes at the challenge — `alpha` IS a root, i.e. a member), then NO
`(w, v)` certifies non-membership: any decomposition forces `v = acc = 0`. So `NonMemberCertified` is not
a constantly-true predicate. -/
theorem member_not_certified (alpha : Ext) : ¬ NonMemberCertified alpha ezero alpha := by
  rintro ⟨w, v, hacc, hv⟩
  have hsub : esub alpha alpha = ezero := by
    simp only [esub, ezero, Ext.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  rw [hsub, emul_ezero_right] at hacc
  apply hv
  obtain ⟨v0, v1, v2, v3⟩ := v
  simp only [eadd, ezero, Ext.mk.injEq] at hacc
  obtain ⟨p0, p1, p2, p3⟩ := hacc
  simp only [ezero, Ext.mk.injEq]
  omega

/-! ## §3 — membership of each declared gate/pin/constancy in the descriptor (the append navigation). -/

theorem mem_c1 (j : Nat) (hj : j < 4) :
    VmConstraint2.base (.gate (c1Body j)) ∈ accumulatorNonRevDesc.constraints := by
  have h1 : VmConstraint2.base (.gate (c1Body j)) ∈ c1Gates := by
    unfold c1Gates; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [accumulatorNonRevDesc]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ h1))))))))))

theorem mem_c2 (j : Nat) (hj : j < 4) :
    VmConstraint2.base (.gate (extMulLane PRODUCT QUOTIENT DIFF j)) ∈ accumulatorNonRevDesc.constraints := by
  have h1 : VmConstraint2.base (.gate (extMulLane PRODUCT QUOTIENT DIFF j)) ∈ c2Gates := by
    unfold c2Gates; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [accumulatorNonRevDesc]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ h1))))))))))

theorem mem_c3 (j : Nat) (hj : j < 4) :
    VmConstraint2.base (.gate (c3Body j)) ∈ accumulatorNonRevDesc.constraints := by
  have h1 : VmConstraint2.base (.gate (c3Body j)) ∈ c3Gates := by
    unfold c3Gates; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [accumulatorNonRevDesc]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ h1)))))))))

theorem mem_c4 (j : Nat) (hj : j < 4) :
    VmConstraint2.base (.gate (extMulLane CHECK REMAINDER V_INV j)) ∈ accumulatorNonRevDesc.constraints := by
  have h1 : VmConstraint2.base (.gate (extMulLane CHECK REMAINDER V_INV j)) ∈ c4Gates := by
    unfold c4Gates; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [accumulatorNonRevDesc]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h1))))))))

theorem mem_sumAcc (j : Nat) (hj : j < 4) :
    VmConstraint2.base (.gate (sumAccBody j)) ∈ accumulatorNonRevDesc.constraints := by
  have h1 : VmConstraint2.base (.gate (sumAccBody j)) ∈ sumAccGates := by
    unfold sumAccGates; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [accumulatorNonRevDesc]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ h1)))))))

theorem mem_checkOne (j : Nat) (hj : j < 4) :
    VmConstraint2.base (.gate (checkOneBody j)) ∈ accumulatorNonRevDesc.constraints := by
  have h1 : VmConstraint2.base (.gate (checkOneBody j)) ∈ checkOneGates := by
    unfold checkOneGates; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [accumulatorNonRevDesc]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h1)))))

theorem mem_alphaPins (j : Nat) (hj : j < 4) :
    VmConstraint2.base (.piBinding VmRow.first (ALPHA_AUX + j) (PI_ALPHA + j))
      ∈ accumulatorNonRevDesc.constraints := by
  have h1 : VmConstraint2.base (.piBinding VmRow.first (ALPHA_AUX + j) (PI_ALPHA + j)) ∈ alphaPins := by
    unfold alphaPins; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [accumulatorNonRevDesc]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ h1)))

theorem mem_accPins (j : Nat) (hj : j < 4) :
    VmConstraint2.base (.piBinding VmRow.first (ACC_AUX + j) (PI_ACC + j))
      ∈ accumulatorNonRevDesc.constraints := by
  have h1 : VmConstraint2.base (.piBinding VmRow.first (ACC_AUX + j) (PI_ACC + j)) ∈ accPins := by
    unfold accPins; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [accumulatorNonRevDesc]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h1))

theorem mem_alphaConst (j : Nat) (hj : j < 4) :
    VmConstraint2.windowGate ⟨constBody (ALPHA_AUX + j), true⟩ ∈ accumulatorNonRevDesc.constraints := by
  have h1 : VmConstraint2.windowGate ⟨constBody (ALPHA_AUX + j), true⟩ ∈ alphaConst := by
    unfold alphaConst; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [accumulatorNonRevDesc]
  exact List.mem_append_left _ (List.mem_append_right _ h1)

theorem mem_accConst (j : Nat) (hj : j < 4) :
    VmConstraint2.windowGate ⟨constBody (ACC_AUX + j), true⟩ ∈ accumulatorNonRevDesc.constraints := by
  have h1 : VmConstraint2.windowGate ⟨constBody (ACC_AUX + j), true⟩ ∈ accConst := by
    unfold accConst; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simp only [accumulatorNonRevDesc]
  exact List.mem_append_right _ h1

/-! ## §4 — the bridge, parametric over any satisfying trace and any active row. -/

section Bridge

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable (h : Satisfied2 hash accumulatorNonRevDesc minit mfin maddrs t)
include h

/-- Any declared `.base (.gate body)` forces `body.eval = 0` on an active (non-last) row. -/
theorem gate_of_active (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length)
    (body : EmittedExpr)
    (hmem : VmConstraint2.base (.gate body) ∈ accumulatorNonRevDesc.constraints) :
    body.eval (envAt t i).loc = 0 := by
  have hb := h.rowConstraints i hi _ hmem
  have hfalse : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hlast
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hfalse] at hb
  exact hb

/-- Any declared row-first `.piBinding col pin` forces `loc col = pub pin` on row 0. -/
theorem pin_first (col pin : Nat) (hi0 : 0 < t.rows.length)
    (hmem : VmConstraint2.base (.piBinding VmRow.first col pin) ∈ accumulatorNonRevDesc.constraints) :
    (envAt t 0).loc col = t.pub pin := by
  have hb := h.rowConstraints 0 hi0 _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hb
  exact hb (by decide)

/-- A constancy `.windowGate` on `col` forces `nxt col = loc col` on an active row. -/
theorem windowConst_active (j : Nat) (hj : j < t.rows.length) (hjl : j + 1 ≠ t.rows.length)
    (c : Nat) (hmem : VmConstraint2.windowGate ⟨constBody c, true⟩ ∈ accumulatorNonRevDesc.constraints) :
    (envAt t j).nxt c = (envAt t j).loc c := by
  have hb := h.rowConstraints j hj _ hmem
  have hfalse : (j + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hjl
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hb
  have heval := hb hfalse
  simp only [constBody, WindowExpr.eval] at heval
  linarith [heval]

/-! ### The six column equations extracted from the whole descriptor on one active row. -/

theorem col_diff (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length) :
    col4 (envAt t i).loc DIFF
      = esub (col4 (envAt t i).loc ALPHA_AUX) (col4 (envAt t i).loc HASH) := by
  have g0 := gate_of_active h i hi hlast _ (mem_c1 0 (by decide))
  have g1 := gate_of_active h i hi hlast _ (mem_c1 1 (by decide))
  have g2 := gate_of_active h i hi hlast _ (mem_c1 2 (by decide))
  have g3 := gate_of_active h i hi hlast _ (mem_c1 3 (by decide))
  simp only [c1Body, coeffVar, EmittedExpr.eval] at g0 g1 g2 g3
  simp only [col4, esub, Ext.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination g0
  · linear_combination g1
  · linear_combination g2
  · linear_combination g3

theorem col_prod (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length) :
    col4 (envAt t i).loc PRODUCT
      = emul (col4 (envAt t i).loc QUOTIENT) (col4 (envAt t i).loc DIFF) := by
  have g0 := gate_of_active h i hi hlast _ (mem_c2 0 (by decide))
  have g1 := gate_of_active h i hi hlast _ (mem_c2 1 (by decide))
  have g2 := gate_of_active h i hi hlast _ (mem_c2 2 (by decide))
  have g3 := gate_of_active h i hi hlast _ (mem_c2 3 (by decide))
  simp only [extMulLane, coeffVar, coeffMul, EmittedExpr.eval, W] at g0 g1 g2 g3
  simp only [col4, emul, Ext.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination g0
  · linear_combination g1
  · linear_combination g2
  · linear_combination g3

theorem col_sum (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length) :
    col4 (envAt t i).loc SUM
      = eadd (col4 (envAt t i).loc PRODUCT) (col4 (envAt t i).loc REMAINDER) := by
  have g0 := gate_of_active h i hi hlast _ (mem_c3 0 (by decide))
  have g1 := gate_of_active h i hi hlast _ (mem_c3 1 (by decide))
  have g2 := gate_of_active h i hi hlast _ (mem_c3 2 (by decide))
  have g3 := gate_of_active h i hi hlast _ (mem_c3 3 (by decide))
  simp only [c3Body, coeffVar, EmittedExpr.eval] at g0 g1 g2 g3
  simp only [col4, eadd, Ext.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination g0
  · linear_combination g1
  · linear_combination g2
  · linear_combination g3

theorem col_accEq (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length) :
    col4 (envAt t i).loc SUM = col4 (envAt t i).loc ACC_AUX := by
  have g0 := gate_of_active h i hi hlast _ (mem_sumAcc 0 (by decide))
  have g1 := gate_of_active h i hi hlast _ (mem_sumAcc 1 (by decide))
  have g2 := gate_of_active h i hi hlast _ (mem_sumAcc 2 (by decide))
  have g3 := gate_of_active h i hi hlast _ (mem_sumAcc 3 (by decide))
  simp only [sumAccBody, coeffVar, EmittedExpr.eval] at g0 g1 g2 g3
  simp only [col4, Ext.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination g0
  · linear_combination g1
  · linear_combination g2
  · linear_combination g3

theorem col_check (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length) :
    col4 (envAt t i).loc CHECK
      = emul (col4 (envAt t i).loc REMAINDER) (col4 (envAt t i).loc V_INV) := by
  have g0 := gate_of_active h i hi hlast _ (mem_c4 0 (by decide))
  have g1 := gate_of_active h i hi hlast _ (mem_c4 1 (by decide))
  have g2 := gate_of_active h i hi hlast _ (mem_c4 2 (by decide))
  have g3 := gate_of_active h i hi hlast _ (mem_c4 3 (by decide))
  simp only [extMulLane, coeffVar, coeffMul, EmittedExpr.eval, W] at g0 g1 g2 g3
  simp only [col4, emul, Ext.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination g0
  · linear_combination g1
  · linear_combination g2
  · linear_combination g3

theorem col_check1 (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length) :
    col4 (envAt t i).loc CHECK = eone := by
  have g0 := gate_of_active h i hi hlast _ (mem_checkOne 0 (by decide))
  have g1 := gate_of_active h i hi hlast _ (mem_checkOne 1 (by decide))
  have g2 := gate_of_active h i hi hlast _ (mem_checkOne 2 (by decide))
  have g3 := gate_of_active h i hi hlast _ (mem_checkOne 3 (by decide))
  rw [show checkOneBody 0 = .add (coeffVar 1 (CHECK + 0)) (.const (-1)) from rfl] at g0
  rw [show checkOneBody 1 = coeffVar 1 (CHECK + 1) from rfl] at g1
  rw [show checkOneBody 2 = coeffVar 1 (CHECK + 2) from rfl] at g2
  rw [show checkOneBody 3 = coeffVar 1 (CHECK + 3) from rfl] at g3
  simp only [coeffVar, EmittedExpr.eval] at g0 g1 g2 g3
  simp only [col4, eone, Ext.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination g0
  · linear_combination g1
  · linear_combination g2
  · linear_combination g3

/-- **THE CORE REFINEMENT (SAT ⟹ SEM), on the row-local aux accumulator/challenge.** On any active row,
the ancestor `(col4 loc HASH)` is `NonMemberCertified` against the row's `(col4 loc ACC_AUX)` /
`(col4 loc ALPHA_AUX)` — the whole descriptor (C1..C4 + sum + check) composed. The witnesses are the
quotient `QUOTIENT` and the nonzero remainder `REMAINDER` (nonzero from the `check` gate = unit). -/
theorem sat_implies_nonmember_aux (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length) :
    NonMemberCertified (col4 (envAt t i).loc ALPHA_AUX) (col4 (envAt t i).loc ACC_AUX)
      (col4 (envAt t i).loc HASH) := by
  refine ⟨col4 (envAt t i).loc QUOTIENT, col4 (envAt t i).loc REMAINDER, ?_, ?_⟩
  · rw [← col_diff h i hi hlast, ← col_prod h i hi hlast, ← col_sum h i hi hlast]
    exact (col_accEq h i hi hlast).symm
  · have hchk := col_check h i hi hlast
    have hchk1 := col_check1 h i hi hlast
    have hu : emul (col4 (envAt t i).loc REMAINDER) (col4 (envAt t i).loc V_INV) = eone := by
      rw [← hchk]; exact hchk1
    exact unit_ne_ezero _ _ hu

/-! ### The PI-transfer: row-0 pin + constancy chain ⟹ aux equals the TRUE public inputs on every row. -/

/-- The constancy chain: a per-column aux value is CONSTANT across the whole trace (propagated from row 0
by the transition `.windowGate`s — the emit file's soundness strengthening, made whole-trace here). -/
theorem getD_const (c : Nat)
    (hc : VmConstraint2.windowGate ⟨constBody c, true⟩ ∈ accumulatorNonRevDesc.constraints) :
    ∀ i, i < t.rows.length → t.rows.getD i (fun _ => 0) c = t.rows.getD 0 (fun _ => 0) c := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk1
    have hk : k < t.rows.length := by omega
    have hkl : k + 1 ≠ t.rows.length := by omega
    have step := windowConst_active h k hk hkl c hc
    have e1 : (envAt t k).nxt c = t.rows.getD (k + 1) (fun _ => 0) c := rfl
    have e2 : (envAt t k).loc c = t.rows.getD k (fun _ => 0) c := rfl
    rw [e1, e2] at step
    rw [step]; exact ih hk

/-- `alpha_aux` on any active row IS the public `alpha` limb (row-0 pin + constancy). -/
theorem aux_pub_alpha (i : Nat) (hi : i < t.rows.length) (k : Nat) (hk : k < 4) :
    (envAt t i).loc (ALPHA_AUX + k) = t.pub (PI_ALPHA + k) := by
  have hlen0 : 0 < t.rows.length := by omega
  have hchain := getD_const h (ALPHA_AUX + k) (mem_alphaConst k hk) i hi
  have hpin := pin_first h (ALPHA_AUX + k) (PI_ALPHA + k) hlen0 (mem_alphaPins k hk)
  calc (envAt t i).loc (ALPHA_AUX + k)
      = t.rows.getD i (fun _ => 0) (ALPHA_AUX + k) := rfl
    _ = t.rows.getD 0 (fun _ => 0) (ALPHA_AUX + k) := hchain
    _ = (envAt t 0).loc (ALPHA_AUX + k) := rfl
    _ = t.pub (PI_ALPHA + k) := hpin

/-- `acc_aux` on any active row IS the public `Acc` limb (row-0 pin + constancy). -/
theorem aux_pub_acc (i : Nat) (hi : i < t.rows.length) (k : Nat) (hk : k < 4) :
    (envAt t i).loc (ACC_AUX + k) = t.pub (PI_ACC + k) := by
  have hlen0 : 0 < t.rows.length := by omega
  have hchain := getD_const h (ACC_AUX + k) (mem_accConst k hk) i hi
  have hpin := pin_first h (ACC_AUX + k) (PI_ACC + k) hlen0 (mem_accPins k hk)
  calc (envAt t i).loc (ACC_AUX + k)
      = t.rows.getD i (fun _ => 0) (ACC_AUX + k) := rfl
    _ = t.rows.getD 0 (fun _ => 0) (ACC_AUX + k) := hchain
    _ = (envAt t 0).loc (ACC_AUX + k) := rfl
    _ = t.pub (PI_ACC + k) := hpin

theorem pub_alpha (i : Nat) (hi : i < t.rows.length) :
    col4 (envAt t i).loc ALPHA_AUX = col4 t.pub PI_ALPHA := by
  simp only [col4, Ext.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩
  · exact aux_pub_alpha h i hi 0 (by decide)
  · exact aux_pub_alpha h i hi 1 (by decide)
  · exact aux_pub_alpha h i hi 2 (by decide)
  · exact aux_pub_alpha h i hi 3 (by decide)

theorem pub_acc (i : Nat) (hi : i < t.rows.length) :
    col4 (envAt t i).loc ACC_AUX = col4 t.pub PI_ACC := by
  simp only [col4, Ext.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩
  · exact aux_pub_acc h i hi 0 (by decide)
  · exact aux_pub_acc h i hi 1 (by decide)
  · exact aux_pub_acc h i hi 2 (by decide)
  · exact aux_pub_acc h i hi 3 (by decide)

/-- **THE WHOLE-DESCRIPTOR BRIDGE (SAT ⟹ SEM, tied to the PUBLIC inputs).** For EVERY active (non-last)
row of a `Satisfied2` trace, the ancestor `(col4 loc HASH)` is genuinely `NonMemberCertified` against the
PUBLIC accumulator `(col4 pub PI_ACC)` and challenge `(col4 pub PI_ALPHA)` — the functional-correctness
statement of the non-revocation AIR. Accept ⟹ the ancestor is really absent from the committed revocation
set (with a nonzero remainder witness). -/
theorem sat_implies_nonmember_public (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 ≠ t.rows.length) :
    NonMemberCertified (col4 t.pub PI_ALPHA) (col4 t.pub PI_ACC) (col4 (envAt t i).loc HASH) := by
  have hbase := sat_implies_nonmember_aux h i hi hlast
  rw [pub_alpha h i hi, pub_acc h i hi] at hbase
  exact hbase

end Bridge

#check @gate_of_active
#check @sat_implies_nonmember_public

/-! ## §5 — NON-VACUITY: a concrete satisfying witness (bridge fires) + a concrete rejecting one. -/

/-- The honest row: `h=(7,·)`, `w=(2,·)`, `v=(1,·)`, `diff=(3,·)`, `prod=(6,·)`, `sum=(7,·)`,
`v_inv=(1,·)`, `check=(1,·)`, `alpha_aux=(10,·)`, `acc_aux=(7,·)`. Satisfies every gate:
`Acc=7 = 2·(10−7)+1`, `v=1 ≠ 0` (genuine non-member). -/
def honestRow : Assignment := fun n =>
  if n = HASH then 7 else if n = QUOTIENT then 2 else if n = REMAINDER then 1
  else if n = DIFF then 3 else if n = PRODUCT then 6 else if n = SUM then 7
  else if n = V_INV then 1 else if n = CHECK then 1
  else if n = ALPHA_AUX then 10 else if n = ACC_AUX then 7 else 0

/-- Public inputs: `Acc=(7,·)` at `PI_ACC`, `alpha=(10,·)` at `PI_ALPHA`. -/
def honestPub : Assignment := fun n =>
  if n = PI_ACC then 7 else if n = PI_ALPHA then 10 else 0

/-- The concrete 2-row honest trace. Row 0 is a GENUINE ACTIVE row (`0+1 ≠ 2`); row 1 is the wrap row. -/
def accTrace : VmTrace := { rows := [honestRow, honestRow], pub := honestPub, tf := fun _ => [] }

theorem memOps_nil : memOpsOf accumulatorNonRevDesc = [] := by
  simp only [memOpsOf, accumulatorNonRevDesc, c1Gates, c2Gates, c3Gates, c4Gates, sumAccGates,
    sumAccLast, checkOneGates, checkOneLast, alphaPins, accPins, alphaConst, accConst,
    List.filterMap_append, List.filterMap_map, List.filterMap_nil]
  rfl

theorem mapOps_nil : mapOpsOf accumulatorNonRevDesc = [] := by
  simp only [mapOpsOf, accumulatorNonRevDesc, c1Gates, c2Gates, c3Gates, c4Gates, sumAccGates,
    sumAccLast, checkOneGates, checkOneLast, alphaPins, accPins, alphaConst, accConst,
    List.filterMap_append, List.filterMap_map, List.filterMap_nil]
  rfl

theorem memLog_nil (tr : VmTrace) : memLog accumulatorNonRevDesc tr = [] := by
  unfold memLog; rw [memOps_nil]; simp

theorem mapLog_nil (tr : VmTrace) : mapLog accumulatorNonRevDesc tr = [] := by
  unfold mapLog; rw [mapOps_nil]; simp

set_option maxHeartbeats 4000000 in
/-- **The concrete `Satisfied2` inhabitant (a CONSTRUCTED non-empty witness).** The honest 2-row trace
satisfies the descriptor: row 0 discharges C1..C4 / sum / check / pins / constancy NON-vacuously (the
active row where the gates fire); row 1 discharges the `.boundary .last` twins. The memory legs collapse
to the empty log (no mem/map ops). This proves the bridge's `Satisfied2` hypothesis is genuinely
inhabited — not an unsatisfiable antecedent. -/
theorem accSat :
    Satisfied2 (fun _ => 0) accumulatorNonRevDesc (fun _ => 0) (fun _ => (0, 0)) [] accTrace where
  rowConstraints := by
    intro i hi
    have hlen : accTrace.rows.length = 2 := rfl
    rw [hlen] at hi
    interval_cases i
    all_goals simp only [accumulatorNonRevDesc, List.forall_mem_append, and_assoc]
    all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intro c hc
    all_goals obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc
    all_goals have hj := List.mem_range.mp hjm
    all_goals
      interval_cases j <;>
      simp [VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt, WindowExpr.eval,
        EmittedExpr.eval, coeffVar, coeffMul, extMulLane, c1Body, c3Body, sumAccBody, checkOneBody,
        constBody, envAt, accTrace, honestRow, honestPub, W, HASH, QUOTIENT, REMAINDER, DIFF, PRODUCT,
        SUM, V_INV, CHECK, ALPHA_AUX, ACC_AUX, PI_ACC, PI_ALPHA]
  rowHashes := by intro i hi; exact trivial
  rowRanges := by intro i hi r hr; simp [accumulatorNonRevDesc] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_nil] at hop; simp at hop
  memDisciplined := by rw [memLog_nil]; trivial
  memBalanced := by rw [memLog_nil]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_nil]; rfl
  mapTableFaithful := by rw [mapLog_nil]; rfl

/-- **The bridge FIRES on the concrete witness (end-to-end).** Running `sat_implies_nonmember_public` on
`accSat` at the active row 0 yields a GENUINE non-membership certificate against the public accumulator
`(7,0,0,0)` / challenge `(10,0,0,0)`: the ancestor `(7,0,0,0)` is certified absent, with a NONZERO
remainder `v = (1,0,0,0)`. This is the anti-vacuity proof: the hypothesis is inhabited and the conclusion
is meaningful. -/
theorem accTrace_nonmember :
    NonMemberCertified (col4 honestPub PI_ALPHA) (col4 honestPub PI_ACC)
      (col4 (envAt accTrace 0).loc HASH) :=
  sat_implies_nonmember_public accSat 0 (by decide) (by decide)

/-- A concrete "member" trace: every column zero, so `v = 0` (a member's remainder vanishes) and the
`check` gate `check[0] − 1` cannot be zero. -/
def badRow : Assignment := fun _ => 0
def badTrace : VmTrace := { rows := [badRow, badRow], pub := fun _ => 0, tf := fun _ => [] }

/-- **The descriptor REJECTS the member trace (the `check` gate bites).** On the active row 0 the
`check[0] == 1` gate cannot hold when `check[0] = 0`, so `badTrace` is NOT `Satisfied2` — the constraint
system genuinely SEPARATES non-members from members. -/
theorem badTrace_rejected (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    ¬ Satisfied2 hash accumulatorNonRevDesc minit mfin maddrs badTrace := by
  intro hsat
  have hg := gate_of_active hsat 0 (by decide) (by decide) _ (mem_checkOne 0 (by decide))
  rw [show checkOneBody 0 = .add (coeffVar 1 (CHECK + 0)) (.const (-1)) from rfl] at hg
  simp only [coeffVar, EmittedExpr.eval] at hg
  exact absurd hg (by decide)

/-! ## §6 — axiom hygiene. -/

#assert_axioms sat_implies_nonmember_public
#assert_axioms sat_implies_nonmember_aux
#assert_axioms member_not_certified
#assert_axioms accSat
#assert_axioms accTrace_nonmember
#assert_axioms badTrace_rejected

end Dregg2.Circuit.Emit.AccumulatorNonRevocationRefine
