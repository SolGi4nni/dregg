/-
# Dregg2.Deos.SettleEscrowSatDescriptor — the WELDED sealed-escrow satisfaction descriptor, made
REAL (the emit keystone the prior VK-epoch pass found was named-only).

`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6 BLOCKER 1 named the gap: the escrow
SATISFACTION gate's soundness (`CapacitySatisfaction.satisfaction_witnessed`) and its in-AIR
`VmConstraint::Gate` polynomials (`circuit/src/effect_vm/satisfaction_weld.rs`) were done, but
`settleEscrowSatVmDescriptor2R24` was NEVER built — it was a name in a comment, with a placeholder
selector column (`SEL = 320`) filled by no producer. This module builds it for real, as a genuine
`EffectVmDescriptor2` over the deployed R=24 rotated cohort, and proves the REFINEMENT rung: a
satisfying trace of the welded descriptor FORCES the sealed-escrow gate (both legs `Deposited`
before, both `Consumed` after) over the rotated state-block FIELD columns the ~124-bit wide commit
absorbs — so the gate is witnessed in a PROOF, not only off-AIR.

## The construction (faithful to the deployed machinery)

`settleEscrowSatVmDescriptor2R24 legA legB` is `graduateV1 (rotateV3 base)` of a settle-shaped v1
base, PLUS the four selector-gated satisfaction gates over the rotated BEFORE/AFTER field columns,
PLUS one selector PI pin — EXACTLY the additive shape the deployed fifth-pin variants use
(`noteSpendV3` = `graduateV1 (rotateV3WithNullifierPin …) ++ [mapOps]`; `transferFeeVmDescriptor`
adds a balance gate + a PI pin). The base is the transfer descriptor with the two LEG field-freeze
gates DROPPED (a settle CHANGES those two status fields `Deposited → Consumed`; the other six fields
stay frozen) — so the welded gates and the base are mutually satisfiable for a settle-carrier turn
(a zero-amount transfer that flips the two leg status fields).

* **The selector** is a free PARAM column (`ESCROW_SEL_COL = prmCol 2`), 1 on the settle row and 0
  on padding — the producer fills it. It replaces the `SEL = 320` placeholder. Pinned to PI
  `ESCROW_SEL_PI = 46` on the first row, so a verifier that KNOWS the cell declares the escrow
  capacity (the deployed COVERAGE carrier, `CapacityCarrier`) can FORCE the selector on. (Binding
  the selector to the committed declaration's required-tag floor IN-AIR — so a forger cannot dodge
  by setting the selector 0 — is the named `DeclCommitBinds` realization, §6 item 2; this
  descriptor makes the selector a real, pinned column it can hang on.)

* **The four welded gates** `sel · (col − const) == 0` read the rotated field columns
  `beforeFieldCol k = EFFECT_VM_WIDTH + 4 + k` and `afterFieldCol k = EFFECT_VM_WIDTH + B_SPAN + 4 + k`
  (the `r3..r10 ↔ fields[0..8]` weld — the Rust `satisfaction_weld::{before,after}_field_col`),
  which the chained `wireCommitR` → rotated state-commit absorbs into the wide commit. The Lean
  satisfaction SOUNDNESS (equal committed state ⟹ same verdict) is the imported
  `CapacitySatisfaction.SettleFieldGate` keystone; THIS module proves the descriptor REFINES that
  gate.

## STAGED — emitted BESIDE the deployed cohort, NO live routing

This descriptor is emitted into `rotation-v3-staged-registry.tsv` as a new staged member; NO live
path routes a turn through it (`rotated_descriptor_name_for_effect` is unchanged), and NO deployed
descriptor is touched (the drift gate's deployed rows are byte-identical). The remaining distance to
a FLIPPABLE escrow weld: commit its VK + route a declared-escrow turn through it + bind the selector
to the committed declaration in-AIR (item 2). The tags 18/19 (discharge/vault) gates need the
range-check + overflow-safe product gadgets (§6 BLOCKER 2) BEFORE their analog can flip.

## Axiom hygiene

`#assert_all_clean` at the close. No axiom, no `sorry`, no core edit. The refinement rung reduces
the descriptor's welded gates through the STABLE `holdsVm_gate_false` interface.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Deos.CapacitySatisfaction

namespace Dregg2.Deos.SettleEscrowSatDescriptor

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotateV3)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Deos.SealedEscrow (stEmpty stDeposited stConsumed)

set_option autoImplicit false

/-! ## §1 — the welded columns + constants (the Rust `satisfaction_weld` twin). -/

/-- The capacity selector column: a free PARAM slot (`prmCol 2`), 1 on the settle row. The REAL
column replacing the `SEL = 320` placeholder; the producer fills it. -/
def ESCROW_SEL_COL : Nat := prmCol 2

/-- The selector PI slot (`pi_base + 4 = 46`): the first row's selector is pinned here so a verifier
that knows the cell declares the escrow capacity can FORCE the selector on. -/
def ESCROW_SEL_PI : Nat := 46

/-- The rotated BEFORE-block field column for slot `k`: `r3..r10 ↔ fields[0..8]` (`r3` is appendix
limb 4), the before block based at `EFFECT_VM_WIDTH` (the `rotateV3` appendix base for a transfer
base). The Rust twin is `satisfaction_weld::before_field_col`. -/
def beforeFieldCol (k : Nat) : Nat := EFFECT_VM_WIDTH + 4 + k

/-- The rotated AFTER-block field column for slot `k` (the after block based at
`EFFECT_VM_WIDTH + B_SPAN`, the rotated block span — 227 at v13). Derived from the canonical
`EffectVmEmitRotationV3.B_SPAN`, NOT a frozen literal, so it tracks the rotated block geometry (the
prior hard-coded `51` was the pre-v11 `B_SPAN` and drifted the AFTER-leg gates off the producer's
columns). The Rust twin is `satisfaction_weld::after_field_col` (`AFTER_BASE = V1_WIDTH + B_SPAN`). -/
def afterFieldCol (k : Nat) : Nat :=
  EFFECT_VM_WIDTH + Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_SPAN + 4 + k

/-! ## §2 — the four selector-gated satisfaction gates (the in-AIR `SETTLE_ESCROW` arm). -/

/-- One selector-gated equality gate `sel · (col − value) == 0` (degree 2): inert when `sel = 0`,
forcing `col = value` when `sel = 1`. The Lean twin of `satisfaction_weld::selector_eq_gate`. -/
def settleEscrowSatGate (selCol col : Nat) (value : ℤ) : VmConstraint2 :=
  .base (.gate (.mul (.var selCol) (.add (.var col) (.const (-value)))))

/-- **THE FOUR WELDED GATES.** Both legs `Deposited` in the BEFORE field columns, both `Consumed` in
the AFTER field columns, gated by the escrow selector. The Lean twin of
`satisfaction_weld::settle_escrow_satisfaction_gates`; a satisfying proof with the selector on FORCES
the sealed-escrow `SettleFieldGate` over the bound rotated columns. -/
def settleEscrowSatGates (selCol legA legB : Nat) : List VmConstraint2 :=
  [ settleEscrowSatGate selCol (beforeFieldCol legA) stDeposited
  , settleEscrowSatGate selCol (beforeFieldCol legB) stDeposited
  , settleEscrowSatGate selCol (afterFieldCol legA) stConsumed
  , settleEscrowSatGate selCol (afterFieldCol legB) stConsumed ]

/-! ## §3 — the settle-shaped v1 base (transfer minus the two leg field-freezes). -/

/-- The transfer per-row gates with the TWO leg field-freeze gates dropped: a settle CHANGES the two
status fields (`Deposited → Consumed`), so freezing them would contradict the welded gates. The other
six fields stay frozen, and the balance/nonce/cap/reserved discipline is unchanged. -/
def settleEscrowRowGates (legA legB : Nat) : List VmConstraint :=
  [ .gate gBalLo, .gate gBalHi, .gate gDirBool, .gate gNonce, .gate gCapPass, .gate gResPass ]
  ++ (List.range 8).filterMap
      (fun i => if i == legA || i == legB then none else some (.gate (gFieldPass i)))

/-- The settle-carrier v1 base: the transfer descriptor with the two leg field-freezes dropped. A
zero-amount transfer (balance unchanged) that flips two status fields. -/
def settleEscrowV1Base (legA legB : Nat) : EffectVmDescriptor :=
  { transferVmDescriptor with
    name        := "dregg-effectvm-settle-escrow-sat-v1"
    constraints := settleEscrowRowGates legA legB ++ transitionAll
                     ++ boundaryFirstPins ++ boundaryLastPins ++ selectorGates sel.TRANSFER }

/-! ## §4 — THE WELDED DESCRIPTOR (the emit keystone, now REAL). -/

/-- **`settleEscrowSatVmDescriptor2R24`** — the welded sealed-escrow satisfaction descriptor over the
R=24 rotated cohort. `graduateV1 (rotateV3 settle-base)` PLUS the four selector-gated satisfaction
gates over the rotated field columns PLUS the selector PI pin — the additive shape every deployed
fifth-pin variant uses. `piCount = 47` (the rotated 46-PI vector + the appended selector slot). The
descriptor a flippable escrow weld commits a VK for. -/
def settleEscrowSatVmDescriptor2R24 (legA legB : Nat) : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3 (settleEscrowV1Base legA legB))
  { base with
    name        := "dregg-effectvm-settle-escrow-sat-v1-rot24-v3-staged"
    piCount     := base.piCount + 1
    constraints := base.constraints ++ settleEscrowSatGates ESCROW_SEL_COL legA legB
                     ++ [.base (.piBinding .first ESCROW_SEL_COL ESCROW_SEL_PI)] }

/-- Each welded gate is a member of the descriptor's constraint list (it lands in the appended
`settleEscrowSatGates` block). -/
theorem settleGate_mem (legA legB : Nat) (g : VmConstraint2)
    (hg : g ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB) :
    g ∈ (settleEscrowSatVmDescriptor2R24 legA legB).constraints := by
  unfold settleEscrowSatVmDescriptor2R24
  simp only [List.mem_append]
  exact Or.inl (Or.inr hg)

/-! ## §5 — THE REFINEMENT RUNG: a satisfying trace FORCES the sealed-escrow gate.

On any NON-LAST row whose selector is on, the four welded gate bodies vanish (the `Satisfied2`
`rowConstraints` clause). With the selector `= 1`, each `sel · (col − const) = 0` collapses to
`col = const`, giving exactly the sealed-escrow `SettleFieldGate` conjuncts over the rotated field
columns the wide commit binds. So the EMITTED descriptor REFINES the gate — it is witnessed in a
proof, not only by the off-AIR re-evaluation. -/

/-- A welded gate's body vanishes on a satisfying NON-LAST row. -/
theorem welded_gate_holds (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (settleEscrowSatVmDescriptor2R24 legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (g : VmConstraint2) (hg : g ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB)
    (body : EmittedExpr) (hbody : g = .base (.gate body)) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi g (settleGate_mem legA legB g hg)
  rw [hbody] at hrow
  -- `holdsAt` for a `.base (.gate body)` is `holdsVm env (i==0) (i+1==len) (.gate body)`;
  -- on a non-last row this reduces (field-faithfully) to `body.eval loc ≡ 0 [ZMOD p]`.
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, hnl] using hrow

/-- **THE REFINEMENT KEYSTONE.** On a satisfying trace, a NON-LAST row whose escrow selector is `1`
FORCES the sealed-escrow gate: both legs read `Deposited` in the rotated BEFORE field columns and
`Consumed` in the rotated AFTER field columns — the four `SettleFieldGate` conjuncts, over the
columns the ~124-bit wide commit absorbs. The emitted welded descriptor witnesses the gate IN-PROOF. -/
theorem settleEscrowSatV3_forces_settle_gate (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (settleEscrowSatVmDescriptor2R24 legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc ESCROW_SEL_COL = 1) :
    (envAt t i).loc (beforeFieldCol legA) ≡ stDeposited [ZMOD 2013265921] ∧
    (envAt t i).loc (beforeFieldCol legB) ≡ stDeposited [ZMOD 2013265921] ∧
    (envAt t i).loc (afterFieldCol legA)  ≡ stConsumed [ZMOD 2013265921] ∧
    (envAt t i).loc (afterFieldCol legB)  ≡ stConsumed [ZMOD 2013265921] := by
  -- Each welded gate body `sel · (col − const)` vanishes mod `p`; `sel = 1` collapses it to
  -- the field-faithful equality `col ≡ const [ZMOD p]`.
  have force : ∀ (col : Nat) (val : ℤ),
      settleEscrowSatGate ESCROW_SEL_COL col val ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB →
      (envAt t i).loc col ≡ val [ZMOD 2013265921] := by
    intro col val hmem
    have h0 := welded_gate_holds hash legA legB hsat i hi hnl
      (settleEscrowSatGate ESCROW_SEL_COL col val) hmem
      (.mul (.var ESCROW_SEL_COL) (.add (.var col) (.const (-val)))) rfl
    -- `EmittedExpr.eval`: `sel * (col + (-val)) ≡ 0 [ZMOD p]`, and `sel = 1`.
    simp only [EmittedExpr.eval, hsel, one_mul] at h0
    -- `col + (-val) ≡ 0  ⟺  col ≡ val  [ZMOD p]`.
    exact (gate_modEq_iff (by ring)).mp h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact force (beforeFieldCol legA) stDeposited (by simp [settleEscrowSatGates])
  · exact force (beforeFieldCol legB) stDeposited (by simp [settleEscrowSatGates])
  · exact force (afterFieldCol legA) stConsumed (by simp [settleEscrowSatGates])
  · exact force (afterFieldCol legB) stConsumed (by simp [settleEscrowSatGates])

/-- **THE NO-PARTIAL TOOTH (in-AIR).** A "partial settle" — leg B left `Deposited` in the rotated
AFTER field column on a selector-on NON-LAST row — CANNOT satisfy the welded descriptor: the
refinement forces leg B `Consumed`, and `Deposited ≠ Consumed`. The half-open trade is UNSAT. -/
theorem partial_settle_unsat (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (settleEscrowSatVmDescriptor2R24 legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc ESCROW_SEL_COL = 1)
    (hpartial : (envAt t i).loc (afterFieldCol legB) = stDeposited) :
    False := by
  have h := (settleEscrowSatV3_forces_settle_gate hash legA legB hsat i hi hnl hsel).2.2.2
  rw [hpartial] at h
  -- `h : stDeposited ≡ stConsumed [ZMOD p]`, i.e. `1 ≡ 2` — impossible: both are canonical and
  -- distinct, so `p ∤ (1 − 2)`.
  simp only [stDeposited, stConsumed] at h
  exact absurd h (by decide)

/-- **THE NO-PHANTOM TOOTH (in-AIR).** A settle whose leg A was never `Deposited` in the rotated
BEFORE field column (e.g. `Empty`) on a selector-on NON-LAST row CANNOT satisfy the welded
descriptor: the refinement forces leg A `Deposited`. A consumption cannot be conjured from a leg that
never locked. -/
theorem phantom_settle_unsat (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (settleEscrowSatVmDescriptor2R24 legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc ESCROW_SEL_COL = 1)
    (hphantom : (envAt t i).loc (beforeFieldCol legA) = stEmpty) :
    False := by
  have h := (settleEscrowSatV3_forces_settle_gate hash legA legB hsat i hi hnl hsel).1
  rw [hphantom] at h
  -- `h : stEmpty ≡ stDeposited [ZMOD p]`, i.e. `0 ≡ 1` — impossible: both are canonical and
  -- distinct, so `p ∤ (0 − 1)`.
  simp only [stEmpty, stDeposited] at h
  exact absurd h (by decide)

/-! ## §6 — NON-VACUITY TEETH (`#guard`): the gate bodies BITE on concrete rows.

A row where the selector is on and both legs settle `Deposited → Consumed` makes EVERY welded gate
body vanish; a forged partial (leg B left `Deposited`) makes the leg-B AFTER gate body non-zero. We
evaluate the gate bodies directly on a hand-built assignment (legs in field slots 0/1). -/

section Witnesses

/-- A row assignment: `sel` at `ESCROW_SEL_COL`, the four leg field columns set, else 0. -/
private def mkLoc (sel beforeA beforeB afterA afterB : ℤ) : Nat → ℤ := fun c =>
  if c == ESCROW_SEL_COL then sel
  else if c == beforeFieldCol 0 then beforeA
  else if c == beforeFieldCol 1 then beforeB
  else if c == afterFieldCol 0 then afterA
  else if c == afterFieldCol 1 then afterB
  else 0

/-- Evaluate a welded gate's body on a row assignment. -/
private def gateVal (g : VmConstraint2) (loc : Nat → ℤ) : ℤ :=
  match g with
  | .base (.gate body) => body.eval loc
  | _ => 999  -- never matched: the welded gates are all `.gate`

-- HONEST: selector on, both legs Deposited→Consumed — every welded gate body is 0.
#guard (settleEscrowSatGates ESCROW_SEL_COL 0 1).all
  (fun g => gateVal g (mkLoc 1 stDeposited stDeposited stConsumed stConsumed) == 0)
-- NO-PARTIAL: leg B left Deposited after — some welded gate body is NON-zero.
#guard !(settleEscrowSatGates ESCROW_SEL_COL 0 1).all
  (fun g => gateVal g (mkLoc 1 stDeposited stDeposited stConsumed stDeposited) == 0)
-- NO-PHANTOM: leg A never Deposited before (Empty) — some welded gate body is NON-zero.
#guard !(settleEscrowSatGates ESCROW_SEL_COL 0 1).all
  (fun g => gateVal g (mkLoc 1 stEmpty stDeposited stConsumed stConsumed) == 0)
-- SELECTOR OFF: the gates are inert (every body 0) even with arbitrary field values.
#guard (settleEscrowSatGates ESCROW_SEL_COL 0 1).all
  (fun g => gateVal g (mkLoc 0 7 9 3 4) == 0)
-- The descriptor publishes 47 PIs (the rotated 46 + the appended selector slot).
#guard (settleEscrowSatVmDescriptor2R24 0 1).piCount == 47

end Witnesses

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  settleGate_mem,
  welded_gate_holds,
  settleEscrowSatV3_forces_settle_gate,
  partial_settle_unsat,
  phantom_settle_unsat
]

end Dregg2.Deos.SettleEscrowSatDescriptor
