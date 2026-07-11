/-
# Dregg2.Deos.SettleEscrowSatWideDescriptor — the WELDED sealed-escrow satisfaction descriptor,
GRADUATED to a WIDE (8-felt, ~124-bit) member: its satisfaction-gate FIELD columns are now absorbed
into the wide commit a PURE light client binds. This is BLOCKER 1, sub-gap (1), of the escrow VK flip.

`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6 BLOCKER 1, and the GENTIAN verifier-lane commit
`b63f75da3`, named the first structural blocker precisely:

  > the welded descriptor `settleEscrowSatVmDescriptor2R24` is a **1-felt V3 staged member, not a
  > WIDE member**, so its satisfaction-gate field columns are NOT absorbed into the ~124-bit wide
  > commit a pure light client binds.

`SettleEscrowSatDescriptor.lean` built the welded descriptor over the V3 cohort
(`graduateV1 (rotateV3 settle-base)`); its four selector-gated satisfaction gates read the rotated
BEFORE/AFTER state-block FIELD columns `beforeFieldCol k = EFFECT_VM_WIDTH + 4 + k` and
`afterFieldCol k = EFFECT_VM_WIDTH + B_SPAN + 4 + k`. In the V3 form the rotated state block is committed
to a single felt (the ~31-bit waist), so a pure light client binding the wide commit did NOT bind
those columns — the satisfaction was witnessed only at the cap-membership posture (a verifier holding
the committed-state opening).

This module GRADUATES the welded descriptor to the WIDE form, EXACTLY as the deployed cohort members
are graduated (`EmitWideRegistryProbe.lean`: `wideAppend host bb (bb+B_SPAN)` — the two 13×8 BEFORE/AFTER
carriers + the 16 wide commit PIs, the 8-felt before/after anchors, appended past the host), THEN
re-appends the four satisfaction gates + the selector PI pin (the additive fifth-pin shape). The
construction's payoff is proven here:

  * **The refinement carries over the WIDE form** (`settleEscrowWide_forces_settle_gate`,
    `partial_settle_unsat_wide`, `phantom_settle_unsat_wide`) — a satisfying WIDE trace whose selector
    is on FORCES the sealed-escrow gate (both legs `Deposited`→`Consumed`); a forged partial/phantom
    settle is UNSAT. The gate bodies are byte-identical to the V3 weld, so the proof is the V3 proof.

  * **THE GRADUATION KEYSTONE** (`beforeFieldCol_absorbed` / `afterFieldCol_absorbed`): the
    satisfaction-gate field columns `bb + 4 + k` (`ab + 4 + k`) are members of the 37 pre-iroot limbs
    `{bb, …, bb+36}` (`{ab, …, ab+36}`) the wide BEFORE/AFTER carriers consume
    (`EffectVmEmitRotationWide.rotV3WideSpecs`). The deployed wide-binding keystone
    `EffectVmEmitRotationWide.rotV3Wide_binds_published` proves equal PUBLISHED 8-felt commits force
    equal limbs (under `Poseidon2WideCR`); so a pure light client binding the wide commit binds those
    very field columns — exactly the `CapacitySatisfaction.stateCommit`/`fieldAt_bound_in_commit`
    chain, now realized over the DEPLOYED wide carriers rather than the modeled sponge. Sub-gap (1) is
    closed at the proof level.

## STAGED — built BESIDE the deployed, NO live routing, NO VK committed, NO flip

This descriptor is a Lean DEFINITION (the source of truth). It is NOT emitted into the deployed wide
registry / VK and NOTHING routes a turn through it. The remaining FLIP distance after this pass:

  * a SATISFYING wide PRODUCER for the welded descriptor (the field-override + 8-felt commit-recompute
    surgery, then a full STARK prove/verify against a committed VK) — `§6 BLOCKER 1` producer tail;
  * the IN-AIR selector binding from `B_AUTHORITY_DIGEST` (`§6 item 2`) — recompute
    `compute_authority_digest_felt` over the witnessed declaration in-AIR, decode the required-tag
    floor, FORCE `sel = 1`. WITHOUT this a pure light client cannot force the selector on (it has only
    the commit, not the declaration preimage), so a forger dodges by `sel = 0` or by routing through
    the bare wide transfer descriptor. This is a Poseidon2-preimage-and-decode gadget — genuinely
    VK-affecting, NOT a mirror of the equality template, and the real terminal blocker to a SOUND
    pure-light-client flip;
  * committing the welded VK + admitting it on the live verify path
    (`verify_effect_vm_rotated_with_cutover`) as the deployed default.

Until those, SettleEscrow is NOT a deployed pure-light-client truth. This module closes ONLY the named
structural sub-gap (1): the welded descriptor now has a WIDE form whose satisfaction-gate field columns
ARE provably absorbed into the wide commit.

## Axiom hygiene

`#assert_all_clean` at the close. No axiom, no `sorry`, no core edit. The refinement reduces through
the STABLE `holdsVm_gate_false` interface (the V3 proof verbatim); the graduation keystone is the limb
arithmetic plus a reference to the deployed `rotV3Wide_binds_published`.
-/
import Dregg2.Deos.SettleEscrowSatDescriptor
import Dregg2.Deos.CapacitySatisfaction
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide

namespace Dregg2.Deos.SettleEscrowSatWideDescriptor

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotateV3 B_SPAN)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide (wideAppend)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Deos.SealedEscrow (stEmpty stDeposited stConsumed)
open Dregg2.Deos.SettleEscrowSatDescriptor
  (ESCROW_SEL_COL beforeFieldCol afterFieldCol settleEscrowSatGate settleEscrowSatGates
   settleEscrowV1Base)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)

set_option autoImplicit false

/-! ## §1 — the WIDE selector PI slot.

The host `graduateV1 (rotateV3 settle-base)` publishes 46 PIs; `wideAppend` appends 16 wide-commit
anchors (BEFORE 8-felt at 46..53, AFTER 8-felt at 54..61), giving 62 PIs; the selector pin then rides
the 63rd slot (`62`). (In the V3 form the selector PI was 46 — the slot just past the rotated 46;
here it is the slot just past the rotated 46 + the 16 wide anchors.) -/

/-- The WIDE selector PI slot (`host.piCount + 16 = 62`): the appended selector pin slot, past the 46
rotated PIs and the 16 wide commit anchors. -/
def ESCROW_SEL_PI_WIDE : Nat := 62

/-! ## §2 — THE WIDE WELDED DESCRIPTOR (the graduation, emit-faithful). -/

/-- **`settleEscrowSatVmDescriptor2R24Wide`** — the welded sealed-escrow satisfaction descriptor made
8-felt-WIDE. `wideAppend (graduateV1 (rotateV3 settle-base)) bb (bb+B_SPAN)` — the EXACT graduation
`EmitWideRegistryProbe.lean` applies to every cohort member (the two 13×8 BEFORE/AFTER carriers + the
16 wide commit PIs) — PLUS the four selector-gated satisfaction gates over the rotated field columns
PLUS the selector PI pin. `bb = (settleEscrowV1Base legA legB).traceWidth = EFFECT_VM_WIDTH`, so the
BEFORE block limbs are based at `bb` and the AFTER block limbs at `bb+B_SPAN` — EXACTLY the bases
`beforeFieldCol`/`afterFieldCol` read. `piCount = 63` (rotated 46 + 16 wide anchors + the selector
slot). -/
def settleEscrowSatVmDescriptor2R24Wide (legA legB : Nat) : EffectVmDescriptor2 :=
  let bb := (settleEscrowV1Base legA legB).traceWidth
  let base := wideAppend (graduateV1 (rotateV3 (settleEscrowV1Base legA legB))) bb (bb + B_SPAN)
  { base with
    name        := "dregg-effectvm-settle-escrow-sat-v1-rot24-v3-wide-staged"
    piCount     := base.piCount + 1
    constraints := base.constraints ++ settleEscrowSatGates ESCROW_SEL_COL legA legB
                     ++ [.base (.piBinding .first ESCROW_SEL_COL ESCROW_SEL_PI_WIDE)] }

/-- Each welded gate is a member of the wide descriptor's constraint list (it lands in the appended
`settleEscrowSatGates` block, between the wide-graduated host and the selector pin). -/
theorem settleGateWide_mem (legA legB : Nat) (g : VmConstraint2)
    (hg : g ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB) :
    g ∈ (settleEscrowSatVmDescriptor2R24Wide legA legB).constraints := by
  unfold settleEscrowSatVmDescriptor2R24Wide
  simp only [List.mem_append]
  exact Or.inl (Or.inr hg)

/-- The selector PI-pin constraint is a member of the wide descriptor's constraint list (the single
appended `.piBinding` after the welded gates). The HALF-B hook for the §6 item-2 selector binding. -/
theorem selPinWide_mem (legA legB : Nat) :
    (VmConstraint2.base (.piBinding .first ESCROW_SEL_COL ESCROW_SEL_PI_WIDE))
      ∈ (settleEscrowSatVmDescriptor2R24Wide legA legB).constraints := by
  unfold settleEscrowSatVmDescriptor2R24Wide
  simp only [List.mem_append, List.mem_singleton, or_true]

/-! ## §3 — THE REFINEMENT RUNG (the V3 proof, verbatim over the WIDE form).

The welded gate BODIES are byte-identical to the V3 weld (`settleEscrowSatGates` is reused), and the
gates enter only through `Satisfied2.rowConstraints`, so the V3 refinement proof carries unchanged. -/

/-- A welded gate's body vanishes on a satisfying NON-LAST row of the WIDE descriptor. -/
theorem welded_gate_holds_wide (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (settleEscrowSatVmDescriptor2R24Wide legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (g : VmConstraint2) (hg : g ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB)
    (body : EmittedExpr) (hbody : g = .base (.gate body)) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi g (settleGateWide_mem legA legB g hg)
  rw [hbody] at hrow
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, hnl] using hrow

/-- **THE WIDE REFINEMENT KEYSTONE.** On a satisfying WIDE trace, a NON-LAST row whose escrow selector
is `1` FORCES the sealed-escrow gate: both legs read `Deposited` in the rotated BEFORE field columns
and `Consumed` in the rotated AFTER field columns — the four `SettleFieldGate` conjuncts, over the
columns the ~124-bit wide commit now absorbs (`beforeFieldCol_absorbed` / `afterFieldCol_absorbed`).
The graduated descriptor witnesses the gate IN-PROOF, over a PURE-light-client-bound commit. -/
theorem settleEscrowWide_forces_settle_gate (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (settleEscrowSatVmDescriptor2R24Wide legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc ESCROW_SEL_COL = 1) :
    (envAt t i).loc (beforeFieldCol legA) ≡ stDeposited [ZMOD 2013265921] ∧
    (envAt t i).loc (beforeFieldCol legB) ≡ stDeposited [ZMOD 2013265921] ∧
    (envAt t i).loc (afterFieldCol legA)  ≡ stConsumed [ZMOD 2013265921] ∧
    (envAt t i).loc (afterFieldCol legB)  ≡ stConsumed [ZMOD 2013265921] := by
  have force : ∀ (col : Nat) (val : ℤ),
      settleEscrowSatGate ESCROW_SEL_COL col val ∈ settleEscrowSatGates ESCROW_SEL_COL legA legB →
      (envAt t i).loc col ≡ val [ZMOD 2013265921] := by
    intro col val hmem
    have h0 := welded_gate_holds_wide hash legA legB hsat i hi hnl
      (settleEscrowSatGate ESCROW_SEL_COL col val) hmem
      (.mul (.var ESCROW_SEL_COL) (.add (.var col) (.const (-val)))) rfl
    simp only [EmittedExpr.eval, hsel, one_mul] at h0
    exact (gate_modEq_iff (by ring)).mp h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact force (beforeFieldCol legA) stDeposited (by simp [settleEscrowSatGates])
  · exact force (beforeFieldCol legB) stDeposited (by simp [settleEscrowSatGates])
  · exact force (afterFieldCol legA) stConsumed (by simp [settleEscrowSatGates])
  · exact force (afterFieldCol legB) stConsumed (by simp [settleEscrowSatGates])

/-- **THE NO-PARTIAL TOOTH (WIDE).** A "partial settle" — leg B left `Deposited` in the rotated AFTER
field column on a selector-on NON-LAST row — CANNOT satisfy the wide welded descriptor. -/
theorem partial_settle_unsat_wide (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (settleEscrowSatVmDescriptor2R24Wide legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc ESCROW_SEL_COL = 1)
    (hpartial : (envAt t i).loc (afterFieldCol legB) = stDeposited) :
    False := by
  have h := (settleEscrowWide_forces_settle_gate hash legA legB hsat i hi hnl hsel).2.2.2
  rw [hpartial] at h
  simp only [stDeposited, stConsumed] at h
  exact absurd h (by decide)

/-- **THE NO-PHANTOM TOOTH (WIDE).** A settle whose leg A was never `Deposited` in the rotated BEFORE
field column on a selector-on NON-LAST row CANNOT satisfy the wide welded descriptor. -/
theorem phantom_settle_unsat_wide (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (settleEscrowSatVmDescriptor2R24Wide legA legB) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc ESCROW_SEL_COL = 1)
    (hphantom : (envAt t i).loc (beforeFieldCol legA) = stEmpty) :
    False := by
  have h := (settleEscrowWide_forces_settle_gate hash legA legB hsat i hi hnl hsel).1
  rw [hphantom] at h
  simp only [stEmpty, stDeposited] at h
  exact absurd h (by decide)

/-! ## §4 — THE GRADUATION KEYSTONE: the satisfaction-gate field columns ARE absorbed into the wide
commit.

The wide BEFORE block (limb base `bb = (settleEscrowV1Base _ _).traceWidth = EFFECT_VM_WIDTH`) and
AFTER block (base `bb+B_SPAN`) each carry 37 pre-iroot limbs `{base, …, base+36}` that
`EffectVmEmitRotationWide.rotV3WideSpecs` consumes into the chained carriers, with carrier 12 = the
published 8-felt state commit (`rotV3WidePin`); the deployed `rotV3Wide_binds_published` proves equal
published commits force equal limbs (under `Poseidon2WideCR`). The satisfaction gates read
`beforeFieldCol k = bb + 4 + k` and `afterFieldCol k = bb + B_SPAN + 4 + k` — both with offset `4 + k` ≤
36 for the 8 field slots (`k ≤ 7`), so they lie INSIDE the absorbed limb window. Hence the field
columns the satisfaction gate touches ARE bound into the wide commit a pure light client binds — the
V3 sub-gap (1) is closed. -/

/-- The escrow wide block's limb base: the settle-carrier v1 base width, definitionally
`EFFECT_VM_WIDTH` (the transfer base, untouched by the settle-carrier with-update). -/
theorem escrow_wide_bb_eq : (settleEscrowV1Base 0 1).traceWidth = EFFECT_VM_WIDTH := rfl

/-- **THE BEFORE-BLOCK ABSORPTION KEYSTONE.** For every field slot `k ≤ 7` (the 8 status fields), the
BEFORE satisfaction-gate column `beforeFieldCol k` is one of the 37 pre-iroot BEFORE limbs
`{bb, …, bb+36}` the wide carriers absorb into the published 8-felt commit (`bb = EFFECT_VM_WIDTH`).
So a pure light client binding the wide BEFORE commit binds this column (via
`rotV3Wide_binds_published`). -/
theorem beforeFieldCol_absorbed (k : Nat) (hk : k ≤ 7) :
    beforeFieldCol k ∈ (List.range 37).map (EFFECT_VM_WIDTH + ·) := by
  rw [List.mem_map]
  refine ⟨4 + k, ?_, ?_⟩
  · rw [List.mem_range]; omega
  · unfold beforeFieldCol; omega

/-- **THE AFTER-BLOCK ABSORPTION KEYSTONE.** For every field slot `k ≤ 7`, the AFTER
satisfaction-gate column `afterFieldCol k` is one of the 37 pre-iroot AFTER limbs
`{bb+B_SPAN, …, bb+B_SPAN+36}` the wide AFTER carriers absorb into the published 8-felt commit. -/
theorem afterFieldCol_absorbed (k : Nat) (hk : k ≤ 7) :
    afterFieldCol k ∈ (List.range 37).map ((EFFECT_VM_WIDTH + B_SPAN) + ·) := by
  rw [List.mem_map]
  refine ⟨4 + k, ?_, ?_⟩
  · rw [List.mem_range]; omega
  · unfold afterFieldCol; omega

/-! ## §5 — NON-VACUITY TEETH (`#guard`). -/

section Witnesses

-- The wide descriptor publishes 63 PIs (the rotated 46 + the 16 wide commit anchors + the selector).
#guard (settleEscrowSatVmDescriptor2R24Wide 0 1).piCount == 63
-- The selector pin rides PI 62 (just past the 16 wide anchors at 46..61).
#guard ESCROW_SEL_PI_WIDE == 62
-- The escrow wide block bases match the satisfaction-gate field bases (the absorption alignment).
#guard (settleEscrowV1Base 0 1).traceWidth == EFFECT_VM_WIDTH
-- The legs (slots 0, 1) land inside the absorbed 37-limb windows.
#guard (List.range 37).map (EFFECT_VM_WIDTH + ·) |>.contains (beforeFieldCol 0)
#guard (List.range 37).map (EFFECT_VM_WIDTH + ·) |>.contains (beforeFieldCol 1)
#guard (List.range 37).map ((EFFECT_VM_WIDTH + B_SPAN) + ·) |>.contains (afterFieldCol 0)
#guard (List.range 37).map ((EFFECT_VM_WIDTH + B_SPAN) + ·) |>.contains (afterFieldCol 1)

end Witnesses

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  settleGateWide_mem,
  selPinWide_mem,
  welded_gate_holds_wide,
  settleEscrowWide_forces_settle_gate,
  partial_settle_unsat_wide,
  phantom_settle_unsat_wide,
  escrow_wide_bb_eq,
  beforeFieldCol_absorbed,
  afterFieldCol_absorbed
]

end Dregg2.Deos.SettleEscrowSatWideDescriptor
