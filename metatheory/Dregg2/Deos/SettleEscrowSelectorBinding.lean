/-
# Dregg2.Deos.SettleEscrowSelectorBinding — the escrow capacity SELECTOR is bound to the cell's
COMMITTED declaration, so the welded satisfaction gate is UN-DODGEABLE (the §6 item-2 soundness
keystone for the escrow VK flip).

`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6 item 2 names the LAST soundness gap before the
escrow weld can be flipped to a deployed light-client truth:

The welded descriptor `settleEscrowSatVmDescriptor2R24` carries four selector-gated satisfaction
gates `sel · (col − const) == 0` over the rotated BEFORE/AFTER field columns. They BITE only when the
capacity selector `sel` (column `ESCROW_SEL_COL`, pinned to PI `ESCROW_SEL_PI`) is `1`
(`satisfaction_weld.rs`: "fail-OPEN only off the selector"). So a forger settling a HALF-OPEN escrow
could try to DODGE the weld by simply setting `sel = 0` (the gates go inert) — UNLESS the selector is
FORCED on for a cell whose committed declaration requires the escrow capacity.

This module proves that forcing, as a theorem. The two halves a flippable weld needs are BOTH
rigorous here:

  * **HALF A — the demand cannot be dodged by an alternate declaration** (the `DeclCommitBinds`
    reuse). A forger cannot escape the selector demand by presenting a HOLLOW declaration (one that
    requires nothing): under the authority-digest collision-resistance floor (`DeclCommitBinds`, the
    `ConstraintBinding` keystone), ANY declaration matching the committed authority digest re-derives
    the SAME required-tag floor — so if the committed cell requires the escrow tag, every admissible
    declaration does too, and the verifier still demands the selector.

  * **HALF B — the demand forces the selector ON, which forces the welded gate** (the descriptor's PI
    pin + the refinement keystone). The descriptor pins the selector column to PI `ESCROW_SEL_PI` on
    the first row (`.piBinding .first ESCROW_SEL_COL ESCROW_SEL_PI`). A verifier that DEMANDS that PI
    `= 1` (its obligation, the discipline below) forces the row-0 selector to `1` on any satisfying
    trace; the refinement keystone `settleEscrowSatV3_forces_settle_gate` then forces the four
    sealed-escrow conjuncts over the committed rotated field columns the ~124-bit wide commit absorbs.

Composed (`escrow_selector_bound_to_declaration`): on a satisfying trace of the welded descriptor, a
cell whose COMMITTED declaration requires the escrow tag has its settle FORCED through the gate over
the committed state — the forger can dodge neither by a hollow declaration (HALF A) nor by `sel = 0`
(HALF B). This is the selector-binding spec the §6 item-2 realization (the verifier pinning the
selector PI on the re-derived required-tag floor, or its in-AIR authority-digest recompute) must meet.

## What this is and is NOT (no overclaim)

This rung proves that IF the verifier honours the selector-PI demand on the committed required-tag
floor (the explicit `hverifier` discipline hypothesis below), THEN the welded gate is un-dodgeable. It
is the SPEC + soundness proof of that obligation; it is NOT itself the deployed enforcement. The
deployed `verify_full_turn_bound` does not yet route a declared-escrow turn through the welded
descriptor nor demand the selector PI from the committed declaration — that wiring (the verifier-side
realization at the cap-membership posture, or the in-AIR authority-digest recompute for a pure light
client) is the remaining gated work, so the escrow weld is NOT yet flipped. See
`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6.

## Axiom hygiene

`#assert_all_clean` at the close. The only named hypotheses are `DeclCommitBinds` (the
`ConstraintBinding` floor, the authority-digest collision-resistance) and the verifier's selector-PI
discipline; never an axiom; no core edit. The gate-forcing leg reduces through the STABLE
`settleEscrowSatV3_forces_settle_gate` interface.
-/
import Dregg2.Deos.SettleEscrowSatDescriptor
import Dregg2.Deos.ConstraintBinding

namespace Dregg2.Deos.SettleEscrowSelectorBinding

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Deos.SealedEscrow (stDeposited stConsumed)
open Dregg2.Deos.ConstraintBinding (Tag tagSettleEscrow DeclCommitBinds)
open Dregg2.Deos.SettleEscrowSatDescriptor
  (ESCROW_SEL_COL ESCROW_SEL_PI beforeFieldCol afterFieldCol
   settleEscrowSatVmDescriptor2R24 settleEscrowSatV3_forces_settle_gate)

set_option autoImplicit false

/-! ## §1 — HALF A: the selector demand cannot be dodged by an alternate declaration.

The verifier DEMANDS the escrow selector exactly when the re-derived required-tag floor includes the
escrow tag. A forger who swaps in a hollow declaration to drop that demand must still hit the committed
authority digest — and `DeclCommitBinds` then forces the SAME required tags. This is the selector
face of `ConstraintBinding.omission_caught_under_binding`. -/

/-- **The verifier's escrow-selector demand**, as a function of the re-derived required-tag floor: the
verifier demands the selector iff the floor includes the escrow tag. -/
def demandsEscrowSelector (required : List Tag) : Prop := tagSettleEscrow ∈ required

instance (required : List Tag) : Decidable (demandsEscrowSelector required) := by
  unfold demandsEscrowSelector; infer_instance

/-- **HALF A — THE DEMAND IS UN-DODGEABLE.** Under `DeclCommitBinds`, a cell whose COMMITTED
declaration requires the escrow tag forces the selector demand for WHATEVER declaration the prover
presents (so long as it matches the committed authority digest). The forger cannot present a hollow
declaration to escape the selector demand: the re-derived floor is the committed one's. -/
theorem escrow_demand_undodgeable {Decl C : Type}
    (declCommit : Decl → C) (requiredTags : Decl → List Tag)
    (hbinds : DeclCommitBinds declCommit requiredTags)
    (committed presented : Decl)
    (hcommit : declCommit presented = declCommit committed)
    (hreq : tagSettleEscrow ∈ requiredTags committed) :
    demandsEscrowSelector (requiredTags presented) := by
  unfold demandsEscrowSelector
  rw [hbinds presented committed hcommit]
  exact hreq

/-! ## §2 — HALF B: the demanded selector PI forces the selector column ON.

The welded descriptor pins the selector column to PI `ESCROW_SEL_PI` on the first row. A satisfying
trace therefore equates the row-0 selector with that public input; a verifier demanding the PI `= 1`
forces the selector on. -/

/-- The descriptor's selector PI-pin constraint is a member of its constraint list (it is the single
appended `.piBinding` after the welded gates). -/
theorem selPin_mem (legA legB : Nat) :
    (VmConstraint2.base (.piBinding .first ESCROW_SEL_COL ESCROW_SEL_PI))
      ∈ (settleEscrowSatVmDescriptor2R24 legA legB).constraints := by
  unfold settleEscrowSatVmDescriptor2R24
  simp only [List.mem_append, List.mem_singleton, or_true]

/-- **HALF B (the PI pin).** On a satisfying trace, the welded descriptor's first-row PI pin equates
the row-0 selector column with the public input at `ESCROW_SEL_PI`. -/
theorem selector_pinned_to_pi (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (settleEscrowSatVmDescriptor2R24 legA legB) minit mfin maddrs t)
    (hrows : 0 < t.rows.length) :
    (envAt t 0).loc ESCROW_SEL_COL = (envAt t 0).pub ESCROW_SEL_PI := by
  have hrow := hsat.rowConstraints 0 hrows
    (.base (.piBinding .first ESCROW_SEL_COL ESCROW_SEL_PI)) (selPin_mem legA legB)
  -- `holdsAt` for a `.base (.piBinding .first …)` on row 0 (isFirst = (0==0) = true) is the PI equality.
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using hrow

/-- **HALF B — THE DEMAND FORCES THE SELECTOR ON.** If the verifier demands the selector PI `= 1`,
then the row-0 selector column is `1` on any satisfying trace. The forger cannot set `sel = 0`. -/
theorem demanded_selector_is_on (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (settleEscrowSatVmDescriptor2R24 legA legB) minit mfin maddrs t)
    (hrows : 0 < t.rows.length)
    (hpi : (envAt t 0).pub ESCROW_SEL_PI = 1) :
    (envAt t 0).loc ESCROW_SEL_COL = 1 := by
  rw [selector_pinned_to_pi hash legA legB hsat hrows]; exact hpi

/-! ## §3 — THE COMPOSED SELECTOR-BINDING KEYSTONE.

A cell whose COMMITTED declaration requires the escrow tag, on a satisfying trace of the welded
descriptor with at least two rows (the settle row is non-last — the real producer carries forward),
has its settle FORCED through the gate over the committed rotated BEFORE/AFTER field columns. The
forger can dodge NEITHER by a hollow declaration (HALF A) NOR by `sel = 0` (HALF B). -/

/-- **THE SELECTOR-BINDING KEYSTONE (the §6 item-2 spec, proven).** Given:
  * the authority-digest binding floor (`DeclCommitBinds`),
  * a committed declaration requiring the escrow tag, and ANY presented declaration matching its
    commitment,
  * the verifier's discipline `hverifier` — it pins the selector PI `= 1` whenever the re-derived
    required-tag floor demands the escrow selector (the obligation §6 item 2's realization must meet),
  * a satisfying trace of the welded descriptor whose first (settle) row is non-last,
then both legs read `Deposited` in the committed BEFORE field columns and `Consumed` in the committed
AFTER field columns — the sealed-escrow gate is forced over the committed state, UN-DODGEABLY. -/
theorem escrow_selector_bound_to_declaration {Decl C : Type}
    (declCommit : Decl → C) (requiredTags : Decl → List Tag)
    (hbinds : DeclCommitBinds declCommit requiredTags)
    (committed presented : Decl)
    (hcommit : declCommit presented = declCommit committed)
    (hreq : tagSettleEscrow ∈ requiredTags committed)
    (hash : List ℤ → ℤ) (legA legB : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (settleEscrowSatVmDescriptor2R24 legA legB) minit mfin maddrs t)
    (hrows : 1 < t.rows.length)
    (hverifier : demandsEscrowSelector (requiredTags presented) →
      (envAt t 0).pub ESCROW_SEL_PI = 1) :
    (envAt t 0).loc (beforeFieldCol legA) = stDeposited ∧
    (envAt t 0).loc (beforeFieldCol legB) = stDeposited ∧
    (envAt t 0).loc (afterFieldCol legA)  = stConsumed ∧
    (envAt t 0).loc (afterFieldCol legB)  = stConsumed := by
  -- HALF A: the demand cannot be dodged → the verifier pins the selector PI = 1.
  have hdemand := escrow_demand_undodgeable declCommit requiredTags hbinds committed presented
    hcommit hreq
  have hpi := hverifier hdemand
  -- HALF B: the pinned PI forces the row-0 selector on.
  have hsel := demanded_selector_is_on hash legA legB hsat (by omega) hpi
  -- Row 0 is non-last (the trace has ≥ 2 rows), so the refinement keystone fires.
  have hnl : ((0 : Nat) + 1 == t.rows.length) = false := by
    simp only [Nat.zero_add, beq_eq_false_iff_ne]; omega
  exact settleEscrowSatV3_forces_settle_gate hash legA legB hsat 0 (by omega) hnl hsel

/-! ## §4 — NON-VACUITY TEETH (`#guard`): the demand predicate bites, both polarities. -/

section Witnesses

-- DEMAND: a required-tag floor including the escrow tag demands the selector.
#guard decide (demandsEscrowSelector [tagSettleEscrow])
-- NO-DEMAND: a floor without the escrow tag (a non-capacity cell) demands nothing.
#guard !decide (demandsEscrowSelector [])
#guard !decide (demandsEscrowSelector [6])  -- a bare Monotonic caveat, not escrow.
-- A multi-capacity floor still demands the escrow selector.
#guard decide (demandsEscrowSelector [18, tagSettleEscrow, 19])

end Witnesses

/-! ## §5 — Axiom hygiene. -/

#assert_all_clean [
  escrow_demand_undodgeable,
  selPin_mem,
  selector_pinned_to_pi,
  demanded_selector_is_on,
  escrow_selector_bound_to_declaration
]

end Dregg2.Deos.SettleEscrowSelectorBinding
