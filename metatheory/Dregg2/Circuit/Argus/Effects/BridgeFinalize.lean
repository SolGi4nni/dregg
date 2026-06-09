/-
# Dregg2.Circuit.Argus.Effects.BridgeFinalize — the bridge-FINALIZE settle leg welded into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and `Argus/
Compile.lean` welded it to the circuit for transfer/mint/burn (single-cell) and the side-table
escrow CREATE; `Argus/Effects/{ReleaseEscrow,RefundEscrow}.lean` did the two SETTLE siblings (read a
record by id, CREDIT the settle target, mark resolved). This module welds the THIRD settle sibling —
**bridgeFinalize** — in its own disjoint file (it imports the Argus IR + the audited bridgeFinalize
emitter read-only and owns only its own declarations; it edits no other Argus file).

## Why bridgeFinalize is the genuinely DIFFERENT settle shape (the de-risk this module buys)

release/refund are SETTLE-BACK legs: read the parked record `r`, CREDIT a cell `+r.amount` at
`r.asset` (`recBalCreditCell`), mark resolved. The COMBINED per-asset measure is CONSERVED (the value
returns to the ledger). bridgeFinalize is the §8 confirmation arriving from the other chain — the
parked value genuinely LEFT, a **no-credit OUTFLOW** (a burn). Precisely, the kernel step
`bridgeFinalizeKAsset` (`RecordKernel.lean:1797`):

    match k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
    | some r => if r.bridge = true ∧ r.asset = asset ∧ r.amount = amount then
                  some (bridgeFinalizeRawAsset k id)
                else none
    | none   => none

  with `bridgeFinalizeRawAsset k id = { k with escrows := markResolved k.escrows id }`,

so a committed finalize READS the parked record `r` (by id), checks it is a BRIDGE record whose
`(asset, amount)` MATCH the receipt-disclosed `(asset, amount)` (dregg1's `finalize_bridge`
receipt-vs-pending check), and then RESOLVES the holding-store WITHOUT a credit — the `bal` ledger is
LEFT UNTOUCHED (the value already departed at lock and now leaves for the other chain). The COMBINED
per-asset total DROPS by the bridged `amount` — the disclosed outflow.

So the genuine structural difference from release/refund: the body has **NO `setBal` leg** — the bare
ledger is FRAMED-UNCHANGED (`k'.bal = k.bal`), and the only mutation is the `escrows` list REPLACE
(`markResolved`). And the descriptor's per-cell spec is the FROZEN-balance + TICKED-nonce case (transfer/
burn-shaped), not the credit + frozen-nonce case (release/refund-shaped): every data column frozen
except the nonce, which TICKS on the runtime's non-NoOp invariant. So the weld carries a nonce-tick
DIVERGENCE (descriptor TICKS, executor FREEZES) exactly as the transfer / burn welds do — NOT the
no-divergence shape of release/refund.

## The IR-grammar finding (same as the other settle legs): the body needs NO new primitive.

The single mutation `escrows := markResolved k.escrows id` is the §A primitive `setEscrows (g :
RecordKernelState → List EscrowRecord)` at `g := fun k => markResolved k.escrows id` — the SAME
primitive create's prepend and release/refund's resolve use. The gate's `find?`/match leaf and the
`setEscrows` leaf both re-read the SAME pure `k.escrows.find?` term, so the term is faithful with the
primitives as they are. The bare-`bal` FREEZE is achieved by OMITTING any `setBal` leg (a finalize
moves nothing on the ledger), so the body is `seq (guard …) (setEscrows …)` — a SINGLE component write
gated, the leanest settle shape.

## What this module proves (the two headline theorems, on the no-credit-resolve shape)

  1. `interp_bridgeFinalizeStmt_eq_bridgeFinalizeKAsset` — the executor IS the term: `interp` of the
     bridgeFinalize IR term is, on the nose, the verified kernel step `bridgeFinalizeKAsset`.
  2. `bridgeFinalize_compile_sound` — the weld: a satisfying witness of the AUDITED class-A genuine
     descriptor `bridgeFinalizeVmDescriptorGenuine` (`EffectVmEmitBridgeFinalize §H`) agrees, per cell,
     with the post-state the IR term's executor produces, AND forces the genuine `escrows`-root
     recompute — welded DIRECTLY against `bridgeFinalizeGenuine_sound`.

(The kernel step `bridgeFinalizeKAsset` is the `RecordKernelState`-level body the chained executor
`bridgeFinalizeChainA` wraps — `bridgeFinalizeChainA s … = if bridgeAuthOK … then match
bridgeFinalizeKAsset s.kernel … | some k' => some { kernel := k', log := … } | none => none`,
`TurnExecutorFull.lean:3009`. The Argus `interp` is a `RecordKernelState → Option RecordKernelState`
transformer, so the kernel step IS its faithful target — exactly as the release/refund welds refine to
`releaseEscrowKAsset`/`refundEscrowKAsset`, not their chained wrappers. The chained layer's EXTRA
creator-authority gate `bridgeAuthOK` and the `escrowReceiptA` log append sit ABOVE the IR-body level;
they are the turn-prologue/log concern, cited not re-claimed.)

## HONEST SURFACE (precise — do NOT over-read)

Identical digest-not-list boundary to the release/refund welds, on the no-credit OUTFLOW direction:

  * **conserved leg (per-cell):** the circuit's pinned post-`balLo` equals the executor's FROZEN
    projection `cellProjFinalize k'.bal c asset` (`= cellProjFinalize k.bal c asset`, since
    `bridgeFinalizeRawAsset` leaves `bal` untouched), for ANY cell `c`/`asset` — the no-credit-outflow
    freeze (the value left the per-cell ledger at LOCK time). `cellProjFinalize` projects ONLY the
    `(c, asset)` ledger entry into `balLo` (every other limb is `0`, FROZEN). The frozen frame
    (balHi/fields/capRoot/reserved) agrees. The per-effect nonce is RECONCILED — the descriptor TICKS the
    cell nonce while the executor FREEZES it (`EffectVmEmitBridgeFinalize §7/§9`), bundled as a
    `NonceReconciled` and discharged to the turn PROLOGUE's single tick
    (`bridgeFinalize_compile_sound_nonce_is_turn_tick`), NOT a carried divergence. The cross-cell
    COMBINED-per-asset DROP (the bridged
    outflow) is the executor's keystone (`bridgeFinalizeKAsset_moves_combined_per_asset`), cited there —
    NOT re-claimed here.
  * **side-table leg (the resolved record):** the circuit FORCES the new escrow-list root to be the
    genuine in-row recompute `hash[ hash[id,creator,recipient,amount,asset,resolved], old_root ]` of the
    bound record + old root (`bridgeFinalizeGenuine_sound`'s root clause, with `resolved = 1` on a
    finalize), absorbed into `state_commit`. So under `Poseidon2SpongeCR` the resolved record is bound —
    a dropped/forged resolve MOVES the commitment (`bridgeFinalizeGenuine_binds_record`, cited). The weld
    EXPOSES this genuine-recompute clause as a conjunct so the side-table binding is part of the welded
    statement, not a side remark.

  What this does NOT claim: it does not assert the circuit row's `escrows`-list state EQUALS the
  executor's `markResolved k.escrows id` as a LIST (the EffectVM row carries a DIGEST, not the list — the
  `SystemRoots` digest connector). The executor produces the real resolved list (the cornerstone +
  `markResolved`); the circuit produces the genuine root of it. That is the faithful digest-not-list
  boundary, stated, not hidden. (The descriptor-level absorption of the escrow root into the deployed
  runtime's `state_commit` is itself gated on the runtime growing the carrier column — reported in the
  emitter as `escrow_root_not_in_descriptor_commit`, cited not claimed.)

## Honesty

`#assert_axioms` on both headline theorems ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR
enters ONLY inside the reused emitter (not in the welded conclusion's statement). No `sorry`, no `:=
True` vacuity, no weakening-that-just-typechecks: the conclusion is the genuine per-cell agreement +
genuine root recompute the reused theorem proves. Imports are read-only; this file owns only itself and
edits no other Argus module.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Argus.Nonce
import Dregg2.Circuit.Emit.EffectVmEmitBridgeFinalize

namespace Dregg2.Circuit.Argus.Effects.BridgeFinalize

open Dregg2.Exec
open Dregg2.Circuit.Argus (RecStmt interp NonceReconciled)
open Dregg2.Exec (RecordKernelState EscrowRecord CellId AssetId
  bridgeFinalizeKAsset bridgeFinalizeRawAsset markResolved)

/-! ## §1 — the gate + the body leaf (the no-credit-resolve shape: a `find?`-keyed gate, ONE
side-table write, the bare ledger framed-unchanged).

`bridgeFinalizeKAsset k id asset amount` admits iff a matching unresolved record EXISTS and it is a
BRIDGE record whose `(asset, amount)` MATCH the receipt-disclosed `(asset, amount)`; on commit it marks
that record resolved WITHOUT any credit (the value left for the other chain). We render the gate as a
`Bool` over `k` and the single mutation as a `setEscrows` closure that `markResolved`s the holding-store
in place. -/

/-- The find-predicate `bridgeFinalizeKAsset` uses (the kernel's `r.id = id ∧ r.resolved = false`).
Named locally so the IR term + the proofs read against the SAME predicate the executor uses. -/
def matchPred (id : Nat) : EscrowRecord → Bool := fun r => decide (r.id = id ∧ r.resolved = false)

/-- The bridge-finalize admissibility gate as a `Bool` — exactly `bridgeFinalizeKAsset`'s admission: a
matching unresolved record EXISTS, and it is a BRIDGE record whose parked `(asset, amount)` MATCH the
receipt-disclosed `(asset, amount)` (the §8 receipt-vs-pending check). `none` (no such record) and a
non-bridge / mismatched record both fail closed. -/
def bridgeFinalizeGuard (id : Nat) (asset : AssetId) (amount : ℤ) (k : RecordKernelState) : Bool :=
  match k.escrows.find? (matchPred id) with
  | some r => r.bridge = true ∧ r.asset = asset ∧ r.amount = amount
  | none   => false

/-- The bridgeFinalize effect as an IR term: gate, then the SINGLE component write — mark the found
record resolved on the `escrows` side-table (`setEscrows`). The no-credit-resolve analog of
`refundEscrowStmt`: SAME `seq (guard …) (setEscrows …)` skeleton, but there is NO `setBal` leg (a
finalize moves nothing on the ledger — the bare `bal` is FRAMED-UNCHANGED), and the `escrows` write is a
list REPLACE (`markResolved`), not a prepend. No new IR constructor is used. -/
def bridgeFinalizeStmt (id : Nat) (asset : AssetId) (amount : ℤ) : RecStmt :=
  RecStmt.seq (RecStmt.guard (bridgeFinalizeGuard id asset amount))
    (RecStmt.setEscrows (fun k => markResolved k.escrows id))

/-! ## §2 — the gate decodes to `bridgeFinalizeKAsset`'s admission, and the body IS
`bridgeFinalizeRawAsset`.

Two ingredients, exactly as release/refund: (a) the `Bool` gate equals the kernel step's bridge/match
`if` condition on the found record, and (b) the single-component body reduces to the kernel's commit
post-state. The no-credit fact (which release/refund did not have): the body is a SINGLE `setEscrows`,
so the post-state is exactly `{ k with escrows := markResolved k.escrows id } = bridgeFinalizeRawAsset
k id` — the bare `bal`/`cell` untouched. -/

/-- The single-component body reduces to `bridgeFinalizeRawAsset`'s post-state. There is no `setBal`
interleave (release/refund's two-write `createEscrowBody_eq` analog collapses to one write here), so the
post-state is `{ k with escrows := markResolved k.escrows id }` — the kernel's `bridgeFinalizeRawAsset`. -/
theorem bridgeFinalizeBody_eq (id : Nat) (k : RecordKernelState) :
    interp (RecStmt.setEscrows (fun k => markResolved k.escrows id)) k
      = some (bridgeFinalizeRawAsset k id) := by
  simp only [interp, bridgeFinalizeRawAsset]

/-- The gate `match` reduces on `hf` (the same find-term the kernel reads). A `none` find fails the
gate; a `some r` find leaves the bridge/match `Bool`. -/
private theorem bridgeFinalizeGuard_none {id : Nat} {asset : AssetId} {amount : ℤ}
    {k : RecordKernelState} (hf : k.escrows.find? (matchPred id) = none) :
    bridgeFinalizeGuard id asset amount k = false := by
  simp only [bridgeFinalizeGuard, hf]

private theorem bridgeFinalizeGuard_some {id : Nat} {asset : AssetId} {amount : ℤ}
    {k : RecordKernelState} {r : EscrowRecord} (hf : k.escrows.find? (matchPred id) = some r) :
    bridgeFinalizeGuard id asset amount k
      = decide (r.bridge = true ∧ r.asset = asset ∧ r.amount = amount) := by
  simp only [bridgeFinalizeGuard, hf]

/-- The kernel step reduces on `hf`: a `none` find rejects; a `some r` find opens the bridge/match `if`
over `bridgeFinalizeRawAsset`. `matchPred` is the common spelling of the kernel's inlined predicate. -/
private theorem bridgeFinalizeKAsset_none {id : Nat} {asset : AssetId} {amount : ℤ}
    {k : RecordKernelState} (hf : k.escrows.find? (matchPred id) = none) :
    bridgeFinalizeKAsset k id asset amount = none := by
  -- the kernel's inlined predicate IS `matchPred id`; fold it in `hf` so it matches the kernel `match`.
  have hf' : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = none := hf
  simp only [bridgeFinalizeKAsset, hf']

private theorem bridgeFinalizeKAsset_some {id : Nat} {asset : AssetId} {amount : ℤ}
    {k : RecordKernelState} {r : EscrowRecord} (hf : k.escrows.find? (matchPred id) = some r) :
    bridgeFinalizeKAsset k id asset amount
      = if r.bridge = true ∧ r.asset = asset ∧ r.amount = amount then
          some (bridgeFinalizeRawAsset k id)
        else none := by
  have hf' : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r := hf
  simp only [bridgeFinalizeKAsset, hf']

/-- **The cornerstone (no-credit settle leg).** `interp` of the bridgeFinalize term IS the verified
kernel step `bridgeFinalizeKAsset` — the same partial function, by construction, exactly as the
transfer/mint/burn/createEscrow/release/refund cornerstones, now over a settle leg that READS the record
and REPLACES it in the side-table WITHOUT crediting (the bare ledger framed-unchanged).

The proof opens the `find?` on the kernel side and the gate's `match` on the IR side against the SAME
`k.escrows.find? (matchPred id)` (the §helper reductions): when it is `some r`, the gate's `Bool` is
exactly the kernel `if` condition (bridge-tagged + disclosed `(asset, amount)` match), the single-write
body reduces to `bridgeFinalizeRawAsset k id`, so the IR post-state is on the nose
`bridgeFinalizeRawAsset k id`; when it is `none`, both sides are `none`. -/
theorem interp_bridgeFinalizeStmt_eq_bridgeFinalizeKAsset (id : Nat) (asset : AssetId) (amount : ℤ)
    (k : RecordKernelState) :
    interp (bridgeFinalizeStmt id asset amount) k = bridgeFinalizeKAsset k id asset amount := by
  -- Reduce the IR `interp` to: gate `if`, then the single component-write bind.
  simp only [bridgeFinalizeStmt, interp, Option.bind]
  -- Case-split on the SHARED find-term (the gate and the kernel both read it).
  cases hf : k.escrows.find? (matchPred id) with
  | none =>
    -- no record found: the gate is `false` ⇒ IR returns `none`; so does the kernel.
    rw [bridgeFinalizeGuard_none hf, bridgeFinalizeKAsset_none hf]; rfl
  | some r =>
    -- record `r` found: rewrite the gate (the `if` condition) and the kernel to their `some r` forms.
    rw [bridgeFinalizeGuard_some hf, bridgeFinalizeKAsset_some hf]
    by_cases hg : r.bridge = true ∧ r.asset = asset ∧ r.amount = amount
    · -- ADMIT: gate `Bool` is `true` ⇒ the gate `if` fires (`some k`), the bind applies the single
      -- write to `k`, giving `bridgeFinalizeRawAsset k id`; the kernel `if` fires on the matching Prop.
      simp only [decide_eq_true_eq.mpr hg, if_true, if_pos hg, bridgeFinalizeRawAsset]
    · -- REJECT: the gate `Bool` is `false` ⇒ the gate `if` is `none`, the bind is `none`; the kernel
      -- `if` closes on the negated Prop.
      simp only [decide_eq_false_iff_not.mpr hg, Bool.false_eq_true, if_false, if_neg hg]

#assert_axioms interp_bridgeFinalizeStmt_eq_bridgeFinalizeKAsset

/-! ## §3 — NON-VACUITY of the cornerstone: the settle term genuinely RESOLVES a parked bridge record.

The cornerstone would be hollow if `bridgeFinalizeStmt` never committed. On a one-account kernel holding
a single unresolved BRIDGE record for `id = 9` (asset `1`, amount `30`), the term commits and the
record's `resolved` flag flips `false → true` (the side-table REPLACE is real, not a no-op), while a
query of a missing id (`8`), a mismatched amount (`99`), and a NON-bridge record each reject. -/

/-- A one-cell kernel (account `0` Live) holding ONE unresolved BRIDGE record (`id 9`, creator `0`,
recipient `1`, amount `30`, asset `1`, bridge `true`). The bridge tag + matching `(asset, amount)` are
what the finalize gate exercises (the bare `bal` is framed-unchanged, so the credit is a non-issue). -/
def kBF : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [("balance", .int 0)], caps := fun _ => []
    escrows := [{ id := 9, creator := 0, recipient := 1, amount := 30, resolved := false,
                  asset := 1, bridge := true }] }

/-- **`bridgeFinalizeStmt_resolves` — the no-credit settle is OBSERVABLE.** Running the finalize term
for `id = 9` / `asset = 1` / `amount = 30` on `kBF` commits and flips the parked record's `resolved`
flag `false → true` (via `markResolved`): the side-table settle is a real, observable state edit, not a
no-op. -/
theorem bridgeFinalizeStmt_resolves :
    (interp (bridgeFinalizeStmt 9 1 30) kBF).map
        (fun k => (k.escrows.find? (fun r => decide (r.id = 9))).map (·.resolved))
      = some (some true) := by
  rw [interp_bridgeFinalizeStmt_eq_bridgeFinalizeKAsset]
  decide

/-- **`bridgeFinalizeStmt_rejects_missing` — fail-closed on a missing id.** A finalize query for an id
with no parked record (`8`) rejects (`none`): the `find?`-gate genuinely fails closed. -/
theorem bridgeFinalizeStmt_rejects_missing :
    interp (bridgeFinalizeStmt 8 1 30) kBF = none := by
  rw [interp_bridgeFinalizeStmt_eq_bridgeFinalizeKAsset]
  decide

/-- **`bridgeFinalizeStmt_rejects_mismatch` — fail-closed on a disclosed-amount mismatch.** A finalize
disclosing `amount = 99` against the parked `30` rejects (`none`): the receipt-vs-pending check is a
genuine, non-vacuous reject (no cross-amount laundering at the bridge boundary). -/
theorem bridgeFinalizeStmt_rejects_mismatch :
    interp (bridgeFinalizeStmt 9 1 99) kBF = none := by
  rw [interp_bridgeFinalizeStmt_eq_bridgeFinalizeKAsset]
  decide

/-- A one-cell kernel holding an ORDINARY (non-bridge) escrow record with the SAME id `9`. A finalize
must REJECT it (only bridge-tagged records are finalizable). -/
def kBF_nonBridge : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [("balance", .int 0)], caps := fun _ => []
    escrows := [{ id := 9, creator := 0, recipient := 1, amount := 30, resolved := false,
                  asset := 1, bridge := false }] }

/-- **`bridgeFinalizeStmt_rejects_nonBridge` — fail-closed on a non-bridge record.** An ordinary escrow
row in the shared holding-store is NOT finalizable: the bridge-tag gate rejects it (`none`). -/
theorem bridgeFinalizeStmt_rejects_nonBridge :
    interp (bridgeFinalizeStmt 9 1 30) kBF_nonBridge = none := by
  rw [interp_bridgeFinalizeStmt_eq_bridgeFinalizeKAsset]
  decide

#assert_axioms bridgeFinalizeStmt_resolves
#assert_axioms bridgeFinalizeStmt_rejects_missing
#assert_axioms bridgeFinalizeStmt_rejects_mismatch
#assert_axioms bridgeFinalizeStmt_rejects_nonBridge

/-! ## §4 — THE WELD: the audited class-A genuine descriptor agrees, per cell, with the IR term's
executor interpretation — AND forces the genuine `escrows`-root recompute.

The SAME shape as the release/refund welds: route the circuit side through the audited
`bridgeFinalizeGenuine_sound` (`EffectVmEmitBridgeFinalize §H`) and the executor side through the
cornerstone above + the per-cell projection `bridgeFinalizeKAsset_proj` — except the conserved leg is a
FREEZE (no credit), and the nonce-tick is RECONCILED to the turn (descriptor TICKS, executor FREEZES;
`NonceReconciled` discharged to the prologue's single tick — NOT a carried divergence). -/

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitBridgeFinalize
  (bridgeFinalizeVmDescriptorGenuine bridgeFinalizeGenuine_sound IsBridgeFinalizeRow
   RowEncodesFinalize CellFinalizeSpec cellProjFinalize)

/-! ### §4.0 — `compileBridgeFinalize` — the effect-keyed circuit interpretation of the term.

Mirroring `Argus/Compile.lean`'s `compileE` (which keys on the effect, not the raw `RecStmt` shape — the
structural match cannot separate same-shaped effects), we name the bridgeFinalize circuit directly as
the audited class-A genuine descriptor. `compileBridgeFinalize = bridgeFinalizeVmDescriptorGenuine` by
`rfl`, so the circuit interpretation of the bridgeFinalize term is, on the nose, the descriptor the Rust
prover runs for the bridge-outbound-finalize. -/

/-- The circuit interpretation of the bridgeFinalize IR term: the audited class-A genuine descriptor
(genuine in-row escrow-root recompute + per-cell freeze/nonce-tick + commitment). -/
def compileBridgeFinalize : Dregg2.Circuit.Emit.EffectVmEmit.EffectVmDescriptor :=
  bridgeFinalizeVmDescriptorGenuine

/-- **`compileBridgeFinalize_eq` — `compileBridgeFinalize` IS the audited runnable genuine descriptor.**
Definitional. -/
theorem compileBridgeFinalize_eq :
    compileBridgeFinalize = bridgeFinalizeVmDescriptorGenuine := rfl

#assert_axioms compileBridgeFinalize_eq

/-! ### §4.1 — the EXECUTOR-side per-cell projection of the kernel step `bridgeFinalizeKAsset`.

The cornerstone refines the IR term to `bridgeFinalizeKAsset` (the `RecordKernelState → Option
RecordKernelState` kernel step). We need its per-cell projection onto `cellProjFinalize …bal c asset` —
the `bridgeFinalizeKAsset` analog of release/refund's `…_proj_balLo`, except this is a FREEZE (no credit):
`bridgeFinalizeRawAsset` leaves `bal` UNTOUCHED, so the projected `(c, asset)` entry is FROZEN for ANY
cell `c`/`asset`. The frozen frame (balHi/nonce/fields/capRoot/reserved) is `0 = 0` on both projections
(definitional). -/

/-- **`bridgeFinalizeKAsset_proj_bal_frozen`.** A committed kernel finalize FREEZES every cell's
projected `(c, asset)` ledger entry (`bridgeFinalizeRawAsset` rewrites only `escrows`, not `bal`), for
ANY cell `c`/`asset`. The per-cell conserved leg the weld pins: a no-credit outflow leaves the per-cell
ledger entry exactly where it was (the value already departed at lock). -/
theorem bridgeFinalizeKAsset_proj_bal_frozen {k k' : RecordKernelState} {id : Nat} {asset0 : AssetId}
    {amount0 : ℤ} (c : CellId) (asset : AssetId)
    (h : bridgeFinalizeKAsset k id asset0 amount0 = some k') :
    (cellProjFinalize k'.bal c asset).balLo = (cellProjFinalize k.bal c asset).balLo := by
  -- reduce the kernel `match`/`if` on the find-term; on commit `k' = bridgeFinalizeRawAsset k id`, whose
  -- `bal` is `k.bal` (only `escrows` is rewritten), so the projected entry is unchanged.
  cases hf : k.escrows.find? (matchPred id) with
  | none => rw [bridgeFinalizeKAsset_none hf] at h; exact absurd h (by simp)
  | some r =>
    rw [bridgeFinalizeKAsset_some hf] at h
    by_cases hg : r.bridge = true ∧ r.asset = asset0 ∧ r.amount = amount0
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
      -- `(cellProjFinalize (bridgeFinalizeRawAsset k id).bal c asset).balLo = k.bal c asset`
      show (bridgeFinalizeRawAsset k id).bal c asset = k.bal c asset
      rfl
    · rw [if_neg hg] at h; exact absurd h (by simp)

#assert_axioms bridgeFinalizeKAsset_proj_bal_frozen

/-! ### §4.2 — THE WELD. -/

/-- **`bridgeFinalize_compile_sound` — the welded soundness (bridgeFinalize slice, the no-credit settle
side-table effect).**

Suppose, for the Argus bridgeFinalize term `bridgeFinalizeStmt id asset amount`, on a bridge-finalize row
(`hrow`):
  * the circuit `compileBridgeFinalize` (= the audited class-A `bridgeFinalizeVmDescriptorGenuine`) is
    SATISFIED by `(env, true, true)` under the abstract Poseidon carrier `hash`, and its
    `RowEncodesFinalize` decoding NAMES the post-state record `post` over ANY cell's projection
    `cellProjFinalize k.bal c asset` (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS:
    `interp (bridgeFinalizeStmt id asset amount) k = some k'` (`hexec`).

Then:
  * **conserved leg (per-cell):** the circuit's pinned post-state `post` AGREES with the executor's
    FROZEN projection `cellProjFinalize k'.bal c asset` — the conserved `balLo` (FROZEN, no credit) AND
    the whole frozen frame (balHi/fields/capRoot/reserved). The ONE divergence — the descriptor TICKS the
    cell nonce while the executor FREEZES it (`cellProjFinalize` sends `nonce` to `0`; the descriptor's
    `CellFinalizeSpec` demands `+ 1`) — is reported as the final conjunct, exactly as the transfer/burn
    welds.
  * **side-table leg:** the circuit FORCES the new escrow-list root carrier to be the genuine in-row
    recompute `hash[ hash[id,creator,recipient,amount,asset,resolved], old_root ]` of the bound record +
    old root — the digest the executor's `escrows := markResolved k.escrows id` resolve commits to
    (absorbed into `state_commit`, so the resolved record is bound; see
    `bridgeFinalizeGenuine_binds_record`).

So the class-A circuit the prover runs for bridgeFinalize pins the per-cell FROZEN state the IR term's
executor produces (the nonce reconciled to the turn's one prologue tick) AND genuinely recomputes the
bound `escrows`
side-table root — the template generalizes to the no-credit OUTFLOW settle leg. -/
theorem bridgeFinalize_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeFinalizeRow env)
    (k k' : RecordKernelState) (id : Nat) (asset : AssetId) (amount : ℤ)
    (c : CellId) (cellAsset : AssetId) (post : CellState)
    (henc : RowEncodesFinalize env (cellProjFinalize k.bal c cellAsset) post)
    (hsat : satisfiedVm hash compileBridgeFinalize env true true)
    (hexec : interp (bridgeFinalizeStmt id asset amount) k = some k') :
    -- conserved leg: the frozen cell's projection agrees on balLo + the whole frozen frame …
    ( post.balLo = (cellProjFinalize k'.bal c cellAsset).balLo
      ∧ post.balHi = (cellProjFinalize k'.bal c cellAsset).balHi
      ∧ (∀ i, post.fields i = (cellProjFinalize k'.bal c cellAsset).fields i)
      ∧ post.capRoot = (cellProjFinalize k'.bal c cellAsset).capRoot
      ∧ post.reserved = (cellProjFinalize k'.bal c cellAsset).reserved )
    -- … and the per-effect nonce is RECONCILED (NOT a divergence): the descriptor TICKS the cell nonce,
    --   the executor FREEZES it; the turn PROLOGUE's single tick is the net.
    ∧ NonceReconciled (cellProjFinalize k.bal c cellAsset).nonce post.nonce
        (cellProjFinalize k'.bal c cellAsset).nonce
    -- … and the SIDE-TABLE leg: the circuit FORCES the genuine escrow-list-root recompute (the bound
    -- resolved record + old root), absorbed into `state_commit`.
    ∧ ( env.loc Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.SYS_DIG_AFTER
          = Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.advanceOf hash
              (Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.leafOf hash
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.ID))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.CREATOR))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.RECIPIENT))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.AMOUNT))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.ASSET))
                (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.ep.RESOLVED)))
              (env.loc Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot.SYS_DIG_BEFORE) ) := by
  -- circuit side: `compileBridgeFinalize` IS the genuine descriptor; the audited class-A soundness forces
  -- the per-cell `CellFinalizeSpec` (frame freeze + nonce tick) + the genuine root recompute.
  rw [compileBridgeFinalize_eq] at hsat
  obtain ⟨hcs, hroot, _hcommit⟩ :=
    bridgeFinalizeGenuine_sound hash env hrow (cellProjFinalize k.bal c cellAsset) post henc hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcs
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the verified kernel step
  -- `bridgeFinalizeKAsset`; its per-cell projection FREEZES the balLo (the frozen limbs are `0 = 0`).
  rw [interp_bridgeFinalizeStmt_eq_bridgeFinalizeKAsset] at hexec
  have heFrozen := bridgeFinalizeKAsset_proj_bal_frozen c cellAsset hexec
  -- the descriptor tick `hcN` (post = pre.nonce + 1) + the executor freeze (`rfl`: `cellProjFinalize`
  -- zeroes both nonces) ARE `NonceReconciled`'s two clauses.
  refine ⟨⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl⟩,
    ⟨hcN, rfl⟩, hroot⟩
  -- balLo: circuit pins post = pre (FROZEN); executor freezes the projected entry ⇒ post = k'-projection.
  · rw [hcLo, heFrozen]

#assert_axioms bridgeFinalize_compile_sound

/-- **`bridgeFinalize_compile_sound_nonce_is_turn_tick` — the close, applied to bridgeFinalize.** The
`NonceReconciled` that `bridgeFinalize_compile_sound` yields, composed with a turn prologue over the
frozen cell `c` (read as the turn's agent), gives the whole-turn ONE-tick law: the body freezes (zero
contribution), the prologue ticks once, and the descriptor's per-effect post nonce EQUALS that single
prologue tick. So bridgeFinalize's row `+1` is the turn's one tick — the divergence is CLOSED. -/
theorem bridgeFinalize_compile_sound_nonce_is_turn_tick
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeFinalizeRow env)
    (k k' : RecordKernelState) (id : Nat) (asset : AssetId) (amount : ℤ)
    (c : CellId) (cellAsset : AssetId) (post : CellState)
    (henc : RowEncodesFinalize env (cellProjFinalize k.bal c cellAsset) post)
    (hsat : satisfiedVm hash compileBridgeFinalize env true true)
    (hexec : interp (bridgeFinalizeStmt id asset amount) k = some k')
    (s : RecChainedState) (fee : Int)
    (hpre  : (cellProjFinalize k.bal c cellAsset).nonce
               = Dregg2.Exec.EffectTransfer.nonceOf (s.kernel.cell c))
    (hexecAgent : (cellProjFinalize k'.bal c cellAsset).nonce
                    = Dregg2.Exec.EffectTransfer.nonceOf (s.kernel.cell c)) :
    Dregg2.Exec.EffectTransfer.nonceOf
        ((Dregg2.Exec.Admission.commitPrologue s c fee).kernel.cell c)
      = Dregg2.Exec.EffectTransfer.nonceOf (s.kernel.cell c) + 1
    ∧ post.nonce = Dregg2.Exec.EffectTransfer.nonceOf
        ((Dregg2.Exec.Admission.commitPrologue s c fee).kernel.cell c)
    ∧ post.nonce = (cellProjFinalize k'.bal c cellAsset).nonce + 1 := by
  have hr : NonceReconciled (cellProjFinalize k.bal c cellAsset).nonce post.nonce
              (cellProjFinalize k'.bal c cellAsset).nonce :=
    (bridgeFinalize_compile_sound hash env hrow k k' id asset amount c cellAsset post
      henc hsat hexec).2.1
  obtain ⟨_hzero, htick, hmatch, hresid⟩ :=
    Dregg2.Circuit.Argus.perEffect_nonce_reconciles_to_turn hr s c fee hexecAgent hpre
  exact ⟨htick, hmatch, hresid⟩

#assert_axioms bridgeFinalize_compile_sound_nonce_is_turn_tick

/-! ### §4.3 — NON-VACUITY: `compileBridgeFinalize` is the genuine class-A descriptor, not a placeholder.

The weld would be worthless if `compileBridgeFinalize` were an inert/empty descriptor. It is the class-A
`bridgeFinalizeVmDescriptorGenuine`, carrying the 13+14+4+3 = 34 per-row gates (balance freeze + frame
freeze + nonce tick + boundary/transition) AND the 2+4 = 6 hash-sites (2 genuine escrow-root-recompute
sites + 4 commitment sites). So `bridgeFinalize_compile_sound` is a statement about a REAL class-A
circuit with a genuinely-recomputed side-table root (the same counts the release/refund genuine
descriptors carry). -/

/-- The compiled bridgeFinalize circuit is the NON-trivial class-A genuine descriptor: it carries the
13+14+4+3 = 34 constraints / 2+4 = 6 hash-sites / 2 range checks of the audited
`bridgeFinalizeVmDescriptorGenuine` (an empty placeholder would have 0/0/0). So
`bridgeFinalize_compile_sound` is about a genuine side-table-binding circuit. -/
theorem compileBridgeFinalize_nontrivial :
    compileBridgeFinalize.constraints.length = 34
    ∧ compileBridgeFinalize.hashSites.length = 6
    ∧ compileBridgeFinalize.ranges.length = 2 := by
  rw [compileBridgeFinalize_eq]
  refine ⟨by decide, by decide, by decide⟩

#assert_axioms compileBridgeFinalize_nontrivial

end Dregg2.Circuit.Argus.Effects.BridgeFinalize
