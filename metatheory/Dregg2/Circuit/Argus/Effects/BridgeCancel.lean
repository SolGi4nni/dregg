/-
# Dregg2.Circuit.Argus.Effects.BridgeCancel — the BRIDGE-SETTLE-leg weld: bridgeCancel as an Argus IR term.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and `Argus/
Compile.lean` welded it to the circuit for transfer/mint/burn (single-cell) and **createEscrow** (the
two-component side-table CREATE). `Effects/RefundEscrow.lean` did the ordinary-escrow SETTLE leg. This
module does the cross-chain bridge's Phase-4 SETTLE — **bridgeCancel** (`cancel_bridge`: the timeout was
reached without a receipt, the parked bridge value is REFUNDED to the locker) — in its own disjoint
file, replicating the refundEscrow method without touching any shared Argus file.

## Why bridgeCancel is the SAME settle SHAPE as refundEscrow but a DIFFERENT circuit (the de-risk)

The EXECUTOR side is the refundEscrow settle shape with ONE extra gate conjunct. `bridgeCancelKAsset`
(`RecordKernel.lean:1813`) is a `find?`-keyed settle leg that READS an existing record and REFUNDS it:

  * it `find?`s the FIRST unresolved record carrying `id` (`matchPred id`, the kernel's
    `r.id = id ∧ r.resolved = false`), and FAILS (`none`) if none exists;
  * gated on the found record being a **BRIDGE** record (`r.bridge = true` — the ONE conjunct refund
    lacks; an ordinary escrow row sharing the holding-store is rejected) AND its **creator** (the refund
    target / originator) being a LIVE account whose lifecycle admits effects
    (`r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator`);
  * on commit it CREDITS the creator's `(creator, asset)` per-asset ledger entry by the record's
    `amount` (`settleEscrowRawAsset … r.creator r.asset r.amount` = `recBalCreditCell …`) AND marks the
    record resolved (`escrows := markResolved k.escrows id`).

So, like refund, the moved amount / target / asset are **read out of the found record `r`** and the
`escrows` write is a list **REPLACE-IN-PLACE** (`markResolved`). The §A component-write primitives
(`setBal`/`setEscrows`, `Stmt.lean`) already suffice — **no new IR primitive is needed** — because each
takes the full `k` and may run the `find?` inside its closure.

(The authority leg `r.creator = actor` and the timeout gate live in the WRAPPER `bridgeCancelChainA`
/`bridgeAuthOK`, NOT in the `RecordKernelState → Option RecordKernelState` kernel step — exactly as
refund's authority is not in `refundEscrowKAsset`. The IR `RecStmt` is a pure state-transformer, so
`bridgeCancelKAsset` is the faithful refinement target, the bridge twin of `refundEscrowKAsset`.)

The CIRCUIT side is genuinely DIFFERENT from refund, and the honest reason this module exists. The
audited bridgeCancel descriptor (`EffectVmEmitBridgeCancel`) was RECONCILED onto the running hand-AIR
trace layout (commit 3aaf0772d's notes pattern): on the cancel row the runtime performs **NO on-trace
balance move** (the refund credit binds OFF-trace via the `effects_hash` accumulator — the bridge state
"lives off-trace"), so the descriptor **FREEZES `bal_lo`** on the per-cell row, and the global nonce gate
**TICKS** the nonce. This is the OPPOSITE of refund's descriptor (which credits `bal_lo` on-trace and
freezes the nonce). The weld below is HONEST about that boundary — see HONEST SURFACE.

## What this module proves (the two task theorems, on the bridge-settle shape)

  1. `interp_bridgeCancelStmt_eq_bridgeCancelKAsset` — the executor IS the term: `interp` of the
     bridgeCancel IR term is, on the nose, the verified kernel step `bridgeCancelKAsset`.
  2. `bridgeCancel_compile_sound` — the weld: a satisfying witness of the AUDITED class-A genuine
     descriptor `bridgeCancelVmDescriptorGenuine` (`EffectVmEmitBridgeCancel §H`) agrees, per cell, with
     the post-state the IR term's executor produces ON A BYSTANDER CELL (where both freeze), AND forces
     the genuine bridge-escrow-root recompute; the refunded-cell on-trace-freeze-vs-executor-credit
     divergence is REPORTED, not papered (`bridgeCancel_refunded_cell_divergence`).

## HONEST SURFACE (precise — do NOT over-read)

The honest boundary is the bridge-settle reconciliation the Emit module establishes (§9–§11), routed
through the IR cornerstone:

  * **conserved leg (per-cell, BYSTANDER):** the descriptor FREEZES every conserved cell column on-trace
    (the refund credit binds off-trace). A BYSTANDER cell `c`/`asset` — one the cancel's executor frame
    leaves untouched (captured by `hframe : k'.bal c asset = k.bal c asset`) — is genuinely frozen by
    BOTH the descriptor (`CellCancelSpec`'s bal-freeze) and the executor's frame, so they AGREE on balLo
    + the whole non-nonce frame (balHi/fields/capRoot/reserved). This is the SURFACE
    `EffectVmEmitBridgeCancel.descriptor_agrees_with_executor_cancel_frame` proves, now welded to the IR
    term. The cross-cell combined-per-asset conservation (ledger credit ⊕ holding-store drop) is the
    executor's keystone (`bridge_cancel_conserves_combined_per_asset`), cited there — NOT re-claimed.
  * **the nonce-TICK divergence is REAL and carried (not papered):** the descriptor TICKS the cell nonce
    while the executor's per-cell projection freezes it at `0`. `bridgeCancel_compile_sound` exposes this
    as an explicit conjunct, identical to the form `descriptor_agrees_with_executor_cancel_frame` carries.
  * **the REFUNDED-cell credit divergence is REAL and reported:** at the refunded `(r.creator, r.asset)`
    the descriptor FREEZES `bal_lo` on-trace while the executor CREDITS it by `+r.amount`; they reconcile
    ONLY at `r.amount = 0`. We surface this precisely (`bridgeCancel_refunded_cell_divergence`) — the
    bridge twin of the Emit module's `runtime_frozen_vs_univA_credit_divergence`. The refund credit lives
    off the per-cell row (the `effects_hash` accumulator), reported not papered.
  * **side-table leg (the resolved record):** the circuit FORCES the new escrow-list root to be the
    genuine in-row recompute `hash[ hash[id,creator,recipient,amount,asset,resolved], old_root ]` of the
    bound record + old root (`bridgeCancelGenuine_sound`'s clause (b)), absorbed into `state_commit`. So
    under `Poseidon2SpongeCR` the resolved bridge record is bound — a dropped/forged resolve MOVES the
    commitment (`bridgeCancelGenuine_binds_record`, cited). The weld EXPOSES this genuine-recompute
    clause as a conjunct so the side-table binding is part of the welded statement, not a side remark.

  What this does NOT claim: it does not assert the descriptor credits the refunded cell `bal_lo`
  on-trace (it freezes it — the credit is off-trace), and it does not assert the circuit row's
  `escrows`-list state EQUALS the executor's `markResolved k.escrows id` as a LIST (the EffectVM row
  carries a DIGEST, not the list — the `SystemRoots` digest connector). The executor produces the real
  list (the cornerstone + `markResolved`); the circuit produces the genuine root of it. That is the
  faithful digest-not-list, on-trace-vs-off-trace boundary, stated, not hidden.

## Honesty

`#assert_axioms` on both theorems ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `:= True`
vacuity, no weakening-that-just-typechecks. Imports are read-only; this file owns only itself and edits
no other Argus module.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitBridgeCancel

namespace Dregg2.Circuit.Argus.Effects.BridgeCancel

open Dregg2.Exec
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Exec (RecordKernelState EscrowRecord CellId AssetId
  bridgeCancelKAsset settleEscrowRawAsset markResolved recBalCreditCell cellLifecycleLive)

/-! ## §1 — the gate + the body leaves (the bridge-settle shape: a `find?`-keyed gate, record-reading
writes). `bridgeCancelKAsset k id` admits iff a matching unresolved BRIDGE record EXISTS and its creator
passes the settle-liveness gate; on commit it credits that creator and marks the record resolved. We
render the gate as a `Bool` over `k` and the two writes as closures that `find?` the record inside. -/

/-- The find-predicate `bridgeCancelKAsset` uses (the kernel's `r.id = id ∧ r.resolved = false`). Named
locally so the IR term + the proofs read against the SAME predicate the executor uses. -/
def matchPred (id : Nat) : EscrowRecord → Bool := fun r => decide (r.id = id ∧ r.resolved = false)

/-- The bridge-cancel admissibility gate as a `Bool` — exactly `bridgeCancelKAsset`'s admission: a
matching unresolved record EXISTS, it is a BRIDGE record (`r.bridge` — the ONE conjunct refund lacks),
and its creator (the refund target / originator) is a LIVE account whose lifecycle admits effects.
`none` (no such record) fails closed. -/
def bridgeCancelGuard (id : Nat) (k : RecordKernelState) : Bool :=
  match k.escrows.find? (matchPred id) with
  | some r => r.bridge && decide (r.creator ∈ k.accounts) && cellLifecycleLive k r.creator
  | none   => false

/-- The bridge-cancel `bal`-write leaf: credit the FOUND record's `creator` at the record's `asset` by
the record's `amount` (the value parked off-ledger, now refunded). Total in `k`: when no record is
found it is the identity ledger (the gate then rejects, so this branch is never committed). -/
def bridgeCancelBalLeaf (id : Nat) (k : RecordKernelState) : CellId → AssetId → Int :=
  match k.escrows.find? (matchPred id) with
  | some r => recBalCreditCell k.bal r.creator r.asset r.amount
  | none   => k.bal

/-- The bridge-cancel effect as an IR term: gate, then the TWO component writes — credit the found
record's creator on the per-asset ledger (`setBal`), then mark the record resolved on the `escrows`
side-table (`setEscrows`). The bridge-settle analog of `refundEscrowStmt`: same `seq (guard …) (seq
(setBal …) (setEscrows …))` skeleton, the leaves READ the record out of `k`, and the `escrows` write is
a list REPLACE (`markResolved`), not a prepend. No new IR constructor is used. -/
def bridgeCancelStmt (id : Nat) : RecStmt :=
  RecStmt.seq (RecStmt.guard (bridgeCancelGuard id))
    (RecStmt.seq
      (RecStmt.setBal (fun k => bridgeCancelBalLeaf id k))
      (RecStmt.setEscrows (fun k => markResolved k.escrows id)))

/-! ## §2 — the gate decodes to `bridgeCancelKAsset`'s admission, and the body IS `settleEscrowRawAsset`.

Two ingredients, exactly as refund: (a) the `Bool` gate equals the kernel step's `if` condition on the
found record (the bridge ∧ creator-live conjunction), and (b) the two-component body reduces to the
kernel's commit post-state. The load-bearing settle fact: the `setBal` leaf and the gate BOTH `find?`
the SAME record `r`, so when the gate commits, the credit lands on `r.creator`/`r.asset`/`r.amount`. -/

/-- The escrows side-table is NOT touched by the `setBal` write, so the `setEscrows` leaf — read on the
intermediate post-`setBal` state — sees the ORIGINAL `escrows`, hence `markResolved` lands on the
original list (the refund-side `refundEscrowBody_eq` analog). The side-table interleaving the single-cell
effects never exercised. -/
theorem bridgeCancelBody_eq (id : Nat) (k : RecordKernelState) :
    interp (RecStmt.seq
        (RecStmt.setBal (fun k => bridgeCancelBalLeaf id k))
        (RecStmt.setEscrows (fun k => markResolved k.escrows id))) k
      = some { k with bal := bridgeCancelBalLeaf id k, escrows := markResolved k.escrows id } := by
  simp only [interp, Option.bind]

/-- The gate `match` reduces on `hf` (the same find-term the kernel reads). A `none` find fails the
gate; a `some r` find leaves the bridge ∧ liveness `Bool`. -/
private theorem bridgeCancelGuard_none {id : Nat} {k : RecordKernelState}
    (hf : k.escrows.find? (matchPred id) = none) : bridgeCancelGuard id k = false := by
  simp only [bridgeCancelGuard, hf]

private theorem bridgeCancelGuard_some {id : Nat} {k : RecordKernelState} {r : EscrowRecord}
    (hf : k.escrows.find? (matchPred id) = some r) :
    bridgeCancelGuard id k
      = (r.bridge && decide (r.creator ∈ k.accounts) && cellLifecycleLive k r.creator) := by
  simp only [bridgeCancelGuard, hf]

/-- The `setBal` leaf reduces on `hf` to the found record's credit. -/
private theorem bridgeCancelBalLeaf_some {id : Nat} {k : RecordKernelState} {r : EscrowRecord}
    (hf : k.escrows.find? (matchPred id) = some r) :
    bridgeCancelBalLeaf id k = recBalCreditCell k.bal r.creator r.asset r.amount := by
  simp only [bridgeCancelBalLeaf, hf]

/-- The kernel step reduces on `hf`: a `none` find rejects; a `some r` find opens the bridge ∧ liveness
`if` over `settleEscrowRawAsset`. `matchPred` is the common spelling of the kernel's inlined predicate. -/
private theorem bridgeCancelKAsset_none {id : Nat} {k : RecordKernelState}
    (hf : k.escrows.find? (matchPred id) = none) : bridgeCancelKAsset k id = none := by
  have hf' : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = none := hf
  simp only [bridgeCancelKAsset, hf']

private theorem bridgeCancelKAsset_some {id : Nat} {k : RecordKernelState} {r : EscrowRecord}
    (hf : k.escrows.find? (matchPred id) = some r) :
    bridgeCancelKAsset k id
      = if r.bridge = true ∧ r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true then
          some (settleEscrowRawAsset k id r.creator r.asset r.amount)
        else none := by
  have hf' : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r := hf
  simp only [bridgeCancelKAsset, hf']

/-- **The cornerstone (bridge-settle leg).** `interp` of the bridgeCancel term IS the verified kernel
step `bridgeCancelKAsset` — the same partial function, by construction, exactly as the transfer/mint/
burn/createEscrow/refundEscrow cornerstones, now over a BRIDGE settle leg (`find?`-keyed, bridge-gated,
record-reading, replace-in-place).

The proof opens the `find?` on the kernel side and the gate's `match` on the IR side against the SAME
`k.escrows.find? (matchPred id)`: when it is `some r`, the gate's `Bool` is exactly the kernel `if`
condition (`r.bridge ∧ creator-member ∧ creator-live`), the body's `bridgeCancelBalLeaf` reduces to the
same `some r` credit, so the IR post-state is on the nose `settleEscrowRawAsset k id r.creator r.asset
r.amount`; when it is `none`, both sides are `none`. -/
theorem interp_bridgeCancelStmt_eq_bridgeCancelKAsset (id : Nat) (k : RecordKernelState) :
    interp (bridgeCancelStmt id) k = bridgeCancelKAsset k id := by
  -- Reduce the IR `interp` to: gate `if`, then the two component-write binds.
  simp only [bridgeCancelStmt, interp, Option.bind]
  -- Case-split on the SHARED find-term (the gate, the `setBal` leaf, and the kernel all read it).
  cases hf : k.escrows.find? (matchPred id) with
  | none =>
    -- no record found: the gate is `false` ⇒ IR returns `none`; so does the kernel.
    rw [bridgeCancelGuard_none hf, bridgeCancelKAsset_none hf]; rfl
  | some r =>
    -- record `r` found: rewrite the gate (the `if` condition) and the kernel to their `some r` forms.
    rw [bridgeCancelGuard_some hf, bridgeCancelKAsset_some hf]
    by_cases hg : r.bridge = true ∧ r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true
    · -- ADMIT: gate `Bool` is `true` ⇒ the gate `if` fires (`some k`), the bind applies the writes to
      -- `k` (exposing `bridgeCancelBalLeaf id k`); the kernel `if` fires on the matching Prop. Both
      -- sides become `settleEscrowRawAsset`'s post-state.
      obtain ⟨hbr, hacc, hlive⟩ := hg
      simp only [hbr, decide_eq_true_eq.mpr hacc, hlive, Bool.and_self, if_true,
        and_true, true_and, if_pos hacc, bridgeCancelBalLeaf_some hf, settleEscrowRawAsset]
    · -- REJECT: the gate `Bool` is `false` ⇒ the gate `if` is `none`, the bind is `none`; the kernel
      -- `if` closes on the negated Prop.
      have hgb : (r.bridge && decide (r.creator ∈ k.accounts) && cellLifecycleLive k r.creator)
          = false := by
        rcases Classical.em (r.bridge = true) with hbr | hbr
        · rcases Classical.em (r.creator ∈ k.accounts) with hin | hin
          · -- bridge ∧ member ⇒ liveness must be the failing leg.
            have hlf : cellLifecycleLive k r.creator = false := by
              by_contra hne; exact hg ⟨hbr, hin, by simpa using hne⟩
            simp [hbr, hin, hlf]
          · simp [hin]
        · simp [hbr]
      simp only [hgb, Bool.false_eq_true, if_false, if_neg hg]

#assert_axioms interp_bridgeCancelStmt_eq_bridgeCancelKAsset

/-! ## §3 — NON-VACUITY of the cornerstone: the bridge-settle term genuinely RESOLVES a parked bridge
record. The cornerstone would be hollow if `bridgeCancelStmt` never committed. On a one-account kernel
holding a single unresolved BRIDGE record for `id = 7` (creator = account `0`, live), the term commits
and the record's `resolved` flag flips `false → true` (the side-table REPLACE is real, not a no-op),
while a query of a missing id (`9`) rejects, and an ORDINARY (non-bridge) record also rejects. -/

/-- A one-cell kernel (account `0` Live) holding ONE unresolved BRIDGE record (`id 7`, creator `0`,
amount `0`, asset `0`, `bridge := true`). The `0` amount keeps the credit trivial so the only thing the
witness exercises is the `find?`-gate + the `markResolved` side-table replace. -/
def kBC : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [("balance", .int 0)], caps := fun _ => []
    escrows := [{ id := 7, creator := 0, recipient := 0, amount := 0, resolved := false,
                  asset := 0, bridge := true }] }

/-- A one-cell kernel identical to `kBC` but holding an ORDINARY (non-bridge) record — the bridge-cancel
gate must REJECT it (the `r.bridge` leg fails closed; the holding-store is shared with plain escrow). -/
def kBCordinary : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [("balance", .int 0)], caps := fun _ => []
    escrows := [{ id := 7, creator := 0, recipient := 0, amount := 0, resolved := false,
                  asset := 0, bridge := false }] }

/-- **`bridgeCancelStmt_resolves` — the bridge-settle is OBSERVABLE.** Running the bridgeCancel term for
`id = 7` on `kBC` commits and flips the parked bridge record's `resolved` flag `false → true` (via
`markResolved`): the side-table settle is a real, observable state edit, not a no-op. -/
theorem bridgeCancelStmt_resolves :
    (interp (bridgeCancelStmt 7) kBC).map
        (fun k => (k.escrows.find? (fun r => decide (r.id = 7))).map (·.resolved))
      = some (some true) := by
  rw [interp_bridgeCancelStmt_eq_bridgeCancelKAsset]
  decide

/-- **`bridgeCancelStmt_rejects_missing` — fail-closed on a missing id.** A bridge-cancel query for an
id with no parked record (`9`) rejects (`none`): the `find?`-gate genuinely fails closed. -/
theorem bridgeCancelStmt_rejects_missing :
    interp (bridgeCancelStmt 9) kBC = none := by
  rw [interp_bridgeCancelStmt_eq_bridgeCancelKAsset]
  decide

/-- **`bridgeCancelStmt_rejects_nonbridge` — fail-closed on an ordinary record.** A bridge-cancel against
a found NON-bridge record (`kBCordinary`) rejects (`none`): the `r.bridge` gate leg fails closed — a
plain escrow row sharing the holding-store cannot be cancelled as a bridge. The leg refund LACKS. -/
theorem bridgeCancelStmt_rejects_nonbridge :
    interp (bridgeCancelStmt 7) kBCordinary = none := by
  rw [interp_bridgeCancelStmt_eq_bridgeCancelKAsset]
  decide

#assert_axioms bridgeCancelStmt_resolves
#assert_axioms bridgeCancelStmt_rejects_missing
#assert_axioms bridgeCancelStmt_rejects_nonbridge

/-! ## §4 — THE WELD: the audited class-A genuine descriptor agrees, per BYSTANDER cell, with the IR
term's executor interpretation — AND forces the genuine `escrows`-root recompute; the refunded-cell
on-trace-freeze-vs-executor-credit divergence (and the nonce-tick) are REPORTED, not papered.

The SAME shape as the refundEscrow weld (`Effects/RefundEscrow.lean §4`), reconciled onto the bridge
descriptor's RUNTIME convention: route the circuit side through the audited `bridgeCancelGenuine_sound`
(`EffectVmEmitBridgeCancel §H`) and the executor side through the §2 cornerstone + the per-cell BYSTANDER
frame projection `bridgeCancelKAsset_proj_frame`. Unlike refund (descriptor credits the cell on-trace,
matching the executor's credit on that cell), bridgeCancel FREEZES the cell on-trace (the refund binds
off-trace), so the on-trace agreement is on a BYSTANDER cell where BOTH freeze; the refunded cell is the
reported divergence. -/

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitBridgeCancel
  (bridgeCancelVmDescriptorGenuine bridgeCancelGenuine_sound IsBridgeCancelRow RowEncodesCancel
   CellCancelSpec cellProjCancel)

/-! ### §4.0 — `compileBridgeCancel` — the effect-keyed circuit interpretation of the bridgeCancel term.

Mirroring `Argus/Compile.lean`'s `compileE` (which keys on the effect, not the raw `RecStmt` shape — the
structural match cannot separate same-shaped effects), we name the bridgeCancel circuit directly as the
audited class-A genuine descriptor. `compileBridgeCancel = bridgeCancelVmDescriptorGenuine` by `rfl`, so
the circuit interpretation of the bridgeCancel term is, on the nose, the descriptor the Rust prover runs
for the bridge-cancel settle. -/

/-- The circuit interpretation of the bridgeCancel IR term: the audited class-A genuine descriptor
(genuine in-row bridge-escrow-root recompute + per-cell freeze/tick + commitment). -/
def compileBridgeCancel : EffectVmDescriptor := bridgeCancelVmDescriptorGenuine

/-- **`compileBridgeCancel_eq` — `compileBridgeCancel` IS the audited runnable bridge-cancel descriptor.**
Definitional. -/
theorem compileBridgeCancel_eq : compileBridgeCancel = bridgeCancelVmDescriptorGenuine := rfl

#assert_axioms compileBridgeCancel_eq

/-! ### §4.1 — the EXECUTOR-side per-cell BYSTANDER-frame projection of the kernel step
`bridgeCancelKAsset`. The cornerstone refines the IR term to `bridgeCancelKAsset`. Its on-trace agreement
is on a BYSTANDER cell `c`/`asset` — one the cancel leaves untouched. We prove: a committed cancel
FREEZES the projected `(c, asset)` ledger entry of any cell whose `bal` entry it does not move. The
descriptor freezes too (its `CellCancelSpec` bal-freeze), so they agree there. The frozen frame
(balHi/fields/capRoot/reserved) is `0 = 0` on both projections (definitional). -/

/-- **`bridgeCancelKAsset_proj_frame`.** A committed kernel bridge-cancel FREEZES the projected
`(c, asset)` ledger entry of a BYSTANDER cell — any `(c, asset)` whose raw entry it leaves unchanged
(`hframe`). The per-cell BYSTANDER leg the weld pins (the descriptor freezes on-trace, so they agree). -/
theorem bridgeCancelKAsset_proj_frame {k k' : RecordKernelState} {id : Nat} {c : CellId}
    {asset : AssetId} (_h : bridgeCancelKAsset k id = some k')
    (hframe : k'.bal c asset = k.bal c asset) :
    (cellProjCancel k'.bal c asset).balLo = (cellProjCancel k.bal c asset).balLo := by
  show k'.bal c asset = k.bal c asset
  exact hframe

#assert_axioms bridgeCancelKAsset_proj_frame

/-! ### §4.2 — THE WELD. -/

/-- **`bridgeCancel_compile_sound` — the welded soundness (bridgeCancel slice, the bridge-settle
side-table effect).**

Suppose, for the Argus bridgeCancel term `bridgeCancelStmt id`, a BYSTANDER cell `c`/`asset` (one the
cancel's executor frame leaves untouched, `hframe`), and a genuine bridge-cancel row (`hrow`):
  * the circuit `compileBridgeCancel` (= the audited class-A `bridgeCancelVmDescriptorGenuine`) is
    SATISFIED by `(env, true, true)` under the abstract Poseidon carrier `hash`, and its `RowEncodesCancel`
    decoding NAMES the post-state record `post` over the bystander cell's projection
    `cellProjCancel k.bal c asset` (`henc`; the cancel takes no on-trace move param);
  * the IR term's EXECUTOR interpretation COMMITS: `interp (bridgeCancelStmt id) k = some k'` (`hexec`).

Then:
  * **conserved leg (per-cell, BYSTANDER):** the circuit's pinned post-state `post` AGREES with the
    executor's FROZEN bystander projection `cellProjCancel k'.bal c asset` — the conserved `balLo`
    (FROZEN: the refund credit is off-trace, and `c` is a bystander) AND the whole non-nonce frame
    (balHi/fields/capRoot/reserved). The descriptor freezes `bal_lo` on-trace, matching the executor's
    frame on `c`.
  * **the nonce-TICK divergence (carried, not papered):** the descriptor TICKS the cell nonce while the
    executor's per-cell projection freezes it at `0` — reported as the final state conjunct, exactly as
    `descriptor_agrees_with_executor_cancel_frame` carries it.
  * **side-table leg:** the circuit FORCES the new escrow-list root carrier to be the genuine in-row
    recompute `hash[ hash[id,creator,recipient,amount,asset,resolved], old_root ]` of the bound record +
    old root — the digest the executor's `escrows := markResolved k.escrows id` resolve commits to
    (absorbed into `state_commit`, so the resolved record is bound; see `bridgeCancelGenuine_binds_record`).

So the class-A circuit the prover runs for bridgeCancel pins the per-cell bystander-frozen state the IR
term's executor produces AND genuinely recomputes the bound `escrows` side-table root. (The REFUNDED cell
`(r.creator, r.asset)` is the reported on-trace-freeze-vs-executor-credit divergence — see
`bridgeCancel_refunded_cell_divergence`; the refund binds off the per-cell row.) -/
theorem bridgeCancel_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeCancelRow env)
    (k k' : RecordKernelState) (id : Nat) (c : CellId) (asset : AssetId)
    (post : CellState)
    (hframe : k'.bal c asset = k.bal c asset)
    (henc : RowEncodesCancel env (cellProjCancel k.bal c asset) post)
    (hsat : satisfiedVm hash compileBridgeCancel env true true)
    (hexec : interp (bridgeCancelStmt id) k = some k') :
    -- conserved leg (BYSTANDER): the frozen bystander cell's projection agrees on balLo + the whole
    -- non-nonce frozen frame …
    ( post.balLo = (cellProjCancel k'.bal c asset).balLo
      ∧ post.balHi = (cellProjCancel k'.bal c asset).balHi
      ∧ (∀ i, post.fields i = (cellProjCancel k'.bal c asset).fields i)
      ∧ post.capRoot = (cellProjCancel k'.bal c asset).capRoot
      ∧ post.reserved = (cellProjCancel k'.bal c asset).reserved )
    -- … the nonce-TICK divergence (descriptor ticks; executor projection freezes at 0), carried …
    ∧ ( post.nonce = (cellProjCancel k.bal c asset).nonce + 1
        ∧ (cellProjCancel k'.bal c asset).nonce = (cellProjCancel k.bal c asset).nonce )
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
  -- circuit side: `compileBridgeCancel` IS the genuine descriptor; the audited class-A soundness forces
  -- the per-cell `CellCancelSpec` (bal-freeze + nonce-tick) + the genuine root recompute.
  rw [compileBridgeCancel_eq] at hsat
  obtain ⟨hcs, hroot, _hcommit⟩ :=
    bridgeCancelGenuine_sound hash env hrow (cellProjCancel k.bal c asset) post henc hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcs
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the verified kernel step
  -- `bridgeCancelKAsset`; its BYSTANDER projection freezes the projected balLo (the frozen limbs are
  -- `0 = 0`, and `cellProjCancel … .nonce = 0` on both sides).
  rw [interp_bridgeCancelStmt_eq_bridgeCancelKAsset] at hexec
  have heLo := bridgeCancelKAsset_proj_frame hexec hframe
  refine ⟨⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl⟩, ⟨?_, ?_⟩,
    hroot⟩
  · -- balLo: circuit pins post = pre.balLo (freeze); executor freezes the bystander entry (= pre.balLo).
    rw [hcLo, heLo]
  · -- the descriptor TICKS the cell nonce: post.nonce = (cellProjCancel k.bal c asset).nonce + 1.
    have hpreN : (cellProjCancel k.bal c asset).nonce = 0 := rfl
    rw [hcN, hpreN]
  · -- the executor's per-cell projection FREEZES the nonce (both projections send nonce to 0).
    rfl

#assert_axioms bridgeCancel_compile_sound

/-! ### §4.3 — the REPORTED divergence (refunded cell) + non-vacuity of the genuine descriptor.

The weld above is on a BYSTANDER cell (where both freeze). At the REFUNDED `(r.creator, r.asset)` the
descriptor's on-trace freeze and the executor's `+r.amount` credit DIVERGE — they reconcile only at
`r.amount = 0`. We surface this precisely (the bridge twin of the Emit module's
`runtime_frozen_vs_univA_credit_divergence`) so the boundary is reported, not papered. -/

/-- **`bridgeCancel_refunded_cell_divergence` — the on-trace-vs-off-trace refund gap, named precisely.**
A committed bridge-cancel CREDITS the found record's `(r.creator, r.asset)` entry by `+r.amount` on the
executor side, whereas the descriptor FREEZES `bal_lo` on-trace (the refund credit binds off the per-cell
row, via `effects_hash`). We expose BOTH: the executor's post-projection at the refunded cell is
`pre + r.amount`, while the descriptor's on-trace post would be the frozen `pre`. They reconcile ONLY at
`r.amount = 0` — the refund credit lives off-trace, reported not papered. -/
theorem bridgeCancel_refunded_cell_divergence {k k' : RecordKernelState} {id : Nat} {r : EscrowRecord}
    (h : interp (bridgeCancelStmt id) k = some k')
    (hr : k.escrows.find? (matchPred id) = some r) :
    (cellProjCancel k'.bal r.creator r.asset).balLo
      = (cellProjCancel k.bal r.creator r.asset).balLo + r.amount := by
  rw [interp_bridgeCancelStmt_eq_bridgeCancelKAsset] at h
  have hr' : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r := by
    simpa only [matchPred] using hr
  simp only [bridgeCancelKAsset, hr'] at h
  by_cases hg : r.bridge = true ∧ r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    show recBalCreditCell k.bal r.creator r.asset r.amount r.creator r.asset
      = k.bal r.creator r.asset + r.amount
    unfold recBalCreditCell; rw [if_pos ⟨rfl, rfl⟩]
  · rw [if_neg hg] at h; exact absurd h (by simp)

#assert_axioms bridgeCancel_refunded_cell_divergence

/-- The compiled bridgeCancel circuit is the NON-trivial class-A genuine descriptor: it carries the
13+14+4+3 = 34 constraints / 2+4 = 6 hash-sites / 2 range checks of the audited
`bridgeCancelVmDescriptorGenuine` (an empty placeholder would have 0/0/0). So `bridgeCancel_compile_sound`
is about a REAL class-A circuit with a genuinely-recomputed side-table root. -/
theorem compileBridgeCancel_nontrivial :
    compileBridgeCancel.constraints.length = 34
    ∧ compileBridgeCancel.hashSites.length = 6
    ∧ compileBridgeCancel.ranges.length = 2 := by
  rw [compileBridgeCancel_eq]
  refine ⟨by decide, by decide, by decide⟩

#assert_axioms compileBridgeCancel_nontrivial

end Dregg2.Circuit.Argus.Effects.BridgeCancel
