/-
# Dregg2.Circuit.Argus.Effects.RefundEscrow — the SETTLE-leg weld: refundEscrow as an Argus IR term.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and `Argus/
Compile.lean` welded it to the circuit for transfer/mint/burn (single-cell) and **createEscrow** (the
two-component side-table CREATE). This module does the OTHER escrow side — **refundEscrow**, a genuine
*settle* leg — in its own disjoint file, replicating the createEscrow method without touching any
shared Argus file.

## Why refundEscrow is a DIFFERENT shape from create (the de-risk this module buys)

createEscrow is an `if`-guarded INSERT: a five-conjunct `Bool` gate over the turn args, then a `bal`
DEBIT + an `escrows` PREPEND of a record built from the args. Every datum the body writes is a free
argument.

refundEscrow (`RecordKernel.refundEscrowKAsset`, `:1576`) is a *settle* leg that READS an existing
record and REFUNDS it:

  * it `find?`s the FIRST unresolved record carrying `id` (`matchPred id`, the kernel's
    `r.id = id ∧ r.resolved = false`), and FAILS (`none`) if none exists;
  * gated on the found record's **creator** (the refund target) being a LIVE account whose lifecycle
    admits effects (`r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator`);
  * on commit it CREDITS the creator's `(creator, asset)` per-asset ledger entry by the record's
    `amount` (`recBalCreditCell k.bal r.creator r.asset r.amount`) AND marks the record resolved
    (`escrows := markResolved k.escrows id`).

So unlike create, the moved amount / target / asset are NOT arguments — they are **read out of the
found record `r`**, and the `escrows` write is a list **REPLACE-IN-PLACE** (`markResolved`), not a
prepend. This is the settle-leg method: a `find?`-keyed gate, then two component writes whose leaves
themselves look the record up out of `k`. The §A component-write primitives (`setBal`/`setEscrows`,
`Stmt.lean`) already suffice — **no new IR primitive is needed** — because each takes the full `k` and
may run the `find?` inside its closure. (Reported in the module trailer: the template GENERALIZED.)

## What this module proves (the same two theorems as createEscrow, on the settle shape)

  1. `interp_refundEscrowStmt_eq_refundEscrowKAsset` — the executor IS the term: `interp` of the
     refundEscrow IR term is, on the nose, the verified kernel step `refundEscrowKAsset`.
  2. `refundEscrow_compile_sound` — the weld: a satisfying witness of the AUDITED class-A genuine
     descriptor `refundEscrowVmDescriptorGenuine` (`EffectVmEmitRefundEscrow`) agrees, per cell, with
     the post-state the IR term's executor produces, AND forces the genuine `escrows`-root recompute.

## HONEST SURFACE (precise — do NOT over-read)

Identical boundary to the createEscrow weld (`Argus/Compile.lean §E`), on the settle direction:

  * **conserved leg (per-cell):** the circuit's pinned post-`balLo` equals the executor's CREDITED
    creator-cell projection `cellProjRefund k'.bal r.creator r.asset` (= pre **+** `r.amount`), with the
    frozen frame (balHi/fields/capRoot/reserved/nonce) agreeing. `cellProjRefund` projects ONLY the
    `(creator, asset)` ledger entry into `balLo` (every other limb is `0`, FROZEN) — so this binds the
    REFUNDED cell, exactly as transfer binds the SRC cell. refundEscrow has NO nonce-tick divergence
    (the descriptor freezes the cell nonce, matching the executor — `cellProjRefund` sends `nonce` to
    `0` on both sides). The cross-cell combined-per-asset conservation (ledger credit ⊕ holding-store
    drop) is the executor's keystone (`escrow_*_conserves_combined_per_asset` family), cited there —
    NOT re-claimed here.
  * **side-table leg (the resolved record):** the circuit FORCES the new escrow-list root to be the
    genuine in-row recompute `hash[ hash[id,creator,recipient,amount,asset,resolved], old_root ]` of the
    bound record + old root (`refundEscrowGenuine_sound`'s clause (b), with `resolved = 1` on a refund),
    absorbed into `state_commit`. So under `Poseidon2SpongeCR` the resolved record is bound — a
    dropped/forged resolve MOVES the commitment (`refundEscrowGenuine_binds_record`, cited). The weld
    EXPOSES this genuine-recompute clause as a conjunct so the side-table binding is part of the welded
    statement, not a side remark.

  What this does NOT claim: it does not assert the circuit row's `escrows`-list state EQUALS the
  executor's `markResolved k.escrows id` as a LIST (the EffectVM row carries a DIGEST, not the list —
  the `SystemRoots` digest connector). The executor produces the real list (the cornerstone +
  `markResolved`); the circuit produces the genuine root of it. That is the faithful digest-not-list
  boundary, stated, not hidden.

## Honesty

`#assert_axioms` on both theorems ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `:= True`
vacuity, no weakening-that-just-typechecks. Imports are read-only; this file owns only itself and edits
no other Argus module.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitRefundEscrow
import Dregg2.Circuit.Emit.EffectVmEmitRefundEscrowWide

namespace Dregg2.Circuit.Argus.Effects.RefundEscrow

open Dregg2.Exec
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Exec (RecordKernelState EscrowRecord CellId AssetId
  refundEscrowKAsset settleEscrowRawAsset markResolved recBalCreditCell cellLifecycleLive)

/-! ## §1 — the gate + the body leaves (the settle shape: a `find?`-keyed gate, record-reading writes).

`refundEscrowKAsset k id` admits iff a matching unresolved record EXISTS and its creator passes the
settle-liveness gate; on commit it credits that creator and marks the record resolved. We render the
gate as a `Bool` over `k` and the two writes as closures that `find?` the record inside. -/

/-- The find-predicate `refundEscrowKAsset` uses (the kernel's `r.id = id ∧ r.resolved = false`).
Named locally so the IR term + the proofs read against the SAME predicate the executor uses. -/
def matchPred (id : Nat) : EscrowRecord → Bool := fun r => decide (r.id = id ∧ r.resolved = false)

/-- The refund admissibility gate as a `Bool` — exactly `refundEscrowKAsset`'s admission: a matching
unresolved record EXISTS, and its creator (the refund target) is a LIVE account whose lifecycle admits
effects. `none` (no such record) fails closed. -/
def refundEscrowGuard (id : Nat) (k : RecordKernelState) : Bool :=
  match k.escrows.find? (matchPred id) with
  | some r => decide (r.creator ∈ k.accounts) && cellLifecycleLive k r.creator
  | none   => false

/-- The refund `bal`-write leaf: credit the FOUND record's `creator` at the record's `asset` by the
record's `amount` (the value parked off-ledger). Total in `k`: when no record is found it is the
identity ledger (the gate then rejects, so this branch is never committed). -/
def refundBalLeaf (id : Nat) (k : RecordKernelState) : CellId → AssetId → Int :=
  match k.escrows.find? (matchPred id) with
  | some r => recBalCreditCell k.bal r.creator r.asset r.amount
  | none   => k.bal

/-- The refund effect as an IR term: gate, then the TWO component writes — credit the found record's
creator on the per-asset ledger (`setBal`), then mark the record resolved on the `escrows` side-table
(`setEscrows`). The settle-leg analog of `createEscrowStmt`: same `seq (guard …) (seq (setBal …)
(setEscrows …))` skeleton, but the leaves READ the record out of `k` and the `escrows` write is a
list REPLACE (`markResolved`), not a prepend. No new IR constructor is used. -/
def refundEscrowStmt (id : Nat) : RecStmt :=
  RecStmt.seq (RecStmt.guard (refundEscrowGuard id))
    (RecStmt.seq
      (RecStmt.setBal (fun k => refundBalLeaf id k))
      (RecStmt.setEscrows (fun k => markResolved k.escrows id)))

/-! ## §2 — the gate decodes to `refundEscrowKAsset`'s admission, and the body IS `settleEscrowRawAsset`.

Two ingredients, exactly as createEscrow: (a) the `Bool` gate equals the kernel step's `if` condition
on the found record, and (b) the two-component body reduces to the kernel's commit post-state. The
load-bearing settle fact (which create did not have): the `setBal` leaf and the gate BOTH `find?` the
SAME record `r`, so when the gate commits, the credit lands on `r.creator`/`r.asset`/`r.amount`. -/

/-- The escrows side-table is NOT touched by the `setBal` write, so the `setEscrows` leaf — read on the
intermediate post-`setBal` state — sees the ORIGINAL `escrows`, hence `markResolved` lands on the
original list (the create-side `createEscrowBody_eq` analog of "the prepend reads `k.escrows`"). This is
the side-table interleaving the single-cell effects never exercised. -/
theorem refundEscrowBody_eq (id : Nat) (k : RecordKernelState) :
    interp (RecStmt.seq
        (RecStmt.setBal (fun k => refundBalLeaf id k))
        (RecStmt.setEscrows (fun k => markResolved k.escrows id))) k
      = some { k with bal := refundBalLeaf id k, escrows := markResolved k.escrows id } := by
  simp only [interp, Option.bind]

/-- The gate `match` reduces on `hf` (the same find-term the kernel reads). A `none` find fails the
gate; a `some r` find leaves the liveness `Bool`. -/
private theorem refundEscrowGuard_none {id : Nat} {k : RecordKernelState}
    (hf : k.escrows.find? (matchPred id) = none) : refundEscrowGuard id k = false := by
  simp only [refundEscrowGuard, hf]

private theorem refundEscrowGuard_some {id : Nat} {k : RecordKernelState} {r : EscrowRecord}
    (hf : k.escrows.find? (matchPred id) = some r) :
    refundEscrowGuard id k = (decide (r.creator ∈ k.accounts) && cellLifecycleLive k r.creator) := by
  simp only [refundEscrowGuard, hf]

/-- The `setBal` leaf reduces on `hf` to the found record's credit. -/
private theorem refundBalLeaf_some {id : Nat} {k : RecordKernelState} {r : EscrowRecord}
    (hf : k.escrows.find? (matchPred id) = some r) :
    refundBalLeaf id k = recBalCreditCell k.bal r.creator r.asset r.amount := by
  simp only [refundBalLeaf, hf]

/-- The kernel step reduces on `hf`: a `none` find rejects; a `some r` find opens the liveness `if`
over `settleEscrowRawAsset`. `matchPred` is the common spelling of the kernel's inlined predicate. -/
private theorem refundEscrowKAsset_none {id : Nat} {k : RecordKernelState}
    (hf : k.escrows.find? (matchPred id) = none) : refundEscrowKAsset k id = none := by
  -- the kernel's inlined predicate IS `matchPred id`; fold it in `hf` so it matches the kernel `match`.
  have hf' : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = none := hf
  simp only [refundEscrowKAsset, hf']

private theorem refundEscrowKAsset_some {id : Nat} {k : RecordKernelState} {r : EscrowRecord}
    (hf : k.escrows.find? (matchPred id) = some r) :
    refundEscrowKAsset k id
      = if r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true then
          some (settleEscrowRawAsset k id r.creator r.asset r.amount)
        else none := by
  have hf' : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r := hf
  simp only [refundEscrowKAsset, hf']

/-- **The cornerstone (settle leg).** `interp` of the refundEscrow term IS the verified kernel step
`refundEscrowKAsset` — the same partial function, by construction, exactly as the transfer/mint/burn/
createEscrow cornerstones, now over a settle leg that READS the record and REPLACES it in the
side-table.

The proof opens the `find?` on the kernel side and the gate's `match` on the IR side against the SAME
`k.escrows.find? (matchPred id)` (the §helper reductions): when it is `some r`, the gate's `Bool` is
exactly the kernel `if` condition (creator live), the body's `refundBalLeaf` reduces to the same
`some r` branch (`recBalCreditCell … r.creator r.asset r.amount`), so the IR post-state is on the nose
`settleEscrowRawAsset k id r.creator r.asset r.amount`; when it is `none`, both sides are `none`. -/
theorem interp_refundEscrowStmt_eq_refundEscrowKAsset (id : Nat) (k : RecordKernelState) :
    interp (refundEscrowStmt id) k = refundEscrowKAsset k id := by
  -- Reduce the IR `interp` to: gate `if`, then the two component-write binds.
  simp only [refundEscrowStmt, interp, Option.bind]
  -- Case-split on the SHARED find-term (the gate, the `setBal` leaf, and the kernel all read it).
  cases hf : k.escrows.find? (matchPred id) with
  | none =>
    -- no record found: the gate is `false` ⇒ IR returns `none`; so does the kernel.
    rw [refundEscrowGuard_none hf, refundEscrowKAsset_none hf]; rfl
  | some r =>
    -- record `r` found: rewrite the gate (the `if` condition) and the kernel to their `some r` forms.
    rw [refundEscrowGuard_some hf, refundEscrowKAsset_some hf]
    by_cases hg : r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true
    · -- ADMIT: gate `Bool` is `true` ⇒ the gate `if` fires (`some k`), the bind applies the writes to
      -- `k` (exposing `refundBalLeaf id k`); the kernel `if` fires on the matching Prop. Both sides
      -- become `settleEscrowRawAsset`'s post-state.
      obtain ⟨hacc, hlive⟩ := hg
      simp only [decide_eq_true_eq.mpr hacc, hlive, Bool.and_self, if_true, and_true,
        if_pos hacc, refundBalLeaf_some hf, settleEscrowRawAsset]
    · -- REJECT: the gate `Bool` is `false` ⇒ the gate `if` is `none`, the bind is `none`; the kernel
      -- `if` closes on the negated Prop.
      have hgb : (decide (r.creator ∈ k.accounts) && cellLifecycleLive k r.creator) = false := by
        rcases Classical.em (r.creator ∈ k.accounts) with hin | hin
        · -- creator IS an account ⇒ liveness must be the failing leg.
          have hlf : cellLifecycleLive k r.creator = false := by
            by_contra hne; exact hg ⟨hin, by simpa using hne⟩
          simp [hlf]
        · -- creator is NOT an account ⇒ the membership leg is false.
          simp [hin]
      simp only [hgb, Bool.false_eq_true, if_false, if_neg hg]

#assert_axioms interp_refundEscrowStmt_eq_refundEscrowKAsset

/-! ## §3 — NON-VACUITY of the cornerstone: the settle term genuinely RESOLVES a parked record.

The cornerstone would be hollow if `refundEscrowStmt` never committed. On a one-account kernel holding a
single unresolved record for `id = 7` (creator = account `0`, live), the term commits and the record's
`resolved` flag flips `false → true` (the side-table REPLACE is real, not a no-op), while a query of a
missing id (`9`) rejects. -/

/-- A one-cell kernel (account `0` Live) holding ONE unresolved escrow record (`id 7`, creator `0`,
amount `0`, asset `0`). The `0` amount keeps the credit trivial so the only thing the witness exercises
is the `find?`-gate + the `markResolved` side-table replace. -/
def kR : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [("balance", .int 0)], caps := fun _ => []
    escrows := [{ id := 7, creator := 0, recipient := 0, amount := 0, resolved := false, asset := 0 }] }

/-- **`refundEscrowStmt_resolves` — the settle is OBSERVABLE.** Running the refund term for `id = 7`
on `kR` commits and flips the parked record's `resolved` flag `false → true` (via `markResolved`): the
side-table settle is a real, observable state edit, not a no-op. -/
theorem refundEscrowStmt_resolves :
    (interp (refundEscrowStmt 7) kR).map (fun k => (k.escrows.find? (fun r => decide (r.id = 7))).map (·.resolved))
      = some (some true) := by
  rw [interp_refundEscrowStmt_eq_refundEscrowKAsset]
  decide

/-- **`refundEscrowStmt_rejects_missing` — fail-closed on a missing id.** A refund query for an id with
no parked record (`9`) rejects (`none`): the `find?`-gate genuinely fails closed (the cornerstone's
two-valued, non-vacuous reject side). -/
theorem refundEscrowStmt_rejects_missing :
    interp (refundEscrowStmt 9) kR = none := by
  rw [interp_refundEscrowStmt_eq_refundEscrowKAsset]
  decide

#assert_axioms refundEscrowStmt_resolves
#assert_axioms refundEscrowStmt_rejects_missing

/-! ## §4 — THE WELD: the audited class-A genuine descriptor agrees, per cell, with the IR term's
executor interpretation — AND forces the genuine `escrows`-root recompute.

The SAME shape as the createEscrow weld (`Argus/Compile.lean §E`): route the circuit side through the
audited `refundEscrowGenuine_sound` (`EffectVmEmitRefundEscrow` §H) and the executor side through the
cornerstone above + the per-cell projection `refundEscrowKAsset_proj_balLo`. -/

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitRefundEscrow
  (refundEscrowVmDescriptorGenuine refundEscrowGenuine_sound cellProjRefund RefundParams
   RowEncodesRefund CellRefundSpec)

/-! ### §4.0 — `compileRefund` — the effect-keyed circuit interpretation of the refundEscrow term.

Mirroring `Argus/Compile.lean`'s `compileE` (which keys on the effect, not the raw `RecStmt` shape —
the structural match cannot separate same-shaped effects), we name the refundEscrow circuit directly as
the audited class-A genuine descriptor. `compileRefund = refundEscrowVmDescriptorGenuine` by `rfl`, so
the circuit interpretation of the refundEscrow term is, on the nose, the descriptor the Rust prover
runs for the supply-refund settle. -/

/-- The circuit interpretation of the refundEscrow IR term: the audited class-A genuine descriptor
(genuine in-row escrow-root recompute + per-cell credit/freeze + commitment). -/
def compileRefund : Dregg2.Circuit.Emit.EffectVmEmit.EffectVmDescriptor := refundEscrowVmDescriptorGenuine

/-- **`compileRefund_eq` — `compileRefund` IS the audited runnable refund descriptor.** Definitional. -/
theorem compileRefund_eq : compileRefund = refundEscrowVmDescriptorGenuine := rfl

#assert_axioms compileRefund_eq

/-! ### §4.1 — the EXECUTOR-side per-cell projection of the kernel step `refundEscrowKAsset`.

The cornerstone refines the IR term to `refundEscrowKAsset` (the `RecordKernelState → Option
RecordKernelState` kernel step). We need its per-cell projection onto `cellProjRefund …bal creator
asset` for the FOUND record — the `refundEscrowKAsset` analog of createEscrow's
`createEscrowKAsset_proj_balLo`, except this is a CREDIT (`+ amount`), and the cell/asset/amount come
from the record `r` carried by the `find?` hypothesis. The frozen frame (balHi/nonce/fields/capRoot/
reserved) is `0 = 0` on both projections (definitional). -/

/-- **`refundEscrowKAsset_proj_balLo`.** A committed kernel refund CREDITS the found record's
`(creator, asset)` ledger entry by exactly `r.amount` (the value parked off-ledger, now returned). The
per-cell conserved leg the weld pins. Takes the `find?` hypothesis `hr` (the settle-leg analog of
create's free args — the moved cell/asset/amount are READ from `r`). -/
theorem refundEscrowKAsset_proj_balLo {k k' : RecordKernelState} {id : Nat} {r : EscrowRecord}
    (h : refundEscrowKAsset k id = some k')
    (hr : k.escrows.find? (matchPred id) = some r) :
    (cellProjRefund k'.bal r.creator r.asset).balLo
      = (cellProjRefund k.bal r.creator r.asset).balLo + r.amount := by
  -- reduce the kernel `match` on the FOUND record `r` (via `hr`), exposing the liveness `if`.
  -- `matchPred` is unfolded so `hr`'s find-term matches the kernel's inlined lambda spelling; then
  -- rewriting the find with `hr` reduces `match some r` and exposes the liveness `if`.
  have hr' : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r := by
    simpa only [matchPred] using hr
  simp only [refundEscrowKAsset, hr'] at h
  by_cases hg : r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    -- `(cellProjRefund (settleEscrowRawAsset …).bal r.creator r.asset).balLo
    --   = recBalCreditCell k.bal r.creator r.asset r.amount r.creator r.asset`
    show recBalCreditCell k.bal r.creator r.asset r.amount r.creator r.asset
      = k.bal r.creator r.asset + r.amount
    unfold recBalCreditCell; rw [if_pos ⟨rfl, rfl⟩]
  · rw [if_neg hg] at h; exact absurd h (by simp)

#assert_axioms refundEscrowKAsset_proj_balLo

/-! ### §4.2 — THE WELD. -/

/-- **`refundEscrow_compile_sound` — the welded soundness (refundEscrow slice, the settle side-table
effect).**

Suppose, for the Argus refundEscrow term `refundEscrowStmt id` and the FOUND unresolved record `r`
(`hr`):
  * the circuit `compileRefund` (= the audited class-A `refundEscrowVmDescriptorGenuine`) is SATISFIED
    by `(env, true, true)` under the abstract Poseidon carrier `hash`, and its `RowEncodesRefund`
    decoding NAMES the post-state record `post` over the creator cell's projection
    `cellProjRefund k.bal r.creator r.asset` with the `⟨r.amount⟩` param block (`henc`);
  * the IR term's EXECUTOR interpretation COMMITS: `interp (refundEscrowStmt id) k = some k'` (`hexec`).

Then:
  * **conserved leg (per-cell):** the circuit's pinned post-state `post` AGREES with the executor's
    CREDITED creator-cell projection `cellProjRefund k'.bal r.creator r.asset` — the conserved `balLo`
    (credited by `r.amount`) AND the whole frozen frame (balHi/fields/capRoot/reserved/nonce).
    refundEscrow has NO nonce-tick divergence (the descriptor FREEZES the cell nonce, matching the
    executor — `cellProjRefund` sends `nonce` to `0` on both sides).
  * **side-table leg:** the circuit FORCES the new escrow-list root carrier to be the genuine in-row
    recompute `hash[ hash[id,creator,recipient,amount,asset,resolved], old_root ]` of the bound record +
    old root — the digest the executor's `escrows := markResolved k.escrows id` resolve commits to
    (absorbed into `state_commit`, so the resolved record is bound; see
    `refundEscrowGenuine_binds_record`).

So the class-A circuit the prover runs for refundEscrow pins the per-cell credited state the IR term's
executor produces AND genuinely recomputes the bound `escrows` side-table root — the template
generalizes to the SETTLE side-table effect (a `find?`-keyed, record-reading, replace-in-place leg). -/
theorem refundEscrow_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (id : Nat) (r : EscrowRecord)
    (post : CellState)
    (hr : k.escrows.find? (matchPred id) = some r)
    (henc : RowEncodesRefund env (cellProjRefund k.bal r.creator r.asset) ⟨r.amount⟩ post)
    (hsat : satisfiedVm hash compileRefund env true true)
    (hexec : interp (refundEscrowStmt id) k = some k') :
    -- conserved leg: the credited cell's projection agrees on balLo + the whole frozen frame …
    ( post.balLo = (cellProjRefund k'.bal r.creator r.asset).balLo
      ∧ post.balHi = (cellProjRefund k'.bal r.creator r.asset).balHi
      ∧ (∀ i, post.fields i = (cellProjRefund k'.bal r.creator r.asset).fields i)
      ∧ post.capRoot = (cellProjRefund k'.bal r.creator r.asset).capRoot
      ∧ post.reserved = (cellProjRefund k'.bal r.creator r.asset).reserved
      ∧ post.nonce = (cellProjRefund k'.bal r.creator r.asset).nonce )
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
  -- circuit side: `compileRefund` IS the genuine descriptor; the audited class-A soundness forces the
  -- per-cell `CellRefundSpec` + the genuine root recompute.
  rw [compileRefund_eq] at hsat
  obtain ⟨hcs, hroot, _hcommit⟩ :=
    refundEscrowGenuine_sound hash env (cellProjRefund k.bal r.creator r.asset) post ⟨r.amount⟩ henc hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcs
  -- executor side: the §2 cornerstone turns the IR term's `interp` into the verified kernel step
  -- `refundEscrowKAsset`; its per-cell projection (for the FOUND record `r`) gives the credited balLo
  -- (the frozen limbs are `0 = 0`).
  rw [interp_refundEscrowStmt_eq_refundEscrowKAsset] at hexec
  have heLo := refundEscrowKAsset_proj_balLo hexec hr
  refine ⟨⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl,
    hcN.trans rfl⟩, hroot⟩
  -- balLo: circuit pins post = pre + r.amount; executor credits the projected entry by r.amount.
  rw [hcLo, heLo]

#assert_axioms refundEscrow_compile_sound

/-! ### §4.3 — NON-VACUITY: `compileRefund` is the genuine class-A descriptor, not the placeholder.

The weld would be worthless if `compileRefund` were an inert/empty descriptor. It is the class-A
`refundEscrowVmDescriptorGenuine`, carrying the 34 per-row gates (credit + frame freeze) +
transition/boundary constraints AND the 6 hash-sites (2 genuine escrow-root-recompute sites + 4
commitment sites). So `refundEscrow_compile_sound` is a statement about a REAL class-A circuit with a
genuinely-recomputed side-table root (the same counts the createEscrow genuine descriptor carries). -/

/-- The compiled refundEscrow circuit is the NON-trivial class-A genuine descriptor: it carries the
13+14+4+3 = 34 constraints / 2+4 = 6 hash-sites / 2 range checks of the audited
`refundEscrowVmDescriptorGenuine` (an empty placeholder would have 0/0/0). So
`refundEscrow_compile_sound` is about a genuine side-table-binding circuit. -/
theorem compileRefund_nontrivial :
    compileRefund.constraints.length = 34
    ∧ compileRefund.hashSites.length = 6
    ∧ compileRefund.ranges.length = 2 := by
  rw [compileRefund_eq]
  refine ⟨by decide, by decide, by decide⟩

#assert_axioms compileRefund_nontrivial

/-! ## §5 — FULL-STATE on the RUNNABLE descriptor (the magnesium breadth — bind ALL 17 fields).

§4 welds the AUDITED class-A descriptor (`refundEscrowVmDescriptorGenuine`), whose root carrier is the
raw `96`. `EffectVmEmitRefundEscrowWide.refundEscrow_runnable_full_sound` lifts the SAME per-row gates
through the generic `runnable_full_sound` over the WIDE descriptor `refundEscrowVmDescriptorWide`
(dedicated `sysRootsDigestCol`, `wideHashSites`, widened width). A satisfying row of THAT descriptor binds
the FULL 17-field post-state: the per-cell CREDIT AND the `escrows` side-table digest advance, with the
generic anti-ghost giving: tamper ANY absorbed state-block column OR ANY of the 8 side-table roots ⇒ UNSAT.

This section welds THAT full-state crown to the SAME executor cornerstone (§2 + the §4.1 projection), so
the welded statement pins the executor's per-cell post-state through the FULL-STATE RUNNABLE descriptor.
Since fulfillObligation is the dispatch-alias of this descriptor
(`Argus/Effects/FulfillObligation.lean`), it inherits the full-state binding through the SAME wide circuit. -/

open Dregg2.Circuit.Emit.EffectVmEmitRefundEscrowWide
  (refundEscrowVmDescriptorWide refundEscrow_runnable_full_sound)
open Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide (ESCROW_STEP_PARAM)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest)

/-- **`refundEscrow_runnable_full_state` — THE FULL-STATE WELD (refundEscrow / fulfillObligation).**

Suppose, for the Argus refundEscrow term and the FOUND record `r` (`hr`):
  * the WIDE RUNNABLE descriptor `refundEscrowVmDescriptorWide` is SATISFIED by `(env, true, true)`, its
    `RowEncodesRefund` decoding NAMES `post` over `cellProjRefund k.bal r.creator r.asset` with `⟨r.amount⟩`,
    and the dedicated digest carriers are pinned to the `systemRootsDigest` of the pre/post sub-blocks
    (`hAfter`/`hBefore`) with the accumulator `step` (`hStep`);
  * the IR term's EXECUTOR interpretation COMMITS (`hexec`).

Then the circuit's pinned `post` AGREES with the executor's CREDITED creator-cell projection
`cellProjRefund k'.bal r.creator r.asset` on EVERY limb (`balLo` credited by `r.amount`, frame frozen,
nonce frozen) AND the WIDE descriptor binds the `escrows` side-table digest advance. So the circuit the
prover RUNS pins the per-cell state the executor produces AND the full side-table digest — all 17 fields. -/
theorem refundEscrow_runnable_full_state
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (id : Nat) (r : EscrowRecord)
    (post : CellState) (preRoots postRoots : SysRoots) (step : ℤ)
    (hrow : Dregg2.Circuit.Emit.EffectVmEmitRefundEscrow.IsRefundEscrowRow env)
    (hr : k.escrows.find? (matchPred id) = some r)
    (henc : RowEncodesRefund env (cellProjRefund k.bal r.creator r.asset) ⟨r.amount⟩ post)
    (hAfter : env.loc Dregg2.Circuit.Emit.EffectVmEmit.sysRootsDigestCol
                = systemRootsDigest hash postRoots)
    (hBefore : env.loc Dregg2.Circuit.Emit.EffectVmEmit.sysRootsDigestColBefore
                = systemRootsDigest hash preRoots)
    (hStep : env.loc (Dregg2.Circuit.Emit.EffectVmEmit.prmCol ESCROW_STEP_PARAM) = step)
    (hsat : satisfiedVm hash refundEscrowVmDescriptorWide env true true)
    (hexec : interp (refundEscrowStmt id) k = some k') :
    ( post.balLo = (cellProjRefund k'.bal r.creator r.asset).balLo
      ∧ post.balHi = (cellProjRefund k'.bal r.creator r.asset).balHi
      ∧ (∀ i, post.fields i = (cellProjRefund k'.bal r.creator r.asset).fields i)
      ∧ post.capRoot = (cellProjRefund k'.bal r.creator r.asset).capRoot
      ∧ post.reserved = (cellProjRefund k'.bal r.creator r.asset).reserved
      ∧ post.nonce = (cellProjRefund k'.bal r.creator r.asset).nonce )
    ∧ systemRootsDigest hash postRoots = systemRootsDigest hash preRoots + step := by
  obtain ⟨hcs, hdig⟩ :=
    refundEscrow_runnable_full_sound ⟨r.amount⟩ hash preRoots step env
      (cellProjRefund k.bal r.creator r.asset) post postRoots hrow henc hAfter hBefore hStep hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcs
  rw [interp_refundEscrowStmt_eq_refundEscrowKAsset] at hexec
  have heLo := refundEscrowKAsset_proj_balLo hexec hr
  refine ⟨⟨?_, hcHi.trans rfl, fun i => (hcF i).trans rfl, hcCap.trans rfl, hcRes.trans rfl,
    hcN.trans rfl⟩, hdig⟩
  rw [hcLo, heLo]

#assert_axioms refundEscrow_runnable_full_state

end Dregg2.Circuit.Argus.Effects.RefundEscrow
