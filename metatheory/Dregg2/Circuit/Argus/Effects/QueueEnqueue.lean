/-
# Dregg2.Circuit.Argus.Effects.QueueEnqueue — the FIFO `queueEnqueueA` effect welded into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn (single-cell `setCell` moves) + createEscrow (a TWO-component `setBal`/`setEscrows`
side-table move). `Effects/BalanceA.lean` then showed the genuinely STRONGER surface: weld against an
effect's OWN standalone `Surface2` `*_full_sound` (concluding the WHOLE 17-field post-state + the receipt
log), routed through an independent executor⟺spec corner. This module welds `queueEnqueueA` on THAT
stronger full-state surface, in a disjoint file (it imports the Argus IR + the audited `queueEnqueueA`
v2-triple instance read-only and owns only its own declarations).

`queueEnqueueA` is the FIFO ring-buffer enqueue + REFUNDABLE anti-spam deposit PARK effect. The running
unified-action executor is `queueEnqueueChainA` (`Exec/TurnExecutorFull.lean:2234`), dispatched from
`execFullA s (.queueEnqueueA …)` (`:3877`):

    queueEnqueueChainA s id m actor cell depId dAsset deposit
      = if stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true then
          match queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
          | some k' => some { kernel := k', log := {actor, src:=actor, dst:=cell, amt:=deposit} :: s.log }
          | none    => none
        else none

so a committed enqueue (a) gates on the writer-ACL + lifecycle-liveness, then (b) runs the KERNEL step
`queueEnqueueDepositK` — which itself APPENDS `m` to queue `id`'s FIFO buffer (`queueEnqueueK`, fail-closed
if absent OR FULL) AND PARKS a refundable `deposit` of asset `dAsset` off-ledger
(`createEscrowRawAssetQueue`: a per-asset `bal` DEBIT at `(actor, dAsset)` + an unresolved tagged
`EscrowRecord` PREPENDED onto `escrows`), then (c) prepends the deposit-move receipt onto the chained log.
This effect touches THREE kernel components — `queues`, `bal`, `escrows` — and the chained `log`.

## The IR term — the THREE component writes, under one composite kernel-admissibility guard

`queueEnqueueDepositK : RecordKernelState → Option RecordKernelState` is `match queueEnqueueK k id m with
| none => none | some k₁ => if <deposit gate on k₁> then some (createEscrowRawAssetQueue k₁ …) else none`
— a NESTED `match`/`if` (the FIFO presence/capacity gate inside `queueEnqueueK`, then the deposit legs).
We capture it with a single `Bool` `guard` of the EXACT composite admissibility (the FIFO step commits to
some `k₁` AND the four deposit legs hold on `k₁`), then the THREE §A component-write primitives
`setQueues`/`setBal`/`setEscrows` whose leaves reproduce the COMPOSED post-state on the commit branch. The
writes hit DISJOINT slices (`queueEnqueueK` touches ONLY `queues`; `createEscrowRawAssetQueue` touches ONLY
`bal`+`escrows`), so each later leaf reads its needed `bal`/`escrows` UNMUTATED by the prior write — the
load-bearing fact the three-write `seq` chain exercises (the createEscrow §E pattern, now at three writes).
The cornerstone is `interp_queueEnqueueStmt_eq_queueEnqueueDepositK` (the KERNEL step IS the IR term).

## The full-state weld (the BalanceA-stronger surface, NOT a per-cell projection)

`queueEnqueueA` carries its OWN standalone v2-triple (`EffectCommit3`) circuit + full soundness in
`Dregg2/Circuit/Inst/queueEnqueueA.lean`: `queueEnqueueE` (the `EffectSpec2Triple` whose three active
components are the `queues` list-digest, the WHOLE `bal` function-digest, and the `escrows` list-digest)
and `queueEnqueueA_full_sound : satisfiedE2Triple … ⟹ QueueEnqueueSpec` — a FULL 17-field declarative
post-state soundness, keyed on the CHAINED executor `queueEnqueueChainA`/`execFullA` via the independent
`execFullA_queueEnqueueA_iff_spec` (`Spec/queuefifocore.lean`). We weld: route the kernel cornerstone to
the chained executor (§3, carrying the `stateAuthB ∧ acceptsEffects` chained gates explicitly), then
collapse the circuit-side spec fact and the executor-side spec fact onto ONE welded post-state. The
conclusion is the FULL `QueueEnqueueSpec` agreement — a satisfying witness of `queueEnqueueA`'s own circuit
agrees with the WHOLE post-state the IR term's executor produces. Strictly stronger than transfer's
per-cell EffectVM weld (the standalone descriptor carries the whole-state triple-component digest + log).

## HONEST SURFACE — what the weld DOES and DOES NOT pin

  * The full-state conclusion is `st' = { kernel := k', log := enqueueReceipt actor cell deposit :: st.log }`
    — every one of the 17 `RecordKernelState` fields (the post-`queues`/`bal`/`escrows` composed move +
    the 14 frozen) AND the chained receipt log, NOT a per-cell projection. (`QueueEnqueueSpec` is functional:
    `queueEnqueueSpec_unique`, via `execFullA_queueEnqueueA_iff_spec` + `Option.some` injectivity, pins a
    UNIQUE post-state, so the circuit-side and executor-side spec facts collapse to one welded state.)
  * NO nonce-tick divergence is carried: this is NOT a per-row EffectVM weld (those carry the row-ticks /
    body-freezes reconciliation); it is the v2-triple full-state surface, whose `QueueEnqueueSpec` already
    pins the WHOLE post-state including the 14 frozen fields. The Poseidon-CR / whole-function-digest
    assumptions enter ONLY inside the reused `queueEnqueueA_full_sound` (its `Function.Injective D`,
    `compressNInjective`, `listLeafInjective`, `RestIffNoQueuesBalEscrows`, `logHashInjective` portal
    hypotheses), NOT in the welded conclusion's statement.
  * The honest CHAINED-vs-RAW contrast (carried as the §3 lift's explicit hypotheses, NOT papered): the
    KERNEL step `queueEnqueueDepositK` is the post-state body; the chained `queueEnqueueChainA` adds the
    writer-ACL gate `stateAuthB actor cell` AND the lifecycle-liveness gate `acceptsEffects cell` AND the
    receipt-log prepend. The lift theorem carries both gates as explicit hypotheses, exactly as the kernel
    layering demands.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no
`:= True`, no `native_decide`. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.queueEnqueueA

namespace Dregg2.Circuit.Argus.Effects.QueueEnqueue

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Circuit.Argus (RecStmt interp)
-- The standalone v2-triple instance + its full soundness + the independent executor⟺spec corner.
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.EffectCommit3 (EffectSpec2Triple satisfiedE2Triple encodeE2Triple)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.Spec.QueueFifoCore
  (QueueEnqueueSpec enqueueReceipt execFullA_queueEnqueueA_iff_spec)
open Dregg2.Circuit.Inst.QueueEnqueueA
  (EnqueueArgs queueEnqueueE queueEnqueueA_full_sound RestIffNoQueuesBalEscrows
   recordKernel_eq_of_fields queueEnqueueK_preserves_frame)

/-! ## §1 — The queueEnqueue effect as an Argus IR term (composite kernel guard, then the THREE writes).

`queueEnqueueDepositK k id m actor cell depId dAsset deposit` is
`match queueEnqueueK k id m with | none => none | some k₁ => if <dep gate on k₁> then some (…) else none`.
We capture it term-for-term: a `Bool` `guard` of the EXACT composite admissibility (the FIFO step yields
some `k₁` AND the four deposit legs hold on `k₁`), then a `seq` of `setQueues`/`setBal`/`setEscrows` whose
leaves reproduce the COMPOSED `createEscrowRawAssetQueue k₁ …` post-state. The contrast with the
single-component effects: the body is THREE component writes (the §A list/func/list primitives), not one. -/

/-- The queueEnqueue admissibility gate as a `Bool` — exactly `queueEnqueueDepositK`'s commit condition:
the FIFO enqueue step `queueEnqueueK k id m` commits to some `k₁` (absent/full ⇒ fail-closed), AND on that
post-append intermediate `k₁` the four deposit legs hold (non-negative, available in asset `dAsset` from
`actor`, `actor` a live account, the deposit id `depId` fresh). This is the KERNEL-step composite guard;
the chained `queueEnqueueChainA` adds `stateAuthB actor cell ∧ acceptsEffects cell` on top (carried
separately in §3). -/
def enqueueDepositGuard (id m : Nat) (actor _cell : CellId) (depId : Nat) (dAsset : AssetId)
    (deposit : ℤ) (k : RecordKernelState) : Bool :=
  match queueEnqueueK k id m with
  | none    => false
  | some k₁ =>
      decide (0 ≤ deposit) && decide (deposit ≤ k₁.bal actor dAsset)
        && decide (actor ∈ k₁.accounts) && decide (¬ (∃ r ∈ k₁.escrows, r.id = depId))

/-- The post-`queues` list after the FIFO append (a pure function of pre+args via `queueEnqueueK`). On the
commit branch this is `k₁.queues`; off the commit branch the guard rejects so the leaf is never observed. -/
def postQueues (id m : Nat) (k : RecordKernelState) : List QueueRecord :=
  match queueEnqueueK k id m with
  | some k₁ => k₁.queues
  | none    => k.queues

/-- **The queueEnqueue effect as an IR term: composite kernel guard, then the THREE component writes.**
Gate on `enqueueDepositGuard` (the FIFO commit + deposit legs), then `setQueues` (the FIFO append) ⊳
`setBal` (debit the deposit at `(actor, dAsset)`) ⊳ `setEscrows` (prepend the tagged unresolved deposit
record). The three writes hit DISJOINT kernel slices, so each later leaf reads its `bal`/`escrows`
unmutated. The leaves reproduce `createEscrowRawAssetQueue (queueEnqueueK …).k₁ …` exactly. -/
def queueEnqueueStmt (id m : Nat) (actor cell : CellId) (depId : Nat) (dAsset : AssetId) (deposit : ℤ) :
    RecStmt :=
  RecStmt.seq (RecStmt.guard (enqueueDepositGuard id m actor cell depId dAsset deposit))
    (RecStmt.seq (RecStmt.setQueues (fun k => postQueues id m k))
      (RecStmt.seq (RecStmt.setBal (fun k => recBalCreditCell k.bal actor dAsset (-deposit)))
        (RecStmt.setEscrows (fun k =>
          { id := depId, creator := actor, recipient := cell, amount := deposit, resolved := false,
            asset := dAsset, queueDep := some id, queueMsg := some m } :: k.escrows))))

/-! ## §2 — The cornerstone: `interp` of the queueEnqueue term IS the kernel step `queueEnqueueDepositK`. -/

/-- **The cornerstone (FIFO + deposit-park kernel step).** `interp` of the queueEnqueue term IS the verified
kernel transition `queueEnqueueDepositK` — the same partial function, by construction, exactly as the
transfer/createEscrow cornerstones, now over a THREE-component (queues + bal + escrows) move. On the commit
branch the guard fires (`some k`), the three writes reproduce `createEscrowRawAssetQueue k₁ …` (the `setBal`
debit and `setEscrows` prepend read `k.bal`/`k.escrows`, unmutated by the disjoint `setQueues` write, and
`k₁.bal = k.bal`, `k₁.escrows = k.escrows` because `queueEnqueueK` touches ONLY `queues`); off it, the guard
rejects (`none`) and the `bind` chain short-circuits. -/
theorem interp_queueEnqueueStmt_eq_queueEnqueueDepositK (id m : Nat) (actor cell : CellId) (depId : Nat)
    (dAsset : AssetId) (deposit : ℤ) (k : RecordKernelState) :
    interp (queueEnqueueStmt id m actor cell depId dAsset deposit) k
      = queueEnqueueDepositK k id m actor cell depId dAsset deposit := by
  -- Case-split on the FIFO step BEFORE unfolding — at this point `queueEnqueueK k id m` is hidden inside the
  -- defs, so `cases` introduces `hk` as a standalone hypothesis without abstracting an ill-typed goal motive.
  cases hk : queueEnqueueK k id m with
  | none =>
      -- FIFO rejects ⇒ guard is `false`, the leading `guard` returns `none`, `bind` short-circuits.
      simp only [queueEnqueueStmt, interp, enqueueDepositGuard, postQueues, queueEnqueueDepositK, hk,
                 Bool.false_eq_true, if_false, Option.bind_none]
  | some k₁ =>
      -- `queueEnqueueK` touches ONLY `queues`, so `k₁.bal = k.bal` and `k₁.escrows = k.escrows` (and every
      -- non-`queues` frame field of `k₁` equals `k`'s). The `bal`/`escrows` facts let the `setBal`/`setEscrows`
      -- leaves (which read the intermediate post-`setQueues` state, whose `bal`/`escrows` are `k`'s) match
      -- `createEscrowRawAssetQueue k₁ …` (which reads `k₁`'s).
      have hframe := queueEnqueueK_preserves_frame hk
      have hbal : k₁.bal = k.bal := by
        unfold queueEnqueueK at hk
        cases hf : findQueue k.queues id with
        | none   => simp only [hf] at hk; exact absurd hk (by simp)
        | some q =>
            simp only [hf] at hk
            by_cases hc : q.buffer.length < q.capacity
            · rw [if_pos hc] at hk; simp only [Option.some.injEq] at hk; subst hk; rfl
            · rw [if_neg hc] at hk; exact absurd hk (by simp)
      have hesc : k₁.escrows = k.escrows := by
        unfold queueEnqueueK at hk
        cases hf : findQueue k.queues id with
        | none   => simp only [hf] at hk; exact absurd hk (by simp)
        | some q =>
            simp only [hf] at hk
            by_cases hc : q.buffer.length < q.capacity
            · rw [if_pos hc] at hk; simp only [Option.some.injEq] at hk; subst hk; rfl
            · rw [if_neg hc] at hk; exact absurd hk (by simp)
      simp only [queueEnqueueStmt, interp, enqueueDepositGuard, postQueues, queueEnqueueDepositK, hk]
      by_cases hd : 0 ≤ deposit ∧ deposit ≤ k₁.bal actor dAsset ∧ actor ∈ k₁.accounts
          ∧ ¬ (∃ r ∈ k₁.escrows, r.id = depId)
      · -- deposit legs hold ⇒ guard is `true`; the three writes reproduce `createEscrowRawAssetQueue k₁ …`.
        obtain ⟨hd1, hd2, hd3, hd4⟩ := hd
        rw [decide_eq_true hd1, decide_eq_true hd2, decide_eq_true hd3, decide_eq_true hd4]
        simp only [Bool.and_true, if_true,
                   if_pos (And.intro hd1 (And.intro hd2 (And.intro hd3 hd4))), Option.bind_some]
        -- the post-state: the three disjoint record-updates collapse to `createEscrowRawAssetQueue k₁ …`.
        -- The LHS is the nested update of `k` (queues:=k₁.queues, bal:=recBalCreditCell k.bal…, escrows:=
        -- record::k.escrows); the RHS unfolds to `{k₁ with bal:=recBalCreditCell k₁.bal…, escrows:=record::
        -- k₁.escrows}`. Field-extensionality: queues agree (k₁.queues), bal/escrows agree via hbal/hesc, and
        -- every frozen field of `k₁` equals `k`'s (queueEnqueueK only touched queues).
        unfold createEscrowRawAssetQueue
        rcases hframe with
          ⟨hAcc, hCell, hCaps, hNul, hRev, hCom, hSw, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
        apply congrArg some
        apply recordKernel_eq_of_fields <;>
          simp only [hk, hbal, hesc, hAcc, hCell, hCaps, hNul, hRev, hCom, hSw, hSC, hFac, hLif, hDC,
                     hDel, hDgs, hSB]
      · -- deposit legs FAIL ⇒ the IR bool guard is `false` (the leading `guard` returns `none`, the `bind`
        -- chain short-circuits to `none`) AND the kernel's Prop `if` is `none` (`if_neg hd`).
        have hfalse : (decide (0 ≤ deposit) && decide (deposit ≤ k₁.bal actor dAsset)
                  && decide (actor ∈ k₁.accounts) && decide (¬ (∃ r ∈ k₁.escrows, r.id = depId))) = false := by
          rw [Bool.eq_false_iff]
          simp only [ne_eq, Bool.and_eq_true, decide_eq_true_eq]
          exact fun h => hd ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
        rw [hfalse, if_neg hd]
        simp only [Bool.false_eq_true, if_false, Option.bind_none]

#assert_axioms interp_queueEnqueueStmt_eq_queueEnqueueDepositK

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `queueEnqueueChainA` / `execFullA`.

The standalone queueEnqueue descriptor (§4) is keyed on the CHAINED executor `queueEnqueueChainA` /
`execFullA` over `RecChainedState` (kernel + receipt log) — the arm
`execFullA s (.queueEnqueueA …) = queueEnqueueChainA s …`. The §2 cornerstone is over the RAW kernel step
`queueEnqueueDepositK`. The chained layer is exactly `queueEnqueueDepositK` PLUS two pre-gates — the
writer-ACL `stateAuthB actor cell` and the lifecycle-liveness `acceptsEffects cell` — and the receipt-log
prepend `enqueueReceipt actor cell deposit :: s.log`. We bridge faithfully, carrying BOTH gate conjuncts as
explicit hypotheses (the honest chained-vs-raw contrast — NOT papered). -/

/-- **`interp_queueEnqueueStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.** When
the writer holds the ACL over the queue cell (`stateAuthB caps actor cell = true`) and the cell accepts
effects (`acceptsEffects kernel cell = true`, the two chained pre-gates) and the §2 cornerstone commits on
the kernel (`interp (queueEnqueueStmt …) st.kernel = some k'`), the unified action executor
`execFullA st (.queueEnqueueA …)` commits to the chained state `⟨k', enqueueReceipt actor cell deposit ::
st.log⟩`. So the Argus term's kernel meaning lifts to the chained executor the standalone descriptor speaks
about, modulo the carried writer-ACL + liveness side-conditions. -/
theorem interp_queueEnqueueStmt_chained
    (st : RecChainedState) (id m : Nat) (actor cell : CellId) (depId : Nat) (dAsset : AssetId)
    (deposit : ℤ) (k' : RecordKernelState)
    (hauth : stateAuthB st.kernel.caps actor cell = true)
    (haccept : acceptsEffects st.kernel cell = true)
    (hexec : interp (queueEnqueueStmt id m actor cell depId dAsset deposit) st.kernel = some k') :
    execFullA st (.queueEnqueueA id m actor cell depId dAsset deposit)
      = some { kernel := k', log := enqueueReceipt actor cell deposit :: st.log } := by
  -- the §2 cornerstone turns the IR term into the raw kernel step `queueEnqueueDepositK`.
  rw [interp_queueEnqueueStmt_eq_queueEnqueueDepositK] at hexec
  -- `execFullA st (.queueEnqueueA …)` reduces to `queueEnqueueChainA st …`, which on the two gates opens to
  -- a `match queueEnqueueDepositK …` — and `hexec` names that as `some k'`.
  show queueEnqueueChainA st id m actor cell depId dAsset deposit
        = some { kernel := k', log := enqueueReceipt actor cell deposit :: st.log }
  unfold queueEnqueueChainA enqueueReceipt
  rw [if_pos ⟨hauth, haccept⟩, hexec]

#assert_axioms interp_queueEnqueueStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of queueEnqueue's OWN standalone circuit agrees with the
FULL post-state the IR term's executor interpretation produces.

This welds against queueEnqueue's GENUINE standalone v2-triple descriptor `queueEnqueueE D hD …` (the
`EffectCommit3` circuit whose soundness is `queueEnqueueA_full_sound`), NOT a per-cell EffectVM descriptor —
the BalanceA-stronger surface. The executor side is routed through §3 (`interp` ⟹ `execFullA`) and the
independent `execFullA_queueEnqueueA_iff_spec` (executor ⟺ `QueueEnqueueSpec`); the circuit side is the
audited `queueEnqueueA_full_sound` (circuit ⟹ `QueueEnqueueSpec`). Both name the SAME `QueueEnqueueSpec`, so
they PROVABLY agree on the WHOLE 17-field state + log. -/

/-- The Argus circuit interpretation of a `queueEnqueue` term: queueEnqueue's OWN audited standalone v2-triple
`EffectCommit3` circuit step — the full-state arithmetization `satisfiedE2Triple S (queueEnqueueE D hD …)
(encodeE2Triple …)` satisfied on the encoded `(st, args, st')` triple. Its soundness `queueEnqueueA_full_sound`
pins the complete `QueueEnqueueSpec`. The `queueEnqueue`-keyed analog of `balanceACircuit`, in the descriptor
universe where queueEnqueue carries its OWN genuine full-state triple-component circuit. -/
def queueEnqueueCircuit
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (st : RecChainedState) (args : EnqueueArgs) (st' : RecChainedState) : Prop :=
  satisfiedE2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
    (encodeE2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) st args st')

/-- **`queueEnqueueSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`QueueEnqueueSpec st … ·` are equal. Rather than re-derive this field-by-field, we route through the PROVEN
executor⟺spec corner `execFullA_queueEnqueueA_iff_spec`: each `QueueEnqueueSpec` reconstructs the SAME
committed value `execFullA st (.queueEnqueueA …) = some ·`, and `some` is injective. This is exactly the sense
in which `QueueEnqueueSpec` is functional — it determines the post-state — so the circuit-side and
executor-side spec facts collapse to one welded post-state. -/
theorem queueEnqueueSpec_unique {st st₁ st₂ : RecChainedState} {id m : Nat} {actor cell : CellId}
    {depId : Nat} {dAsset : AssetId} {deposit : ℤ}
    (h₁ : QueueEnqueueSpec st id m actor cell depId dAsset deposit st₁)
    (h₂ : QueueEnqueueSpec st id m actor cell depId dAsset deposit st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.queueEnqueueA id m actor cell depId dAsset deposit) = some st₁ :=
    (execFullA_queueEnqueueA_iff_spec st id m actor cell depId dAsset deposit st₁).mpr h₁
  have e₂ : execFullA st (.queueEnqueueA id m actor cell depId dAsset deposit) = some st₂ :=
    (execFullA_queueEnqueueA_iff_spec st id m actor cell depId dAsset deposit st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`queueEnqueue_compile_sound` — the welded soundness (queueEnqueue slice), against queueEnqueue's OWN
descriptor.**

Suppose, for the Argus queueEnqueue term `queueEnqueueStmt id m actor cell depId dAsset deposit` (with
`args = ⟨id, m, actor, cell, depId, dAsset, deposit⟩`):
  * the standalone queueEnqueue circuit `queueEnqueueCircuit S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE st args st'`
    (= `queueEnqueueE`'s full-state triple arithmetization satisfied on the encoded triple) holds, under the
    realizable digest portals (`hRest : RestIffNoQueuesBalEscrows S.RH`, `hLog : logHashInjective S.LH`,
    `hD : Function.Injective D`, the two `compressNInjective`/`listLeafInjective` pairs for the `queues` and
    `escrows` list-digests);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel:
    `interp (queueEnqueueStmt …) st.kernel = some k'` (`hexec`), with the writer holding the ACL
    (`hauth`) and the cell accepting effects (`haccept`, the chained pre-gates).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := enqueueReceipt actor cell deposit :: st.log }`. I.e. queueEnqueue's
OWN circuit and the IR term AGREE on the WHOLE 17-field `RecordKernelState` (the composed `queues` FIFO
append + `bal` deposit debit + `escrows` deposit-record prepend, every other field frozen) AND the receipt
log — the full `QueueEnqueueSpec`, not a per-cell projection. So the circuit the prover runs for
queueEnqueue pins the complete state the IR term's executor produces. -/
theorem queueEnqueue_compile_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (id m : Nat) (actor cell : CellId) (depId : Nat) (dAsset : AssetId)
    (deposit : ℤ) (k' : RecordKernelState)
    (hcirc : queueEnqueueCircuit S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE st
                ⟨id, m, actor, cell, depId, dAsset, deposit⟩ st')
    (hauth : stateAuthB st.kernel.caps actor cell = true)
    (haccept : acceptsEffects st.kernel cell = true)
    (hexec : interp (queueEnqueueStmt id m actor cell depId dAsset deposit) st.kernel = some k') :
    st' = { kernel := k', log := enqueueReceipt actor cell deposit :: st.log } := by
  -- circuit side: queueEnqueue's OWN audited soundness forces the FULL `QueueEnqueueSpec` on `(st, args, st')`.
  have hspec : QueueEnqueueSpec st id m actor cell depId dAsset deposit st' :=
    queueEnqueueA_full_sound S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest hLog st
      ⟨id, m, actor, cell, depId, dAsset, deposit⟩ st' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.queueEnqueueA …) = some ⟨k', receipt :: log⟩`,
  -- and the independent executor⟺spec corner turns THAT into the `QueueEnqueueSpec` over that state.
  have hspec' : QueueEnqueueSpec st id m actor cell depId dAsset deposit
      { kernel := k', log := enqueueReceipt actor cell deposit :: st.log } :=
    (execFullA_queueEnqueueA_iff_spec st id m actor cell depId dAsset deposit _).mp
      (interp_queueEnqueueStmt_chained st id m actor cell depId dAsset deposit k' hauth haccept hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact queueEnqueueSpec_unique hspec hspec'

#assert_axioms queueEnqueue_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely MOVES all three components (FIFO append + deposit debit +
record park observable), and the gate REJECTS forged inputs (fail-closed).

The cornerstone/weld would be hollow if queueEnqueue never committed, if any of the three writes were a
no-op, or if the gate admitted everything. A concrete kernel `kQ0` (cell 0 live, a fresh empty capacity-2
queue id 7, cell 0 holds 30 of asset 0) exercises a real enqueue+park; the rejection lemmas show the FIFO
capacity leg and the deposit-availability leg each fail closed. -/

/-- A concrete kernel for the witnesses: cells 0 and 1 are live accounts, a single empty queue (id 7, owner
0, capacity 2) sits in `queues`, cell 0 holds 30 of asset 0 on the per-asset ledger `bal`, `escrows` empty. -/
def kQ0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 ∧ a = 0 then 30 else 0
    queues := [{ id := 7, owner := 0, capacity := 2, buffer := [] }] }

/-- **NON-VACUITY (the FIFO APPEND is OBSERVABLE).** A committed enqueue of message `99` into queue `7`
GROWS the queue's buffer from `[]` to `[99]` — the message genuinely lands at the tail (the `setQueues`/
`qbufEnqueue` append is real, not a no-op). Deposit `0` keeps the deposit legs trivially satisfied. -/
theorem queueEnqueueStmt_appends :
    (interp (queueEnqueueStmt 7 99 0 0 5 0 0) kQ0).map
        (fun k => (findQueue k.queues 7).map (·.buffer)) = some (some [99]) := by
  rw [interp_queueEnqueueStmt_eq_queueEnqueueDepositK]
  decide

/-- **NON-VACUITY (the deposit PARK is OBSERVABLE).** A committed enqueue with a positive deposit PREPENDS
an unresolved deposit record onto `escrows`, growing it from `[]` to length `1` — the off-ledger park is
real. (Cell 0 holds 30 of asset 0, so a deposit of 5 is available.) -/
theorem queueEnqueueStmt_parks_deposit :
    (interp (queueEnqueueStmt 7 99 0 0 5 0 5) kQ0).map (fun k => k.escrows.length) = some 1 := by
  rw [interp_queueEnqueueStmt_eq_queueEnqueueDepositK]
  decide

/-- **NON-VACUITY (the deposit DEBIT is OBSERVABLE).** A committed enqueue with deposit `5` of asset `0`
DROPS cell 0's asset-0 ledger entry from `30` to `25` — the value genuinely LEAVES the sender's bare ledger
(parked off-ledger; the `setBal`/`recBalCreditCell` debit is real). -/
theorem queueEnqueueStmt_debits_deposit :
    (interp (queueEnqueueStmt 7 99 0 0 5 0 5) kQ0).map (fun k => k.bal 0 0) = some 25 := by
  rw [interp_queueEnqueueStmt_eq_queueEnqueueDepositK]
  decide

/-- **NON-VACUITY (fail-closed: queue FULL).** Enqueuing into a queue already at capacity does NOT commit —
the term returns `none` (the FIFO capacity leg of the guard fails). A capacity-0 queue (id 8) can never
accept a message. No buffer overflow. -/
theorem queueEnqueueStmt_rejects_full :
    interp (queueEnqueueStmt 8 99 0 0 5 0 0)
      { kQ0 with queues := [{ id := 8, owner := 0, capacity := 0, buffer := [] }] } = none := by
  rw [interp_queueEnqueueStmt_eq_queueEnqueueDepositK]
  decide

/-- **NON-VACUITY (fail-closed: absent queue).** Enqueuing into a NON-existent queue id does NOT commit —
the term returns `none` (the FIFO presence leg fails). No message lands. -/
theorem queueEnqueueStmt_rejects_absent :
    interp (queueEnqueueStmt 999 99 0 0 5 0 0) kQ0 = none := by
  rw [interp_queueEnqueueStmt_eq_queueEnqueueDepositK]
  decide

/-- **NON-VACUITY (fail-closed: insufficient deposit).** An enqueue whose deposit (here 31) exceeds the
sender's holding in asset `0` (30 available) does NOT commit — the term returns `none` (the deposit
AVAILABILITY leg fails). No value is conjured. -/
theorem queueEnqueueStmt_rejects_overdeposit :
    interp (queueEnqueueStmt 7 99 0 0 5 0 31) kQ0 = none := by
  rw [interp_queueEnqueueStmt_eq_queueEnqueueDepositK]
  decide

/-- **NON-VACUITY (fail-closed: negative deposit).** An enqueue with a NEGATIVE deposit does NOT commit —
the term returns `none` (the non-negativity leg fails). Value cannot be conjured by a negative park. -/
theorem queueEnqueueStmt_rejects_negative_deposit :
    interp (queueEnqueueStmt 7 99 0 0 5 0 (-1)) kQ0 = none := by
  rw [interp_queueEnqueueStmt_eq_queueEnqueueDepositK]
  decide

#assert_axioms queueEnqueueStmt_appends
#assert_axioms queueEnqueueStmt_parks_deposit
#assert_axioms queueEnqueueStmt_debits_deposit
#assert_axioms queueEnqueueStmt_rejects_full
#assert_axioms queueEnqueueStmt_rejects_absent
#assert_axioms queueEnqueueStmt_rejects_overdeposit
#assert_axioms queueEnqueueStmt_rejects_negative_deposit

end Dregg2.Circuit.Argus.Effects.QueueEnqueue
