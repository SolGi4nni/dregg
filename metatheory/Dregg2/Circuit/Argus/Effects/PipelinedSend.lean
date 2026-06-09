/-
# Dregg2.Circuit.Argus.Effects.PipelinedSend — the CapTP-routing apply-time clock effect
`pipelinedSendA` welded into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn/createEscrow; `Effects/BalanceA.lean` welded a per-asset move against a
FULL-STATE descriptor; `Effects/Seal.lean` welded a kernel-touching LIST-side-table effect against its
own full-state descriptor over the chained executor. This module welds the genuinely DIFFERENT
**CapTP pipelined-send** primitive `pipelinedSendA` — the apply-time NEUTRAL clock row of captp routing
(a pipelined send whose real dispatch / `EventualRef`→prior-result resolution already ran in the
`ConditionalTurn` pass; at apply time it is a balance-neutral clock tick). It lives in a disjoint file
(it imports the Argus IR + the audited `pipelinedSendA` v1 instance + the queue-pipelined-send spec
read-only, and owns only its own declarations).

`pipelinedSendA` is the apply-time-neutral arm of the FULL op-set executor `execFullA`
(`TurnExecutorFull.lean:3885`):

    | .pipelinedSendA actor => some { kernel := s.kernel, log := escrowReceiptA actor :: s.log }

so a committed pipelined-send (the executor's `pipelinedSendA` arm):

  * is **TOTAL** — there is **NO fail-closed gate** at apply time (`some { … }` UNCONDITIONALLY; the
    admissibility already happened in the deferred-dispatch resolution pass). Contrast every prior weld
    (transfer's six-conjunct gate, balanceA's six, seal's two): this arm has NO precondition whatsoever.
  * **FREEZES the entire kernel** — it sets `kernel := s.kernel` VERBATIM, so ALL 17 `RecordKernelState`
    fields are LITERALLY unchanged (the `frame-mostly-frozen` shape of captp routing — the whole kernel,
    in fact).
  * **PREPENDS one NEUTRAL receipt** `escrowReceiptA actor = ⟨actor, actor, actor, 0⟩` to the receipt
    LOG — a balance-`0` self-`Turn` clock row (no send-specific payload), the SOLE post-state change.

That is the structural contrast with every prior weld: transfer/balanceA touch the per-cell/per-asset
value tables, seal touches the `sealedBoxes` list — pipelinedSend touches the bare `RecordKernelState`
in NO field at all, only the chained-runtime receipt LOG.

## THE DESCRIPTOR (a FULL-STATE `CommitSurface` weld, the strong surface BalanceA/Seal prefer).

`pipelinedSendA` carries its OWN genuine standalone circuit⟺spec crown jewel in the v1 `EffectCommit`
`CommitSurface` universe (`Dregg2/Circuit/Inst/pipelinedSendA.lean`): `pipelinedSendE` (the `EffectSpec`
whose touched set is `∅` — the kernel is frozen — and whose `logUpdate` GROWS the log by exactly the
neutral receipt) and `pipelinedSendA_full_sound : satisfiedE … pipelinedSendE … ⟹ PipelinedSendSpec` —
a FULL 18-component (all 17 kernel fields + the receipt `log`) declarative post-state soundness, whose
executor corner is the independent `execFullA_pipelinedSend_iff_spec` (`Spec/queuepipelinedsend.lean`).
So — exactly like BalanceA/Seal — this module welds the FULL-STATE `pipelinedSendA_full_sound` DIRECTLY
against the Argus term, concluding the WHOLE `PipelinedSendSpec` agreement (strictly stronger than a
per-cell EffectVM weld). There is no v2 `Surface2`/`EffectVm` descriptor for this effect; the v1
`CommitSurface` one is the genuine standalone descriptor (it is exactly the one
`EffectRefinementBatch2.pipelinedSendCircuitStep` / `…_circuit_refines_spec` uses).

## THE KERNEL-vs-RUNTIME DIVERGENCE (the task's `divergence` field — carried, NOT papered).

The Argus `RecStmt`/`interp` runs on the bare `RecordKernelState` (kernel-only). The pipelined-send's
ENTIRE post-state change — the neutral receipt prepended to the receipt LOG — lives OUTSIDE the kernel,
in the `RecChainedState.log` the IR cannot name. So the KERNEL fragment of `pipelinedSendA` is the
**IDENTITY** (the kernel is frozen verbatim), captured by the IR term `RecStmt.skip` (TOTAL, mutates
nothing — the faithful kernel projection of a frozen-kernel total effect). The cornerstone (§2) pins
`interp pipelinedSendStmt k = some k` (the kernel half IS the identity), and the §3 lift carries the
log-prepend as the EXPLICIT divergence leg: `execFullA st (.pipelinedSendA actor)` does the bare-kernel
identity PLUS prepend exactly `pipelinedSendReceipt actor :: st.log`. This is the SAME kernel-vs-chained
divergence shape `Seal.lean`/`BalanceA.lean` carry (their §3 lifts add a receipt-log prepend / a
dst-liveness side-condition); here it is the WHOLE effect (the kernel half is vacuous), made fully
explicit. This is the honest cost of welding a chained-LOG effect against a KERNEL-only IR: the IR term
is `skip`, and ALL of the effect's content is in the carried chained leg.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
frame-digest assumptions enter ONLY inside the reused `pipelinedSendA_full_sound` (its
`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective` portal hypotheses + the
`AccountsWF` well-formedness preconditions of the v1 framework), not in the welded conclusion's
statement. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only; this file owns only
itself. Build: `lake build Dregg2.Circuit.Argus.Effects.PipelinedSend`.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.pipelinedSendA
import Dregg2.Circuit.Spec.queuepipelinedsend

namespace Dregg2.Circuit.Argus.Effects.PipelinedSend

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/pipelinedSendA.lean` / `EffectRefinementBatch2.pipelinedSend…` so the
-- standalone-descriptor names resolve unqualified: the v1 `CommitSurface` + its `satisfiedE`/`encodeE`
-- carriers + the CR/WF portals in `EffectCommit`/`StateCommit`; the v1 `pipelinedSendA` descriptor
-- (`pipelinedSendE`/`pipelinedSendA_full_sound`/the args) in `Inst.PipelinedSendA`; the INDEPENDENT
-- full-state `PipelinedSendSpec` + executor corner + the neutral receipt in the queue-pipelined-send spec.
open Dregg2.Circuit.StateCommit
  (compressNInjective cellLeafInjective RestHashIffFrame logHashInjective AccountsWF)
open Dregg2.Circuit.EffectCommit (CommitSurface EffectSpec satisfiedE encodeE)
open Dregg2.Circuit.Inst.PipelinedSendA (PipelinedSendArgs pipelinedSendE pipelinedSendA_full_sound)
open Dregg2.Circuit.Spec.QueuePipelinedSend
  (PipelinedSendSpec pipelinedSendReceipt execFullA_pipelinedSend_iff_spec)

/-! ## §1 — The pipelinedSend effect as an Argus IR term (the FROZEN-KERNEL identity).

`pipelinedSendA`'s KERNEL content is the IDENTITY: the executor sets `kernel := s.kernel` verbatim under
NO guard (TOTAL). The faithful Argus term for "freeze the whole kernel, always commit" is `RecStmt.skip`
— its `interp` is `some k` unconditionally, mutating no `RecordKernelState` field. The effect's SOLE
post-state change — the neutral receipt prepended to the receipt LOG — is NOT a `RecordKernelState`
component (it lives in `RecChainedState.log`), so it is OUTSIDE the kernel-only IR and is carried as the
explicit chained-divergence leg in §3 (the kernel-vs-runtime divergence this effect makes maximal — the
kernel half is the identity, and ALL of the effect is the carried log leg). -/

/-- **The pipelinedSend effect as an IR term: the frozen-kernel identity (`skip`).** Unlike
transfer/balanceA (a `setCell`/`setBal` move) or seal (a `setSealedBoxes` list write), the apply-time
pipelined-send touches NO kernel field — it freezes the whole kernel verbatim (`kernel := s.kernel`) and
is TOTAL (no gate). So the kernel-half Argus term is `RecStmt.skip`: it always commits and mutates
nothing, EXACTLY the kernel projection of `pipelinedSendA`. The receipt-log prepend `pipelinedSendA` ALSO
does lives at the chained layer, off the bare `RecordKernelState` the IR mutates — carried in §3 as the
explicit divergence leg. (`actor` is unused in the kernel half: the kernel is frozen regardless of who
acts; the actor enters only the receipt row, in the carried log leg.) -/
def pipelinedSendStmt (_actor : CellId) : RecStmt :=
  RecStmt.skip

/-! ## §2 — The cornerstone: `interp` of the pipelinedSend term IS the KERNEL fragment (the identity).

The Argus `interp` runs on the bare `RecordKernelState`. `pipelinedSendA`'s kernel post is exactly
`s.kernel` (frozen verbatim, TOTAL). We pin that the IR term commits to PRECISELY that kernel state
(unconditionally — there is no reject branch, the effect is total). This is the frozen-kernel analog of
`interp_balanceAStmt_eq_recKExecAsset` / `interp_sealStmt_eq_sealKernel`: the executor's kernel half IS
the meaning of the term, here the identity. -/

/-- **The cornerstone (pipelined-send, kernel fragment).** `interp` of the pipelinedSend term IS the
IDENTITY on the kernel — the same (total) partial function `pipelinedSendA` realizes on the kernel
(`kernel := s.kernel` verbatim), by construction. There is NO guard branch: the effect is TOTAL, so
`interp` always commits to the unchanged `k`. The executor's kernel half IS the meaning of the term. -/
theorem interp_pipelinedSendStmt_eq_id (actor : CellId) (k : RecordKernelState) :
    interp (pipelinedSendStmt actor) k = some k := by
  simp only [pipelinedSendStmt, interp]

#assert_axioms interp_pipelinedSendStmt_eq_id

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `execFullA` (carrying the log divergence).

The standalone pipelinedSend descriptor (§4) is keyed on the CHAINED executor `execFullA` over
`RecChainedState` (kernel + receipt log) — the arm `execFullA s (.pipelinedSendA actor) = some { kernel
:= s.kernel, log := escrowReceiptA actor :: s.log }`. The §2 cornerstone is over the bare KERNEL step
(the identity). The chained layer is exactly that identity PLUS the receipt-log prepend
`pipelinedSendReceipt actor :: s.log` (= `escrowReceiptA actor :: s.log`, the neutral `⟨actor,actor,actor,
0⟩` clock row). We bridge faithfully, CARRYING that log-prepend as an explicit equality leg — the honest
kernel-vs-chained (kernel-vs-runtime) DIVERGENCE, NOT papered. Here that leg is the WHOLE effect (the
kernel half being the identity), made fully explicit. -/

/-- **`interp_pipelinedSendStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.**
When the §2 cornerstone commits on the kernel (`interp (pipelinedSendStmt actor) st.kernel = some k'`, so
`k' = st.kernel` — the kernel is frozen), the unified action executor `execFullA st (.pipelinedSendA
actor)` commits to the chained state `⟨k', pipelinedSendReceipt actor :: st.log⟩`. So the Argus term's
kernel meaning (the identity) lifts to the chained executor the standalone descriptor speaks about, with
the receipt-log prepend made EXPLICIT — the chained runtime does the bare-kernel identity PLUS one neutral
clock row (the carried divergence; here, the entirety of the effect's behaviour). -/
theorem interp_pipelinedSendStmt_chained
    (st : RecChainedState) (actor : CellId) (k' : RecordKernelState)
    (hexec : interp (pipelinedSendStmt actor) st.kernel = some k') :
    execFullA st (.pipelinedSendA actor)
      = some { kernel := k', log := pipelinedSendReceipt actor :: st.log } := by
  -- the §2 cornerstone fixes `k' = st.kernel` (the kernel half is the identity, TOTAL).
  rw [interp_pipelinedSendStmt_eq_id] at hexec
  simp only [Option.some.injEq] at hexec
  subst hexec
  -- `execFullA st (.pipelinedSendA actor)` reduces to `some { kernel := st.kernel, log := escrowReceiptA
  -- actor :: st.log }`; the receipt row is `pipelinedSendReceipt actor` by definition (`⟨a,a,a,0⟩`).
  show (some { kernel := st.kernel, log := escrowReceiptA actor :: st.log } : Option RecChainedState)
      = some { kernel := st.kernel, log := pipelinedSendReceipt actor :: st.log }
  simp only [pipelinedSendReceipt, escrowReceiptA]

#assert_axioms interp_pipelinedSendStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of pipelinedSend's OWN standalone circuit agrees with
the FULL post-state the IR term's executor interpretation produces.

This welds against pipelinedSend's GENUINE standalone descriptor `pipelinedSendCircuit S st actor st'`
(the v1 `CommitSurface` circuit whose soundness is `pipelinedSendA_full_sound`), exactly the BalanceA/Seal
pattern. The executor side is routed through §3 (`interp` ⟹ `execFullA`) and the independent
`execFullA_pipelinedSend_iff_spec` (executor ⟺ `PipelinedSendSpec`); the circuit side is the audited
`pipelinedSendA_full_sound` (circuit ⟹ `PipelinedSendSpec`). Both name the SAME `PipelinedSendSpec`, so
they PROVABLY agree on the WHOLE 18-component state (all 17 frozen kernel fields + the receipt log grown
by exactly the neutral receipt) — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `pipelinedSendA` term: pipelinedSend's OWN audited standalone v1
`CommitSurface` circuit step — the full-state arithmetization `satisfiedE S pipelinedSendE (encodeE …)`
satisfied on the encoded `(st, ⟨actor⟩, st')` triple (DEFINITIONALLY
`EffectRefinementBatch2.pipelinedSendCircuitStep S st ⟨actor⟩ st'`, inlined here so this module imports
only `Inst.pipelinedSendA`). Its soundness `pipelinedSendA_full_sound` pins the complete
`PipelinedSendSpec`. The `pipelinedSendA`-keyed analog of `BalanceA`'s `balanceACircuit` / `Seal`'s
`sealCircuit`, in the descriptor universe where pipelinedSend carries its OWN genuine full-state
(frozen-kernel + growing-log) circuit. -/
def pipelinedSendCircuit (S : CommitSurface) (st : RecChainedState) (actor : CellId)
    (st' : RecChainedState) : Prop :=
  satisfiedE S pipelinedSendE (encodeE S pipelinedSendE st ({ actor := actor } : PipelinedSendArgs) st')

/-- **`pipelinedSendSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH
satisfy `PipelinedSendSpec st actor ·` are equal. Rather than re-derive this field-by-field, we route
through the PROVEN executor⟺spec corner `execFullA_pipelinedSend_iff_spec`: each `PipelinedSendSpec`
reconstructs the SAME committed value `execFullA st (.pipelinedSendA actor) = some ·`, and `some` is
injective. This is exactly the sense in which `PipelinedSendSpec` is functional — it determines the
post-state — so the circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem pipelinedSendSpec_unique {st st₁ st₂ : RecChainedState} {actor : CellId}
    (h₁ : PipelinedSendSpec st actor st₁) (h₂ : PipelinedSendSpec st actor st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.pipelinedSendA actor) = some st₁ :=
    (execFullA_pipelinedSend_iff_spec st actor st₁).mpr h₁
  have e₂ : execFullA st (.pipelinedSendA actor) = some st₂ :=
    (execFullA_pipelinedSend_iff_spec st actor st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`pipelinedSend_compile_sound` — the welded soundness (pipelinedSend slice), against pipelinedSend's
OWN descriptor.**

Suppose, for the Argus pipelinedSend term `pipelinedSendStmt actor`:
  * the standalone pipelinedSend circuit `pipelinedSendCircuit S st actor st'` (= `pipelinedSendE`'s
    full-state v1 arithmetization satisfied on the encoded triple) holds, under the realizable portals
    (`hN : compressNInjective S.compressN`, `hL : cellLeafInjective S.CH`, `hRest : RestHashIffFrame S.RH`,
    `hLog : logHashInjective S.LH`) and the framework's well-formedness preconditions (`hwf`/`hwf'` —
    cells outside `accounts` hold `default`, the v1 `CommitSurface` `AccountsWF` requirement);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel: `interp (pipelinedSendStmt actor)
    st.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := pipelinedSendReceipt actor :: st.log }`. I.e. pipelinedSend's OWN
circuit and the IR term AGREE on the WHOLE 18-component state (all 17 kernel fields frozen — the
`frame-mostly-frozen` shape, here the whole kernel) AND the receipt log (grown by exactly the neutral
`pipelinedSendReceipt actor` clock row — the §3 carried kernel-vs-chained divergence). So the circuit the
prover runs for pipelinedSend pins the complete state the IR term's executor produces. -/
theorem pipelinedSend_compile_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (actor : CellId) (k' : RecordKernelState)
    (hwf : AccountsWF st.kernel) (hwf' : AccountsWF st'.kernel)
    (hcirc : pipelinedSendCircuit S st actor st')
    (hexec : interp (pipelinedSendStmt actor) st.kernel = some k') :
    st' = { kernel := k', log := pipelinedSendReceipt actor :: st.log } := by
  -- circuit side: pipelinedSend's OWN audited soundness forces the FULL `PipelinedSendSpec` on
  -- `(st, ⟨actor⟩, st')` (all 17 kernel fields + the log).
  have hspec : PipelinedSendSpec st actor st' :=
    pipelinedSendA_full_sound S hN hL hRest hLog st ({ actor := actor } : PipelinedSendArgs) st'
      hwf hwf' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.pipelinedSendA actor) = some ⟨k',
  -- pipelinedSendReceipt :: log⟩`, and the independent executor⟺spec corner turns THAT into
  -- `PipelinedSendSpec st actor ⟨k', …⟩`.
  have hspec' : PipelinedSendSpec st actor { kernel := k', log := pipelinedSendReceipt actor :: st.log } :=
    (execFullA_pipelinedSend_iff_spec st actor _).mp
      (interp_pipelinedSendStmt_chained st actor k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + log).
  exact pipelinedSendSpec_unique hspec hspec'

#assert_axioms pipelinedSend_compile_sound

/-! ## §5 — NON-VACUITY: the chained step genuinely TICKS the log with the NEUTRAL receipt (observable),
the kernel is genuinely FROZEN, and the effect is TOTAL (commits unconditionally, regardless of actor).

The cornerstone/weld would be hollow if the kernel term were not the identity, if the chained step never
committed, or if the log were not actually grown. A concrete chained pre-state `stPS0` (live accounts
{0,1}, empty log) exercises a real clock tick; the totality lemmas show it commits with NO precondition
(even on a non-account actor). These exhibit the §2/§3 facts DIRECTLY on the Argus term + its chained
lift, not just on the executor. -/

/-- A concrete chained pre-state for the witnesses: cells 0 and 1 are live accounts (lifecycle defaults
Live), empty receipt log. -/
def stPS0 : RecChainedState :=
  { kernel := { accounts := {0, 1}, cell := fun _ => .record [], caps := fun _ => [] }
    log    := [] }

/-- **NON-VACUITY (the kernel term is the IDENTITY, observable).** The Argus kernel term `interp
(pipelinedSendStmt 0) stPS0.kernel` commits to PRECISELY the unchanged kernel — the frozen-kernel half is
a genuine `some`, not `none`, and the post-kernel IS the input (cell `0` still holds `.record []`). The
kernel half is the identity, exhibited on the concrete state. -/
theorem pipelinedSendStmt_kernel_id :
    interp (pipelinedSendStmt 0) stPS0.kernel = some stPS0.kernel := by
  rw [interp_pipelinedSendStmt_eq_id]

/-- **NON-VACUITY (the chained step COMMITS — TOTAL).** The chained lift of a pipelined-send (actor 0)
commits unconditionally — `execFullA stPS0 (.pipelinedSendA 0)` is `some _`, with NO precondition (the
apply-time effect has no fail-closed gate). Exhibited through the §3 lift fed by the §2 cornerstone. -/
theorem pipelinedSendStmt_chained_commits :
    (execFullA stPS0 (.pipelinedSendA 0)).isSome = true := by
  rw [interp_pipelinedSendStmt_chained stPS0 0 stPS0.kernel
      (interp_pipelinedSendStmt_eq_id 0 stPS0.kernel)]
  rfl

/-- **NON-VACUITY (the log TICKS by exactly ONE NEUTRAL receipt, observable).** The chained step GROWS the
receipt log from `[]` to length `1` — the clock genuinely ticks by exactly one audited row (the carried
divergence leg is REAL, not a no-op). The post-log head is the neutral `pipelinedSendReceipt 0` marker. -/
theorem pipelinedSendStmt_log_ticks :
    (execFullA stPS0 (.pipelinedSendA 0)).map (fun s => s.log) = some [pipelinedSendReceipt 0] := by
  rw [interp_pipelinedSendStmt_chained stPS0 0 stPS0.kernel
      (interp_pipelinedSendStmt_eq_id 0 stPS0.kernel)]
  rfl

/-- **NON-VACUITY (the receipt is the NEUTRAL clock row).** The prepended receipt is the apply-time
NEUTRAL marker `⟨0, 0, 0, 0⟩` (actor = src = dst, amount `0`) — balance-neutral, carrying no
send-specific payload. The teeth of "apply-time NEUTRAL clock tick". -/
theorem pipelinedSendStmt_receipt_neutral :
    (execFullA stPS0 (.pipelinedSendA 0)).bind (fun s => s.log.head?)
      = some { actor := 0, src := 0, dst := 0, amt := 0 } := by
  rw [interp_pipelinedSendStmt_chained stPS0 0 stPS0.kernel
      (interp_pipelinedSendStmt_eq_id 0 stPS0.kernel)]
  rfl

/-- **NON-VACUITY (TOTAL — commits regardless of actor).** The chained step commits even on a non-account
actor `7` (no admissibility gate whatsoever — the dual of every prior effect, which fails closed on a
bad actor/cap). Confirms the §2 term's `skip` (always-commit) is faithful to the TOTAL executor arm. -/
theorem pipelinedSendStmt_total_any_actor :
    (execFullA stPS0 (.pipelinedSendA 7)).isSome = true := by
  rw [interp_pipelinedSendStmt_chained stPS0 7 stPS0.kernel
      (interp_pipelinedSendStmt_eq_id 7 stPS0.kernel)]
  rfl

#assert_axioms pipelinedSendStmt_kernel_id
#assert_axioms pipelinedSendStmt_chained_commits
#assert_axioms pipelinedSendStmt_log_ticks
#assert_axioms pipelinedSendStmt_receipt_neutral
#assert_axioms pipelinedSendStmt_total_any_actor

end Dregg2.Circuit.Argus.Effects.PipelinedSend
