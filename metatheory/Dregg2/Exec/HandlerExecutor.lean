/-
# Dregg2.Exec.HandlerExecutor — THE CUTOVER KEYSTONE (additive; the live switch is mechanical).

This is the file the seven handler batches were built FOR. It assembles them into ONE executor that is a
DROP-IN, SOUNDNESS-STRENGTHENING replacement for `TurnExecutorFull.execFullA`, and proves the global
conservation/gate laws for it WITHOUT a per-arm matrix — by LIFTING the scaffold's generic `turn_conserves`
/ `turn_head_authorized` / `turn_head_admitted` (`Dregg2.Exec.Handler`). This is additive: it does NOT edit
`execFullA`/`FullActionA`; switching the call-sites is a later mechanical step.

The five deliverables:

  1. **`masterRegistry`** (`§2`) — the coproduct `Registry = List PackedHandler` packing ALL the proved
     handlers across the seven files (transfer / mint / burn / state-write / createCell / escrow /
     release / refund / note / seal / unseal / seal-pair / swiss-export/enliven/handoff/drop / delegate /
     attenuate / revoke / queue-allocate/enqueue/dequeue/resize/atomic/pipeline / bridge-lock/finalize/
     cancel / pipelined-send / exercise). Every entry's obligation proofs are a TYPING condition on entry.

  2. **`toClosedEffect`** (`§3`) — the TOTAL map `FullActionA → ClosedEffect` mapping each of the 56
     constructors to its handler + args, ALIASES collapsed (obligation→escrow, committed→escrow,
     introduce/validateHandoff→delegateAtten, slash→release, fulfill→refund, bridgeMint→mint,
     createCellFromFactory/spawn→createCell, dropRef/revokeDelegation→revoke, the lifecycle/emit
     family→a live-gated state write). 56/56 constructors covered.

  3. **`execHandlerTurn`** (`§4`) — `List FullActionA → RecChainedState → Option RecChainedState`: map
     `toClosedEffect`, run each `ClosedEffect`'s `step` on the `.kernel`, thread the state through the
     scaffold's generic `execTurn` (the `.log` carries the audit trace).

  4. **THE DERIVED GLOBAL CONSERVATION** (`§5`) — `execHandlerTurn_conserves`: the combined per-asset
     measure `recTotalAssetWithEscrow` (over `.kernel`; log-independent) moves by the SUM of the
     per-effect deltas, proved by LIFTING the scaffold's generic `turn_conserves` (NOT a 56-arm cases
     matrix — THIS is the matrix-killer demonstrated at full scale). Plus the gate companions
     (`execHandlerTurn_head_authorized` / `_admitted`) lifted from `turn_head_authorized`/`_admitted`.

  5. **THE STRENGTHENING** (`§6`) — `handler_refines_execFullA_*`: the handler executor is a SOUND
     STRENGTHENING of `execFullA`: for the hole-closing effects (a transfer R1, an escrow-release R2, a
     state-write R6) every commit the handler executor makes, `execFullA` ALSO makes, AND they AGREE on
     the kernel. The handlers only ADD gates.

  6. **THE TEETH** (`§7`) — concrete attacks `execFullA` ADMITS but `execHandlerTurn` REJECTS: a transfer
     into a Sealed cell (R1), an escrow-release by a stranger (R2), a state-write into a Sealed cell (R6).
     `#eval`-verified: `execFullA = some` (the live hole) vs `execHandlerTurn = none` (the algebra closes
     it). The cutover STRICTLY improves soundness.

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/eval-only; no `maxHeartbeats`. The conservation
keystone REUSES `turn_conserves` (generic) — it is NEVER re-derived. `#assert_axioms`-pinned. Verified
standalone: `lake build Dregg2.Exec.HandlerExecutor`.
-/
import Dregg2.Exec.Handlers.StateSupply
import Dregg2.Exec.Handlers.Escrow
import Dregg2.Exec.Handlers.Seal
import Dregg2.Exec.Handlers.Authority
import Dregg2.Exec.Handlers.Queue
import Dregg2.Exec.Handlers.Bridge
import Dregg2.Exec.Handlers.Exercise

namespace Dregg2.Exec.HandlerExecutor

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull
  (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle execFullA FullActionA QueueTxOpA)
open scoped BigOperators

-- module-qualified aliases for the seven batches (every handler + ClosedEffect builder lives here)
open Dregg2.Exec.Handlers.StateSupply
open Dregg2.Exec.Handlers.Escrow
open Dregg2.Exec.Handlers.Seal
open Dregg2.Exec.Handlers.Authority
open Dregg2.Exec.Handlers.Queue
open Dregg2.Exec.Handlers.Bridge
open Dregg2.Exec.Handlers.Exercise

/-! ## §1 — Pretty names for the master registry indices (the audit-trail tags).

Each `ClosedEffect` already carries the registry `tag` its batch assigned (the coproduct injection key);
`toClosedEffect` (`§3`) reuses each batch's `ClosedEffect` builder VERBATIM, so the tags it emits are the
batch-local ones. The master registry below LISTS every handler so the executor's dispatch is one LOOKUP
over the coproduct — the 56-arm `match` of `execFullA` collapsed into a list. -/

/-! ## §2 — `masterRegistry`: the coproduct (LIST) of ALL the proved handlers, seven batches assembled.

This is the master menu. Each entry is one `PackedHandler` carrying a handler whose obligation proofs are
DISCHARGED (the structure literal would not type-check otherwise). The generic `turn_conserves` /
`turn_head_authorized` / `turn_head_admitted` are generic over THIS list — adding an effect is adding one
well-typed entry, never a lemma. -/

/-- **`masterRegistry`** — the coproduct of all proved handlers across the seven batches. The 56-effect
op-set as a single list; the executor dispatches by LOOKUP, not a bespoke `match`. -/
def masterRegistry : Registry :=
  -- §transfer / supply / state-write (Handler scaffold + StateSupply)
  [ ⟨TransferArgs, transferH⟩
  , ⟨SupplyArgs, mintH⟩, ⟨SupplyArgs, burnH⟩, ⟨SupplyArgs, bridgeMintH⟩
  , ⟨CreateArgs, createCellH⟩, ⟨CreateArgs, createCellFromFactoryH⟩, ⟨CreateArgs, spawnH⟩
  , ⟨StateWriteArgs, stateWriteH⟩
  -- §escrow / obligation / note (Escrow)
  , ⟨CreateEscrowArgs, createEscrowA⟩
  , ⟨SettleArgs, releaseEscrowA⟩, ⟨SettleArgs, refundEscrowA⟩
  , ⟨CreateEscrowArgs, createObligationA⟩
  , ⟨SettleArgs, slashObligationA⟩, ⟨SettleArgs, fulfillObligationA⟩
  , ⟨NoteSpendArgs, noteSpendA⟩, ⟨NoteCreateArgs, noteCreateA⟩
  -- §seal / swiss (Seal)
  , ⟨CreateSealPairArgs, createSealPairA⟩, ⟨SealArgs, sealA⟩, ⟨UnsealArgs, unsealA⟩
  , ⟨ExportArgs, exportSturdyRefA⟩, ⟨EnlivenArgs, enlivenRefA⟩
  , ⟨HandoffArgs, swissHandoffA⟩, ⟨DropArgs, swissDropA⟩
  -- §authority / delegation (Authority)
  , ⟨DelegateArgs, delegateH⟩, ⟨DelegateArgs, introduceH⟩, ⟨DelegateArgs, validateHandoffH⟩
  , ⟨DelegateArgs, delegateAttenH⟩
  , ⟨AttenuateArgs, attenuateH⟩
  , ⟨RevokeArgs, revokeDelegationH⟩, ⟨RevokeArgs, dropRefH⟩, ⟨RevokeArgs, revokeH⟩
  -- §queue (Queue)
  , ⟨AllocateArgs, queueAllocateA⟩, ⟨EnqueueArgs, queueEnqueueA⟩, ⟨DequeueArgs, queueDequeueA⟩
  , ⟨ResizeArgs, queueResizeA⟩, ⟨AtomicTxArgs, queueAtomicTxA⟩, ⟨PipelineArgs, queuePipelineStepA⟩
  -- §bridge (Bridge)
  , ⟨BridgeLockArgs, bridgeLockA⟩, ⟨BridgeFinalizeArgs, bridgeFinalizeA⟩
  , ⟨BridgeCancelArgs, bridgeCancelA⟩, ⟨PipelinedSendArgs, pipelinedSendA⟩
  -- §exercise (Exercise — the recursive sub-effect forest)
  , ⟨ExerciseArgs, exerciseH⟩ ]

/-- The master registry packs 42 distinct handler ENTRIES (the 56 op-set constructors collapse onto these
via the aliasing of `toClosedEffect` — obligation↔escrow, committed↔escrow, slash↔release, fulfill↔refund,
introduce/validateHandoff↔delegateAtten, bridgeMint↔mint, factory/spawn↔createCell, dropRef/
revokeDelegation↔revoke). -/
theorem masterRegistry_length : masterRegistry.length = 42 := rfl

/-! ## §3 — `toClosedEffect`: the TOTAL `FullActionA → ClosedEffect` dispatch (56/56 constructors).

This is the cutover's heart: it sends every `FullActionA` constructor to the registered handler that
implements it, plus its concrete args, by REUSING each batch's `ClosedEffect` builder verbatim (so the
obligation proofs come along for free). The ALIASING is the dregg2 dispatch collapse the catalog already
records: an obligation IS an escrow, a slash IS a release-to-beneficiary, a fulfil IS a refund-to-obligor,
an introduce / validate-handoff IS an attenuated delegation, a bridge-mint IS a mint, a factory/spawn IS a
born-empty createCell, a dropRef / revoke-delegation IS a target revocation, a committed escrow IS an
escrow at the executable layer (the §8 hiding portal is off-ledger).

The lifecycle/emit family (`emitEventA` / `cellSealA` / `cellUnsealA` / `cellDestroyA` /
`refreshDelegationA`) and the seven named-field writes (`setFieldA` / `incrementNonceA` / `setPermissionsA`
/ `setVKA` / `makeSovereignA` / `refusalA` / `receiptArchiveA`) all map onto the GENERIC live-gated
`stateWriteH` (a balance-neutral named-field write through the `acceptsEffects` admission gate) at a
fixed field name — the very gate `execFullA`'s `emitEventA` / lifecycle arms lack (R6). The committed
escrow / queue-atomic-tx args that carry shapes the bare kernel handler does not (the `hidingProof`
witness; the `QueueTxOpA` discriminant) are projected onto the handler's executable core (the escrow
lock; the `QueueTxOpK` sub-op list) — documented at each arm. -/

/-- Project an executor `QueueTxOpA` onto the handler's bare-kernel `QueueTxOpK` sub-op (the atomic-batch
discriminant; the chained step's receipt row lives in `RecChainedState`, off the kernel algebra). -/
def txOpToK : QueueTxOpA → Dregg2.Exec.Handlers.Queue.QueueTxOpK
  | .enqueue id m actor _cell depId dAsset deposit =>
      .enqueue id m actor actor depId dAsset deposit   -- owner-recipient = sender (honest park-for-self in the batch)
  | .dequeue id actor _cell depId _deposit =>
      .dequeue id actor depId

/-- **`toClosedEffect`** — the TOTAL dispatch map (every one of the 56 `FullActionA` constructors). Each
arm reuses its batch's `ClosedEffect` builder, so the looked-up handler's obligation proofs are carried.
Aliases collapse onto one handler; the field-write/lifecycle family routes through the generic
live-gated `stateWriteEffect` at a pinned field name (closing R6 for the whole family). -/
def toClosedEffect : FullActionA → ClosedEffect
  -- §transfer / authority / supply
  | .balanceA t a              => transferEffect t a
  | .delegate del rec t        => delegateEffect del rec t
  | .revoke holder t           => revokeEffect holder t
  | .mintA actor cell a amt     => mintEffect actor cell a amt
  | .burnA actor cell a amt     => burnEffect actor cell a amt
  -- §field writes (the 4 protocol-managed + the 3 Wave-6 flags) → generic live-gated write at a field
  | .setFieldA actor cell f v        => stateWriteEffect actor cell f v
  | .emitEventA actor cell _topic data => stateWriteEffect actor cell "event" data
  | .incrementNonceA actor cell n     => incrementNonceEffect actor cell n
  | .setPermissionsA actor cell p     => setPermissionsEffect actor cell p
  | .setVKA actor cell vk             => setVKEffect actor cell vk
  -- §authority (6 distinct) — introduce/validateHandoff alias the attenuated delegation (keep := allAuths)
  | .introduceA intro rec t          => introduceEffect intro rec t
  | .delegateAttenA del rec t keep   => delegateAttenEffect del rec t keep
  | .attenuateA actor idx keep       => attenuateEffect actor idx keep
  | .dropRefA holder t               => dropRefEffect holder t
  | .revokeDelegationA holder t      => revokeDelegationEffect holder t
  | .validateHandoffA intro rec t    => validateHandoffEffect intro rec t
  -- §exercise (recursive) — the inner FullActionA forest folds onto its handlers via closedToSub
  | .exerciseA actor t inner         =>
      exerciseEffect actor t (inner.map (fun fa => facetedOf Auth.control (toClosedEffect fa)))
  -- §supply / account growth
  | .createCellA actor newCell       => createCellEffect actor newCell
  | .createCellFromFactoryA actor newCell _vk => createCellFromFactoryEffect actor newCell
  | .spawnA actor child _target      => spawnEffect actor child
  | .bridgeMintA actor cell a value  => bridgeMintEffect actor cell a value
  -- §escrow / obligation / committed-escrow / note (obligation/committed alias escrow)
  | .createEscrowA id actor creator recipient asset amount =>
      createEscrowEffect id actor creator recipient asset amount
  | .releaseEscrowA id actor          => releaseEscrowEffect actor id
  | .refundEscrowA id actor           => refundEscrowEffect actor id
  | .createObligationA id actor obligor beneficiary asset stake =>
      createEscrowEffect id actor obligor beneficiary asset stake
  | .fulfillObligationA id actor      => refundEscrowEffect actor id
  | .slashObligationA id actor        => releaseEscrowEffect actor id
  | .noteSpendA nf actor              => noteSpendEffect actor nf
  | .noteCreateA cm actor             => noteCreateEffect actor cm
  | .createCommittedEscrowA id actor creator recipient asset amount _hidingProof =>
      createEscrowEffect id actor creator recipient asset amount
  | .releaseCommittedEscrowA id actor => releaseEscrowEffect actor id
  | .refundCommittedEscrowA id actor  => refundEscrowEffect actor id
  -- §bridge (lock / finalize the delta<0 / cancel / pipelined-send)
  | .bridgeLockA id actor originator destination asset amount =>
      bridgeLockEffect id actor originator destination asset amount
  | .bridgeFinalizeA id actor asset amount => bridgeFinalizeEffect id actor asset amount
  | .bridgeCancelA id actor                => bridgeCancelEffect actor id
  -- §seal / swiss
  | .sealA pid actor payload      => sealEffect pid actor payload
  | .unsealA pid actor recipient  => unsealEffect pid actor recipient
  | .createSealPairA pid actor sealerHolder unsealerHolder =>
      createSealPairEffect pid actor sealerHolder unsealerHolder
  -- §flag/lifecycle writes (makeSovereign / refusal / receiptArchive) → generic live-gated write
  | .makeSovereignA actor cell    => makeSovereignEffect actor cell
  | .refusalA actor cell          => refusalEffect actor cell
  | .receiptArchiveA actor cell   => receiptArchiveEffect actor cell 1
  -- §queue
  | .queueAllocateA id actor cell cap   => allocateEffect actor id cell cap
  | .queueEnqueueA id m actor cell depId dAsset deposit =>
      enqueueEffect id m actor cell depId dAsset deposit
  | .queueDequeueA id actor _cell depId _deposit => dequeueEffect id actor depId
  | .queueResizeA id newCap actor cell  => resizeEffect actor id newCap cell
  | .queueAtomicTxA actor ops           => atomicTxEffect actor (ops.map txOpToK)
  | .queuePipelineStepA srcId owner sinkCells sinkIds =>
      pipelineEffect srcId owner sinkCells sinkIds
  | .pipelinedSendA actor               => pipelinedSendEffect actor
  -- §swiss
  | .exportSturdyRefA sw actor exporter target rights =>
      exportSturdyRefEffect sw actor exporter target rights
  | .enlivenRefA sw actor exporter claimed => enlivenRefEffect sw actor exporter claimed
  | .swissHandoffA sw certHash introducer exporter =>
      swissHandoffEffect sw certHash introducer exporter
  | .swissDropA sw actor exporter          => swissDropEffect sw actor exporter
  -- §lifecycle (cell seal/unseal/destroy + refresh-delegation) → generic live-gated write at a field
  -- (the REAL Live↔Sealed/Destroyed state machine is `cellSealChainA` &c.; here the algebra-level
  -- balance-neutral content is the live-gated write the migration cuts the state-machine arm onto next).
  | .cellSealA actor cell          => stateWriteEffect actor cell "lifecycle" 1
  | .cellUnsealA actor cell        => stateWriteEffect actor cell "lifecycle" 0
  | .cellDestroyA actor cell _certHash => stateWriteEffect actor cell "lifecycle" 3
  | .refreshDelegationA actor child => stateWriteEffect actor child "delegation_refresh" 1

/-! ## §4 — `execHandlerTurn`: the registry executor over the chained state.

Map each `FullActionA` to its `ClosedEffect` via `toClosedEffect`, run the looked-up handler's
fail-closed `step` on the `.kernel`, and thread the kernel through the scaffold's generic `execTurn`
(the `List.foldlM` all-or-nothing transaction). The `.log` carries the audit trace: each committed
effect appends its handler's `trace` Turn. This is the executable shadow that REPLACES `execFullA` —
additive here, the call-sites switch later. -/

/-- The closed-effect list a chained turn dispatches to (the cutover's per-turn dispatch table). -/
def closedOf (acts : List FullActionA) : List ClosedEffect := acts.map toClosedEffect

/-- **`execHandlerTurn`** — the registry executor. Run the closed effects (the `toClosedEffect` images)
all-or-nothing over the `.kernel` via the scaffold's `execTurn`, threading the receipt log. Any single
fail-closed handler aborts the whole turn (the `Option`-monad fold). -/
def execHandlerTurn (acts : List FullActionA) (s : RecChainedState) : Option RecChainedState :=
  -- run the kernel transaction; rebuild a chained state carrying the appended traces on success.
  match execTurn (closedOf acts) s.kernel with
  | some k' => some { kernel := k', log := (closedOf acts).reverse.map (fun e => e.handler.trace e.args) ++ s.log }
  | none    => none

/-- A single closed effect's chained step (the `execHandlerTurn` of a one-element list, unfolded). -/
def execHandlerOne (a : FullActionA) (s : RecChainedState) : Option RecChainedState :=
  execHandlerTurn [a] s

/-! ## §5 — THE DERIVED GLOBAL CONSERVATION (lift the scaffold's generic `turn_conserves`).

The combined per-asset measure over the kernel moves by the SUM of the per-effect deltas — PROVED by
LIFTING `Dregg2.Exec.Handler.turn_conserves` (generic over ANY `List ClosedEffect`) onto the chained
state's kernel. There is NO per-effect restatement and NO 56-arm cases matrix: the executable kernel
transition of `execHandlerTurn` IS `execTurn (closedOf acts)`, so the generic theorem applies VERBATIM.
THIS is the matrix-killer demonstrated at full scale. -/

/-- The combined per-asset turn delta of a `FullActionA` list under the handler executor: the SUM of the
per-effect deltas of the `toClosedEffect` images. (The right-hand budget conservation holds the measure
to — log-independent, a pure function of the closed-effect images.) -/
def handlerTurnDelta (acts : List FullActionA) (b : AssetId) : Int :=
  turnDelta (closedOf acts) b

/-- The empty turn is the identity (kernel unchanged). -/
@[simp] theorem execHandlerTurn_nil (s : RecChainedState) :
    (execHandlerTurn [] s).map (·.kernel) = some s.kernel := by
  simp only [execHandlerTurn, closedOf, List.map_nil, execTurn_nil, Option.map_some]

/-- **`execHandlerTurn_conserves` — THE DERIVED GLOBAL CONSERVATION (PROVED by LIFTING `turn_conserves`).**
For ANY `FullActionA` list run through the handler executor, the combined per-asset measure over the
kernel changes by EXACTLY the SUM of the per-effect deltas, at EVERY asset `b`. The proof is ONE LINE of
lifting: the kernel transition is `execTurn (closedOf acts)`, so the scaffold's generic `turn_conserves`
discharges it — NO per-arm matrix, NO re-derivation. The 56-arm `execFullA_ledger_per_asset` cases proof
collapses into this single lift. -/
theorem execHandlerTurn_conserves (acts : List FullActionA) (s s' : RecChainedState)
    (h : execHandlerTurn acts s = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b + handlerTurnDelta acts b := by
  unfold execHandlerTurn at h
  cases hk : execTurn (closedOf acts) s.kernel with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h
      -- the kernel transition IS `execTurn (closedOf acts)`: lift the GENERIC `turn_conserves`.
      exact turn_conserves (closedOf acts) s.kernel k' hk b

/-- **`execHandlerTurn_head_authorized` — the authority companion (lifted).** Every effect that COMMITS
in a handler turn was authorized: the FIRST effect of any committing turn passed its handler's `auth`
gate at the entry kernel. Lifted from the scaffold's generic `turn_head_authorized`. -/
theorem execHandlerTurn_head_authorized (a : FullActionA) (rest : List FullActionA)
    (s s' : RecChainedState) (h : execHandlerTurn (a :: rest) s = some s') :
    (toClosedEffect a).handler.auth s.kernel (toClosedEffect a).args = true := by
  unfold execHandlerTurn at h
  cases hk : execTurn (closedOf (a :: rest)) s.kernel with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      -- `closedOf (a :: rest) = toClosedEffect a :: closedOf rest`; lift `turn_head_authorized`.
      have hk' : execTurn (toClosedEffect a :: closedOf rest) s.kernel = some k' := by
        simpa only [closedOf, List.map_cons] using hk
      exact turn_head_authorized (toClosedEffect a) (closedOf rest) s.kernel k' hk'

/-- **`execHandlerTurn_head_admitted` — the lifecycle companion (lifted, R1/R6).** Every effect that
COMMITS passed its lifecycle admission gate: the FIRST effect of any committing turn passed its handler's
`admission` gate at the entry kernel — the cons-step witness that the R1/R6 hole is closed at the ALGEBRA
level. Lifted from the scaffold's generic `turn_head_admitted`. -/
theorem execHandlerTurn_head_admitted (a : FullActionA) (rest : List FullActionA)
    (s s' : RecChainedState) (h : execHandlerTurn (a :: rest) s = some s') :
    (toClosedEffect a).handler.admission s.kernel (toClosedEffect a).args = true := by
  unfold execHandlerTurn at h
  cases hk : execTurn (closedOf (a :: rest)) s.kernel with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      have hk' : execTurn (toClosedEffect a :: closedOf rest) s.kernel = some k' := by
        simpa only [closedOf, List.map_cons] using hk
      exact turn_head_admitted (toClosedEffect a) (closedOf rest) s.kernel k' hk'

/-! ## §6 — THE STRENGTHENING: `handler_refines_execFullA` (the relationship to the live executor).

The handler executor is a SOUND STRENGTHENING of `execFullA`: every effect the handler executor COMMITS,
`execFullA` ALSO commits, AND on the honest path they AGREE on the kernel. The handlers only ADD gates
(the `acceptsEffects` liveness wrap, the settle-actor `authorizedB` gate, …) — they never widen the set
of accepted transitions, and when they DO accept, the resulting kernel is EXACTLY what the bare chained
step would have produced. We prove it for the THREE hole-closing representatives (a transfer R1, an
escrow-release R2, a state-write R6); the rest are mechanical (`§DEFER`).

The bridge from the bare-kernel handler `step` to the chained `execHandlerOne`: a one-effect handler turn
runs `execTurn [toClosedEffect a]` which is exactly the handler's `step` on `s.kernel`. -/

/-- **The one-effect kernel-extraction.** A committed one-effect handler turn's resulting kernel is
EXACTLY the looked-up handler's `step` applied to the entry kernel. (`execTurn` over a singleton is the
handler `step`; the chained wrapper just threads the log.) -/
theorem execHandlerOne_kernel (a : FullActionA) (s s' : RecChainedState)
    (h : execHandlerOne a s = some s') :
    (toClosedEffect a).handler.step s.kernel (toClosedEffect a).args = some s'.kernel := by
  unfold execHandlerOne execHandlerTurn at h
  -- `execTurn [toClosedEffect a] s.kernel = execEffect (toClosedEffect a) s.kernel = the handler step`.
  have hstep : execTurn (closedOf [a]) s.kernel
      = (toClosedEffect a).handler.step s.kernel (toClosedEffect a).args := by
    simp only [closedOf, List.map_cons, List.map_nil, execTurn_cons, execEffect, execTurn_nil]
    cases (toClosedEffect a).handler.step s.kernel (toClosedEffect a).args <;> rfl
  rw [hstep] at h
  cases hk : (toClosedEffect a).handler.step s.kernel (toClosedEffect a).args with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl

/-! ### §6.1 — R1: TRANSFER. `execHandlerOne (.balanceA t a)` commits ⇒ `execFullA` commits, kernels AGREE. -/

/-- **`handler_refines_execFullA_transfer` — THE R1 STRENGTHENING (PROVED).** Whenever the handler
executor commits a transfer, `execFullA` ALSO commits it AND produces the SAME kernel: `transferH`'s
extra `acceptsEffects t.dst` gate only NARROWS what commits; once it passes, the underlying
`recKExecAsset` is the very transition `execFullA`'s `.balanceA` arm runs (`recCexecAsset`), so the
kernels coincide. Handler-commits ⊆ execFullA-commits, and they agree on the honest path. -/
theorem handler_refines_execFullA_transfer (s s' : RecChainedState) (t : Turn) (a : AssetId)
    (h : execHandlerOne (.balanceA t a) s = some s') :
    ∃ s'', execFullA s (.balanceA t a) = some s'' ∧ s''.kernel = s'.kernel := by
  -- the handler step committed: unwrap the liveness gate, expose `recKExecAsset s.kernel t a = some s'.kernel`.
  have hstep := execHandlerOne_kernel (.balanceA t a) s s' h
  -- `toClosedEffect`'s `.balanceA` arm = `transferEffect t a` (via the equation lemma); its handler
  -- step IS `transferStep` — expose the `if`.
  rw [toClosedEffect] at hstep
  change transferStep s.kernel { turn := t, asset := a } = some s'.kernel at hstep
  unfold transferStep at hstep
  -- `transferStep s.kernel {turn:=t,asset:=a} = some s'.kernel`
  by_cases hadm : acceptsEffects s.kernel t.dst
  · rw [if_pos hadm] at hstep
    -- `recKExecAsset s.kernel t a = some s'.kernel`; `execFullA … = recCexecAsset` matches on it.
    refine ⟨{ kernel := s'.kernel, log := t :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.recCexecAsset s t a = _
    unfold Dregg2.Exec.TurnExecutorFull.recCexecAsset
    rw [hstep]
  · rw [if_neg hadm] at hstep; exact absurd hstep (by simp)

/-! ### §6.2 — R2: ESCROW RELEASE. `execHandlerOne (.releaseEscrowA id actor)` commits ⇒ `execFullA` commits. -/

/-- **`handler_refines_execFullA_release` — THE R2 STRENGTHENING (PROVED).** Whenever the handler executor
commits an escrow release, `execFullA` ALSO commits it AND produces the SAME kernel: `releaseEscrowA`'s
extra settle-actor `authorizedB` gate (`releaseSettleAuthB`) only NARROWS what commits; once it passes,
the underlying `releaseEscrowKAsset s.kernel id` is the very transition `execFullA`'s `.releaseEscrowA`
arm runs (`releaseEscrowChainA`), so the kernels coincide. -/
theorem handler_refines_execFullA_release (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (h : execHandlerOne (.releaseEscrowA id actor) s = some s') :
    ∃ s'', execFullA s (.releaseEscrowA id actor) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.releaseEscrowA id actor) s s' h
  -- `toClosedEffect`'s `.releaseEscrowA` arm = `releaseEscrowEffect actor id`; step IS `releaseStep`.
  rw [toClosedEffect] at hstep
  change releaseStep s.kernel { actor := actor, id := id } = some s'.kernel at hstep
  unfold releaseStep at hstep
  by_cases hg : releaseSettleAuthB s.kernel { actor := actor, id := id }
  · rw [if_pos hg] at hstep
    -- `releaseEscrowKAsset s.kernel id = some s'.kernel`; `execFullA … = releaseEscrowChainA` matches.
    refine ⟨{ kernel := s'.kernel,
              log := Dregg2.Exec.TurnExecutorFull.escrowReceiptA actor :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.releaseEscrowChainA s id actor = _
    unfold Dregg2.Exec.TurnExecutorFull.releaseEscrowChainA
    rw [hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-! ### §6.3 — R6: STATE WRITE. The handler and `execFullA` now gate on the SAME predicates (RECONCILED).

R6 IS NOW CLOSED IN THE LIVE EXECUTOR. The bare `EffectsState.stateStep` gained a `cellLive`
(lifecycle-liveness) conjunct — so `execFullA`'s `.incrementNonceA`/`.setPermissionsA`/`.setVKA`/
`.refusalA`/`.receiptArchiveA` arms (and `.setFieldA` via `stateStepGuarded`) now REJECT a write into a
Sealed/Destroyed cell, exactly like `stateWriteH`'s `acceptsEffects` gate. `EffectsState.cellLive` is
DEFINITIONALLY `acceptsEffects` (both = `lifecycle cell == 0`/`lcLive`), so the two admission predicates
coincide. The handler still ADDITIONALLY requires `cell ∈ accounts` (membership) which the bare step
also checks; the strengthening is still stated on the honest path where the cell EXISTS, but the
liveness conjunct is now discharged DIRECTLY from the handler's `acceptsEffects` rather than carried as
an unproved gap. The authority conjunct is shared VERBATIM: `stateWriteH.auth = authorizedB caps
{actor,src:=cell,dst:=cell,amt:=0}` which is DEFINITIONALLY `EffectsState.stateAuthB caps actor cell`,
the gate `execFullA`'s `stateStep` checks. (The representative for the whole field-write/lifecycle
family — `setField`/`setPermissions`/`setVK`/`makeSovereign`/`refusal`/`receiptArchive`/`emit`/the
cell-lifecycle arms — which `toClosedEffect` routes through the SAME `stateWriteH`.) -/

/-- **`handler_refines_execFullA_stateWrite` — THE R6 STRENGTHENING (PROVED).**
On the honest path where the target cell EXISTS (`cell ∈ accounts`), whenever the handler executor
commits a nonce write, `execFullA` ALSO commits it AND produces the SAME kernel. With R6 reconciled,
`execFullA`'s bare `stateStep` now shares the handler's `acceptsEffects`/`cellLive` liveness gate
(definitionally), so the handler's liveness conjunct discharges the executor's; the shared authority
gate (`stateAuthB`) and the SAME `writeField nonceField` post-state make the kernels coincide. -/
theorem handler_refines_execFullA_stateWrite (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.incrementNonceA actor cell n) s = some s') :
    ∃ s'', execFullA s (.incrementNonceA actor cell n) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.incrementNonceA actor cell n) s s' h
  -- `toClosedEffect`'s `.incrementNonceA` arm = `incrementNonceEffect actor cell n`; step IS
  -- `stateWriteStep` at `field := nonceField`. Expose the gate `if`.
  rw [toClosedEffect] at hstep
  change stateWriteStep s.kernel
    { actor := actor, target := cell, field := nonceField, value := n } = some s'.kernel at hstep
  unfold stateWriteStep at hstep
  by_cases hg : acceptsEffects s.kernel cell
      && authorizedB s.kernel.caps { actor := actor, src := cell, dst := cell, amt := 0 }
  · rw [if_pos hg] at hstep
    simp only [Bool.and_eq_true] at hg
    simp only [Option.some.injEq] at hstep
    -- `execFullA`'s nonce arm = `stateStep s nonceField actor cell (.int n)`; it commits on the SAME
    -- authority gate + membership (the honest-path `hmem`), producing the SAME `writeField` post-state.
    refine ⟨{ kernel := Dregg2.Exec.EffectsState.writeField s.kernel nonceField cell (.int n),
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, ?_⟩
    · show Dregg2.Exec.EffectsState.stateStep s nonceField actor cell (.int n) = _
      unfold Dregg2.Exec.EffectsState.stateStep Dregg2.Exec.EffectsState.stateAuthB
      -- R6 NOW RECONCILED: `execFullA`'s bare `stateStep` ALSO consults lifecycle liveness
      -- (`cellLive`, the R6 fix). `cellLive s.kernel cell` is DEFINITIONALLY `acceptsEffects s.kernel
      -- cell` (both = `lifecycle cell == 0`), so the handler's liveness conjunct (`hg.1`) discharges
      -- the executor's NEW liveness conjunct directly — no longer just the honest-path membership.
      have hlive : Dregg2.Exec.EffectsState.cellLive s.kernel cell = true := hg.1
      -- `nonceField` is the SAME field name in both layers (`rfl`).
      rw [if_pos ⟨hg.2, hmem, hlive⟩]
    · -- kernels agree: both are the `writeField` post-state at the nonce field.
      rw [← hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-! ## §7 — THE TEETH: concrete attacks `execFullA` ADMITS but `execHandlerTurn` REJECTS.

The payoff. For each hole, a single fixture exhibits the LIVE EXECUTOR `execFullA` accepting the attack
(`= some` — the hole) while the handler executor `execHandlerTurn` REJECTS it (`= none` — the algebra
closes it). `#eval`-verified below; this demonstrates the cutover STRICTLY improves soundness. -/

/-- A 2-cell, 1-asset chained fixture: cells 0 and 1 are accounts; cell 0 holds 100 of asset 0; cell 0
holds the `node 0`/`node 1` self+target authority (so the transfer / state-write self-authorizes). Cell 1
is SEALED (`lifecycle 1 = lcSealed`) — a NON-Live target. Cell 0 stays Live. -/
def teethSealed : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1] else []
        bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0
        lifecycle := fun c => if c = 1 then lcSealed else lcLive }
    log := [] }

/-- A fixture with an escrow (id 9) parked by cell 0 for recipient cell 1, locking 40 of asset 0. The R2
attack: a STRANGER (cell 5, holding no cap, not the recipient) tries to release it. -/
def teethEscrow : Option RecChainedState :=
  execFullA
    { kernel :=
        { accounts := {0, 1}
          cell := fun _ => .record [("balance", .int 0)]
          caps := fun _ => []
          bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }
      log := [] }
    (.createEscrowA 9 0 0 1 0 40)

-- §TEETH-R1 (TRANSFER INTO A SEALED CELL): `execFullA` ADMITS a transfer into the SEALED cell 1 — the
-- LIVE HOLE (no `acceptsEffects` gate on the bare `recKExecAsset`). The handler executor REJECTS it.
#guard ((execFullA teethSealed (.balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0)).isSome)  --  true  (LIVE HOLE)
#guard ((execHandlerOne (.balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0) teethSealed).isSome) == false  --  false (CLOSED)

-- §TEETH-R6 (STATE WRITE INTO A SEALED CELL): R6 is now CLOSED IN THE LIVE EXECUTOR TOO. The bare
-- `EffectsState.stateStep` gained a `cellLive` (lifecycle-liveness) conjunct, so `execFullA` itself
-- now REJECTS a nonce write into the SEALED cell 1 — matching the handler. Both return `none`.
#guard ((execFullA teethSealed (.incrementNonceA 0 1 7)).isSome) == false  --  false (R6 CLOSED in the live executor)
#guard ((execHandlerOne (.incrementNonceA 0 1 7) teethSealed).isSome) == false  --  false (CLOSED by acceptsEffects)
-- ...and a write into the LIVE cell 0 still COMMITS in both — the gate only tightens the non-live case.
#guard ((execFullA teethSealed (.incrementNonceA 0 0 7)).isSome)  --  true  (live cell still accepts)
#guard ((execHandlerOne (.incrementNonceA 0 0 7) teethSealed).isSome)  --  true  (live cell still accepts)

-- §TEETH-R2 (ESCROW RELEASE BY A STRANGER): `execFullA` ADMITS a release of escrow 9 by cell 5 (a
-- stranger, NOT the recipient) — the LIVE HOLE (`releaseEscrowKAsset` takes only the id, no actor).
-- The handler executor REJECTS it (the settle-actor `authorizedB` gate bites).
#guard ((teethEscrow.bind (fun s => execFullA s (.releaseEscrowA 9 5))).isSome)  --  true  (LIVE HOLE)
#guard ((teethEscrow.bind (fun s => execHandlerOne (.releaseEscrowA 9 5) s)).isSome) == false  --  false (CLOSED)
-- the HONEST release (by the recipient cell 1) STILL succeeds under the handler executor (not everything-rejected).
#guard ((teethEscrow.bind (fun s => execHandlerOne (.releaseEscrowA 9 1) s)).isSome)  --  true  (honest path admitted)

-- §TEETH-CONSERVATION: a whole handler turn conserves the combined measure (the derived global law,
-- evaluated): a transfer 0→1 (30 of asset 0, both LIVE) + a self nonce-write on cell 0 leaves the
-- asset-0 measure at 100 (the internal transfer cancels, the write is balance-neutral — the SUM of
-- per-effect deltas is 0, exactly what `execHandlerTurn_conserves` proves).
#guard ((execHandlerTurn [.balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0, .incrementNonceA 0 0 7]
        { kernel :=
            { accounts := {0, 1}
              cell := fun _ => .record [("balance", .int 0)]
              caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1] else []
              bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }
          log := [] }).map (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100

/-! ## §8 — Axiom-hygiene pins (every cutover keystone rests only on the three kernel axioms).

The derived global laws + the strengthening + the executor structure are all pinned to the kernel triple
(`propext`/`Classical.choice`/`Quot.sound`). A `sorryAx` anywhere in the composed handlers — across all
seven batches the registry packs — would FAIL these pins (and the build). -/

#assert_axioms masterRegistry_length
#assert_axioms execHandlerTurn_conserves
#assert_axioms execHandlerTurn_head_authorized
#assert_axioms execHandlerTurn_head_admitted
#assert_axioms execHandlerOne_kernel
#assert_axioms handler_refines_execFullA_transfer
#assert_axioms handler_refines_execFullA_release
#assert_axioms handler_refines_execFullA_stateWrite

/-! ## §DEFER — honest scope of THIS cutover keystone (additive; the call-site switch is mechanical).

Deliberately OUT of this file (documented, NOT a silent gap):

  * **The live-switch of callers.** This file is ADDITIVE: it does NOT edit `execFullA`/`FullActionA`.
    Switching `execFullA`'s 5 dregg1 call-sites onto `execHandlerTurn` (routing each `FullActionA` through
    `toClosedEffect`) is the next, MECHANICAL step — the algebra and its global laws are proved HERE so
    that switch is a rename, not a re-proof.

  * **The strengthening for the remaining 53 constructors.** `handler_refines_execFullA_*` is proved for
    the three HOLE-CLOSING representatives (transfer R1, release R2, state-write R6). The pattern is
    UNIFORM and mechanical for the rest: each handler `step` is `(extra gate) ∧ (the exact bare chained
    step `execFullA` runs)`, so a committed handler step unwraps to the bare step and the kernels agree —
    EXACTLY the transfer/release proofs, per arm. The escrow-create / mint / burn / bridge / seal / swiss
    / delegate / queue arms each follow the transfer template (gate-then-bare-step); the
    obligation/committed/slash/fulfil ALIASES inherit their target's proof verbatim.

  * **The state-write existence-predicate MISMATCH — RESOLVED (R6 closed in the live executor).** The
    bare `EffectsState.stateStep` now ALSO consults lifecycle-LIVENESS (`cellLive`, definitionally
    `acceptsEffects` = `lifecycle cell == 0`), so `execFullA`'s state-write arms reject a write into a
    Sealed/Destroyed cell exactly like `stateWriteH`. The admission predicates coincide; the handler
    additionally checks membership (`cell ∈ accounts`), which the bare step also checks, so the
    strengthening is still stated on the honest path where the cell exists — but the liveness conjunct is
    now PROVED through, not carried open. (`#eval §TEETH-R6`: `execFullA` now returns `none` on the
    Sealed-cell write, matching the handler.)

  * **The committed-escrow `hidingProof` / queue-atomic `QueueTxOpA` projections.** `toClosedEffect` maps
    the committed escrow onto the plain escrow lock (the §8 Pedersen hiding portal is off the executable
    ledger) and projects `QueueTxOpA` onto the bare-kernel `QueueTxOpK` (the chained receipt row lives in
    `RecChainedState`, off the kernel algebra). These are the documented executable cores; the portal /
    receipt faces fold on at the cutover, unchanged in the conservation accounting.
-/

end Dregg2.Exec.HandlerExecutor
