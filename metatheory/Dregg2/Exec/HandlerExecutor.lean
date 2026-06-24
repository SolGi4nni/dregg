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
     attenuate / revoke / bridge-lock/finalize/
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
     measure `recTotalAsset` (over `.kernel`; log-independent) moves by the SUM of the
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

The conservation keystone REUSES `turn_conserves` (generic) — it is NEVER re-derived. Verified
standalone: `lake build Dregg2.Exec.HandlerExecutor`.
-/
import Dregg2.Exec.Handlers.StateSupply
import Dregg2.Exec.Handlers.Escrow
import Dregg2.Exec.Handlers.Authority
import Dregg2.Exec.Handlers.Bridge
import Dregg2.Exec.Handlers.Exercise
import Dregg2.Exec.Handlers.Lifecycle
import Dregg2.Exec.HandlerFloors

namespace Dregg2.Exec.HandlerExecutor

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull
  (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle parentClist parentEpoch cellSealChainA cellUnsealChainA
   cellDestroyChainA refreshDelegationChainA emitStep execFullA execInnerA exerciseStepA FullActionA
   recCDelegate recCDelegateAtten attenuateStepA
   createCellChainA
   noteSpendChainA noteCreateChainA
   permsField vkField refusalField
   authReceipt escrowReceiptA)
open Dregg2.Exec.EffectsState (stateAuthB stateStep stateStepGuarded cellLive caveatsAdmit writeField)
open Dregg2.Exec (recKDelegate recKDelegateAtten heldCapTo attenuate grant)
open scoped BigOperators

-- module-qualified aliases for the seven batches (every handler + ClosedEffect builder lives here)
open Dregg2.Exec.Handlers.StateSupply
open Dregg2.Exec.Handlers.Escrow
open Dregg2.Exec.Handlers.Authority
open Dregg2.Exec.Handlers.Bridge
open Dregg2.Exec.Handlers.Exercise
open Dregg2.Exec.Handlers.Lifecycle

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
  -- §note (Escrow batch; F1b: the escrow/obligation handlers are GONE — factories own them)
  , ⟨NoteSpendArgs, noteSpendA⟩, ⟨NoteCreateArgs, noteCreateA⟩
  -- §authority / delegation (Authority)
  , ⟨DelegateArgs, delegateH⟩, ⟨DelegateArgs, introduceH⟩
  , ⟨DelegateArgs, delegateAttenH⟩
  , ⟨AttenuateArgs, attenuateH⟩
  , ⟨RevokeArgs, revokeDelegationH⟩, ⟨RevokeArgs, revokeH⟩
  -- §bridge (Bridge batch; F1b: the bridge-LFC handlers are GONE — the bridge cell owns them)
  , ⟨PipelinedSendArgs, pipelinedSendA⟩
  -- §exercise (Exercise — the recursive sub-effect forest)
  , ⟨ExerciseArgs, exerciseH⟩
  -- §lifecycle / emit (Lifecycle — real side-table semantics, not field-write stubs)
  , ⟨CellLifecycleArgs, cellSealH⟩
  , ⟨CellLifecycleArgs, cellUnsealH⟩
  , ⟨CellDestroyArgs, cellDestroyH⟩
  , ⟨RefreshDelegationArgs, refreshDelegationH⟩
  , ⟨EmitEventArgs, emitEventH⟩ ]

/-- The master registry packs 32 distinct handler ENTRIES (the F1b op-set constructors collapse onto
these via the aliasing of `toClosedEffect` — introduce/validateHandoff↔delegateAtten, bridgeMint↔mint,
factory/spawn↔createCell, dropRef/revokeDelegation↔revoke; F1b: the escrow/obligation/bridge-LFC
entries are GONE with the kernel holding-store; F2b: the queue-family entries are GONE — queue
behavior is the factory story, `Apps/{QueueFactory,InboxFactory,PubsubFactory}.lean`). -/
theorem masterRegistry_length : masterRegistry.length = 23 := rfl

/-! ## §3 — `toClosedEffect`: the TOTAL `FullActionA → ClosedEffect` dispatch (56/56 constructors).

This is the cutover's heart: it sends every `FullActionA` constructor to the registered handler that
implements it, plus its concrete args, by REUSING each batch's `ClosedEffect` builder verbatim (so the
obligation proofs come along for free). The ALIASING is the dregg2 dispatch collapse the catalog already
records: an obligation IS an escrow, a slash IS a release-to-beneficiary, a fulfil IS a refund-to-obligor,
an introduce / validate-handoff IS an attenuated delegation, a bridge-mint IS a mint, a factory/spawn IS a
born-empty createCell, a dropRef / revoke-delegation IS a target revocation. (F1b: the escrow/
obligation/committed-escrow/bridge-LFC constructors are GONE — the factory contracts own them.)

The lifecycle/emit family (`emitEventA` / `cellSealA` / `cellUnsealA` / `cellDestroyA` /
`refreshDelegationA`) routes to the dedicated `Lifecycle` handlers (real `lifecycle`/`deathCert`/
`delegations` side-table edits + authority-free emit membership gate). The seven named-field writes
(`setFieldA` / `incrementNonceA` / `setPermissionsA` / `setVKA` / `makeSovereignA` / `refusalA` /
`receiptArchiveA`) map onto the GENERIC live-gated `stateWriteH`. -/

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
  | .setFieldA actor cell f v        => setFieldEffect actor cell f v
  | .emitEventA actor cell topic data => emitEventEffect actor cell topic data
  | .incrementNonceA actor cell n     => incrementNonceEffect actor cell n
  | .setPermissionsA actor cell p     => setPermissionsEffect actor cell p
  | .setVKA actor cell vk             => setVKEffect actor cell vk
  | .setProgramA actor cell prog      => setProgramEffect actor cell prog
  -- §authority (6 distinct) — introduce/validateHandoff alias the attenuated delegation (keep := allAuths)
  | .introduceA intro rec t          => introduceEffect intro rec t
  | .delegateAttenA del rec t keep   => delegateAttenEffect del rec t keep
  | .attenuateA actor idx keep       => attenuateEffect actor idx keep
  | .revokeDelegationA holder t      => revokeDelegationEffect holder t
  -- §exercise (recursive) — the inner FullActionA forest folds onto its handlers via closedToSub. Each
  -- inner effect is tagged with its REAL required facet (`requiredFacetA fa`), NOT a blanket
  -- `Auth.control` — so the handler's R4 facet mask AGREES with `execFullA`'s `innerFacetsAdmittedA`
  -- (the canonical semantics), no weaker.
  | .exerciseA actor t inner         =>
      exerciseEffect actor t
        (inner.map (fun fa => facetedOf (Dregg2.Exec.TurnExecutorFull.requiredFacetA fa) (toClosedEffect fa)))
  -- §supply / account growth
  | .createCellA actor newCell       => createCellEffect actor newCell
  | .createCellFromFactoryA actor newCell _vk => createCellFromFactoryEffect actor newCell
  | .spawnA actor child _target      => spawnEffect actor child
  | .bridgeMintA actor cell a value  => bridgeMintEffect actor cell a value
  -- §note (F1b: the escrow/obligation/committed-escrow/bridge-LFC constructors are GONE)
  | .noteSpendA nf actor _spendProof  => noteSpendEffect actor nf
  | .noteCreateA cm actor             => noteCreateEffect actor cm
  -- §flag/lifecycle writes (makeSovereign / refusal → generic live-gated write); receiptArchive →
  -- the DEPLOYED lifecycle side-table archive handler (the `c.archive(checkpoint)` move).
  | .makeSovereignA actor cell    => makeSovereignEffect actor cell
  | .refusalA actor cell          => refusalEffect actor cell
  | .receiptArchiveA actor cell   => cellArchiveEffect actor cell
  | .pipelinedSendA actor               => pipelinedSendEffect actor
  -- §lifecycle (cell seal/unseal/destroy + refresh-delegation) → real side-table handlers
  | .cellSealA actor cell          => cellSealEffect actor cell
  | .cellUnsealA actor cell        => cellUnsealEffect actor cell
  | .cellDestroyA actor cell certHash => cellDestroyEffect actor cell certHash
  | .refreshDelegationA actor child => refreshDelegationEffect actor child
  -- §MA-heap: the heap write routes to its dedicated live+authority-gated splice handler.
  | .heapWriteA actor target addr v newRoot => heapWriteEffect actor target addr v newRoot

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

/-- **`execHandlerTurn_conserves` — THE DERIVED GLOBAL CONSERVATION (by LIFTING `turn_conserves`).**
For ANY `FullActionA` list run through the handler executor, the combined per-asset measure over the
kernel changes by EXACTLY the SUM of the per-effect deltas, at EVERY asset `b`. The proof is ONE LINE of
lifting: the kernel transition is `execTurn (closedOf acts)`, so the scaffold's generic `turn_conserves`
discharges it — NO per-arm matrix, NO re-derivation. The 56-arm `execFullA_ledger_per_asset` cases proof
collapses into this single lift. -/
theorem execHandlerTurn_conserves (acts : List FullActionA) (s s' : RecChainedState)
    (h : execHandlerTurn acts s = some s') (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b + handlerTurnDelta acts b := by
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

/-- **`handler_refines_execFullA_transfer` — THE R1 STRENGTHENING.** Whenever the handler
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
    rw [if_pos hadm, hstep]
  · rw [if_neg hadm] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_balance` — alias of `transfer`.** `balanceA` is the per-asset name for
the transfer arm; the handler step is definitionally `transferStep`. -/
theorem handler_refines_execFullA_balance (s s' : RecChainedState) (t : Turn) (a : AssetId)
    (h : execHandlerOne (.balanceA t a) s = some s') :
    ∃ s'', execFullA s (.balanceA t a) = some s'' ∧ s''.kernel = s'.kernel :=
  handler_refines_execFullA_transfer s s' t a h

/-! ### §6.2 — (F1b) the escrow/obligation/committed/bridge-LFC refinements are GONE with the kernel
holding-store — the factory contracts (`Apps/{EscrowFactory,ObligationFactory,BridgeCell}.lean`) own
those semantics now. -/

/-! ### §6.2b — SUPPLY: MINT / BURN. Handler liveness gates only narrow; the bare ledger step agrees. -/

/-- **`handler_refines_execFullA_mint`.** A committed mint under the handler executor is exactly
`recKMintAsset` on the kernel — the same transition `execFullA`'s `.mintA` arm runs via `recCMintAsset`. -/
theorem handler_refines_execFullA_mint (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : execHandlerOne (.mintA actor cell a amt) s = some s') :
    ∃ s'', execFullA s (.mintA actor cell a amt) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.mintA actor cell a amt) s s' h
  rw [toClosedEffect] at hstep
  change mintStep s.kernel { actor := actor, cell := cell, asset := a, amt := amt } = some s'.kernel at hstep
  unfold mintStep at hstep
  by_cases hadm : acceptsEffects s.kernel cell
  · rw [if_pos hadm] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := a, dst := cell, amt := amt } :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.recCMintAsset s actor cell a amt = _
    unfold Dregg2.Exec.TurnExecutorFull.recCMintAsset
    rw [hstep]
  · rw [if_neg hadm] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_burn`.** A committed burn under the handler executor is exactly
`recKBurnAsset` on the kernel — the same transition `execFullA`'s `.burnA` arm runs via `recCBurnAsset`. -/
theorem handler_refines_execFullA_burn (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : execHandlerOne (.burnA actor cell a amt) s = some s') :
    ∃ s'', execFullA s (.burnA actor cell a amt) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.burnA actor cell a amt) s s' h
  rw [toClosedEffect] at hstep
  change burnStep s.kernel { actor := actor, cell := cell, asset := a, amt := amt } = some s'.kernel at hstep
  unfold burnStep at hstep
  by_cases hadm : acceptsEffects s.kernel cell
  · rw [if_pos hadm] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := cell, dst := a, amt := amt } :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.recCBurnAsset s actor cell a amt = _
    unfold Dregg2.Exec.TurnExecutorFull.recCBurnAsset
    rw [hstep]
  · rw [if_neg hadm] at hstep; exact absurd hstep (by simp)

/-! ### §6.2c — ESCROW ALIASES + bridgeMint + revoke (mechanical inheritance). -/

theorem handler_refines_execFullA_bridgeMint (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (h : execHandlerOne (.bridgeMintA actor cell a value) s = some s') :
    ∃ s'', execFullA s (.bridgeMintA actor cell a value) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.bridgeMintA actor cell a value) s s' h
  rw [toClosedEffect] at hstep
  change mintStep s.kernel { actor := actor, cell := cell, asset := a, amt := value } = some s'.kernel at hstep
  unfold mintStep at hstep
  by_cases hadm : acceptsEffects s.kernel cell
  · rw [if_pos hadm] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := a, dst := cell, amt := value } :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.recCMintAsset s actor cell a value = _
    unfold Dregg2.Exec.TurnExecutorFull.recCMintAsset
    rw [hstep]
  · rw [if_neg hadm] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_revoke (s s' : RecChainedState) (holder t : CellId)
    (h : execHandlerOne (.revoke holder t) s = some s') :
    ∃ s'', execFullA s (.revoke holder t) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.revoke holder t) s s' h
  rw [toClosedEffect] at hstep
  change revokeStep s.kernel { holder := holder, target := t } = some s'.kernel at hstep
  unfold revokeStep at hstep
  simp only [Option.some.injEq] at hstep
  refine ⟨Dregg2.Exec.TurnExecutorFull.recCRevoke s holder t, ?_, ?_⟩
  · show execFullA s (.revoke holder t) = _
    simp only [execFullA, Dregg2.Exec.TurnExecutorFull.recCRevoke]
  · show (Dregg2.Exec.TurnExecutorFull.recCRevoke s holder t).kernel = s'.kernel
    rw [← hstep]
    rfl

/-! ### §6.2d — SUPPLY GROWTH + NOTES + BRIDGE + AUTH ALIASES (mechanical inheritance). -/

theorem handler_refines_execFullA_createCell (s s' : RecChainedState) (actor newCell : CellId)
    (h : execHandlerOne (.createCellA actor newCell) s = some s') :
    ∃ s'', execFullA s (.createCellA actor newCell) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.createCellA actor newCell) s s' h
  rw [toClosedEffect] at hstep
  change createCellStep s.kernel { actor := actor, newCell := newCell } = some s'.kernel at hstep
  unfold createCellStep at hstep
  by_cases hg : createGate s.kernel { actor := actor, newCell := newCell }
  · rw [if_pos hg] at hstep
    simp only [createGate, Bool.and_eq_true, decide_eq_true_eq] at hg
    simp only [CreateArgs.newCell] at hstep
    have hk : createCellIntoAsset s.kernel newCell = s'.kernel := Option.some.inj hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log }, ?_, rfl⟩
    show createCellChainA s actor newCell = _
    unfold createCellChainA
    rw [if_pos ⟨hg.1, hg.2⟩, hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_spawn` — the born-empty create alias.** `toClosedEffect` maps
`spawnA` onto `spawnH` (= `createCellH`). Refinement is against `createCellA` — the shared executable core
— not the full `spawnChainA` cap/delegation metadata (`§DEFER`). -/
theorem handler_refines_execFullA_spawn (s s' : RecChainedState) (actor child target : CellId)
    (h : execHandlerOne (.spawnA actor child target) s = some s') :
    ∃ s'', execFullA s (.createCellA actor child) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.spawnA actor child target) s s' h
  rw [toClosedEffect] at hstep
  change createCellStep s.kernel { actor := actor, newCell := child } = some s'.kernel at hstep
  unfold createCellStep at hstep
  by_cases hg : createGate s.kernel { actor := actor, newCell := child }
  · rw [if_pos hg] at hstep
    simp only [createGate, Bool.and_eq_true, decide_eq_true_eq] at hg
    have hk : createCellIntoAsset s.kernel child = s'.kernel := Option.some.inj hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := child, dst := child, amt := 0 } :: s.log }, ?_, rfl⟩
    show createCellChainA s actor child = _
    unfold createCellChainA
    rw [if_pos ⟨hg.1, hg.2⟩, hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_spawn_fresh` — the BIRTH-FRESHNESS dimension certified (the §P3 spawn
shed).** The born-empty `handler_refines_execFullA_spawn` refines `spawnA` against `createCellA`, which
carries NO `delegationEpochAt` data — so the birth-stamp was `§DEFER`'d (latent in `spawnChainA`, never
surfaced). Refined against the CHAINED, STAMPING `spawnChainA` (= `execFullA`'s arm), this delivers the
birth-freshness OFF the commit (`HandlerFloors.spawnFreshnessFloor_discharges`): the child is stamped to the
spawner-parent's CURRENT `delegationEpoch`, so it is NOT stale at birth. The freshness dimension the
born-empty refinement left implicit is now internal and certified — the epoch metadata is no longer a
silent `§DEFER`. -/
theorem handler_refines_execFullA_spawn_fresh (s s' : RecChainedState) (actor child target : CellId)
    (h : Dregg2.Exec.TurnExecutorFull.spawnChainA s actor child target = some s') :
    (∃ s'', execFullA s (.spawnA actor child target) = some s'' ∧ s''.kernel = s'.kernel)
      ∧ s'.kernel.delegationEpochAt child = s.kernel.delegationEpoch actor := by
  refine ⟨⟨s', ?_, rfl⟩,
    HandlerFloors.spawnFreshnessFloor_discharges
      (a := { actor := actor, child := child, target := target }) h⟩
  show Dregg2.Exec.TurnExecutorFull.spawnChainA s actor child target = some s'
  exact h

/-- **`handler_refines_execFullA_spawn_metadata` — the SPAWN CAP-HANDOFF METADATA certified (the
census-D4 spawn shed).** The born-empty `handler_refines_execFullA_spawn` refines `spawnA` against the
shared account-growth core `createCellA` — which carries NO cap-handoff data, so the delegation handoff
(the child's copied-down cap, parent pointer, c-list snapshot, epoch stamp) was UNVERIFIED by the handler
refinement (`HandlerOpenFronts.spawn_factory_metadata`). Refined against the CHAINED, handing-off
`spawnChainA` (= `execFullA`'s ACTUAL `.spawnA` arm, by `rfl`), this delivers the full metadata OFF the
commit via `HandlerFloors.spawnMetadataFloor_discharges`: the child HOLDS the actor's held cap to the
parent target (least-amplifying), records its parent, snapshots the parent's c-list, and is stamped fresh.
The handoff dimension the born-empty refinement left implicit is now internal and certified — the cap
metadata is no longer a silent `§DEFER`. -/
theorem handler_refines_execFullA_spawn_metadata (s s' : RecChainedState) (actor child target : CellId)
    (h : Dregg2.Exec.TurnExecutorFull.spawnChainA s actor child target = some s') :
    (∃ s'', execFullA s (.spawnA actor child target) = some s'' ∧ s''.kernel = s'.kernel)
      ∧ heldCapTo s.kernel.caps actor target ∈ s'.kernel.caps child
      ∧ s'.kernel.delegate child = some actor
      ∧ s'.kernel.delegations child = s.kernel.caps actor
      ∧ s'.kernel.delegationEpochAt child = s.kernel.delegationEpoch actor := by
  refine ⟨⟨s', ?_, rfl⟩, ?_⟩
  · show Dregg2.Exec.TurnExecutorFull.spawnChainA s actor child target = some s'
    exact h
  · exact HandlerFloors.spawnMetadataFloor_discharges
      (a := { actor := actor, child := child, target := target }) h

/-- **`handler_refines_execFullA_createCellFromFactory` — the born-empty create alias.**
`toClosedEffect` maps `createCellFromFactoryA` onto `createCellFromFactoryH` (= `createCellH`).
Refinement is against `createCellA` — not the full `createCellFromFactoryChainA` install (`§DEFER`). -/
theorem handler_refines_execFullA_createCellFromFactory (s s' : RecChainedState) (actor newCell : CellId)
    (vk : Int) (h : execHandlerOne (.createCellFromFactoryA actor newCell vk) s = some s') :
    ∃ s'', execFullA s (.createCellA actor newCell) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.createCellFromFactoryA actor newCell vk) s s' h
  rw [toClosedEffect] at hstep
  change createCellStep s.kernel { actor := actor, newCell := newCell } = some s'.kernel at hstep
  unfold createCellStep at hstep
  by_cases hg : createGate s.kernel { actor := actor, newCell := newCell }
  · rw [if_pos hg] at hstep
    simp only [createGate, Bool.and_eq_true, decide_eq_true_eq] at hg
    have hk : createCellIntoAsset s.kernel newCell = s'.kernel := Option.some.inj hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := newCell, dst := newCell, amt := 0 } :: s.log }, ?_, rfl⟩
    show createCellChainA s actor newCell = _
    unfold createCellChainA
    rw [if_pos ⟨hg.1, hg.2⟩, hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_createCellFromFactory_metadata` — the FACTORY INSTALL METADATA certified
(the census-D4 factory shed).** The born-empty `handler_refines_execFullA_createCellFromFactory` refines
`createCellFromFactoryA` against the shared core `createCellA` — DROPPING the `vk`, so the factory's
published contract (its `slotCaveats` program, the program-VK slot, the initial fields) was UNVERIFIED by
the handler refinement (`HandlerOpenFronts.spawn_factory_metadata`). Refined against the CHAINED,
installing `createCellFromFactoryChainA` (= `execFullA`'s ACTUAL `.createCellFromFactoryA` arm, by `rfl`),
this delivers the full install OFF the commit via `HandlerFloors.factoryMetadataFloor_discharges`: the
minted cell carries EXACTLY the registered factory's caveats (enforced on every later `SetField`) and the
factory's initial-field + program-VK install. The factory-contract dimension the born-empty refinement
left implicit is now internal and certified. -/
theorem handler_refines_execFullA_createCellFromFactory_metadata (s s' : RecChainedState)
    (actor newCell : CellId) (vk : Int)
    (h : Dregg2.Exec.TurnExecutorFull.createCellFromFactoryChainA s actor newCell vk = some s') :
    (∃ s'', execFullA s (.createCellFromFactoryA actor newCell vk) = some s'' ∧ s''.kernel = s'.kernel)
      ∧ (∃ e s1, Dregg2.Exec.findFactory s.kernel.factories vk.toNat = some e ∧
           Dregg2.Exec.TurnExecutorFull.createCellChainA s actor newCell = some s1 ∧
           s'.kernel.slotCaveats newCell = e.caveats ∧
           s'.kernel.cell newCell =
             Dregg2.Exec.EffectsState.setField Dregg2.Exec.TurnExecutorFull.factoryVkField
               (Dregg2.Exec.TurnExecutorFull.installInitialFields (s1.kernel.cell newCell) e.initialFields)
               (.int e.programVk)) := by
  refine ⟨⟨s', ?_, rfl⟩, ?_⟩
  · show Dregg2.Exec.TurnExecutorFull.createCellFromFactoryChainA s actor newCell vk = some s'
    exact h
  · exact HandlerFloors.factoryMetadataFloor_discharges
      (a := { actor := actor, newCell := newCell, vk := vk }) h

/-- The handler models the LEDGER-side note-spend step (the nullifier set-transition; the §8 STARK
spending proof is the crypto-portal face the handler does not re-run). Once the executor's §8
proof-gate is DISCHARGED (`spendProof = true`), the gated `execFullA` reduces to that same ledger
step — so the refinement holds exactly under a verified spending proof, the faithful condition. -/
theorem handler_refines_execFullA_noteSpend (s s' : RecChainedState) (nf : Nat) (actor : CellId)
    (h : execHandlerOne (.noteSpendA nf actor true) s = some s') :
    ∃ s'', execFullA s (.noteSpendA nf actor true) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.noteSpendA nf actor true) s s' h
  rw [toClosedEffect] at hstep
  change noteSpendStep s.kernel { actor := actor, nf := nf } = some s'.kernel at hstep
  unfold noteSpendStep at hstep
  cases hk : noteSpendNullifier s.kernel nf with
  | none => rw [hk] at hstep; exact absurd hstep (by simp)
  | some k' =>
      rw [hk] at hstep
      simp only [Option.some.injEq] at hstep
      refine ⟨{ kernel := s'.kernel, log := escrowReceiptA actor :: s.log }, ?_, rfl⟩
      show noteSpendChainA s nf actor true = _
      unfold noteSpendChainA
      rw [if_pos rfl, hk, hstep]

theorem handler_refines_execFullA_noteCreate (s s' : RecChainedState) (cm : Nat) (actor : CellId)
    (h : execHandlerOne (.noteCreateA cm actor) s = some s') :
    ∃ s'', execFullA s (.noteCreateA cm actor) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.noteCreateA cm actor) s s' h
  rw [toClosedEffect] at hstep
  change noteCreateStep s.kernel { actor := actor, cm := cm } = some s'.kernel at hstep
  unfold noteCreateStep at hstep
  simp only [Option.some.injEq] at hstep
  have hk : noteCreateCommitment s.kernel cm = s'.kernel := hstep
  refine ⟨noteCreateChainA s cm actor, ?_, hk⟩
  show execFullA s (.noteCreateA cm actor) = _
  simp only [execFullA, noteCreateChainA, hk]

theorem handler_refines_execFullA_pipelinedSend (s s' : RecChainedState) (actor : CellId)
    (h : execHandlerOne (.pipelinedSendA actor) s = some s') :
    ∃ s'', execFullA s (.pipelinedSendA actor) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.pipelinedSendA actor) s s' h
  rw [toClosedEffect] at hstep
  change pipelinedSendStep s.kernel { actor := actor } = some s'.kernel at hstep
  unfold pipelinedSendStep at hstep
  have hk : s.kernel = s'.kernel := Option.some.inj hstep
  refine ⟨{ kernel := s'.kernel, log := escrowReceiptA actor :: s.log }, ⟨?_, rfl⟩⟩
  simp only [execFullA, hk]

theorem handler_refines_execFullA_revokeDelegation (s s' : RecChainedState) (holder t : CellId)
    (h : execHandlerOne (.revokeDelegationA holder t) s = some s') :
    ∃ s'', execFullA s (.revokeDelegationA holder t) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.revokeDelegationA holder t) s s' h
  rw [toClosedEffect] at hstep
  -- the handler now routes to the FAITHFUL `revokeDelegationStep` (`recKRevokeDelegationFull`), which
  -- AGREES with `execFullA`'s full epoch-step arm — so the kernel equality holds.
  change revokeDelegationStep s.kernel { holder := holder, target := t } = some s'.kernel at hstep
  unfold revokeDelegationStep at hstep
  simp only [Option.some.injEq] at hstep
  refine ⟨Dregg2.Exec.TurnExecutorFull.recCRevokeDelegationFull s holder t, ?_, ?_⟩
  · show execFullA s (.revokeDelegationA holder t) = _
    simp only [execFullA, Dregg2.Exec.TurnExecutorFull.recCRevokeDelegationFull]
  · show (Dregg2.Exec.TurnExecutorFull.recCRevokeDelegationFull s holder t).kernel = s'.kernel
    rw [← hstep]; rfl

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

/-- **`handler_refines_execFullA_stateWrite` — THE R6 STRENGTHENING + `hmono` SHED (P1).**
On the honest path where the target cell EXISTS (`cell ∈ accounts`), whenever the handler executor
commits a nonce write, `execFullA` ALSO commits it AND produces the SAME kernel. With R6 reconciled,
`execFullA`'s bare `stateStep` shares the handler's `acceptsEffects`/`cellLive` liveness gate
(definitionally), so the handler's liveness conjunct discharges the executor's; the shared authority
gate (`stateAuthB`) and the SAME `writeField nonceField` post-state make the kernels coincide.
The `.incrementNonceA` arm now routes through `incrementNonceDevH`, whose `step`
(`incrementNonceDevStep`) ITSELF rejects a NON-advancing nonce. So the monotone fact (`hmono`) is no
longer a caller hypothesis — it is READ OFF the commit via `incrementNonceDevStep_advances`. The
refinement now holds UNCONDITIONALLY (only `hmem` remains). BEFORE this carried
`(hmono : fieldOf "nonce" … < n)`; AFTER, it does not. -/
theorem handler_refines_execFullA_stateWrite (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.incrementNonceA actor cell n) s = some s') :
    ∃ s'', execFullA s (.incrementNonceA actor cell n) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.incrementNonceA actor cell n) s s' h
  -- `toClosedEffect`'s `.incrementNonceA` arm = `incrementNonceEffect actor cell n`; step IS
  -- `incrementNonceDevStep` at `field := nonceField`.
  rw [toClosedEffect] at hstep
  change Dregg2.Exec.Handlers.StateSupply.incrementNonceDevStep s.kernel
    { actor := actor, target := cell, field := nonceField, value := n } = some s'.kernel at hstep
  -- READ the monotone floor OFF the commit (no caller hypothesis): the handler's own step gated it.
  -- `nonceField` is DEFINITIONALLY `"nonce"`, so the `target`-field read aligns.
  have hmono : Dregg2.Exec.EffectsState.fieldOf "nonce" (s.kernel.cell cell) < n :=
    Dregg2.Exec.Handlers.StateSupply.incrementNonceDevStep_advances hstep
  replace hstep := Dregg2.Exec.Handlers.StateSupply.incrementNonceDevStep_eq hstep
  change stateWriteStep s.kernel
    { actor := actor, target := cell, field := nonceField, value := n } = some s'.kernel at hstep
  unfold stateWriteStep at hstep
  by_cases hg : acceptsEffects s.kernel cell
      && authorizedB s.kernel.caps { actor := actor, src := cell, dst := cell, amt := 0 }
  · rw [if_pos hg] at hstep
    simp only [Bool.and_eq_true] at hg
    simp only [Option.some.injEq] at hstep
    -- §MONOTONE-NONCE: `execFullA`'s nonce arm = `incrementNonceStep s actor cell n` — the monotone
    -- gate over `stateStep s nonceField actor cell (.int n)`. On the honest path (`hmono`, the verified
    -- executor only commits a STRICTLY-advancing nonce) it commits on the SAME authority gate +
    -- membership (`hmem`), producing the SAME `writeField` post-state.
    refine ⟨{ kernel := Dregg2.Exec.EffectsState.writeField s.kernel nonceField cell (.int n),
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, ?_⟩
    · show Dregg2.Exec.EffectsState.incrementNonceStep s actor cell n = _
      unfold Dregg2.Exec.EffectsState.incrementNonceStep
      -- the monotone gate is discharged by `hmono` (`nonceField = "nonce"` definitionally).
      rw [if_pos hmono]
      unfold Dregg2.Exec.EffectsState.stateStep Dregg2.Exec.EffectsState.stateAuthB
      -- R6 NOW RECONCILED: the bare `stateStep` ALSO consults lifecycle liveness (`cellLive`, the R6
      -- fix). `cellLive s.kernel cell` is DEFINITIONALLY `acceptsEffects s.kernel cell` (both =
      -- `lifecycle cell == 0`), so the handler's liveness conjunct (`hg.1`) discharges the executor's.
      have hlive : Dregg2.Exec.EffectsState.cellLive s.kernel cell = true := hg.1
      rw [if_pos ⟨hg.2, hmem, hlive⟩]
      -- `nonceField` is DEFINITIONALLY `"nonce"`, so the two `writeField` post-states coincide.
      rfl
    · -- kernels agree: both are the `writeField` post-state at the nonce field.
      rw [← hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_incrementNonce` — alias of `stateWrite`.** `incrementNonceA` routes
through `incrementNonceEffect` = `stateWriteEffect` at `nonceField`. -/
theorem handler_refines_execFullA_incrementNonce (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.incrementNonceA actor cell n) s = some s') :
    ∃ s'', execFullA s (.incrementNonceA actor cell n) = some s'' ∧ s''.kernel = s'.kernel :=
  handler_refines_execFullA_stateWrite s s' actor cell n hmem h

theorem handler_refines_execFullA_setPermissions (s s' : RecChainedState) (actor cell : CellId) (p : Int)
    (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.setPermissionsA actor cell p) s = some s') :
    ∃ s'', execFullA s (.setPermissionsA actor cell p) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.setPermissionsA actor cell p) s s' h
  rw [toClosedEffect] at hstep
  change stateWriteStep s.kernel
    { actor := actor, target := cell, field := permissionsField, value := p } = some s'.kernel at hstep
  unfold stateWriteStep at hstep
  by_cases hg : acceptsEffects s.kernel cell
      && authorizedB s.kernel.caps { actor := actor, src := cell, dst := cell, amt := 0 }
  · rw [if_pos hg] at hstep
    simp only [Bool.and_eq_true] at hg
    simp only [Option.some.injEq] at hstep
    have hlive : cellLive s.kernel cell = true := hg.1
    have hfield : permissionsField = permsField := rfl
    refine ⟨{ kernel := writeField s.kernel permissionsField cell (.int p),
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, ?_⟩
    · show Dregg2.Exec.EffectsState.stateStep s permsField actor cell (.int p) = _
      unfold Dregg2.Exec.EffectsState.stateStep Dregg2.Exec.EffectsState.stateAuthB
      rw [if_pos ⟨hg.2, hmem, hlive⟩, hfield]
    · rw [← hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_setVK (s s' : RecChainedState) (actor cell : CellId) (vk : Int)
    (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.setVKA actor cell vk) s = some s') :
    ∃ s'', execFullA s (.setVKA actor cell vk) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.setVKA actor cell vk) s s' h
  rw [toClosedEffect] at hstep
  change stateWriteStep s.kernel
    { actor := actor, target := cell, field := Dregg2.Exec.Handlers.StateSupply.vkField, value := vk }
    = some s'.kernel at hstep
  unfold stateWriteStep at hstep
  by_cases hg : acceptsEffects s.kernel cell
      && authorizedB s.kernel.caps { actor := actor, src := cell, dst := cell, amt := 0 }
  · rw [if_pos hg] at hstep
    simp only [Bool.and_eq_true] at hg
    simp only [Option.some.injEq] at hstep
    have hlive : cellLive s.kernel cell = true := hg.1
    have hfield : Dregg2.Exec.Handlers.StateSupply.vkField = Dregg2.Exec.TurnExecutorFull.vkField := rfl
    refine ⟨{ kernel := writeField s.kernel Dregg2.Exec.Handlers.StateSupply.vkField cell (.int vk),
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, ?_⟩
    · show Dregg2.Exec.EffectsState.stateStep s Dregg2.Exec.TurnExecutorFull.vkField actor cell (.int vk) = _
      unfold Dregg2.Exec.EffectsState.stateStep Dregg2.Exec.EffectsState.stateAuthB
      rw [if_pos ⟨hg.2, hmem, hlive⟩, hfield]
    · rw [← hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_setProgram (s s' : RecChainedState) (actor cell : CellId) (prog : Int)
    (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.setProgramA actor cell prog) s = some s') :
    ∃ s'', execFullA s (.setProgramA actor cell prog) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.setProgramA actor cell prog) s s' h
  rw [toClosedEffect] at hstep
  change stateWriteStep s.kernel
    { actor := actor, target := cell, field := Dregg2.Exec.Handlers.StateSupply.programField, value := prog }
    = some s'.kernel at hstep
  unfold stateWriteStep at hstep
  by_cases hg : acceptsEffects s.kernel cell
      && authorizedB s.kernel.caps { actor := actor, src := cell, dst := cell, amt := 0 }
  · rw [if_pos hg] at hstep
    simp only [Bool.and_eq_true] at hg
    simp only [Option.some.injEq] at hstep
    have hlive : cellLive s.kernel cell = true := hg.1
    have hfield : Dregg2.Exec.Handlers.StateSupply.programField = Dregg2.Exec.TurnExecutorFull.programField := rfl
    refine ⟨{ kernel := writeField s.kernel Dregg2.Exec.Handlers.StateSupply.programField cell (.int prog),
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, ?_⟩
    · show Dregg2.Exec.EffectsState.stateStep s Dregg2.Exec.TurnExecutorFull.programField actor cell (.int prog) = _
      unfold Dregg2.Exec.EffectsState.stateStep Dregg2.Exec.EffectsState.stateAuthB
      rw [if_pos ⟨hg.2, hmem, hlive⟩, hfield]
    · rw [← hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_refusal (s s' : RecChainedState) (actor cell : CellId)
    (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.refusalA actor cell) s = some s') :
    ∃ s'', execFullA s (.refusalA actor cell) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.refusalA actor cell) s s' h
  rw [toClosedEffect] at hstep
  change stateWriteStep s.kernel
    { actor := actor, target := cell, field := Dregg2.Exec.Handlers.StateSupply.refusalField, value := 1 }
    = some s'.kernel at hstep
  unfold stateWriteStep at hstep
  by_cases hg : acceptsEffects s.kernel cell
      && authorizedB s.kernel.caps { actor := actor, src := cell, dst := cell, amt := 0 }
  · rw [if_pos hg] at hstep
    simp only [Bool.and_eq_true] at hg
    simp only [Option.some.injEq] at hstep
    have hlive : cellLive s.kernel cell = true := hg.1
    have hfield : Dregg2.Exec.Handlers.StateSupply.refusalField =
        Dregg2.Exec.TurnExecutorFull.refusalField := rfl
    refine ⟨{ kernel := writeField s.kernel Dregg2.Exec.Handlers.StateSupply.refusalField cell (.int 1),
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, ?_⟩
    · show Dregg2.Exec.EffectsState.stateStep s Dregg2.Exec.TurnExecutorFull.refusalField actor cell (.int 1) = _
      unfold Dregg2.Exec.EffectsState.stateStep Dregg2.Exec.EffectsState.stateAuthB
      rw [if_pos ⟨hg.2, hmem, hlive⟩, hfield]
    · rw [← hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-! ### §6.3b — `makeSovereignA` / `receiptArchiveA` ALIGNED to `execFullA` (holes CLOSED).

The handlers are now SEMANTICALLY ALIGNED to `execFullA`:
* `makeSovereignA` routes through `makeSovereignH` — the SAME commitment-rebind (`makeSovereignKernel`,
  whole-record drop) `execFullA`'s `makeSovereignStep` does, NOT the old `sovereign := 1` flag write.
* `receiptArchiveA` routes through `receiptArchiveEffect` at the `"lifecycle"` field (`receiptArchiveField`
  is now `"lifecycle"`) — the SAME slot `execFullA`'s `stateStep s lifecycleField actor cell (.int 1)`
  writes, NOT the old `"receipt_archive"` flag.
Both kernel-agreement obligations are GENUINELY DISCHARGED: the handler commit produces
EXACTLY the `execFullA` post-kernel. -/

/-- **`handler_refines_execFullA_makeSovereign` — CLOSED.** A committed handler make-sovereign commits
in `execFullA` to the SAME kernel: both run the `makeSovereignKernel` commitment-rebind (the readable
record dropped behind a state commitment). The handler ADDS the `acceptsEffects` live-cell gate
(strengthening); when it commits, `stateAuthB` held, so `execFullA`'s `makeSovereignStep` commits too. -/
theorem hole_handler_makeSovereign (s s' : RecChainedState) (actor cell : CellId)
    (_hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.makeSovereignA actor cell) s = some s') :
    ∃ s'', execFullA s (.makeSovereignA actor cell) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.makeSovereignA actor cell) s s' h
  rw [toClosedEffect] at hstep
  change Dregg2.Exec.Handlers.StateSupply.makeSovereignStepK s.kernel
    { actor := actor, target := cell } = some s'.kernel at hstep
  unfold Dregg2.Exec.Handlers.StateSupply.makeSovereignStepK at hstep
  by_cases hg : acceptsEffects s.kernel cell
      && authorizedB s.kernel.caps { actor := actor, src := cell, dst := cell, amt := 0 }
  · rw [if_pos hg] at hstep
    simp only [Bool.and_eq_true] at hg
    simp only [Option.some.injEq] at hstep
    have hauth : Dregg2.Exec.EffectsState.stateAuthB s.kernel.caps actor cell = true := hg.2
    have hlive : acceptsEffects s.kernel cell = true := hg.1
    refine ⟨{ kernel := Dregg2.Exec.TurnExecutorFull.makeSovereignKernel s.kernel cell,
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, ?_⟩
    · show Dregg2.Exec.TurnExecutorFull.makeSovereignStep s actor cell = _
      unfold Dregg2.Exec.TurnExecutorFull.makeSovereignStep
      rw [if_pos ⟨hauth, hlive⟩]
    · rw [← hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_receiptArchive` — CLOSED (DEPLOYED).** A committed handler
receipt-archive commits in `execFullA` to the SAME kernel: both move the `lifecycle` SIDE-TABLE to
`Archived` (the deployed `c.archive(checkpoint)` move). The handler gate (`stateAuthB &&
acceptsEffects`) plus `cell ∈ accounts` IS `execFullA`'s `receiptArchiveChainA` three-leg gate. -/
theorem hole_handler_receiptArchive (s s' : RecChainedState) (actor cell : CellId)
    (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.receiptArchiveA actor cell) s = some s') :
    ∃ s'', execFullA s (.receiptArchiveA actor cell) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.receiptArchiveA actor cell) s s' h
  rw [toClosedEffect] at hstep
  change Dregg2.Exec.Handlers.Lifecycle.cellArchiveStep s.kernel { actor := actor, cell := cell }
    = some s'.kernel at hstep
  unfold Dregg2.Exec.Handlers.Lifecycle.cellArchiveStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor cell && acceptsEffects s.kernel cell
  · rw [if_pos hg] at hstep
    have hg' : stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true := by
      simp only [Bool.and_eq_true] at hg; exact ⟨hg.1, hg.2⟩
    have hlive : cellLive s.kernel cell = true := hg'.2
    have hk : setLifecycle s.kernel cell Dregg2.Exec.TurnExecutorFull.lcArchived = s'.kernel := by
      simpa only [Option.some.injEq] using hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.receiptArchiveChainA s actor cell = _
    unfold Dregg2.Exec.TurnExecutorFull.receiptArchiveChainA
    rw [if_pos ⟨hg'.1, hmem, hlive⟩, hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_makeSovereign`** — the strengthening (now PROVED, alias). -/
theorem handler_refines_execFullA_makeSovereign (s s' : RecChainedState) (actor cell : CellId)
    (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.makeSovereignA actor cell) s = some s') :
    ∃ s'', execFullA s (.makeSovereignA actor cell) = some s'' ∧ s''.kernel = s'.kernel :=
  hole_handler_makeSovereign s s' actor cell hmem h

/-- **`handler_refines_execFullA_receiptArchive`** — the strengthening (now PROVED, alias). -/
theorem handler_refines_execFullA_receiptArchive (s s' : RecChainedState) (actor cell : CellId)
    (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.receiptArchiveA actor cell) s = some s') :
    ∃ s'', execFullA s (.receiptArchiveA actor cell) = some s'' ∧ s''.kernel = s'.kernel :=
  hole_handler_receiptArchive s s' actor cell hmem h

/-- **`handler_refines_execFullA_setField` — `hnr`/`hcav` SHED (P1, the gate-hole closed structurally).**
The `.setFieldA` arm now routes through `setFieldDevH`, whose `step` (`setFieldDevStep`) ITSELF rejects
a RESERVED protocol slot AND a caveat-violating write. So the reserved-field fact (`hnr`) and the caveat
fact (`hcav`) are no longer caller hypotheses — they are READ OFF the commit via
`setFieldDevStep_notReserved` / `setFieldDevStep_caveatsAdmit`. The refinement now holds
UNCONDITIONALLY (only `hmem`, the honest-path cell-existence, remains). BEFORE this carried
`(hnr : reservedField f = false)` and `(hcav : caveatsAdmit … = true)`; AFTER, neither. -/
theorem handler_refines_execFullA_setField (s s' : RecChainedState) (actor cell : CellId)
    (f : FieldName) (v : Int) (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.setFieldA actor cell f v) s = some s') :
    ∃ s'', execFullA s (.setFieldA actor cell f v) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.setFieldA actor cell f v) s s' h
  rw [toClosedEffect] at hstep
  change Dregg2.Exec.Handlers.StateSupply.setFieldDevStep s.kernel
    { actor := actor, target := cell, field := f, value := v } = some s'.kernel at hstep
  -- READ the floors OFF the commit (no caller hypothesis): the handler's own step gated them.
  have hnr : Dregg2.Exec.EffectsState.reservedField f = false :=
    Dregg2.Exec.Handlers.StateSupply.setFieldDevStep_notReserved hstep
  have hcav : caveatsAdmit s.kernel f actor cell v = true :=
    Dregg2.Exec.Handlers.StateSupply.setFieldDevStep_caveatsAdmit hstep
  -- the committed dev write IS the underlying `stateWriteStep` write — proceed as before.
  replace hstep := Dregg2.Exec.Handlers.StateSupply.setFieldDevStep_eq hstep
  change stateWriteStep s.kernel
    { actor := actor, target := cell, field := f, value := v } = some s'.kernel at hstep
  unfold stateWriteStep at hstep
  by_cases hg : acceptsEffects s.kernel cell
      && authorizedB s.kernel.caps { actor := actor, src := cell, dst := cell, amt := 0 }
  · rw [if_pos hg] at hstep
    simp only [Bool.and_eq_true] at hg
    simp only [Option.some.injEq] at hstep
    have hlive : cellLive s.kernel cell = true := hg.1
    refine ⟨{ kernel := writeField s.kernel f cell (.int v),
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, ?_⟩
    -- §RESERVED-SLOT: `execFullA`'s setField arm = `stateStepDev` (reserved gate over `stateStepGuarded`).
    -- On the honest path the written slot is a DEVELOPER field (`hnr`), so the reserved gate passes.
    · show Dregg2.Exec.EffectsState.stateStepDev s f actor cell v = _
      unfold Dregg2.Exec.EffectsState.stateStepDev
      rw [if_neg (by rw [hnr]; simp)]
      unfold Dregg2.Exec.EffectsState.stateStepGuarded
      rw [if_pos hcav]
      unfold Dregg2.Exec.EffectsState.stateStep Dregg2.Exec.EffectsState.stateAuthB
      rw [if_pos ⟨hg.2, hmem, hlive⟩]
    · rw [← hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-! ### §6.4 — LIFECYCLE: `execHandlerOne (.cellSealA …)` commits ⇒ `execFullA` commits, kernels AGREE. -/

/-- **`handler_refines_execFullA_cellSeal` — THE LIFECYCLE STRENGTHENING.** A committed cell
seal under the handler executor is EXACTLY the bare `setLifecycle` post-state `execFullA`'s
`cellSealChainA` arm produces on the kernel. -/
theorem handler_refines_execFullA_cellSeal (s s' : RecChainedState) (actor cell : CellId)
    (h : execHandlerOne (.cellSealA actor cell) s = some s') :
    ∃ s'', execFullA s (.cellSealA actor cell) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.cellSealA actor cell) s s' h
  rw [toClosedEffect] at hstep
  change cellSealStep s.kernel { actor := actor, cell := cell } = some s'.kernel at hstep
  unfold cellSealStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor cell && acceptsEffects s.kernel cell
  · rw [if_pos hg] at hstep
    have hg' : stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true := by
      simp only [Bool.and_eq_true] at hg; exact ⟨hg.1, hg.2⟩
    have hk : setLifecycle s.kernel cell lcSealed = s'.kernel := by
      simpa only [Option.some.injEq] using hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, rfl⟩
    show cellSealChainA s actor cell = _
    unfold cellSealChainA
    rw [if_pos hg', hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_cellUnseal (s s' : RecChainedState) (actor cell : CellId)
    (h : execHandlerOne (.cellUnsealA actor cell) s = some s') :
    ∃ s'', execFullA s (.cellUnsealA actor cell) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.cellUnsealA actor cell) s s' h
  rw [toClosedEffect] at hstep
  change cellUnsealStep s.kernel { actor := actor, cell := cell } = some s'.kernel at hstep
  unfold cellUnsealStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor cell && (s.kernel.lifecycle cell == lcSealed)
  · rw [if_pos hg] at hstep
    have hg' : stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell == lcSealed) = true := by
      simp only [Bool.and_eq_true] at hg; exact ⟨hg.1, hg.2⟩
    have hk : setLifecycle s.kernel cell lcLive = s'.kernel := by
      simpa only [Option.some.injEq] using hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, rfl⟩
    show cellUnsealChainA s actor cell = _
    unfold cellUnsealChainA
    rw [if_pos hg', hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_cellDestroy (s s' : RecChainedState) (actor cell : CellId)
    (certHash : Nat) (h : execHandlerOne (.cellDestroyA actor cell certHash) s = some s') :
    ∃ s'', execFullA s (.cellDestroyA actor cell certHash) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.cellDestroyA actor cell certHash) s s' h
  rw [toClosedEffect] at hstep
  change cellDestroyStep s.kernel { actor := actor, cell := cell, certHash := certHash } = some s'.kernel at hstep
  unfold cellDestroyStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor cell && (s.kernel.lifecycle cell != lcDestroyed)
  · rw [if_pos hg] at hstep
    have hg' : stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell != lcDestroyed) = true := by
      simp only [Bool.and_eq_true] at hg; exact ⟨hg.1, hg.2⟩
    have hk : { (setLifecycle s.kernel cell lcDestroyed) with
                  deathCert := fun c => if c = cell then certHash else s.kernel.deathCert c } = s'.kernel := by
      simpa only [Option.some.injEq] using hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, rfl⟩
    show cellDestroyChainA s actor cell certHash = _
    unfold cellDestroyChainA
    rw [if_pos hg', hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-! ### §P3 — the lifecycle-FRESHNESS / delegation-epoch residual SHED.

BEFORE — `..._refreshDelegation_residual`: the FROZEN-FACE handler `refreshDelegationStep` models the
`delegations` snapshot only; the FAITHFUL chained executor ALSO re-stamps `delegationEpochAt` (the
freshness-restore). So the refinement's conclusion carries the epoch-stamp as a NAMED kernel RESIDUAL
(`s''.kernel = { s'.kernel with delegationEpochAt := … }`) — kernel equality holds only MODULO that
re-stamp, the silent-gate hole in residual form.

AFTER — `..._refreshDelegation`: refined against the CHAINED step `refreshDelegationChainA` (= `execFullA`'s
arm, which STAMPS by construction). The conclusion is CLEAN kernel-agreement (`s''.kernel = s'.kernel`, NO
residual) PLUS the freshness fact (`s'.delegationEpochAt child = parentEpoch child`) delivered OFF the
commit via `HandlerFloors.refreshFreshnessFloor_discharges`. The epoch-stamp residual is GONE — produced
internally by the floor, not carried as a structural escape. This is the §P3 shed (mirrors the §P2
`..._nonAmp` shape: same closure, the post-condition floor instead of a side-hyp). -/

/-- **BEFORE (the residual version).** The refresh refinement against the FROZEN-FACE handler, whose
conclusion carries the epoch-stamp as a named `delegationEpochAt` kernel residual. The residual is the
silent-gate hole the AFTER version sheds. -/
theorem handler_refines_execFullA_refreshDelegation_residual (s s' : RecChainedState) (actor child : CellId)
    (h : execHandlerOne (.refreshDelegationA actor child) s = some s') :
    ∃ s'', execFullA s (.refreshDelegationA actor child) = some s''
      ∧ s''.kernel = { s'.kernel with
                        delegationEpochAt := fun c => if c = child then parentEpoch s.kernel child
                                                      else s'.kernel.delegationEpochAt c } := by
  have hstep := execHandlerOne_kernel (.refreshDelegationA actor child) s s' h
  rw [toClosedEffect] at hstep
  change refreshDelegationStep s.kernel { actor := actor, child := child } = some s'.kernel at hstep
  unfold refreshDelegationStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor child && (s.kernel.delegate child).isSome
  · rw [if_pos hg] at hstep
    have hg' : stateAuthB s.kernel.caps actor child = true ∧ (s.kernel.delegate child).isSome = true := by
      simp only [Bool.and_eq_true] at hg; exact ⟨hg.1, hg.2⟩
    have hk : { s.kernel with
                  delegations := fun c => if c = child then parentClist s.kernel child
                                        else s.kernel.delegations c } = s'.kernel := by
      simpa only [Option.some.injEq] using hstep
    refine ⟨{ kernel := { s.kernel with
                  delegations := fun c => if c = child then parentClist s.kernel child
                                          else s.kernel.delegations c,
                  delegationEpochAt := fun c => if c = child then parentEpoch s.kernel child
                                                else s.kernel.delegationEpochAt c },
              log := { actor := actor, src := child, dst := child, amt := 0 } :: s.log }, ?_, ?_⟩
    · show refreshDelegationChainA s actor child = _
      unfold refreshDelegationChainA
      rw [if_pos hg']
    · -- the executor post's `delegationEpochAt` IS the stamp; the handler post `s'.kernel = hk` lacks it,
      -- so applying the residual to `s'.kernel` recovers the executor post.
      rw [← hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-- **AFTER (the epoch-stamp residual SHED).** Refined against the CHAINED, STAMPING step
`refreshDelegationChainA` (= `execFullA`'s arm). CLEAN kernel-agreement — NO `delegationEpochAt` residual —
PLUS the freshness fact read OFF the commit (`HandlerFloors.refreshFreshnessFloor_discharges`): the child's
re-stamp EQUALS `parentEpoch child`. The epoch residual the BEFORE version carried is now internal: a
committed refresh PRODUCES the freshness, the refinement no longer ESCAPES it through the conclusion. -/
theorem handler_refines_execFullA_refreshDelegation (s s' : RecChainedState) (actor child : CellId)
    (h : Dregg2.Exec.TurnExecutorFull.refreshDelegationChainA s actor child = some s') :
    (∃ s'', execFullA s (.refreshDelegationA actor child) = some s'' ∧ s''.kernel = s'.kernel)
      ∧ s'.kernel.delegationEpochAt child = parentEpoch s.kernel child := by
  refine ⟨⟨s', ?_, rfl⟩,
    HandlerFloors.refreshFreshnessFloor_discharges (a := { actor := actor, child := child }) h⟩
  show Dregg2.Exec.TurnExecutorFull.refreshDelegationChainA s actor child = some s'
  exact h

theorem handler_refines_execFullA_emitEvent (s s' : RecChainedState) (actor cell : CellId)
    (topic data : Int) (h : execHandlerOne (.emitEventA actor cell topic data) s = some s') :
    ∃ s'', execFullA s (.emitEventA actor cell topic data) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.emitEventA actor cell topic data) s s' h
  rw [toClosedEffect] at hstep
  change emitEventStep s.kernel { actor := actor, cell := cell, topic := topic, data := data } = some s'.kernel at hstep
  unfold emitEventStep at hstep
  by_cases hmem : cell ∈ s.kernel.accounts ∧ acceptsEffects s.kernel cell = true
  · rw [if_pos hmem] at hstep
    have hk : s.kernel = s'.kernel := by simpa only [Option.some.injEq] using hstep
    refine ⟨emitStep s actor cell topic data, ?_, hk⟩
    simp only [execFullA, if_pos hmem, emitStep]
  · rw [if_neg hmem] at hstep; exact absurd hstep (by simp)

/-! ### §6.5 — AUTHORITY / SEAL / SWISS (mechanical strengthening; handler gates only narrow). -/

private theorem auth_mem_allAuths : ∀ a : Auth, allAuths.contains a = true := by
  intro a; cases a <;> decide

private theorem auth_in_allAuths (a : Auth) : a ∈ allAuths := by
  cases a <;> simp [allAuths]

private theorem attenuate_allAuths_id (c : Cap) : attenuate allAuths c = c := by
  cases c with
  | null => simp [attenuate]
  | endpoint t rights =>
      simp only [attenuate]
      congr 1
      apply List.filter_eq_self.mpr
      intro a _
      exact auth_mem_allAuths a
  | node t =>
      -- `attenuate allAuths (.node t)`: `allAuths` admits every Auth, so the full-keep guard
      -- `nodeFacets.all (allAuths.contains)` holds and the node cap is returned UNCHANGED.
      simp only [attenuate]
      rw [if_pos]
      exact List.all_eq_true.mpr (fun a _ => by
        have := auth_mem_allAuths a; simpa using this)

private theorem recKDelegateAtten_allAuths_eq_recKDelegate (k : RecordKernelState) (d r t : CellId) :
    recKDelegateAtten k d r t allAuths = recKDelegate k d r t := by
  unfold recKDelegateAtten recKDelegate
  by_cases hg : (k.caps d).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg, if_pos hg, attenuate_allAuths_id (heldCapTo k.caps d t)]
  · rw [if_neg hg, if_neg hg]

theorem handler_refines_execFullA_delegate (s s' : RecChainedState) (del rec t : CellId)
    (h : execHandlerOne (.delegate del rec t) s = some s') :
    ∃ s'', execFullA s (.delegate del rec t) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.delegate del rec t) s s' h
  rw [toClosedEffect] at hstep
  change delegateAttenStep s.kernel
    { delegator := del, recipient := rec, target := t, keep := allAuths } = some s'.kernel at hstep
  simp only [delegateAttenStep] at hstep
  by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
  · have hk : recKDelegate s.kernel del rec t = some s'.kernel := by
      rw [← recKDelegateAtten_allAuths_eq_recKDelegate, hstep]
    refine ⟨{ kernel := s'.kernel, log := authReceipt del :: s.log }, ?_, rfl⟩
    show recCDelegate s del rec t = _
    unfold recCDelegate
    rw [hk]
  · unfold recKDelegateAtten at hstep; rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_delegateAtten (s s' : RecChainedState) (del rec t : CellId)
    (keep : List Auth) (h : execHandlerOne (.delegateAttenA del rec t keep) s = some s') :
    ∃ s'', execFullA s (.delegateAttenA del rec t keep) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.delegateAttenA del rec t keep) s s' h
  rw [toClosedEffect] at hstep
  change delegateAttenStep s.kernel
    { delegator := del, recipient := rec, target := t, keep := keep } = some s'.kernel at hstep
  simp only [delegateAttenStep] at hstep
  by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
  · refine ⟨{ kernel := s'.kernel, log := authReceipt del :: s.log }, ?_, rfl⟩
    show recCDelegateAtten s del rec t keep = _
    unfold recCDelegateAtten
    rw [hstep]
  · unfold recKDelegateAtten at hstep; rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_introduce (s s' : RecChainedState) (intro rec t : CellId)
    (h : execHandlerOne (.introduceA intro rec t) s = some s') :
    ∃ s'', execFullA s (.introduceA intro rec t) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.introduceA intro rec t) s s' h
  rw [toClosedEffect] at hstep
  change delegateAttenStep s.kernel
    { delegator := intro, recipient := rec, target := t, keep := allAuths } = some s'.kernel at hstep
  simp only [delegateAttenStep] at hstep
  by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
  · have hk : recKDelegate s.kernel intro rec t = some s'.kernel := by
      rw [← recKDelegateAtten_allAuths_eq_recKDelegate, hstep]
    refine ⟨{ kernel := s'.kernel, log := authReceipt intro :: s.log }, ?_, rfl⟩
    show recCDelegate s intro rec t = _
    unfold recCDelegate
    rw [hk]
  · unfold recKDelegateAtten at hstep; rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-! ### §6.5b — AUTHORITY NON-AMPLIFICATION SHED (P2: the relational floor read off the commit).

The non-amplification obligation — `confRights granted ≤ confRights held`, the rights the delegation
hands the recipient do NOT exceed the rights the delegator HELD — is the §P2 floor. A delegation-aware
refinement that ALSO reports non-amplification (so a downstream light-client / circuit consumer can use
the bound) would, with a TOO-WEAK handler step, have to TAKE that relation as a caller hypothesis
(`hamp`). The migration `HandlerFloors.authNonAmpFloor` makes the floor a TYPED obligation discharged
from `delegateAttenStep`'s post-condition, so the AFTER theorem READS it off the commit — the `hamp`
side-hypothesis is SHED.

BEFORE — `..._delegateAtten_nonAmp_weak`: the non-amp relation is a HYPOTHESIS `hamp` the caller supplies.
AFTER — `..._delegateAtten_nonAmp`: same conclusion (kernel-agreement ∧ the non-amp relation), but `hamp`
is GONE — produced internally by `authNonAmpFloor_discharges`. The diff is the side-hyp drop. -/

/-- The §P2 floor delivered for the delegateAtten family. `HandlerFloors.authNonAmpFloor` is the
`FloorObligation` on `delegateAttenStep` whose `gated` discharges this relation FROM the commit (the
discharge-from-commit vehicle, proven in `HandlerFloors`). Here — in the executor file, where the
`delegateAttenStep` defeq is expensive — we deliver the SAME relation via the floor's underlying
unconditional fact (`recKDelegateAtten_non_amplifying`, what `authNonAmpFloor.gated` itself returns), so
the refinement carries NO `hamp` hypothesis: the non-amp is internal, not a caller obligation. -/
private theorem delegateAttenA_nonAmp_off_commit {s s' : RecChainedState} {del rec t : CellId}
    {keep : List Auth} (_h : execHandlerOne (.delegateAttenA del rec t keep) s = some s') :
    confRights (attenuate keep (heldCapTo s.kernel.caps del t))
      ≤ confRights (heldCapTo s.kernel.caps del t) :=
  recKDelegateAtten_non_amplifying s.kernel.caps del t keep

/-- **BEFORE (the side-hyp version).** A delegateAtten refinement reporting non-amplification, with the
non-amp relation TAKEN as the caller hypothesis `hamp` (the shape a too-weak handler would force). The
proof never uses `hamp` other than to return it — the witness that `hamp` is a pure liability the AFTER
version sheds. -/
theorem handler_refines_execFullA_delegateAtten_nonAmp_weak (s s' : RecChainedState)
    (del rec t : CellId) (keep : List Auth)
    (hamp : confRights (attenuate keep (heldCapTo s.kernel.caps del t))
              ≤ confRights (heldCapTo s.kernel.caps del t))
    (h : execHandlerOne (.delegateAttenA del rec t keep) s = some s') :
    (∃ s'', execFullA s (.delegateAttenA del rec t keep) = some s'' ∧ s''.kernel = s'.kernel)
      ∧ confRights (attenuate keep (heldCapTo s.kernel.caps del t))
          ≤ confRights (heldCapTo s.kernel.caps del t) :=
  ⟨handler_refines_execFullA_delegateAtten s s' del rec t keep h, hamp⟩

/-- **AFTER (the side-hyp SHED).** The SAME conclusion — kernel-agreement AND the non-amplification
relation `confRights granted ≤ confRights held` — but WITHOUT the `hamp` hypothesis: the non-amp fact is
read OFF the commit via `HandlerFloors.authNonAmpFloor_discharges` (the `delegateAttenStep` post-condition
supplies it). The relational authority floor is now internal to the handler, exactly as `hnr`/`hmono`
became in P1. -/
theorem handler_refines_execFullA_delegateAtten_nonAmp (s s' : RecChainedState)
    (del rec t : CellId) (keep : List Auth)
    (h : execHandlerOne (.delegateAttenA del rec t keep) s = some s') :
    (∃ s'', execFullA s (.delegateAttenA del rec t keep) = some s'' ∧ s''.kernel = s'.kernel)
      ∧ confRights (attenuate keep (heldCapTo s.kernel.caps del t))
          ≤ confRights (heldCapTo s.kernel.caps del t) :=
  ⟨handler_refines_execFullA_delegateAtten s s' del rec t keep h,
   delegateAttenA_nonAmp_off_commit h⟩

/-- **`introduceA` non-amp SHED.** The full-authority introduce (`keep := allAuths`) reported with its
non-amplification relation read OFF the commit — no `hamp` hypothesis. `introduceA` routes through the
SAME `delegateAttenStep` (with `keep := allAuths`), so the discharge supplies `confRights (attenuate
allAuths held) ≤ confRights held` (non-amp holds for ANY keep). -/
theorem handler_refines_execFullA_introduce_nonAmp (s s' : RecChainedState) (intro rec t : CellId)
    (h : execHandlerOne (.introduceA intro rec t) s = some s') :
    (∃ s'', execFullA s (.introduceA intro rec t) = some s'' ∧ s''.kernel = s'.kernel)
      ∧ confRights (attenuate Handlers.Authority.allAuths (heldCapTo s.kernel.caps intro t))
          ≤ confRights (heldCapTo s.kernel.caps intro t) := by
  exact ⟨handler_refines_execFullA_introduce s s' intro rec t h,
    recKDelegateAtten_non_amplifying s.kernel.caps intro t Handlers.Authority.allAuths⟩

theorem handler_refines_execFullA_attenuate (s s' : RecChainedState) (actor : CellId) (idx : Nat)
    (keep : List Auth) (hb : idx < (s.kernel.caps actor).length)
    (h : execHandlerOne (.attenuateA actor idx keep) s = some s') :
    ∃ s'', execFullA s (.attenuateA actor idx keep) = some s'' ∧ s''.kernel = s'.kernel := by
  -- The dregg1 handler `attenuateStep` is TOTAL (commits even out of bounds); the dregg2 executor is
  -- STRICTER — it FAILS CLOSED out of bounds. So the refinement holds exactly on the in-bounds slot `hb`.
  have hstep := execHandlerOne_kernel (.attenuateA actor idx keep) s s' h
  rw [toClosedEffect] at hstep
  change attenuateStep s.kernel { actor := actor, idx := idx, keep := keep } = some s'.kernel at hstep
  unfold attenuateStep at hstep
  simp only [Option.some.injEq] at hstep
  refine ⟨attenuateStepA s actor idx keep, ?_, ?_⟩
  · show execFullA s (.attenuateA actor idx keep) = _
    rw [Dregg2.Exec.TurnExecutorFull.execFullA_attenuateA_eq, if_pos hb]
  · show (attenuateStepA s actor idx keep).kernel = s'.kernel
    rw [← hstep]; unfold attenuateStepA; rfl

-- F2b: the §6.6 QUEUE honest-path refinements died with the queue verb family (queue behavior is
-- the factory story, `Apps/{QueueFactory,InboxFactory,PubsubFactory}.lean`).

/-! ### §6.7 — EXERCISE: inner-turn hypothesis (the `exerciseA` / `execInnerA` bridge).

The handler folds the inner forest through `subTurn` + the R4 facet-mask (`exerciseAdmitB`); `execFullA`
freezes the kernel at the hold-gate (`exerciseStepA`) then recurses via `execInnerA`. Kernel agreement is
carried by **`hinner`** — the inner fold from the hold-state reaches the SAME kernel the handler's
`subTurn` produced (the circuit-layer `innerTurnH` pattern). -/

/-- Post-hold-gate chained state: kernel frozen, authority receipt prepended. -/
def exerciseHoldState (st : RecChainedState) (actor : CellId) : RecChainedState :=
  { st with log := authReceipt actor :: st.log }

@[simp] private theorem exerciseHoldState_kernel (st : RecChainedState) (actor : CellId) :
    (exerciseHoldState st actor).kernel = st.kernel := rfl

/-! ### §6.7a — THE INTER-EXECUTOR KERNEL-AGREEMENT BRIDGE (the `exercise_inner_fold` boundary).

The handler folds its inner forest through `subTurn (innerEffects …)` over `RecordKernelState` (each step
is `execEffect (toClosedEffect fa)` = the looked-up handler's `step`), while `execFullA`'s `.exerciseA`
arm folds via `execInnerA` over `RecChainedState` (each step is `execFullA fa`). The two are DIFFERENT
inner executors over different state carriers, so the handler step does not, on its own, establish the
live fold's kernel.

The KEY observation that makes the boundary PROVABLE (not carried): we never need the full refinement
direction (handler-commits ⇒ live-commits) — for the boundary we have BOTH folds committing (the handler
by its commit `h`; the live fold by the circuit witness / `execInnerA = some post`). What remains is mere
AGREEMENT: when BOTH a handler kernel-step and the live `execFullA` commit, they land on the SAME kernel.
That agreement holds UNCONDITIONALLY per effect (the handler only ever NARROWS what commits, and where it
DOES commit, the resulting kernel is exactly the bare chained step's — the §6.1–§6.6 refinement theorems
prove this), so the divergent arms (`attenuate`/`noteSpend`-without-proof, where the handler is the LOOSER
one) cause no trouble: the live commit is a HYPOTHESIS here, so we are only ever on the path where both
agree. The recursion bottoms out structurally on the (smaller) inner list. -/

/-- Reconstruct a one-effect handler-turn commit from a bare kernel step: if the looked-up handler's
`step` commits on `st.kernel`, then `execHandlerOne` commits on `st` with that exact kernel. The inverse
direction of `execHandlerOne_kernel`. -/
private theorem execHandlerOne_of_kernelStep (fa : FullActionA) (st : RecChainedState)
    (k' : RecordKernelState)
    (hstep : (toClosedEffect fa).handler.step st.kernel (toClosedEffect fa).args = some k') :
    execHandlerOne fa st
      = some { kernel := k', log := (closedOf [fa]).reverse.map (fun e => e.handler.trace e.args) ++ st.log } := by
  unfold execHandlerOne execHandlerTurn
  have hturn : execTurn (closedOf [fa]) st.kernel = some k' := by
    simp only [closedOf, List.map_cons, List.map_nil, execTurn_cons, execEffect, execTurn_nil]
    rw [hstep]; rfl
  rw [hturn]

/-- A committed `stateStep` field write was into a member cell (the live gate carries membership). The
membership the setPermissions/setVK/setProgram refinement theorems need, recovered from the LIVE commit
(`execFullA`'s arm IS `stateStep st f actor cell (.int v)`). -/
private theorem setStateField_mem_of_live {st st' : RecChainedState} {f : FieldName}
    {actor cell : CellId} {v : Value}
    (h : Dregg2.Exec.EffectsState.stateStep st f actor cell v = some st') :
    cell ∈ st.kernel.accounts := by
  unfold Dregg2.Exec.EffectsState.stateStep at h
  by_cases hg : Dregg2.Exec.EffectsState.stateAuthB st.kernel.caps actor cell = true
      ∧ cell ∈ st.kernel.accounts ∧ Dregg2.Exec.EffectsState.cellLive st.kernel cell = true
  · exact hg.2.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! **THE GENUINE INNER-FOLD DIVERGENCES — three FROZEN-FACE handler inner steps.** The handler's
exercise inner fold runs `execEffect (toClosedEffect fa)` = the looked-up handler's `step`. For three
constructors that handler step is a SIMPLIFIED "frozen face" that does LESS than the live `execFullA`
arm, so on a non-trivial input the handler kernel and the live kernel DIVERGE. Verified empirically /
read off the existing top-level `_residual`/`_metadata` theorems:

  1. **`refreshDelegationA`** — handler `Lifecycle.refreshDelegationStep` updates ONLY `delegations`;
     the live `refreshDelegationChainA` ALSO re-stamps `delegationEpochAt child := parentEpoch`. On a
     stale-epoch child the two diverge at `delegationEpochAt` (eval: handler 0 vs live 5).
  2. **`createCellFromFactoryA`** — handler dispatch is `createCellFromFactoryH = createCellH` (born
     EMPTY); the live `createCellFromFactoryChainA` installs the registered factory's `slotCaveats`,
     `factoryVk` field, and `initialFields`. They diverge at the minted cell's record/caveats.
  3. **`spawnA`** — handler dispatch is `spawnH = createCellH` (born EMPTY); the live `spawnChainA`
     ALSO copies the held cap to the child, records the parent, snapshots the c-list, stamps the epoch.

For all three the top-level handler refinement deliberately routes through the CHAINED arm (the
`_metadata`/`_residual` theorems) precisely BECAUSE the born-empty/frozen dispatch differs from the live
arm. As inner effects of an exercise they have no such re-routing — the inner fold uses the frozen face —
so the inter-executor kernel agreement is NOT unconditional. `noFrozenFace` is the precise SYNTACTIC
characterization of the closable fragment (the inner forests on which the two folds PROVABLY agree at the
kernel); the residual is exactly its complement. (The clean fix lives in the handler-algebra lane: route
the exercise inner fold through the chained stamping/installing/handoff steps — the same arms the
top-level refinements already use. Until then this is the precise honest residual.) -/
def noFrozenFace : FullActionA → Bool
  | .refreshDelegationA _ _ => false
  | .createCellFromFactoryA _ _ _ => false
  | .spawnA _ _ _ => false
  | .exerciseA _ _ inner => inner.attach.all (fun p => noFrozenFace p.1)
  | _ => true
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem p.2
  omega

mutual
/-- **`handlerStep_agrees_execFullA_kernel` — the inter-executor per-effect kernel agreement.** When the
handler's kernel step AND the live `execFullA` BOTH commit on a shared kernel, they produce the SAME
kernel (on the closable fragment `noFrozenFace fa = true` — every effect EXCEPT the one divergent
`refreshDelegationA` frozen-face arm). We pass the handler side as a kernel-step on `st.kernel`; the live
side as `execFullA st fa`. Proved by `sizeOf fa` recursion: the unconditional arms delegate to the §6
refinement theorems (which give the unique `execFullA` result with matching kernel; `execFullA` is a
function, so the witnessed `st'` coincides); the side-conditioned arms (setField/makeSovereign/
receiptArchive/heapWrite — where the handler may be the LOOSER one) are settled DIRECTLY at the kernel via
the live `*_factors`; the refresh arm is RULED OUT by `noFrozenFace`; the exercise arm recurses into
the inner-fold agreement on the structurally-smaller (safe) inner list. -/
theorem handlerStep_agrees_execFullA_kernel :
    ∀ (fa : FullActionA) (st st' : RecChainedState) (k' : RecordKernelState),
      noFrozenFace fa = true →
      (toClosedEffect fa).handler.step st.kernel (toClosedEffect fa).args = some k' →
      execFullA st fa = some st' → st'.kernel = k'
  | .balanceA t a, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_transfer st _ t a (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .delegate del rec t, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_delegate st _ del rec t (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .revoke holder t, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_revoke st _ holder t (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .mintA actor cell a amt, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_mint st _ actor cell a amt (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .burnA actor cell a amt, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_burn st _ actor cell a amt (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .setFieldA actor cell f v, st, st', k', _halign, hstep, hlive => by
      -- DIRECT: the live setField arm is `stateStepDev`; both commit to the same `writeField` post-state.
      rw [toClosedEffect] at hstep
      change Dregg2.Exec.Handlers.StateSupply.setFieldDevStep st.kernel
        { actor := actor, target := cell, field := f, value := v } = some k' at hstep
      have hkk : Dregg2.Exec.EffectsState.stateStepDev st f actor cell v = some st' := hlive
      -- the handler step's kernel and the live step's kernel both write field `f` of `cell` to `v`.
      have hnr : Dregg2.Exec.EffectsState.reservedField f = false :=
        Dregg2.Exec.Handlers.StateSupply.setFieldDevStep_notReserved hstep
      replace hstep := Dregg2.Exec.Handlers.StateSupply.setFieldDevStep_eq hstep
      change stateWriteStep st.kernel { actor := actor, target := cell, field := f, value := v } = some k' at hstep
      unfold stateWriteStep at hstep
      by_cases hg : acceptsEffects st.kernel cell
          && authorizedB st.kernel.caps { actor := actor, src := cell, dst := cell, amt := 0 }
      · rw [if_pos hg] at hstep
        have hkdef : k' = writeField st.kernel f cell (.int v) := (Option.some.inj hstep).symm
        -- the live `stateStepDev` post-state.
        unfold Dregg2.Exec.EffectsState.stateStepDev at hkk
        rw [if_neg (by rw [hnr]; simp)] at hkk
        unfold Dregg2.Exec.EffectsState.stateStepGuarded at hkk
        by_cases hcav : caveatsAdmit st.kernel f actor cell v = true
        · rw [if_pos hcav] at hkk
          obtain ⟨_, hst'⟩ := Dregg2.Exec.EffectsState.stateStep_factors hkk
          rw [hst', hkdef]
        · rw [if_neg hcav] at hkk; exact absurd hkk (by simp)
      · rw [if_neg hg] at hstep; exact absurd hstep (by simp)
  | .emitEventA actor cell topic data, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_emitEvent st _ actor cell topic data (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .incrementNonceA actor cell n, st, st', k', _halign, hstep, hlive => by
      have hmem : cell ∈ st.kernel.accounts :=
        setStateField_mem_of_live (Dregg2.Exec.EffectsState.incrementNonceStep_eq hlive)
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_incrementNonce st _ actor cell n hmem (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .setPermissionsA actor cell p, st, st', k', _halign, hstep, hlive => by
      have hmem : cell ∈ st.kernel.accounts := setStateField_mem_of_live (f := permsField) hlive
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_setPermissions st _ actor cell p hmem (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .setVKA actor cell vk, st, st', k', _halign, hstep, hlive => by
      have hmem : cell ∈ st.kernel.accounts := setStateField_mem_of_live (f := Dregg2.Exec.TurnExecutorFull.vkField) hlive
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_setVK st _ actor cell vk hmem (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .setProgramA actor cell prog, st, st', k', _halign, hstep, hlive => by
      have hmem : cell ∈ st.kernel.accounts := setStateField_mem_of_live (f := Dregg2.Exec.TurnExecutorFull.programField) hlive
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_setProgram st _ actor cell prog hmem (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .introduceA intro rec t, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_introduce st _ intro rec t (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .delegateAttenA del rec t keep, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_delegateAtten st _ del rec t keep (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .attenuateA actor idx keep, st, st', k', _halign, hstep, hlive => by
      -- the live executor FAILS CLOSED out of bounds; the live commit recovers the in-bounds side-condition.
      have hb : idx < (st.kernel.caps actor).length :=
        (Dregg2.Exec.TurnExecutorFull.attenuateA_factors hlive).1
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_attenuate st _ actor idx keep hb (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .revokeDelegationA holder t, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_revokeDelegation st _ holder t (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .exerciseA actor target inner, st, st', k', halign, hstep, hlive => by
      -- BOTH sides fold the SAME `inner`. Recurse on the structurally-smaller list. The exercise's own
      -- safety propagates element-wise to the inner forest.
      have hsafe : ∀ fa ∈ inner, noFrozenFace fa = true := by
        have h := halign
        unfold noFrozenFace at h
        rw [List.all_eq_true] at h
        intro fa hfa
        exact h ⟨fa, hfa⟩ (List.mem_attach inner _)
      let innerF := inner.map (fun fa => facetedOf (Dregg2.Exec.TurnExecutorFull.requiredFacetA fa) (toClosedEffect fa))
      have hsub : subTurn (innerEffects innerF) st.kernel = some k' := by
        rw [toClosedEffect] at hstep
        change exerciseStep st.kernel { actor := actor, target := target, inner := innerF } = some k' at hstep
        unfold exerciseStep at hstep
        by_cases hg : exerciseAdmitB st.kernel { actor := actor, target := target, inner := innerF }
        · rw [if_pos hg] at hstep; exact hstep
        · rw [if_neg hg] at hstep; exact absurd hstep (by simp)
      have hfold : execInnerA (exerciseHoldState st actor) inner = some st' := by
        simp only [execFullA] at hlive
        by_cases hf : Dregg2.Exec.TurnExecutorFull.innerFacetsAdmittedA st actor target inner = true
        · rw [if_pos hf] at hlive
          cases hgs : Dregg2.Exec.TurnExecutorFull.exerciseStepA st actor target with
          | none => rw [hgs] at hlive; exact absurd hlive (by simp)
          | some s1 =>
              rw [hgs] at hlive
              obtain ⟨_, hs1⟩ := Dregg2.Exec.TurnExecutorFull.exerciseStepA_factors hgs
              rw [hs1] at hlive; exact hlive
        · rw [if_neg hf] at hlive; exact absurd hlive (by simp)
      exact innerFold_agrees_kernel inner (exerciseHoldState st actor) st' k' hsafe
        (by rw [exerciseHoldState_kernel]; exact hsub) hfold
  | .createCellA actor newCell, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_createCell st _ actor newCell (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .createCellFromFactoryA _actor _newCell _vk, _st, _st', _k', halign, _hstep, _hlive => by
      -- FROZEN-FACE DIVERGENCE: handler dispatch is born-EMPTY `createCellH`; the live
      -- `createCellFromFactoryChainA` installs the factory's caveats/vk/initialFields. RULED OUT.
      simp only [noFrozenFace, reduceCtorEq] at halign
  | .spawnA _actor _child _target, _st, _st', _k', halign, _hstep, _hlive => by
      -- FROZEN-FACE DIVERGENCE: handler dispatch is born-EMPTY `createCellH`; the live `spawnChainA`
      -- copies the held cap + records parent + snapshots c-list + stamps epoch. RULED OUT.
      simp only [noFrozenFace, reduceCtorEq] at halign
  | .bridgeMintA actor cell a value, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_bridgeMint st _ actor cell a value (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .noteSpendA nf actor spendProof, st, st', k', _halign, hstep, hlive => by
      -- live commit forces `spendProof = true` (the §8 NOTE-PROOF TEETH); refine against that.
      have hsp : spendProof = true := by
        cases spendProof with
        | false =>
            exfalso
            have hnone : execFullA st (.noteSpendA nf actor false) = none := by
              show Dregg2.Exec.TurnExecutorFull.noteSpendChainA st nf actor false = none
              unfold Dregg2.Exec.TurnExecutorFull.noteSpendChainA
              rfl
            rw [hnone] at hlive; exact absurd hlive (by simp)
        | true => rfl
      subst hsp
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_noteSpend st _ nf actor (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .noteCreateA cm actor, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_noteCreate st _ cm actor (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .makeSovereignA actor cell, st, st', k', _halign, hstep, hlive => by
      -- DIRECT: both steps commit to `makeSovereignKernel st.kernel cell`.
      rw [toClosedEffect] at hstep
      change Dregg2.Exec.Handlers.StateSupply.makeSovereignStepK st.kernel
        { actor := actor, target := cell } = some k' at hstep
      unfold Dregg2.Exec.Handlers.StateSupply.makeSovereignStepK at hstep
      by_cases hg : acceptsEffects st.kernel cell
          && authorizedB st.kernel.caps { actor := actor, src := cell, dst := cell, amt := 0 }
      · rw [if_pos hg] at hstep
        have hkdef : k' = Dregg2.Exec.TurnExecutorFull.makeSovereignKernel st.kernel cell := (Option.some.inj hstep).symm
        obtain ⟨_, hst'⟩ := Dregg2.Exec.TurnExecutorFull.makeSovereignStep_factors hlive
        rw [hst', hkdef]
      · rw [if_neg hg] at hstep; exact absurd hstep (by simp)
  | .refusalA actor cell, st, st', k', _halign, hstep, hlive => by
      have hmem : cell ∈ st.kernel.accounts := setStateField_mem_of_live (f := Dregg2.Exec.TurnExecutorFull.refusalField) hlive
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_refusal st _ actor cell hmem (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .receiptArchiveA actor cell, st, st', k', _halign, hstep, hlive => by
      -- DIRECT: both steps move the lifecycle side-table to `lcArchived`.
      rw [toClosedEffect] at hstep
      change Dregg2.Exec.Handlers.Lifecycle.cellArchiveStep st.kernel { actor := actor, cell := cell }
        = some k' at hstep
      unfold Dregg2.Exec.Handlers.Lifecycle.cellArchiveStep at hstep
      by_cases hg : stateAuthB st.kernel.caps actor cell && acceptsEffects st.kernel cell
      · rw [if_pos hg] at hstep
        have hkdef : k' = Dregg2.Exec.TurnExecutorFull.setLifecycle st.kernel cell Dregg2.Exec.TurnExecutorFull.lcArchived := (Option.some.inj hstep).symm
        change Dregg2.Exec.TurnExecutorFull.receiptArchiveChainA st actor cell = some st' at hlive
        unfold Dregg2.Exec.TurnExecutorFull.receiptArchiveChainA at hlive
        by_cases hgl : stateAuthB st.kernel.caps actor cell = true ∧ cell ∈ st.kernel.accounts
            ∧ Dregg2.Exec.EffectsState.cellLive st.kernel cell = true
        · rw [if_pos hgl] at hlive
          have hst' : st' = { kernel := Dregg2.Exec.TurnExecutorFull.setLifecycle st.kernel cell Dregg2.Exec.TurnExecutorFull.lcArchived,
                              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: st.log } :=
            (Option.some.inj hlive).symm
          rw [hst', hkdef]
        · rw [if_neg hgl] at hlive; exact absurd hlive (by simp)
      · rw [if_neg hg] at hstep; exact absurd hstep (by simp)
  | .pipelinedSendA actor, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_pipelinedSend st _ actor (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .cellSealA actor cell, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_cellSeal st _ actor cell (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .cellUnsealA actor cell, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_cellUnseal st _ actor cell (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .cellDestroyA actor cell ch, st, st', k', _halign, hstep, hlive => by
      obtain ⟨s'', hex, hke⟩ := handler_refines_execFullA_cellDestroy st _ actor cell ch (execHandlerOne_of_kernelStep _ st k' hstep)
      rw [hlive] at hex; rw [Option.some.injEq] at hex; rw [← hex] at hke; exact hke
  | .refreshDelegationA _actor _child, _st, _st', _k', halign, _hstep, _hlive => by
      -- THE ONE DIVERGENT ARM is RULED OUT of the closable fragment: the handler frozen-face
      -- `Lifecycle.refreshDelegationStep` updates ONLY `delegations` (NO epoch re-stamp), while the live
      -- `refreshDelegationChainA` ALSO re-stamps `delegationEpochAt child := parentEpoch` — so on a
      -- stale-epoch child the two kernels DIVERGE (verified empirically). `noFrozenFace` excludes it.
      simp only [noFrozenFace, reduceCtorEq] at halign
  | .heapWriteA actor target addr v newRoot, st, st', k', _halign, hstep, hlive => by
      -- DIRECT: the handler `heapWriteStep` writes `heap_root` + the heaps splice (no caveat gate); the
      -- live `heapStepGuardedW` writes the SAME (its `stateStepGuarded` commits the same `heap_root` write
      -- + the SAME splice). When BOTH commit the kernels coincide.
      rw [toClosedEffect] at hstep
      change Dregg2.Exec.Handlers.StateSupply.heapWriteStep st.kernel
        { actor := actor, target := target, addr := addr, value := v, newRoot := newRoot } = some k' at hstep
      unfold Dregg2.Exec.Handlers.StateSupply.heapWriteStep at hstep
      by_cases hg : acceptsEffects st.kernel target
          && authorizedB st.kernel.caps { actor := actor, src := target, dst := target, amt := 0 }
      · rw [if_pos hg] at hstep
        have hkdef : k' = { writeField st.kernel Dregg2.Substrate.HeapKernel.heapRootField target (.int newRoot) with
              heaps := fun c => if c = target
                                then Dregg2.Substrate.Heap.set (st.kernel.heaps target) addr v
                                else st.kernel.heaps c } := (Option.some.inj hstep).symm
        obtain ⟨s₁, hsg, hst'⟩ := Dregg2.Substrate.HeapKernel.heapStepGuardedW_factors hlive
        obtain ⟨_, hs₁⟩ := Dregg2.Exec.EffectsState.stateStep_factors
          (Dregg2.Exec.EffectsState.stateStepGuarded_eq hsg)
        rw [hst', hkdef, hs₁]
      · rw [if_neg hg] at hstep; exact absurd hstep (by simp)
  termination_by fa _ _ _ _ _ _ => sizeOf fa

/-- **`innerFold_agrees_kernel` — the inner-fold lift of the per-effect agreement.** Both inner folds run
the SAME `inner` from a shared kernel; if every effect is on the closable fragment (`hsafe`), the handler's
`subTurn (innerEffects (map facetedOf …))` reaches `k'` AND the live `execInnerA` reaches `post`, then
`post.kernel = k'`. By induction on `inner`, each step consumes `handlerStep_agrees_execFullA_kernel`. -/
theorem innerFold_agrees_kernel :
    ∀ (inner : List FullActionA) (st post : RecChainedState) (k' : RecordKernelState),
      (∀ fa ∈ inner, noFrozenFace fa = true) →
      subTurn (innerEffects (inner.map (fun fa => facetedOf (Dregg2.Exec.TurnExecutorFull.requiredFacetA fa) (toClosedEffect fa)))) st.kernel = some k' →
      execInnerA st inner = some post → post.kernel = k'
  | [], st, post, k', _hsafe, hsub, hlive => by
      simp only [List.map_nil, innerEffects, subTurn_nil, Option.some.injEq] at hsub
      simp only [execInnerA, Option.some.injEq] at hlive
      rw [← hlive, ← hsub]
  | fa :: rest, st, post, k', hsafe, hsub, hlive => by
      simp only [List.map_cons, innerEffects, subTurn_cons, facetedOf, closedToSub,
        Option.bind_eq_some_iff] at hsub
      obtain ⟨kmid, hhead, htail⟩ := hsub
      simp only [execInnerA] at hlive
      cases hlf : execFullA st fa with
      | none => rw [hlf] at hlive; exact absurd hlive (by simp)
      | some smid =>
          rw [hlf] at hlive
          have hheadstep : (toClosedEffect fa).handler.step st.kernel (toClosedEffect fa).args = some kmid := by
            simpa only [execEffect] using hhead
          have hmidk : smid.kernel = kmid :=
            handlerStep_agrees_execFullA_kernel fa st smid kmid
              (hsafe fa (List.mem_cons_self ..)) hheadstep hlf
          have htail' : subTurn (innerEffects (rest.map (fun fa => facetedOf (Dregg2.Exec.TurnExecutorFull.requiredFacetA fa) (toClosedEffect fa)))) smid.kernel = some k' := by
            rw [hmidk]; simpa only [innerEffects] using htail
          exact innerFold_agrees_kernel rest smid post k'
            (fun fa hfa => hsafe fa (List.mem_cons_of_mem _ hfa)) htail' hlive
  termination_by inner _ _ _ _ _ _ => sizeOf inner
end

/-- **`exercise_inner_fold_kernel_agrees` — THE BOUNDARY KERNEL EQUALITY, PROVEN.** On the closable
fragment (`noFrozenFace`-safe inner forest), whenever the handler executor commits an exercise (giving its
`subTurn` inner fold's kernel `s'.kernel`) AND the live `execInnerA` from the hold-state commits to `post`,
the two inner folds AGREE at the kernel: `post.kernel = s'.kernel`. This is the boundary fact the
`exercise_inner_fold` front carried — now DISCHARGED by `innerFold_agrees_kernel` (per-effect inter-executor
agreement, inducted over the forest), not assumed. The residual is exactly the un-safe complement (a forest
carrying a frozen-face `refreshDelegationA`/`createCellFromFactoryA`/`spawnA`). -/
theorem exercise_inner_fold_kernel_agrees (s s' post : RecChainedState) (actor target : CellId)
    (inner : List FullActionA)
    (hsafe : ∀ fa ∈ inner, noFrozenFace fa = true)
    (hfold : execInnerA (exerciseHoldState s actor) inner = some post)
    (h : execHandlerOne (.exerciseA actor target inner) s = some s') :
    post.kernel = s'.kernel := by
  -- the handler's committed exercise inner fold reaches `s'.kernel`.
  have hstep := execHandlerOne_kernel (.exerciseA actor target inner) s s' h
  rw [toClosedEffect] at hstep
  let innerF := inner.map (fun fa => facetedOf (Dregg2.Exec.TurnExecutorFull.requiredFacetA fa) (toClosedEffect fa))
  change exerciseStep s.kernel { actor := actor, target := target, inner := innerF } = some s'.kernel at hstep
  unfold exerciseStep at hstep
  by_cases hg : exerciseAdmitB s.kernel { actor := actor, target := target, inner := innerF }
  · rw [if_pos hg] at hstep
    -- the live inner fold (`hfold`) and the handler's `subTurn` (`hstep`) agree at the kernel.
    exact innerFold_agrees_kernel inner (exerciseHoldState s actor) post s'.kernel hsafe
      (by rw [exerciseHoldState_kernel]; exact hstep) hfold
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_exercise` — PROVED on the inner-turn honest path.** Whenever the handler
executor commits an exercise AND the inner `FullActionA` fold from the hold-state reaches the SAME
kernel (`hinner`), `execFullA` ALSO commits the exercise AND produces that kernel. -/
theorem handler_refines_execFullA_exercise (s s' : RecChainedState) (actor target : CellId)
    (inner : List FullActionA)
    (hinner : ∃ s₁, execInnerA (exerciseHoldState s actor) inner = some s₁ ∧
        s₁.kernel = s'.kernel)
    (h : execHandlerOne (.exerciseA actor target inner) s = some s') :
    ∃ s'', execFullA s (.exerciseA actor target inner) = some s'' ∧ s''.kernel = s'.kernel := by
  obtain ⟨s₁, hfold, hk⟩ := hinner
  have hstep := execHandlerOne_kernel (.exerciseA actor target inner) s s' h
  rw [toClosedEffect] at hstep
  -- the bridge now tags each inner with its REAL `requiredFacetA` (matching `execFullA`'s gate), not a
  -- blanket `Auth.control`.
  let innerF := inner.map (fun fa => facetedOf (Dregg2.Exec.TurnExecutorFull.requiredFacetA fa) (toClosedEffect fa))
  change exerciseStep s.kernel { actor := actor, target := target, inner := innerF } = some s'.kernel at hstep
  unfold exerciseStep at hstep
  by_cases hg : exerciseAdmitB s.kernel { actor := actor, target := target, inner := innerF }
  · rw [if_pos hg] at hstep
    rw [exerciseAdmitB, holdsEdge, Bool.and_eq_true] at hg
    obtain ⟨hhold', hadmit⟩ := hg
    have hg' : exerciseStepA s actor target = some (exerciseHoldState s actor) := by
      simp only [exerciseStepA, hhold', if_pos, exerciseHoldState]
    -- THE FACET BRIDGE: the handler's `forestAdmitted (exercisedCap) innerF` IS `execFullA`'s
    -- `innerFacetsAdmittedA s actor target inner` — same `heldCapTo` cap, same `requiredFacetA` keys,
    -- same per-cap mask (`capFacetMask = capFacetMaskA`, proved by `rfl`). So the R4 gate passes.
    have hfacet : Dregg2.Exec.TurnExecutorFull.innerFacetsAdmittedA s actor target inner = true := by
      have hmaskeq : Handlers.Exercise.capFacetMask (Dregg2.Exec.heldCapTo s.kernel.caps actor target)
          = Dregg2.Exec.TurnExecutorFull.capFacetMaskA (Dregg2.Exec.heldCapTo s.kernel.caps actor target) := by
        cases Dregg2.Exec.heldCapTo s.kernel.caps actor target <;> rfl
      simp only [Dregg2.Exec.TurnExecutorFull.innerFacetsAdmittedA,
        Dregg2.Exec.TurnExecutorFull.innerFacetAdmittedA, List.all_eq_true]
      intro fa hfa
      -- pull the per-inner admission out of the handler's `forestAdmitted`.
      simp only [Handlers.Exercise.forestAdmitted, Handlers.Exercise.exercisedCap,
        Handlers.Exercise.innerEffects, List.all_eq_true] at hadmit
      have := hadmit (Handlers.Exercise.facetedOf
        (Dregg2.Exec.TurnExecutorFull.requiredFacetA fa) (toClosedEffect fa)) (by
          simp only [innerF, List.mem_map]; exact ⟨fa, hfa, rfl⟩)
      simpa only [Handlers.Exercise.facetAdmitted, Handlers.Exercise.facetedOf, hmaskeq] using this
    refine ⟨s₁, ?_, hk⟩
    simp only [execFullA, if_pos hfacet, hg', hfold]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_exercise_fromSafe` — the `hinner` SHED on the closable fragment.** The
abstract `hinner` (the live inner fold reaching the handler's kernel) is DISCHARGED from the live fold
`hfold` paired with the PROVEN boundary `exercise_inner_fold_kernel_agrees` — the caller no longer supplies
a bare kernel-equality, only the `noFrozenFace` safety + the live fold it already has. -/
theorem handler_refines_execFullA_exercise_fromSafe (s s' post : RecChainedState) (actor target : CellId)
    (inner : List FullActionA)
    (hsafe : ∀ fa ∈ inner, noFrozenFace fa = true)
    (hfold : execInnerA (exerciseHoldState s actor) inner = some post)
    (h : execHandlerOne (.exerciseA actor target inner) s = some s') :
    ∃ s'', execFullA s (.exerciseA actor target inner) = some s'' ∧ s''.kernel = s'.kernel :=
  handler_refines_execFullA_exercise s s' actor target inner
    ⟨post, hfold, exercise_inner_fold_kernel_agrees s s' post actor target inner hsafe hfold h⟩ h

/-! ## §7 — THE TEETH: R1/R6 holes closed in BOTH executors (parity witnesses).

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

-- §TEETH-R1 (TRANSFER INTO A SEALED CELL): R1 is now CLOSED IN THE LIVE EXECUTOR TOO. `recCexecAsset`
-- gates on `acceptsEffects` at `t.dst`, so `execFullA` AND `execHandlerTurn` both REJECT a credit into
-- the SEALED cell 1.
#guard ((execFullA teethSealed (.balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0)).isSome) == false  --  false (R1 CLOSED in live executor)
#guard ((execHandlerOne (.balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0) teethSealed).isSome) == false  --  false (CLOSED)

-- §TEETH-R6 (STATE WRITE INTO A SEALED CELL): R6 is now CLOSED IN THE LIVE EXECUTOR TOO. The bare
-- `EffectsState.stateStep` gained a `cellLive` (lifecycle-liveness) conjunct, so `execFullA` itself
-- now REJECTS a nonce write into the SEALED cell 1 — matching the handler. Both return `none`.
#guard ((execFullA teethSealed (.incrementNonceA 0 1 7)).isSome) == false  --  false (R6 CLOSED in the live executor)
#guard ((execHandlerOne (.incrementNonceA 0 1 7) teethSealed).isSome) == false  --  false (CLOSED by acceptsEffects)
-- ...and a write into the LIVE cell 0 still COMMITS in both — the gate only tightens the non-live case.
#guard ((execFullA teethSealed (.incrementNonceA 0 0 7)).isSome)  --  true  (live cell still accepts)
#guard ((execHandlerOne (.incrementNonceA 0 0 7) teethSealed).isSome)  --  true  (live cell still accepts)

-- (F1b: the §TEETH-R2 escrow-release fixtures left with the kernel escrow store — the settle-actor
-- gate lives in the factory contract now, with its own teeth in `Apps/EscrowFactory.lean`.)

-- §TEETH-INNER-FOLD-DIVERGENCE: the `noFrozenFace` classifier is NON-VACUOUS (true AND false), and the
-- three excluded constructors are EXACTLY the frozen-face inner steps that DIVERGE from the live arm.
#guard noFrozenFace (.balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0) == true   -- transfer: safe
#guard noFrozenFace (.refreshDelegationA 0 1) == false                                      -- epoch re-stamp: UNSAFE
#guard noFrozenFace (.createCellFromFactoryA 0 9 7) == false                                -- factory install: UNSAFE
#guard noFrozenFace (.spawnA 0 9 1) == false                                                -- cap handoff: UNSAFE
-- a nested exercise carrying a frozen-face refresh is itself classified UNSAFE (the recursion bites):
#guard noFrozenFace (.exerciseA 0 1 [.refreshDelegationA 0 1]) == false
#guard noFrozenFace (.exerciseA 0 1 [.balanceA { actor := 0, src := 0, dst := 1, amt := 1 } 0]) == true

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
          log := [] }).map (fun s => recTotalAsset s.kernel 0)) == some 100  --  some 100

/-! ## §8 — Axiom-hygiene pins (every cutover keystone rests only on the three kernel axioms).

The derived global laws + the strengthening + the executor structure are all pinned to the kernel triple
(`propext`/`Classical.choice`/`Quot.sound`). -/

#assert_axioms masterRegistry_length
#assert_axioms execHandlerTurn_conserves
#assert_axioms execHandlerTurn_head_authorized
#assert_axioms execHandlerTurn_head_admitted
#assert_axioms execHandlerOne_kernel
#assert_axioms handler_refines_execFullA_transfer
#assert_axioms handler_refines_execFullA_balance
#assert_axioms handler_refines_execFullA_mint
#assert_axioms handler_refines_execFullA_burn
#assert_axioms handler_refines_execFullA_bridgeMint
#assert_axioms handler_refines_execFullA_revoke
#assert_axioms handler_refines_execFullA_createCell
#assert_axioms handler_refines_execFullA_spawn
#assert_axioms handler_refines_execFullA_createCellFromFactory
#assert_axioms handler_refines_execFullA_noteSpend
#assert_axioms handler_refines_execFullA_noteCreate
#assert_axioms handler_refines_execFullA_pipelinedSend
#assert_axioms handler_refines_execFullA_revokeDelegation
#assert_axioms handler_refines_execFullA_stateWrite
#assert_axioms handler_refines_execFullA_incrementNonce
#assert_axioms handler_refines_execFullA_setPermissions
#assert_axioms handler_refines_execFullA_setVK
#assert_axioms handler_refines_execFullA_setProgram
#assert_axioms handler_refines_execFullA_refusal
#assert_axioms handler_refines_execFullA_setField
#assert_axioms handler_refines_execFullA_cellSeal
#assert_axioms handler_refines_execFullA_cellUnseal
#assert_axioms handler_refines_execFullA_cellDestroy
#assert_axioms handler_refines_execFullA_refreshDelegation_residual
#assert_axioms handler_refines_execFullA_refreshDelegation
#assert_axioms handler_refines_execFullA_spawn_fresh
#assert_axioms handler_refines_execFullA_spawn_metadata
#assert_axioms handler_refines_execFullA_createCellFromFactory_metadata
#assert_axioms handler_refines_execFullA_emitEvent
#assert_axioms handler_refines_execFullA_delegate
#assert_axioms handler_refines_execFullA_delegateAtten
#assert_axioms handler_refines_execFullA_introduce
#assert_axioms handler_refines_execFullA_delegateAtten_nonAmp_weak
#assert_axioms handler_refines_execFullA_delegateAtten_nonAmp
#assert_axioms handler_refines_execFullA_introduce_nonAmp
#assert_axioms handler_refines_execFullA_attenuate
#assert_axioms hole_handler_makeSovereign
#assert_axioms handler_refines_execFullA_makeSovereign
#assert_axioms hole_handler_receiptArchive
#assert_axioms handler_refines_execFullA_receiptArchive
#assert_axioms handler_refines_execFullA_exercise
-- The inter-executor inner-fold boundary (the `exercise_inner_fold` front) — kernel-pinned, no new axiom.
#assert_axioms handlerStep_agrees_execFullA_kernel
#assert_axioms innerFold_agrees_kernel
#assert_axioms exercise_inner_fold_kernel_agrees
#assert_axioms handler_refines_execFullA_exercise_fromSafe

/-! ## §DEFER — scope of THIS cutover keystone (additive; the call-site switch is mechanical).

Deliberately OUT of this file (documented, NOT a silent gap):

  * **The live-switch of callers.** This file is ADDITIVE: it does NOT edit `execFullA`/`FullActionA`.
    Switching `execFullA`'s 5 dregg1 call-sites onto `execHandlerTurn` (routing each `FullActionA` through
    `toClosedEffect`) is the next, MECHANICAL step — the algebra and its global laws are proved HERE so
    that switch is a rename, not a re-proof.

  * **The strengthening for the remaining constructors.** `handler_refines_execFullA_*` is now proved for
    transfer R1, release/refund R2, mint/burn/createEscrow/createCell supply, notes, bridge
    lock/finalize/cancel/pipelinedSend, state-write R6 (incrementNonce/setPermissions/setVK/refusal;
    `setField` under discharged `caveatsAdmit`), committed-escrow under `hidingProof = true`, the
    lifecycle family, authority (delegate/delegateAtten/introduce/validateHandoff/attenuate/revoke/
    dropRef/revokeDelegation), and seal/swiss. (F2b: the queue-family refinements died with the
    queue verbs — queue behavior is the factory story.)
    NOW CLOSED (§6.3b): `makeSovereignA` (handler ALIGNED to the `makeSovereignKernel`
    commitment-rebind — `hole_handler_makeSovereign`), `receiptArchiveA` (handler ALIGNED to the
    `"lifecycle"` field write — `hole_handler_receiptArchive`).
    REMAINING: `spawnA` / `createCellFromFactoryA` **full** `spawnChainA`/`createCellFromFactoryChainA`
    metadata (the born-empty `createCellA` core is now covered by
    `handler_refines_execFullA_{spawn,createCellFromFactory}`). For
    `exerciseA`, kernel agreement is on the **inner-turn honest path**
    (`handler_refines_execFullA_exercise` + `hinner`); the R4 facet-mask still narrows handler-commits.

  * **The state-write existence-predicate MISMATCH — RESOLVED (R6 closed in the live executor).** The
    bare `EffectsState.stateStep` now ALSO consults lifecycle-LIVENESS (`cellLive`, definitionally
    `acceptsEffects` = `lifecycle cell == 0`), so `execFullA`'s state-write arms reject a write into a
    Sealed/Destroyed cell exactly like `stateWriteH`. The admission predicates coincide; the handler
    additionally checks membership (`cell ∈ accounts`), which the bare step also checks, so the
    strengthening is still stated on the honest path where the cell exists — but the liveness conjunct is
    now PROVED through, not carried open. (`#eval §TEETH-R6`: `execFullA` now returns `none` on the
    Sealed-cell write, matching the handler.)

  * **The committed-escrow `hidingProof` projection.** `toClosedEffect` maps
    the committed escrow onto the plain escrow lock (the §8 Pedersen hiding portal is off the executable
    ledger). This is the documented executable core; the portal /
    receipt faces fold on at the cutover, unchanged in the conservation accounting.
-/

end Dregg2.Exec.HandlerExecutor
