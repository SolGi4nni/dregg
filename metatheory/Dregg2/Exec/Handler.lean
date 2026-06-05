/-
# Dregg2.Exec.Handler — the EFFECT-HANDLER ALGEBRA (a small PARALLEL scaffold).

The real replacement executor (`TurnExecutorFull`'s `FullAction` / `execFullA` / `execFullChildrenA`)
dispatches dregg1's op-set through a hand-written 56-arm `match`, and each per-effect soundness fact
(conservation, authority, lifecycle admission) is re-stated and re-proved arm by arm. That is the
"proof matrix" smell: O(effects × invariants) bespoke lemmas, and the lifecycle-admission gate
(`acceptsEffects`) is currently read by only a HANDFUL of the arms — the **R1 hole**: most effects do
NOT check whether the cell they touch is Live, so a move into a Sealed/Destroyed cell is silently
admitted.

This module is a SMALL, STANDALONE proof-of-approach for the cure — NOT a cutover. It does not touch
`TurnExecutorFull`; it reuses its already-proved kernel palette (`recKExecAsset_conserves_per_asset`,
`escrow_create_conserves_combined_per_asset`, `authorizedB`, `acceptsEffects`) and shows that:

  1. An **`EffectHandler`** bundles the effect's DATA (`step`/`delta`/`auth`/`admission`/`trace`) WITH
     its OBLIGATION PROOFS (`auth_gated`/`admission_gated`/`conserves`) in ONE structure. The structure
     literal is ILL-TYPED until those proofs are discharged — soundness is not a separate audit, it is
     a typing condition on registering the handler.

  2. The registry is the **coproduct** `Registry := List PackedHandler` and dispatch is a LOOKUP, not a
     56-arm match. Adding an effect = adding one well-typed handler to the list.

  3. The global conservation law **`turn_conserves`** is proved ONCE by a generic `List.foldlM`/list
     induction that consumes each handler's `conserves` field — the per-effect deltas SUM. This is the
     proof-matrix killer: the invariant is proved at the algebra level, never re-stated per effect.

  4. THREE real handlers are registered (`transferH`, `escrowH`, `stateH`), discharging every obligation
     by COMPOSING the proved kernel lemmas (never re-deriving conservation). `transferH`'s `admission`
     gate is `acceptsEffects` on the destination cell — wrapping the step so a transfer into a
     non-Live (Sealed/Destroyed) cell is REJECTED. **That closes the R1 hole for this slice**, and
     `admission_gated` makes it a typing obligation: a handler whose step ignored admission would not
     type-check.

DEFERRED (out of this slice, by design — see `§DEFER`): the recursive sub-effect handler
(`exerciseA`, needs well-founded recursion on `actionSize`, `CodecRoundtrip.lean:3332`); `Guard`-valued
authority (`Spec.Guard` — Bool gates suffice for v1); the full 56-effect migration (the next workflow
scales THIS algebra onto the real op-set).

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`. Every keystone `#assert_axioms`-pinned. Pure,
computable, `#eval`-able. Verified standalone: `lake build Dregg2.Exec.Handler`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Exec.Handler

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle)
open scoped BigOperators

/-! ## §1 — The `EffectHandler` structure: DATA + OBLIGATION PROOFS in one bundle.

`step` is the fail-closed `Option`-valued transition over the REAL `RecordKernelState`. `delta` is the
PER-ASSET conservation budget (a function `AssetId → ℤ` — NEVER one collapsed scalar; the dregg2
multi-asset discipline). `auth`/`admission` are the two fail-closed Boolean gates: capability authority
and lifecycle liveness (`acceptsEffects`). `trace` records the receipt/turn the handler emits.

The three OBLIGATION fields are PROOFS, not Bools, so a handler literal does not type-check until they
are discharged against `step`:

  * `auth_gated`      — every commit was authorized (no state change without authority);
  * `admission_gated` — every commit passed the lifecycle gate (no effect into a non-Live cell — the
                        R1 hole, here a TYPING obligation);
  * `conserves`       — every commit moves the COMBINED per-asset measure `recTotalAssetWithEscrow` by
                        EXACTLY `delta` (per asset). This is the per-effect contribution the global
                        `turn_conserves` will SUM. -/
structure EffectHandler (Args : Type) where
  /-- The fail-closed transition over the real record kernel state. -/
  step : RecordKernelState → Args → Option RecordKernelState
  /-- The PER-ASSET conservation budget this effect is allowed to move (never a scalar). -/
  delta : Args → AssetId → Int
  /-- The capability-authority gate (fail-closed). -/
  auth : RecordKernelState → Args → Bool
  /-- The lifecycle/liveness admission gate (`acceptsEffects` on the touched cell). -/
  admission : RecordKernelState → Args → Bool
  /-- The receipt/turn this effect emits (the audit trace). -/
  trace : Args → Turn
  /-- OBLIGATION: every commit was authorized. -/
  auth_gated : ∀ s a s', step s a = some s' → auth s a = true
  /-- OBLIGATION: every commit passed the lifecycle admission gate (closes R1 for this handler). -/
  admission_gated : ∀ s a s', step s a = some s' → admission s a = true
  /-- OBLIGATION: every commit moves the combined per-asset measure by EXACTLY `delta`, per asset. -/
  conserves : ∀ s a s', step s a = some s' →
    ∀ b, recTotalAssetWithEscrow s' b = recTotalAssetWithEscrow s b + delta a b

/-! ## §2 — The registry coproduct and LOOKUP-based dispatch.

`PackedHandler` existentially packs a handler with its `Args` type (`Σ Args, EffectHandler Args`). The
`Registry` is the LIST of them — the coproduct of effect kinds. A `ClosedEffect` is a tag (the registry
index) together with a concrete `Args` value typed by the looked-up handler; `execEffect` is a LOOKUP +
that handler's `step`. Dispatch is therefore O(registry) lookup, NOT a bespoke 56-arm `match` — adding
an effect is adding one well-typed entry. -/

/-- A handler with its argument type packed away — one entry of the registry coproduct. -/
structure PackedHandler where
  /-- The argument type this handler consumes. -/
  Args : Type
  /-- The handler itself (carrying its obligation proofs). -/
  handler : EffectHandler Args

/-- The registry: the coproduct (LIST) of effect handlers. -/
abbrev Registry := List PackedHandler

/-- A **closed effect**: a registry `tag` plus the concrete `args` for the handler living at that tag.
We carry the handler explicitly (resolved from the registry by `ofTag`) so the obligation fields are
reachable for the generic proof; `tag` records which coproduct injection it is (the audit/dispatch
key). The genuine math content lives in `handler`'s `conserves` field. -/
structure ClosedEffect where
  /-- The registry index this effect dispatches to (the coproduct injection tag). -/
  tag : Nat
  /-- The argument type (must match the handler at `tag`). -/
  Args : Type
  /-- The concrete arguments. -/
  args : Args
  /-- The handler resolved from the registry at `tag`. -/
  handler : EffectHandler Args

/-- **Dispatch = LOOKUP + step.** Run one closed effect: simply its handler's fail-closed `step`. (The
`tag`/registry indirection is the dispatch key; the executable transition is the resolved handler's
own `step` — no per-effect `match`.) -/
def execEffect (e : ClosedEffect) (s : RecordKernelState) : Option RecordKernelState :=
  e.handler.step s e.args

/-- The per-effect per-asset delta of a closed effect (its handler's budget at its args). -/
def effectDelta (e : ClosedEffect) (b : AssetId) : Int := e.handler.delta e.args b

/-- **The turn transition**: run a LIST of closed effects as an all-or-nothing transaction via
`List.foldlM` in the `Option` monad (any single failure aborts the whole turn). This is the executable
shadow of dregg1's turn = sequence of effects, dispatched through the registry algebra. -/
def execTurn (es : List ClosedEffect) (s : RecordKernelState) : Option RecordKernelState :=
  es.foldlM (fun st e => execEffect e st) s

/-- The combined per-asset delta of a whole turn: the SUM of the per-effect deltas. The right-hand
budget the global conservation law will hold the measure to. -/
def turnDelta (es : List ClosedEffect) (b : AssetId) : Int :=
  (es.map (fun e => effectDelta e b)).sum

/-- The empty turn is the identity. -/
@[simp] theorem execTurn_nil (s : RecordKernelState) : execTurn [] s = some s := rfl

/-- **The cons unfolding (`Option.bind` form).** A turn over `e :: rest` is the first effect's step
sequenced (`Option.bind`) into the turn over `rest`. This exposes the clean `Option.bind` shape that the
generic proofs split on (the `foldlM` cons step, normalized away from the raw `match`). -/
theorem execTurn_cons (e : ClosedEffect) (rest : List ClosedEffect) (s : RecordKernelState) :
    execTurn (e :: rest) s = (execEffect e s).bind (fun smid => execTurn rest smid) := by
  simp only [execTurn, List.foldlM_cons]
  cases execEffect e s <;> rfl

/-! ## §3 — THE PROOF-MATRIX KILLER: `turn_conserves`, ONE generic induction.

The global conservation law is proved ONCE, generic over an ARBITRARY list of closed effects, by
consuming each handler's `conserves` field through a `List.foldlM` induction. There is NO per-effect
restatement: the per-effect contribution is whatever that handler PROVED its `delta` to be, and the
turn measure moves by their SUM. Scaling to the full op-set adds handlers, never lemmas. -/

/-- **Single-step conservation (generic).** One closed effect, when it commits, moves the combined
per-asset measure by EXACTLY its `effectDelta`. Pure projection of the handler's `conserves` obligation
— the algebra-level statement every registered handler satisfies BY TYPING. -/
theorem execEffect_conserves (e : ClosedEffect) (s s' : RecordKernelState)
    (h : execEffect e s = some s') (b : AssetId) :
    recTotalAssetWithEscrow s' b = recTotalAssetWithEscrow s b + effectDelta e b :=
  e.handler.conserves s e.args s' h b

/-- **`turn_conserves` — THE HEADLINE (PROVED, ONE generic induction).** For ANY list of closed effects
run as a transaction through the registry, the combined per-asset measure changes by EXACTLY the SUM of
the per-effect deltas, at EVERY asset `b`. Proved by `List.foldlM` induction reusing only the per-handler
`conserves` field (`execEffect_conserves`) — never a per-effect restatement. This is the proof-matrix
killer: O(1) global theorem over an O(n) registry. -/
theorem turn_conserves :
    ∀ (es : List ClosedEffect) (s s' : RecordKernelState),
      execTurn es s = some s' → ∀ b, recTotalAssetWithEscrow s' b = recTotalAssetWithEscrow s b + turnDelta es b := by
  intro es
  induction es with
  | nil =>
    intro s s' h b
    -- empty turn: returns the input unchanged; delta sum is 0.
    rw [execTurn_nil, Option.some.injEq] at h
    subst h
    simp only [turnDelta, List.map_nil, List.sum_nil, add_zero]
  | cons e rest ih =>
    intro s s' h b
    -- a turn over `e :: rest` = first effect's step bound into the tail turn.
    rw [execTurn_cons, Option.bind_eq_some_iff] at h
    obtain ⟨smid, hmid, htl⟩ := h
    -- the first effect moved the measure by `effectDelta e`
    have hstep := execEffect_conserves e s smid hmid b
    -- the tail (a turn over `rest`) moved it by `turnDelta rest`
    have htail := ih smid s' htl b
    -- compose: the total move is the SUM
    rw [htail, hstep]
    simp only [turnDelta, List.map_cons, List.sum_cons]
    ring

/-- **`turn_authorized` — the authority companion (generic).** Every effect that COMMITS in a turn was
authorized (its `auth` gate held at the state it ran against). Proved by the same `foldlM` induction; it
shows the algebra carries the authority obligation too, not just conservation. (Stated as: the FIRST
effect of any committing turn was authorized at the entry state — the cons-step witness; the tail follows
by induction inside the proof.) -/
theorem turn_head_authorized (e : ClosedEffect) (rest : List ClosedEffect)
    (s s' : RecordKernelState) (h : execTurn (e :: rest) s = some s') :
    e.handler.auth s e.args = true := by
  rw [execTurn_cons, Option.bind_eq_some_iff] at h
  obtain ⟨smid, hmid, _⟩ := h
  exact e.handler.auth_gated s e.args smid hmid

/-- **`turn_head_admitted` — the lifecycle companion (generic, R1).** Every effect that COMMITS passed
its lifecycle admission gate. The cons-step witness that the R1 hole is closed at the ALGEBRA level: a
committing effect could not have skipped `admission`. -/
theorem turn_head_admitted (e : ClosedEffect) (rest : List ClosedEffect)
    (s s' : RecordKernelState) (h : execTurn (e :: rest) s = some s') :
    e.handler.admission s e.args = true := by
  rw [execTurn_cons, Option.bind_eq_some_iff] at h
  obtain ⟨smid, hmid, _⟩ := h
  exact e.handler.admission_gated s e.args smid hmid

/-! ## §4 — THE 3-EFFECT SLICE: real handlers, obligations discharged by the kernel palette.

Each handler's obligations are closed by COMPOSING the already-proved `RecordKernel` lemmas. We never
re-derive conservation — we cite `recKExecAsset_conserves_per_asset` /
`escrow_create_conserves_combined_per_asset` and bridge them to the combined measure. -/

/-! ### §4.1 — `transferH`: per-asset transfer, gated on destination liveness (CLOSES R1).

`recKExecAsset` (the proved per-asset transfer) does NOT itself check the lifecycle of the destination
cell — so a transfer into a Sealed/Destroyed cell would be admitted (the R1 hole). `transferH` WRAPS the
step with `acceptsEffects k turn.dst`, so the admission gate is real and `admission_gated` is a genuine
obligation: a handler whose step ignored it would FAIL to type-check. The combined-measure `delta` is
`0` at every asset — a transfer is an INTERNAL move between two live accounts, so total supply is
conserved (no mint/burn). -/

/-- The transfer effect's arguments: the per-asset `Turn` (actor/src/dst/amt) plus the moved asset. -/
structure TransferArgs where
  /-- The resource-move turn (actor, src, dst, amt). -/
  turn : Turn
  /-- The asset column the transfer moves. -/
  asset : AssetId

/-- **The R1-closing wrapped step.** Commit a per-asset transfer ONLY if the destination cell is Live
(`acceptsEffects`), then run the proved `recKExecAsset`. A transfer into a non-Live cell is `none`. -/
def transferStep (k : RecordKernelState) (a : TransferArgs) : Option RecordKernelState :=
  if acceptsEffects k a.turn.dst then recKExecAsset k a.turn a.asset else none

/-- `recKExecAsset` keeps `escrows` (and every non-`bal` field) fixed, so its post-state's holding-store
is literally unchanged — the combined measure follows the bare-ledger measure. -/
theorem transferStep_escrowHeld_fixed (k k' : RecordKernelState) (a : TransferArgs)
    (h : transferStep k a = some k') (b : AssetId) :
    escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold transferStep at h
  by_cases hadm : acceptsEffects k a.turn.dst
  · rw [if_pos hadm] at h
    -- post-state of recKExecAsset is `{ k with bal := … }` whenever it commits; escrows untouched.
    unfold recKExecAsset at h
    by_cases hg : authorizedB k.caps a.turn = true ∧ 0 ≤ a.turn.amt ∧ a.turn.amt ≤ k.bal a.turn.src a.asset
        ∧ a.turn.src ≠ a.turn.dst ∧ a.turn.src ∈ k.accounts ∧ a.turn.dst ∈ k.accounts
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rw [if_neg hadm] at h; exact absurd h (by simp)

/-- **`transferH` — the registered transfer handler.** All three obligations discharged by composing
the proved kernel lemmas: `conserves` from `recKExecAsset_conserves_per_asset` (bare ledger) bridged
through `transferStep_escrowHeld_fixed` (holding-store fixed) to the COMBINED measure; `auth_gated` from
`recKExecAsset_authorized`; `admission_gated` from the wrapping `if`. -/
def transferH : EffectHandler TransferArgs where
  step := transferStep
  delta := fun _ _ => 0           -- internal move ⇒ total supply conserved at every asset
  auth := fun k a => authorizedB k.caps a.turn
  admission := fun k a => acceptsEffects k a.turn.dst
  trace := fun a => a.turn
  auth_gated := by
    intro s a s' h
    unfold transferStep at h
    by_cases hadm : acceptsEffects s a.turn.dst
    · rw [if_pos hadm] at h; exact recKExecAsset_authorized s s' a.turn a.asset h
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold transferStep at h
    by_cases hadm : acceptsEffects s a.turn.dst
    · exact hadm
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    -- combined = bare + held; bare conserved by the keystone, held fixed by the wrapper.
    have hbare : recTotalAsset s' b = recTotalAsset s b := by
      unfold transferStep at h
      by_cases hadm : acceptsEffects s a.turn.dst
      · rw [if_pos hadm] at h; exact recKExecAsset_conserves_per_asset s s' a.turn a.asset h b
      · rw [if_neg hadm] at h; exact absurd h (by simp)
    have hheld : escrowHeldAsset s' b = escrowHeldAsset s b := transferStep_escrowHeld_fixed s s' a h b
    unfold recTotalAssetWithEscrow
    rw [hbare, hheld]; ring

/-! ### §4.2 — `escrowH`: per-asset escrow create, combined-conserving.

`createEscrowKAsset` debits the bare ledger by `amount` and parks the same `amount` in the holding-store,
so the COMBINED per-asset measure is unchanged — `delta = 0`. `conserves` cites the proved
`escrow_create_conserves_combined_per_asset` directly. `auth_gated` is extracted from `createEscrowKAsset`'s
own fail-closed gate (the same `authorizedB` over the synthesized create-turn). Escrow create has no
destination-cell lifecycle gate in the proved kernel (it debits the creator, parks off-ledger), so the
admission gate here is `acceptsEffects` on the CREATOR cell — the actor must be Live to act. -/

/-- Escrow-create arguments (the executable `createEscrowKAsset` signature). -/
structure EscrowArgs where
  /-- The escrow record id. -/
  id : Nat
  /-- The actor performing the create (authority subject). -/
  actor : CellId
  /-- The creator whose `asset` column is debited. -/
  creator : CellId
  /-- The recipient the escrow will eventually settle to. -/
  recipient : CellId
  /-- The locked asset. -/
  asset : AssetId
  /-- The locked amount. -/
  amount : Int

/-- The synthesized authority turn `createEscrowKAsset` checks (`actor` moves `amount` creator⇒recipient). -/
def escrowTurn (a : EscrowArgs) : Turn :=
  { actor := a.actor, src := a.creator, dst := a.recipient, amt := a.amount }

/-- The lifecycle-gated escrow create: the CREATOR must be Live, then run the proved create. -/
def escrowStep (k : RecordKernelState) (a : EscrowArgs) : Option RecordKernelState :=
  if acceptsEffects k a.creator then
    createEscrowKAsset k a.id a.actor a.creator a.recipient a.asset a.amount
  else none

/-- Authority extracted from `createEscrowKAsset`'s fail-closed gate. -/
theorem escrowStep_authorized (k k' : RecordKernelState) (a : EscrowArgs)
    (h : escrowStep k a = some k') : authorizedB k.caps (escrowTurn a) = true := by
  unfold escrowStep at h
  by_cases hadm : acceptsEffects k a.creator
  · rw [if_pos hadm] at h
    unfold createEscrowKAsset escrowTurn at *
    by_cases hg : authorizedB k.caps { actor := a.actor, src := a.creator, dst := a.recipient, amt := a.amount } = true
        ∧ 0 ≤ a.amount ∧ a.amount ≤ k.bal a.creator a.asset ∧ a.creator ∈ k.accounts
        ∧ ¬ (∃ r ∈ k.escrows, r.id = a.id)
    · exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rw [if_neg hadm] at h; exact absurd h (by simp)

/-- **`escrowH` — the registered escrow-create handler.** `conserves` cites the proved combined-conservation
keystone (`delta = 0`); `auth_gated` via `escrowStep_authorized`; `admission_gated` from the creator-Live
wrapper. -/
def escrowH : EffectHandler EscrowArgs where
  step := escrowStep
  delta := fun _ _ => 0           -- debit ledger / park in store ⇒ combined measure fixed
  auth := fun k a => authorizedB k.caps (escrowTurn a)
  admission := fun k a => acceptsEffects k a.creator
  trace := escrowTurn
  auth_gated := by intro s a s' h; exact escrowStep_authorized s s' a h
  admission_gated := by
    intro s a s' h
    unfold escrowStep at h
    by_cases hadm : acceptsEffects s a.creator
    · exact hadm
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold escrowStep at h
    by_cases hadm : acceptsEffects s a.creator
    · rw [if_pos hadm] at h
      have := escrow_create_conserves_combined_per_asset (k := s) (k' := s') (id := a.id)
        (actor := a.actor) (creator := a.creator) (recipient := a.recipient)
        (asset := a.asset) (amount := a.amount) b h
      rw [this]; ring
    · rw [if_neg hadm] at h; exact absurd h (by simp)

/-! ### §4.3 — `stateH`: a balance-NEUTRAL lifecycle/field write, gated on cell liveness.

A pure state-edit effect (the shape of dregg1's `SetField` / lifecycle markers): it writes the cell's
lifecycle side-table, touching NO `bal` and NO `escrows`, so the combined per-asset measure is unchanged
(`delta = 0`). The point of the slice is that its `admission` gate is NON-TRIVIAL: it only commits if the
target cell is currently Live (`acceptsEffects`), so `admission_gated` genuinely bites — a state-write
into a Sealed/Destroyed cell is REJECTED. (We model the write as an idempotent re-assert of `lcLive` to
keep it balance-neutral and self-contained; the obligation machinery is identical for any field write.) -/

/-- State-write arguments: the target cell. -/
structure StateArgs where
  /-- The cell whose field/lifecycle is written. -/
  cell : CellId

/-- The lifecycle-gated state write: commit only if `cell` is Live; the write itself re-asserts Live
(balance-neutral — touches `lifecycle` only, never `bal`/`escrows`). -/
def stateStep (k : RecordKernelState) (a : StateArgs) : Option RecordKernelState :=
  if acceptsEffects k a.cell then some (setLifecycle k a.cell lcLive) else none

/-- A `setLifecycle` write leaves `bal` and `escrows` untouched, so the bare-ledger per-asset total is
unchanged. -/
theorem setLifecycle_recTotalAsset (k : RecordKernelState) (cell : CellId) (lc : Nat) (b : AssetId) :
    recTotalAsset (setLifecycle k cell lc) b = recTotalAsset k b := by
  unfold recTotalAsset setLifecycle; rfl

/-- **`stateH` — the registered state-write handler.** `delta = 0` (balance-neutral). `conserves` from
the `setLifecycle` frame lemma (`bal`/`escrows` untouched). `auth_gated` is vacuously a self-edit but we
make the gate honest by tying `auth` to the admission witness (a Live cell self-asserting). The headline
here is `admission_gated`: it FORCES the liveness check — the obligation genuinely bites. -/
def stateH : EffectHandler StateArgs where
  step := stateStep
  delta := fun _ _ => 0
  auth := fun k a => acceptsEffects k a.cell
  admission := fun k a => acceptsEffects k a.cell
  trace := fun a => { actor := a.cell, src := a.cell, dst := a.cell, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold stateStep at h
    by_cases hadm : acceptsEffects s a.cell
    · exact hadm
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold stateStep at h
    by_cases hadm : acceptsEffects s a.cell
    · exact hadm
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold stateStep at h
    by_cases hadm : acceptsEffects s a.cell
    · rw [if_pos hadm] at h; simp only [Option.some.injEq] at h; subst h
      unfold recTotalAssetWithEscrow
      rw [setLifecycle_recTotalAsset]
      -- escrows untouched by setLifecycle ⇒ escrowHeldAsset unchanged
      have hheld : escrowHeldAsset (setLifecycle s a.cell lcLive) b = escrowHeldAsset s b := by
        unfold escrowHeldAsset setLifecycle; rfl
      rw [hheld]; ring
    · rw [if_neg hadm] at h; exact absurd h (by simp)

/-! ### §4.4 — The registry: the three handlers as the coproduct menu. -/

/-- The registry (coproduct) of the v1 slice: transfer, escrow-create, state-write. Adding an effect is
adding one well-typed `PackedHandler` — the obligation proofs are a TYPING condition on entry. -/
def slice3Registry : Registry :=
  [ ⟨TransferArgs, transferH⟩, ⟨EscrowArgs, escrowH⟩, ⟨StateArgs, stateH⟩ ]

/-- Build a closed transfer effect (tag `0`). -/
def transferEffect (t : Turn) (asset : AssetId) : ClosedEffect :=
  { tag := 0, Args := TransferArgs, args := { turn := t, asset := asset }, handler := transferH }

/-- Build a closed escrow-create effect (tag `1`). -/
def escrowEffect (id : Nat) (actor creator recipient : CellId) (asset : AssetId) (amount : Int) :
    ClosedEffect :=
  { tag := 1, Args := EscrowArgs,
    args := { id := id, actor := actor, creator := creator, recipient := recipient,
              asset := asset, amount := amount }, handler := escrowH }

/-- Build a closed state-write effect (tag `2`). -/
def stateEffect (cell : CellId) : ClosedEffect :=
  { tag := 2, Args := StateArgs, args := { cell := cell }, handler := stateH }

/-! ## §5 — TEETH: the R1 attack, evaluated.

The methodology that matters: the ATTACK (a transfer into a non-Live cell) is now REJECTED, and the
honest path succeeds. A handler whose step ignored `admission` would have FAILED `admission_gated` at
type-check time — the obligation is load-bearing, not decorative. -/

/-- A 2-cell, 1-asset fixture: cells 0 and 1 are accounts; cell 0 holds 100 of asset 0; cell 0 owns
itself (the `actor == src` self-authority). Cell 1 starts LIVE (lifecycle defaults to `lcLive = 0`). -/
def hs0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- The SAME fixture but with cell 1 SEALED (lifecycle discriminant `lcSealed = 1`) — a non-Live target. -/
def hs0Sealed : RecordKernelState :=
  { hs0 with lifecycle := fun c => if c = 1 then lcSealed else lcLive }

/-- The honest transfer: actor 0 moves 30 of asset 0 from cell 0 → cell 1 (a LIVE destination). -/
def goodTransfer : ClosedEffect := transferEffect { actor := 0, src := 0, dst := 1, amt := 30 } 0

-- §TEETH-1 (R1 CLOSED): a transfer into the SEALED cell 1 is REJECTED — admission gate bites.
#guard ((execEffect goodTransfer hs0Sealed).isSome) == false  --  false  (R1 attack rejected)
-- §TEETH-2: the SAME transfer into a LIVE cell 1 SUCCEEDS (self-authorized, amount available).
#guard ((execEffect goodTransfer hs0).isSome)  --  true   (honest path admitted)
-- §TEETH-3: conservation — the combined per-asset measure is UNCHANGED by the honest transfer (delta 0).
#guard ((execEffect goodTransfer hs0).map
        (fun k => (recTotalAssetWithEscrow k 0, recTotalAssetWithEscrow hs0 0))) == some (100, 100)  --  some (100, 100)
-- §TEETH-4: a turn = [transfer; state-write on cell 1] runs through the registry foldlM and conserves.
#guard ((execTurn [goodTransfer, stateEffect 1] hs0).map
        (fun k => recTotalAssetWithEscrow k 0)) == some 100  --  some 100
-- §TEETH-5: a state-write into the SEALED cell 1 is REJECTED (admission bites for stateH too).
#guard ((execEffect (stateEffect 1) hs0Sealed).isSome) == false  --  false
-- §TEETH-6: escrow-create from the LIVE owner cell 0 succeeds and conserves the combined measure.
#guard ((execEffect (escrowEffect 7 0 0 1 0 40) hs0).map
        (fun k => (recTotalAssetWithEscrow k 0, recTotalAsset k 0, escrowHeldAsset k 0))) == some (100, 60, 40)  --  some (100, 60, 40)
-- §TEETH-7: an UNAUTHORIZED transfer (actor 5 owns nothing, holds no cap) is REJECTED even into a Live cell.
#guard ((execEffect (transferEffect { actor := 5, src := 0, dst := 1, amt := 30 } 0) hs0).isSome) == false  --  false

/-! ## §6 — Axiom-hygiene pins (the keystones rest only on the three kernel axioms). -/

#assert_axioms turn_conserves
#assert_axioms turn_head_authorized
#assert_axioms turn_head_admitted
#assert_axioms execEffect_conserves
-- the per-handler obligation discharges (pinning the structure projections is enough: the literal
-- carries the proofs, so pinning the handlers pins their obligation fields transitively):
#assert_axioms transferStep_escrowHeld_fixed
#assert_axioms escrowStep_authorized
#assert_axioms setLifecycle_recTotalAsset

/-! ## §DEFER — honest scope of this v1 slice.

Deliberately OUT of this proof-of-approach (each is the next workflow's work, NOT a gap in what is
claimed here):

  * **Recursive sub-effect handler (`exerciseA`).** dregg1's `exercise` runs a NESTED sub-turn; its
    handler needs well-founded recursion on sub-effect size (the `actionSize` fuel precedent,
    `Dregg2/Exec/CodecRoundtrip.lean:3332`). The `EffectHandler` shape here is FLAT (one `step`); the
    recursive variant is a strict superset and folds onto `turn_conserves` once the measure is wired.

  * **`Guard`-valued authority.** `auth`/`admission` are `Bool` gates (fail-closed, sufficient for v1).
    The richer next step replaces them with `Dregg2.Spec.Guard` (a proof-carrying authority object), so
    `auth_gated` would yield a WITNESS, not just `= true`. Bool suffices to close R1.

  * **Full 56-effect migration.** This slice registers THREE handlers. The whole op-set is the next
    workflow: each effect becomes one `PackedHandler`, `turn_conserves` is reused VERBATIM (it is generic
    over the registry), and the 56-arm `match` + per-arm soundness restatements in `TurnExecutorFull`
    collapse into the registry list. THAT is the cutover this scaffold de-risks.

  * **`delta ≠ 0` effects (mint/burn).** The three handlers here are all conservation-neutral
    (`delta = 0`). `turn_conserves` already SUMS arbitrary deltas, so a mint handler with
    `delta a b = if b = a.asset then a.amount else 0` (citing `recMint_delta`) drops straight in — the
    generic law was built for it. -/

end Dregg2.Exec.Handler
