/-
# Dregg2.Circuit.Inst.queueEnqueueA — the v2-triple (`EffectCommit3`) VALIDATION for `queueEnqueueA`.

`queueEnqueueA` is the FIFO enqueue + refundable deposit PARK effect: it APPENDS a message to queue
`id`'s buffer (via `queueEnqueueK`), DEBITS the per-asset ledger `bal` at `(actor, dAsset)` by
`deposit`, and PREPENDS an unresolved deposit `EscrowRecord` onto `escrows` (via `createEscrowRawAsset`
off the post-append intermediate `k₁`), advances the log by `enqueueReceipt actor cell deposit ::`, and
FREEZES the other 14 kernel fields. Gate 3 validator: `queueEnqueueA_full_sound ⇒ QueueEnqueueSpec`
THROUGH the generic triple-component framework.

ADDITIVE: imports `EffectCommit3` + `Spec/queuefifocore`; edits neither.
-/
import Dregg2.Circuit.EffectCommit3
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Inst.QueueEnqueueA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit3
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Exec
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoQueuesBalEscrows` portal (frame omits `queues` + `bal` + `escrows`). -/

/-- **`RestIffNoQueuesBalEscrows RH`** — the rest hash binds the 14 non-`queues`-non-`bal`-non-`escrows`
components (BIDIRECTIONAL). -/
def RestIffNoQueuesBalEscrows (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `queueEnqueueE` triple instance (`queues` + `bal` + `escrows`). -/

structure EnqueueArgs where
  id      : Nat
  m       : Nat
  actor   : CellId
  cell    : CellId
  depId   : Nat
  dAsset  : AssetId
  deposit : ℤ

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The enqueue guard as a `Prop` — equivalent to `enqueueGuard` but WITHOUT an explicit `∃ k₁`
(existential eliminated via `queueEnqueueK` match for `Decidable` + `propBit`). -/
def enqueueGuardProp (s : RecChainedState) (args : EnqueueArgs) : Prop :=
  stateAuthB s.kernel.caps args.actor args.cell = true ∧ acceptsEffects s.kernel args.cell = true
    ∧ match queueEnqueueK s.kernel args.id args.m with
      | some k₁ =>
          0 ≤ args.deposit ∧ args.deposit ≤ k₁.bal args.actor args.dAsset ∧ args.actor ∈ k₁.accounts
            ∧ ¬ (∃ r ∈ k₁.escrows, r.id = args.depId)
      | none => False

instance (s : RecChainedState) (args : EnqueueArgs) : Decidable (enqueueGuardProp s args) := by
  unfold enqueueGuardProp
  cases hk : queueEnqueueK s.kernel args.id args.m with
  | none   => simp only [hk]; infer_instance
  | some _ => simp only [hk]; infer_instance

def enqueueGuardEncode (s : RecChainedState) (args : EnqueueArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (enqueueGuardProp s args) else 0

def enqueueGuardGates : ConstraintSystem := [cBitGuard]

theorem enqueueGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied enqueueGuardGates a ↔ satisfied enqueueGuardGates b := by
  unfold satisfied enqueueGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- Canonical post-`queues` after the composed enqueue+park (pure function of pre+args). -/
def enqueuePostQueues (s : RecChainedState) (args : EnqueueArgs) : List QueueRecord :=
  match queueEnqueueK s.kernel args.id args.m with
  | some k₁ => k₁.queues
  | none   => s.kernel.queues

/-- Canonical post-`bal` after the composed enqueue+park. -/
def enqueuePostBal (s : RecChainedState) (args : EnqueueArgs) : CellId → AssetId → ℤ :=
  match queueEnqueueK s.kernel args.id args.m with
  | some k₁ =>
      (createEscrowRawAssetQueue k₁ args.depId args.actor args.cell args.dAsset args.deposit
        args.id args.m).bal
  | none => s.kernel.bal

/-- Canonical post-`escrows` after the composed enqueue+park. -/
def enqueuePostEscrows (s : RecChainedState) (args : EnqueueArgs) : List EscrowRecord :=
  match queueEnqueueK s.kernel args.id args.m with
  | some k₁ =>
      (createEscrowRawAssetQueue k₁ args.depId args.actor args.cell args.dAsset args.deposit
        args.id args.m).escrows
  | none => s.kernel.escrows

def queuesComponent (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState EnqueueArgs :=
  listComponent (·.queues) LE cN hN hLE enqueuePostQueues

def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState EnqueueArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD enqueuePostBal

def escrowsComponent (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState EnqueueArgs :=
  listComponent (·.escrows) LE cN hN hLE enqueuePostEscrows

def queueEnqueueE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE) :
    EffectSpec2Triple RecChainedState EnqueueArgs where
  view         := chainView
  active1      := queuesComponent LQ cNQ hNQ hLQ
  active2      := balComponent D hD
  active3      := escrowsComponent LE cNE hNE hLE
  logUpdate    := some (fun s args => enqueueReceipt args.actor args.cell args.deposit :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := enqueueGuardGates
  guardProp    := enqueueGuardProp
  guardWidth   := 1
  guardEncode  := enqueueGuardEncode
  guardLocal   := enqueueGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem enqueueGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE) :
    GuardDecodes2Triple (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) := by
  intro s args s' hsat
  change satisfied enqueueGuardGates (enqueueGuardEncode s args s') at hsat
  show enqueueGuardProp s args
  have hg := hsat cBitGuard (by simp [enqueueGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, enqueueGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem enqueueGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE) :
    GuardEncodes2Triple (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) := by
  intro s args s' hg
  show satisfied enqueueGuardGates (enqueueGuardEncode s args s')
  intro c hc
  simp only [enqueueGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, enqueueGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem enqueueRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ)
    (cNE : List ℤ → ℤ) (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) :
    RestFrameDecodes2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) :=
  fun k k' h => (hRest k k').mp h

/-! ### §2b — helper: `enqueueGuardProp` ↔ the spec's `enqueueGuard` (existential `k₁`). -/

theorem enqueueGuardProp_iff_enqueueGuard (s : RecChainedState) (args : EnqueueArgs) :
    enqueueGuardProp s args ↔
      enqueueGuard s.kernel args.id args.m args.actor args.cell args.depId args.dAsset
        args.deposit := by
  unfold enqueueGuardProp enqueueGuard
  constructor
  · rintro ⟨hauth, hacc, hg⟩
    cases hk₁ : queueEnqueueK s.kernel args.id args.m with
    | none =>
        exact absurd hg (by simp [enqueueGuardProp, hk₁])
    | some k₁ =>
        simp only [enqueueGuardProp, hk₁] at hg
        exact ⟨hauth, hacc, ⟨k₁, rfl, hg⟩⟩
  · rintro ⟨hauth, hacc, ⟨k₁, hk₁, hd⟩⟩
    simp only [enqueueGuardProp, hk₁]
    exact ⟨hauth, hacc, hd⟩

/-! ### §2c — kernel extensionality (17 fields). -/

theorem recordKernel_eq_of_fields {k k' : RecordKernelState}
    (haccounts : k.accounts = k'.accounts) (hcell : k.cell = k'.cell) (hcaps : k.caps = k'.caps)
    (hescrows : k.escrows = k'.escrows) (hnullifiers : k.nullifiers = k'.nullifiers)
    (hrevoked : k.revoked = k'.revoked) (hcommitments : k.commitments = k'.commitments)
    (hbal : k.bal = k'.bal) (hqueues : k.queues = k'.queues) (hswiss : k.swiss = k'.swiss)
    (hslotCaveats : k.slotCaveats = k'.slotCaveats) (hfactories : k.factories = k'.factories)
    (hlifecycle : k.lifecycle = k'.lifecycle) (hdeathCert : k.deathCert = k'.deathCert)
    (hdelegate : k.delegate = k'.delegate) (hdelegations : k.delegations = k'.delegations)
    (hsealedBoxes : k.sealedBoxes = k'.sealedBoxes) : k = k' := by
  cases k; cases k'; simp_all

/-! ### §2d — post-shape helpers (layered `queueEnqueueK` then `createEscrowRawAsset`). -/

theorem enqueuePostQueues_some (s : RecChainedState) (args : EnqueueArgs) (k₁ : RecordKernelState)
    (hk₁ : queueEnqueueK s.kernel args.id args.m = some k₁) :
    enqueuePostQueues s args = k₁.queues := by
  unfold enqueuePostQueues; rw [hk₁]

theorem enqueuePostBal_some (s : RecChainedState) (args : EnqueueArgs) (k₁ : RecordKernelState)
    (hk₁ : queueEnqueueK s.kernel args.id args.m = some k₁) :
    enqueuePostBal s args =
      (createEscrowRawAssetQueue k₁ args.depId args.actor args.cell args.dAsset args.deposit
        args.id args.m).bal := by
  unfold enqueuePostBal; rw [hk₁]

theorem enqueuePostEscrows_some (s : RecChainedState) (args : EnqueueArgs) (k₁ : RecordKernelState)
    (hk₁ : queueEnqueueK s.kernel args.id args.m = some k₁) :
    enqueuePostEscrows s args =
      (createEscrowRawAssetQueue k₁ args.depId args.actor args.cell args.dAsset args.deposit
        args.id args.m).escrows := by
  unfold enqueuePostEscrows; rw [hk₁]

theorem queueEnqueueK_preserves_frame {k k' : RecordKernelState} {id m : Nat}
    (h : queueEnqueueK k id m = some k') :
    k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes := by
  unfold queueEnqueueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases hc : q.buffer.length < q.capacity
      · rw [if_pos hc] at h; simp only [Option.some.injEq] at h; subst h
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [if_neg hc] at h; exact absurd h (by simp)

theorem createEscrowRawAssetQueue_preserves_frame (k₁ : RecordKernelState) (depId : Nat)
    (actor cell : CellId) (dAsset : AssetId) (deposit : ℤ) (id m : Nat) :
    (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).accounts = k₁.accounts
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).cell = k₁.cell
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).caps = k₁.caps
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).queues = k₁.queues
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).nullifiers = k₁.nullifiers
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).revoked = k₁.revoked
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).commitments = k₁.commitments
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).swiss = k₁.swiss
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).slotCaveats = k₁.slotCaveats
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).factories = k₁.factories
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).lifecycle = k₁.lifecycle
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).deathCert = k₁.deathCert
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).delegate = k₁.delegate
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).delegations = k₁.delegations
      ∧ (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).sealedBoxes = k₁.sealedBoxes := by
  dsimp [createEscrowRawAssetQueue]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem enqueue_composed_preserves_frame (k : RecordKernelState) (k₁ : RecordKernelState)
    (args : EnqueueArgs) (hk₁ : queueEnqueueK k args.id args.m = some k₁)
    (k₂ : RecordKernelState)
    (hk₂ : k₂ = createEscrowRawAssetQueue k₁ args.depId args.actor args.cell args.dAsset args.deposit
        args.id args.m) :
    k₂.accounts = k.accounts ∧ k₂.cell = k.cell ∧ k₂.caps = k.caps
      ∧ k₂.nullifiers = k.nullifiers ∧ k₂.revoked = k.revoked ∧ k₂.commitments = k.commitments
      ∧ k₂.swiss = k.swiss ∧ k₂.slotCaveats = k.slotCaveats ∧ k₂.factories = k.factories
      ∧ k₂.lifecycle = k.lifecycle ∧ k₂.deathCert = k.deathCert ∧ k₂.delegate = k.delegate
      ∧ k₂.delegations = k.delegations ∧ k₂.sealedBoxes = k.sealedBoxes := by
  subst hk₂
  rcases createEscrowRawAssetQueue_preserves_frame k₁ args.depId args.actor args.cell args.dAsset
      args.deposit args.id args.m with
    ⟨hAcc₂, hCell₂, hCaps₂, hQ₂, hNul₂, hRev₂, hCom₂, hSw₂, hSC₂, hFac₂, hLif₂, hDC₂, hDel₂, hDgs₂, hSB₂⟩
  rcases queueEnqueueK_preserves_frame hk₁ with
    ⟨hAcc₁, hCell₁, hCaps₁, hNul₁, hRev₁, hCom₁, hSw₁, hSC₁, hFac₁, hLif₁, hDC₁, hDel₁, hDgs₁, hSB₁⟩
  exact ⟨hAcc₂.trans hAcc₁, hCell₂.trans hCell₁, hCaps₂.trans hCaps₁, hNul₂.trans hNul₁,
    hRev₂.trans hRev₁, hCom₂.trans hCom₁, hSw₂.trans hSw₁, hSC₂.trans hSC₁, hFac₂.trans hFac₁,
    hLif₂.trans hLif₁, hDC₂.trans hDC₁, hDel₂.trans hDel₁, hDgs₂.trans hDgs₁, hSB₂.trans hSB₁⟩

theorem kernel_eq_createEscrowRawAssetQueue_of_components
    (s s' : RecChainedState) (args : EnqueueArgs) (k₁ : RecordKernelState)
    (hk₁ : queueEnqueueK s.kernel args.id args.m = some k₁)
    (hq : s'.kernel.queues = enqueuePostQueues s args)
    (hbal : s'.kernel.bal = enqueuePostBal s args)
    (hesc : s'.kernel.escrows = enqueuePostEscrows s args)
    (hAcc : s'.kernel.accounts = s.kernel.accounts)
    (hCell : s'.kernel.cell = s.kernel.cell)
    (hCaps : s'.kernel.caps = s.kernel.caps)
    (hNul : s'.kernel.nullifiers = s.kernel.nullifiers)
    (hRev : s'.kernel.revoked = s.kernel.revoked)
    (hCom : s'.kernel.commitments = s.kernel.commitments)
    (hSw : s'.kernel.swiss = s.kernel.swiss)
    (hSC : s'.kernel.slotCaveats = s.kernel.slotCaveats)
    (hFac : s'.kernel.factories = s.kernel.factories)
    (hLif : s'.kernel.lifecycle = s.kernel.lifecycle)
    (hDC : s'.kernel.deathCert = s.kernel.deathCert)
    (hDel : s'.kernel.delegate = s.kernel.delegate)
    (hDgs : s'.kernel.delegations = s.kernel.delegations)
    (hSB : s'.kernel.sealedBoxes = s.kernel.sealedBoxes) :
    s'.kernel = createEscrowRawAssetQueue k₁ args.depId args.actor args.cell args.dAsset args.deposit
        args.id args.m := by
  have hkq := enqueuePostQueues_some s args k₁ hk₁
  have hbal' := enqueuePostBal_some s args k₁ hk₁
  have hesc' := enqueuePostEscrows_some s args k₁ hk₁
  have hframe₁ := queueEnqueueK_preserves_frame hk₁
  have hframe₂ := createEscrowRawAssetQueue_preserves_frame k₁ args.depId args.actor args.cell
      args.dAsset args.deposit args.id args.m
  rcases hframe₁ with
    ⟨hAcc₁, hCell₁, hCaps₁, hNul₁, hRev₁, hCom₁, hSw₁, hSC₁, hFac₁, hLif₁, hDC₁, hDel₁, hDgs₁, hSB₁⟩
  rcases hframe₂ with
    ⟨hAcc₂, hCell₂, hCaps₂, hQ₂, hNul₂, hRev₂, hCom₂, hSw₂, hSC₂, hFac₂, hLif₂, hDC₂, hDel₂, hDgs₂, hSB₂⟩
  apply recordKernel_eq_of_fields
  · exact (hAcc.trans hAcc₁.symm).trans hAcc₂.symm
  · exact (hCell.trans hCell₁.symm).trans hCell₂.symm
  · exact (hCaps.trans hCaps₁.symm).trans hCaps₂.symm
  · exact hesc.trans hesc'
  · exact (hNul.trans hNul₁.symm).trans hNul₂.symm
  · exact (hRev.trans hRev₁.symm).trans hRev₂.symm
  · exact (hCom.trans hCom₁.symm).trans hCom₂.symm
  · funext c; funext a; exact congrFun (congrFun (hbal.trans hbal') c) a
  · exact hq.trans hkq
  · exact (hSw.trans hSw₁.symm).trans hSw₂.symm
  · exact (hSC.trans hSC₁.symm).trans hSC₂.symm
  · exact (hFac.trans hFac₁.symm).trans hFac₂.symm
  · exact (hLif.trans hLif₁.symm).trans hLif₂.symm
  · exact (hDC.trans hDC₁.symm).trans hDC₂.symm
  · exact (hDel.trans hDel₁.symm).trans hDel₂.symm
  · exact (hDgs.trans hDgs₁.symm).trans hDgs₂.symm
  · exact (hSB.trans hSB₁.symm).trans hSB₂.symm

/-! ### §2e — apex ↔ `QueueEnqueueSpec`. -/

theorem apex_iff_queueEnqueueSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState) :
    (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE).apex s args s' ↔
      QueueEnqueueSpec s args.id args.m args.actor args.cell args.depId args.dAsset args.deposit s' := by
  constructor
  · rintro ⟨hg, hq, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    rcases enqueueGuardProp_iff_enqueueGuard s args |>.mp hg with
      ⟨hauth, hacc, k₁, hk₁, hd1, hd2, hd3, hd4⟩
    refine ⟨k₁, hauth, hacc, hk₁, hd1, hd2, hd3, hd4, ?_, hlog⟩
    exact kernel_eq_createEscrowRawAssetQueue_of_components s s' args k₁ hk₁ hq hbal hesc
      hAcc hCell hCaps hNul hRev hCom hSw hSC hFac hLif hDC hDel hDgs hSB
  · rintro ⟨k₁, hauth, hacc, hk₁, hd1, hd2, hd3, hd4, hker, hlog⟩
    have hg : enqueueGuardProp s args :=
      enqueueGuardProp_iff_enqueueGuard s args |>.mpr
        ⟨hauth, hacc, k₁, hk₁, hd1, hd2, hd3, hd4⟩
    have hkq := enqueuePostQueues_some s args k₁ hk₁
    have hbal' := enqueuePostBal_some s args k₁ hk₁
    have hesc' := enqueuePostEscrows_some s args k₁ hk₁
    have hframe := enqueue_composed_preserves_frame s.kernel k₁ args hk₁ _ hker
    rcases hframe with
      ⟨hAcc, hCell, hCaps, hNul, hRev, hCom, hSw, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
    rcases createEscrowRawAssetQueue_preserves_frame k₁ args.depId args.actor args.cell args.dAsset
        args.deposit args.id args.m with ⟨_, _, _, hQ₂, _, _, _, _, _, _, _, _, _, _, _⟩
    refine ⟨hg, ?_, ?_, ?_, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    · show s'.kernel.queues = enqueuePostQueues s args
      exact Eq.trans ((congrArg (fun k => k.queues) hker).trans hQ₂) hkq.symm
    · show s'.kernel.bal = enqueuePostBal s args
      exact (congrArg (fun k => k.bal) hker).trans hbal'.symm
    · show s'.kernel.escrows = enqueuePostEscrows s args
      exact (congrArg (fun k => k.escrows) hker).trans hesc'.symm

/-! ### §2f — THE VALIDATION: `queueEnqueueA_full_sound ⇒ QueueEnqueueSpec`. -/

theorem queueEnqueueA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (h : satisfiedE2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
        (encodeE2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s')) :
    QueueEnqueueSpec s args.id args.m args.actor args.cell args.depId args.dAsset args.deposit s' := by
  have hapex : (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE).apex s args s' :=
    effect2triple_circuit_full_sound S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
      (enqueueRestFrameDecodes S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest) hLog
      (enqueueGuardDecodes D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s' h
  exact (apex_iff_queueEnqueueSpec D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def queueEnqueueEWire : EffectSpec2Triple RecChainedState EnqueueArgs where
  view         := chainView
  active1      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  active2      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  active3      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := enqueueGuardGates
  guardProp    := enqueueGuardProp
  guardWidth   := 1
  guardEncode  := enqueueGuardEncode
  guardLocal   := enqueueGuardLocal
  guardWidth_le := by decide

def queueEnqueueAAirName : String := "dregg-queueEnqueueA-v2"

def queueEnqueueAEmitted : EmittedDescriptor := emittedEffect2Triple queueEnqueueAAirName queueEnqueueEWire

#guard queueEnqueueAEmitted.name == queueEnqueueAAirName

#assert_axioms enqueueGuardLocal
#assert_axioms enqueueGuardProp_iff_enqueueGuard
#assert_axioms enqueueGuardDecodes
#assert_axioms enqueueGuardEncodes
#assert_axioms apex_iff_queueEnqueueSpec
#assert_axioms queueEnqueueA_full_sound

end Dregg2.Circuit.Inst.QueueEnqueueA