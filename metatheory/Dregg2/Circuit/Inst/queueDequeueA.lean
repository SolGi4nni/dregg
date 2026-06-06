/-
# Dregg2.Circuit.Inst.queueDequeueA — the v2-triple (`EffectCommit3`) VALIDATION for `queueDequeueA`.

`queueDequeueA` is the FIFO dequeue + deposit REFUND effect: it POP-FRONTS queue `id`'s buffer (via
`queueDequeueK`), CREDITS the per-asset ledger `bal` at `(actor, asset)` by the deposit amount, and
RESOLVES the deposit `EscrowRecord` in `escrows` (via `settleEscrowRawAsset` inside
`queueDequeueRefundK`), advances the log by `dequeueReceipt actor cell deposit ::`, and FREEZES the
other 14 kernel fields. Gate 3 validator: `queueDequeueA_full_sound ⇒ QueueDequeueSpec` THROUGH the
generic triple-component framework.

ADDITIVE: imports `EffectCommit3` + `Spec/queuefifocore`; edits neither.
-/
import Dregg2.Circuit.EffectCommit3
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Inst.QueueDequeueA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
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

/-! ## §2 — the `queueDequeueE` triple instance (`queues` + `bal` + `escrows`). -/

structure DequeueArgs where
  id      : Nat
  actor   : CellId
  cell    : CellId
  depId   : Nat
  deposit : ℤ

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The dequeue guard — auth ∧ live cell ∧ **P0-1 deposit binding** (`r.recipient = actor`) ∧ kernel commits. -/
def dequeueGuardProp (s : RecChainedState) (args : DequeueArgs) : Prop :=
  stateAuthB s.kernel.caps args.actor args.cell = true ∧ acceptsEffects s.kernel args.cell = true
    ∧ dequeueBindB s.kernel args.actor args.depId = true
    ∧ queueDequeueHeadB s.kernel args.id args.actor args.depId = true
    ∧ match queueDequeueRefundK s.kernel args.id args.actor args.depId with
      | some _ => True
      | none   => False

instance (s : RecChainedState) (args : DequeueArgs) : Decidable (dequeueGuardProp s args) := by
  unfold dequeueGuardProp
  cases hk : queueDequeueRefundK s.kernel args.id args.actor args.depId with
  | none   => simp only [hk]; infer_instance
  | some _ => simp only [hk]; infer_instance

def dequeueGuardEncode (s : RecChainedState) (args : DequeueArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (dequeueGuardProp s args) else 0

def dequeueGuardGates : ConstraintSystem := [cBitGuard]

theorem dequeueGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied dequeueGuardGates a ↔ satisfied dequeueGuardGates b := by
  unfold satisfied dequeueGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- Canonical post-`queues` from `queueDequeueRefundK` (pure function of pre+args). -/
def dequeuePostQueues (s : RecChainedState) (args : DequeueArgs) : List QueueRecord :=
  match queueDequeueRefundK s.kernel args.id args.actor args.depId with
  | some (k', _) => k'.queues
  | none         => s.kernel.queues

/-- Canonical post-`bal` from `queueDequeueRefundK`. -/
def dequeuePostBal (s : RecChainedState) (args : DequeueArgs) : CellId → AssetId → ℤ :=
  match queueDequeueRefundK s.kernel args.id args.actor args.depId with
  | some (k', _) => k'.bal
  | none         => s.kernel.bal

/-- Canonical post-`escrows` from `queueDequeueRefundK`. -/
def dequeuePostEscrows (s : RecChainedState) (args : DequeueArgs) : List EscrowRecord :=
  match queueDequeueRefundK s.kernel args.id args.actor args.depId with
  | some (k', _) => k'.escrows
  | none         => s.kernel.escrows

def queuesComponent (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState DequeueArgs :=
  listComponent (·.queues) LE cN hN hLE dequeuePostQueues

def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState DequeueArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD dequeuePostBal

def escrowsComponent (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState DequeueArgs :=
  listComponent (·.escrows) LE cN hN hLE dequeuePostEscrows

def queueDequeueE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE) :
    EffectSpec2Triple RecChainedState DequeueArgs where
  view         := chainView
  active1      := queuesComponent LQ cNQ hNQ hLQ
  active2      := balComponent D hD
  active3      := escrowsComponent LE cNE hNE hLE
  logUpdate    := some (fun s args => dequeueReceipt args.actor args.cell args.deposit :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := dequeueGuardGates
  guardProp    := dequeueGuardProp
  guardWidth   := 1
  guardEncode  := dequeueGuardEncode
  guardLocal   := dequeueGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem dequeueGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE) :
    GuardDecodes2Triple (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) := by
  intro s args s' hsat
  change satisfied dequeueGuardGates (dequeueGuardEncode s args s') at hsat
  show dequeueGuardProp s args
  have hg := hsat cBitGuard (by simp [dequeueGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, dequeueGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem dequeueGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE) :
    GuardEncodes2Triple (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) := by
  intro s args s' hg
  show satisfied dequeueGuardGates (dequeueGuardEncode s args s')
  intro c hc
  simp only [dequeueGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, dequeueGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem dequeueRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ)
    (cNE : List ℤ → ℤ) (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) :
    RestFrameDecodes2Triple S (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) :=
  fun k k' h => (hRest k k').mp h

/-! ### §2b — kernel extensionality (17 fields). -/

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

/-! ### §2c — post-shape helpers (`queueDequeueRefundK` composed kernel fields). -/

theorem dequeuePostQueues_some (s : RecChainedState) (args : DequeueArgs) (k' : RecordKernelState)
    (m : Nat) (hk : queueDequeueRefundK s.kernel args.id args.actor args.depId = some (k', m)) :
    dequeuePostQueues s args = k'.queues := by
  unfold dequeuePostQueues; rw [hk]

theorem dequeuePostBal_some (s : RecChainedState) (args : DequeueArgs) (k' : RecordKernelState)
    (m : Nat) (hk : queueDequeueRefundK s.kernel args.id args.actor args.depId = some (k', m)) :
    dequeuePostBal s args = k'.bal := by
  unfold dequeuePostBal; rw [hk]

theorem dequeuePostEscrows_some (s : RecChainedState) (args : DequeueArgs) (k' : RecordKernelState)
    (m : Nat) (hk : queueDequeueRefundK s.kernel args.id args.actor args.depId = some (k', m)) :
    dequeuePostEscrows s args = k'.escrows := by
  unfold dequeuePostEscrows; rw [hk]

theorem queueDequeueK_preserves_frame {k k' : RecordKernelState} {id : Nat} {actor : CellId} {m : Nat}
    (h : queueDequeueK k id actor = some (k', m)) :
    k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes := by
  unfold queueDequeueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases ho : actor = q.owner
      · rw [if_pos ho] at h
        cases hd : qbufDequeue q.buffer with
        | none           => rw [hd] at h; exact absurd h (by simp)
        | some hr        =>
            obtain ⟨hm, rest⟩ := hr
            rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk, _⟩ := h; subst hk
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [if_neg ho] at h; exact absurd h (by simp)

theorem settleEscrowRawAsset_preserves_frame (k₁ : RecordKernelState) (id : Nat) (target : CellId)
    (asset : AssetId) (amount : ℤ) :
    (settleEscrowRawAsset k₁ id target asset amount).accounts = k₁.accounts
      ∧ (settleEscrowRawAsset k₁ id target asset amount).cell = k₁.cell
      ∧ (settleEscrowRawAsset k₁ id target asset amount).caps = k₁.caps
      ∧ (settleEscrowRawAsset k₁ id target asset amount).queues = k₁.queues
      ∧ (settleEscrowRawAsset k₁ id target asset amount).nullifiers = k₁.nullifiers
      ∧ (settleEscrowRawAsset k₁ id target asset amount).revoked = k₁.revoked
      ∧ (settleEscrowRawAsset k₁ id target asset amount).commitments = k₁.commitments
      ∧ (settleEscrowRawAsset k₁ id target asset amount).swiss = k₁.swiss
      ∧ (settleEscrowRawAsset k₁ id target asset amount).slotCaveats = k₁.slotCaveats
      ∧ (settleEscrowRawAsset k₁ id target asset amount).factories = k₁.factories
      ∧ (settleEscrowRawAsset k₁ id target asset amount).lifecycle = k₁.lifecycle
      ∧ (settleEscrowRawAsset k₁ id target asset amount).deathCert = k₁.deathCert
      ∧ (settleEscrowRawAsset k₁ id target asset amount).delegate = k₁.delegate
      ∧ (settleEscrowRawAsset k₁ id target asset amount).delegations = k₁.delegations
      ∧ (settleEscrowRawAsset k₁ id target asset amount).sealedBoxes = k₁.sealedBoxes := by
  dsimp [settleEscrowRawAsset]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem queueDequeueRefundK_preserves_frame {k k' : RecordKernelState} {id : Nat} {actor : CellId}
    {depId m : Nat} (h : queueDequeueRefundK k id actor depId = some (k', m)) :
    k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes := by
  unfold queueDequeueRefundK at h
  cases hk₁ : queueDequeueK k id actor with
  | none => simp only [hk₁] at h; exact absurd h (by simp)
  | some kr =>
      obtain ⟨k₁, mh⟩ := kr
      simp only [hk₁] at h
      split at h
      · cases hfind : findUnresolvedDeposit k₁ depId with
        | none => simp only [hfind] at h; exact absurd h (by simp)
        | some r =>
            simp only [hfind] at h
            split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hk', _⟩ := h; subst hk'
              rcases settleEscrowRawAsset_preserves_frame k₁ depId actor r.asset r.amount with
                ⟨hAcc, hCell, hCaps, hQ, hNul, hRev, hCom, hSw, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
              rcases queueDequeueK_preserves_frame hk₁ with
                ⟨hAcc₁, hCell₁, hCaps₁, hNul₁, hRev₁, hCom₁, hSw₁, hSC₁, hFac₁, hLif₁, hDC₁, hDel₁, hDgs₁, hSB₁⟩
              exact ⟨hAcc.trans hAcc₁, hCell.trans hCell₁, hCaps.trans hCaps₁, hNul.trans hNul₁,
                hRev.trans hRev₁, hCom.trans hCom₁, hSw.trans hSw₁, hSC.trans hSC₁, hFac.trans hFac₁,
                hLif.trans hLif₁, hDC.trans hDC₁, hDel.trans hDel₁, hDgs.trans hDgs₁, hSB.trans hSB₁⟩
            · exact absurd h (by simp)
      · exact absurd h (by simp)

theorem kernel_eq_of_components
    (s s' : RecChainedState) (args : DequeueArgs) (k' : RecordKernelState) (m : Nat)
    (hk : queueDequeueRefundK s.kernel args.id args.actor args.depId = some (k', m))
    (hq : s'.kernel.queues = dequeuePostQueues s args)
    (hbal : s'.kernel.bal = dequeuePostBal s args)
    (hesc : s'.kernel.escrows = dequeuePostEscrows s args)
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
    s'.kernel = k' := by
  have hkq := dequeuePostQueues_some s args k' m hk
  have hbal' := dequeuePostBal_some s args k' m hk
  have hesc' := dequeuePostEscrows_some s args k' m hk
  have hframe := queueDequeueRefundK_preserves_frame (k := s.kernel) hk
  rcases hframe with
    ⟨hAccF, hCellF, hCapsF, hNulF, hRevF, hComF, hSwF, hSCF, hFacF, hLifF, hDCF, hDelF, hDgsF, hSBF⟩
  apply recordKernel_eq_of_fields
  · exact hAcc.trans hAccF.symm
  · exact hCell.trans hCellF.symm
  · exact hCaps.trans hCapsF.symm
  · exact hesc.trans hesc'
  · exact hNul.trans hNulF.symm
  · exact hRev.trans hRevF.symm
  · exact hCom.trans hComF.symm
  · funext c; funext a; exact congrFun (congrFun (hbal.trans hbal') c) a
  · exact hq.trans hkq
  · exact hSw.trans hSwF.symm
  · exact hSC.trans hSCF.symm
  · exact hFac.trans hFacF.symm
  · exact hLif.trans hLifF.symm
  · exact hDC.trans hDCF.symm
  · exact hDel.trans hDelF.symm
  · exact hDgs.trans hDgsF.symm
  · exact hSB.trans hSBF.symm

/-! ### §2c — apex ↔ `QueueDequeueSpec`. -/

theorem apex_iff_queueDequeueSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState) :
    (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE).apex s args s' ↔
      QueueDequeueSpec s args.id args.actor args.cell args.depId args.deposit s' := by
  constructor
  · rintro ⟨hg, hq, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    obtain ⟨hauth, hacc, hbind, hhead, hgok⟩ := hg
    cases hk : queueDequeueRefundK s.kernel args.id args.actor args.depId with
    | none => exact absurd hgok (by simp [hk])
    | some kr =>
        obtain ⟨k', m⟩ := kr
        refine ⟨hauth, hacc, hbind, hhead, k', m, hk, ?_, hlog⟩
        exact kernel_eq_of_components s s' args k' m hk hq hbal hesc
          hAcc hCell hCaps hNul hRev hCom hSw hSC hFac hLif hDC hDel hDgs hSB
  · rintro ⟨hauth, hacc, hbind, hhead, k', m, hk, hker, hlog⟩
    have hg : dequeueGuardProp s args := ⟨hauth, hacc, hbind, hhead, by simp [dequeueGuardProp, hk]⟩
    have hkq := dequeuePostQueues_some s args k' m hk
    have hbal' := dequeuePostBal_some s args k' m hk
    have hesc' := dequeuePostEscrows_some s args k' m hk
    have hframe := queueDequeueRefundK_preserves_frame (k := s.kernel) hk
    rcases hframe with
      ⟨hAccF, hCellF, hCapsF, hNulF, hRevF, hComF, hSwF, hSCF, hFacF, hLifF, hDCF, hDelF, hDgsF, hSBF⟩
    refine ⟨hg, ?_, ?_, ?_, hlog, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show s'.kernel.queues = dequeuePostQueues s args
      exact (congrArg (fun k => k.queues) hker).trans hkq.symm
    · show s'.kernel.bal = dequeuePostBal s args
      exact (congrArg (fun k => k.bal) hker).trans hbal'.symm
    · show s'.kernel.escrows = dequeuePostEscrows s args
      exact (congrArg (fun k => k.escrows) hker).trans hesc'.symm
    · exact (congrArg (fun k => k.accounts) hker).trans hAccF
    · exact (congrArg (fun k => k.cell) hker).trans hCellF
    · exact (congrArg (fun k => k.caps) hker).trans hCapsF
    · exact (congrArg (fun k => k.nullifiers) hker).trans hNulF
    · exact (congrArg (fun k => k.revoked) hker).trans hRevF
    · exact (congrArg (fun k => k.commitments) hker).trans hComF
    · exact (congrArg (fun k => k.swiss) hker).trans hSwF
    · exact (congrArg (fun k => k.slotCaveats) hker).trans hSCF
    · exact (congrArg (fun k => k.factories) hker).trans hFacF
    · exact (congrArg (fun k => k.lifecycle) hker).trans hLifF
    · exact (congrArg (fun k => k.deathCert) hker).trans hDCF
    · exact (congrArg (fun k => k.delegate) hker).trans hDelF
    · exact (congrArg (fun k => k.delegations) hker).trans hDgsF
    · exact (congrArg (fun k => k.sealedBoxes) hker).trans hSBF

/-! ### §2d — THE VALIDATION: `queueDequeueA_full_sound ⇒ QueueDequeueSpec`. -/

theorem queueDequeueA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState)
    (h : satisfiedE2Triple S (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
        (encodeE2Triple S (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s')) :
    QueueDequeueSpec s args.id args.actor args.cell args.depId args.deposit s' := by
  have hapex : (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE).apex s args s' :=
    effect2triple_circuit_full_sound S (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
      (dequeueRestFrameDecodes S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest) hLog
      (dequeueGuardDecodes D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s' h
  exact (apex_iff_queueDequeueSpec D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s').mp hapex

#assert_axioms dequeueGuardLocal
#assert_axioms dequeueGuardDecodes
#assert_axioms dequeueGuardEncodes
#assert_axioms apex_iff_queueDequeueSpec
#assert_axioms queueDequeueA_full_sound

end Dregg2.Circuit.Inst.QueueDequeueA