/-
# Dregg2.Circuit.Inst.queueAtomicTxA — the v2-triple (`EffectCommit3`) VALIDATION for `queueAtomicTxA`.

`queueAtomicTxA` is the ALL-OR-NOTHING atomic queue-op batch: it FOLDS a `List QueueTxOpA` through
`queueTxOpStepA` (each sub-op routes to the proven `queueEnqueueChainA` / `queueDequeueChainA` steps),
touching `queues` + `bal` + `escrows` via the composed sub-ops, then prepends the batch-commit row
`escrowReceiptA actor ::` atop the fold's per-op receipt log. Gate 3 validator:
`queueAtomicTxA_full_sound ⇒ QueueAtomicTxSpec` THROUGH the generic triple-component framework.

ADDITIVE: imports `EffectCommit3` + `Spec/queueatomictx`; edits neither.
-/
import Dregg2.Circuit.EffectCommit3
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.queueatomictx

namespace Dregg2.Circuit.Inst.QueueAtomicTxA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit3
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.QueueAtomicTx
open Dregg2.Exec
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

/-! ## §2 — the `queueAtomicTxE` triple instance (`queues` + `bal` + `escrows`). -/

structure AtomicTxArgs where
  actor : CellId
  ops   : List QueueTxOpA

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The atomic-batch guard — the all-or-nothing fold COMMITS. -/
def atomicTxGuardProp (s : RecChainedState) (args : AtomicTxArgs) : Prop :=
  match queueAtomicTxChainA s args.ops with
  | some _ => True
  | none   => False

instance (s : RecChainedState) (args : AtomicTxArgs) : Decidable (atomicTxGuardProp s args) := by
  unfold atomicTxGuardProp
  cases queueAtomicTxChainA s args.ops with
  | none   => simp; infer_instance
  | some _ => simp; infer_instance

def atomicTxGuardEncode (s : RecChainedState) (args : AtomicTxArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (atomicTxGuardProp s args) else 0

def atomicTxGuardGates : ConstraintSystem := [cBitGuard]

theorem atomicTxGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied atomicTxGuardGates a ↔ satisfied atomicTxGuardGates b := by
  unfold satisfied atomicTxGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- Canonical post-`queues` after the atomic batch fold (pure function of pre+args). -/
def atomicTxPostQueues (s : RecChainedState) (args : AtomicTxArgs) : List QueueRecord :=
  match queueAtomicTxChainA s args.ops with
  | some s1 => s1.kernel.queues
  | none    => s.kernel.queues

/-- Canonical post-`bal` after the atomic batch fold. -/
def atomicTxPostBal (s : RecChainedState) (args : AtomicTxArgs) : CellId → AssetId → ℤ :=
  match queueAtomicTxChainA s args.ops with
  | some s1 => s1.kernel.bal
  | none    => s.kernel.bal

/-- Canonical post-`escrows` after the atomic batch fold. -/
def atomicTxPostEscrows (s : RecChainedState) (args : AtomicTxArgs) : List EscrowRecord :=
  match queueAtomicTxChainA s args.ops with
  | some s1 => s1.kernel.escrows
  | none    => s.kernel.escrows

def queuesComponent (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState AtomicTxArgs :=
  listComponent (·.queues) LE cN hN hLE atomicTxPostQueues

def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState AtomicTxArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD atomicTxPostBal

def escrowsComponent (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState AtomicTxArgs :=
  listComponent (·.escrows) LE cN hN hLE atomicTxPostEscrows

def queueAtomicTxE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE) :
    EffectSpec2Triple RecChainedState AtomicTxArgs where
  view         := chainView
  active1      := queuesComponent LQ cNQ hNQ hLQ
  active2      := balComponent D hD
  active3      := escrowsComponent LE cNE hNE hLE
  logUpdate    := some (fun s args =>
    match queueAtomicTxChainA s args.ops with
    | some s1 => escrowReceiptA args.actor :: s1.log
    | none    => s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := atomicTxGuardGates
  guardProp    := atomicTxGuardProp
  guardWidth   := 1
  guardEncode  := atomicTxGuardEncode
  guardLocal   := atomicTxGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem atomicTxGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE) :
    GuardDecodes2Triple (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) := by
  intro s args s' hsat
  change satisfied atomicTxGuardGates (atomicTxGuardEncode s args s') at hsat
  show atomicTxGuardProp s args
  have hg := hsat cBitGuard (by simp [atomicTxGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, atomicTxGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem atomicTxGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE) :
    GuardEncodes2Triple (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) := by
  intro s args s' hg
  show satisfied atomicTxGuardGates (atomicTxGuardEncode s args s')
  intro c hc
  simp only [atomicTxGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, atomicTxGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem atomicTxRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ)
    (cNE : List ℤ → ℤ) (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) :
    RestFrameDecodes2Triple S (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) :=
  fun k k' h => (hRest k k').mp h

/-! ### §2b — helper: `atomicTxGuardProp` ↔ the spec's `atomicTxGuard`. -/

theorem atomicTxGuardProp_iff_atomicTxGuard (s : RecChainedState) (args : AtomicTxArgs) :
    atomicTxGuardProp s args ↔ atomicTxGuard s args.ops := by
  unfold atomicTxGuardProp atomicTxGuard
  cases hf : queueAtomicTxChainA s args.ops with
  | none   => simp [hf]
  | some s1 => simp [hf]

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

/-! ### §2d — post-shape helpers + batch frame preservation. -/

theorem atomicTxPostQueues_some (s : RecChainedState) (args : AtomicTxArgs) (s1 : RecChainedState)
    (hf : queueAtomicTxChainA s args.ops = some s1) :
    atomicTxPostQueues s args = s1.kernel.queues := by
  unfold atomicTxPostQueues; rw [hf]

theorem atomicTxPostBal_some (s : RecChainedState) (args : AtomicTxArgs) (s1 : RecChainedState)
    (hf : queueAtomicTxChainA s args.ops = some s1) :
    atomicTxPostBal s args = s1.kernel.bal := by
  unfold atomicTxPostBal; rw [hf]

theorem atomicTxPostEscrows_some (s : RecChainedState) (args : AtomicTxArgs) (s1 : RecChainedState)
    (hf : queueAtomicTxChainA s args.ops = some s1) :
    atomicTxPostEscrows s args = s1.kernel.escrows := by
  unfold atomicTxPostEscrows; rw [hf]

theorem kernel_eq_batch_of_components
    (s s' : RecChainedState) (args : AtomicTxArgs) (s1 : RecChainedState)
    (hf : queueAtomicTxChainA s args.ops = some s1)
    (hq : s'.kernel.queues = atomicTxPostQueues s args)
    (hbal : s'.kernel.bal = atomicTxPostBal s args)
    (hesc : s'.kernel.escrows = atomicTxPostEscrows s args)
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
    s'.kernel = s1.kernel := by
  have hkq := atomicTxPostQueues_some s args s1 hf
  have hbal' := atomicTxPostBal_some s args s1 hf
  have hesc' := atomicTxPostEscrows_some s args s1 hf
  rcases queueAtomicTxChainA_preserves_rest hf with
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

/-! ### §2e — apex ↔ `QueueAtomicTxSpec`. -/

theorem apex_iff_queueAtomicTxSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState) :
    (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE).apex s args s' ↔
      QueueAtomicTxSpec s args.actor args.ops s' := by
  unfold QueueAtomicTxSpec queueAtomicTxE EffectSpec2Triple.apex EffectSpec2Triple.postLog
  constructor
  · rintro ⟨hg, hq, hbal, hesc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    rcases atomicTxGuardProp_iff_atomicTxGuard s args |>.mp hg with ⟨s1, hf⟩
    refine ⟨s1, hf, ?_, ?_⟩
    · exact kernel_eq_batch_of_components s s' args s1 hf hq hbal hesc
        hAcc hCell hCaps hNul hRev hCom hSw hSC hFac hLif hDC hDel hDgs hSB
    · simp only [hf, queueAtomicTxE] at hlog ⊢
      exact hlog
  · rintro ⟨s1, hf, hker, hlog⟩
    have hg : atomicTxGuardProp s args :=
      atomicTxGuardProp_iff_atomicTxGuard s args |>.mpr ⟨s1, hf⟩
    have hkq := atomicTxPostQueues_some s args s1 hf
    have hbal' := atomicTxPostBal_some s args s1 hf
    have hesc' := atomicTxPostEscrows_some s args s1 hf
    rcases queueAtomicTxChainA_preserves_rest hf with
      ⟨hAccF, hCellF, hCapsF, hNulF, hRevF, hComF, hSwF, hSCF, hFacF, hLifF, hDCF, hDelF, hDgsF, hSBF⟩
    refine ⟨hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show s'.kernel.queues = atomicTxPostQueues s args
      exact (congrArg (fun k => k.queues) hker).trans hkq.symm
    · show s'.kernel.bal = atomicTxPostBal s args
      exact (congrArg (fun k => k.bal) hker).trans hbal'.symm
    · show s'.kernel.escrows = atomicTxPostEscrows s args
      exact (congrArg (fun k => k.escrows) hker).trans hesc'.symm
    · show s'.log = (match queueAtomicTxChainA s args.ops with
        | some s1 => escrowReceiptA args.actor :: s1.log
        | none => s.log)
      rw [hf]; exact hlog
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

/-! ### §2f — THE VALIDATION: `queueAtomicTxA_full_sound ⇒ QueueAtomicTxSpec`. -/

theorem queueAtomicTxA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState)
    (h : satisfiedE2Triple S (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
        (encodeE2Triple S (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s')) :
    QueueAtomicTxSpec s args.actor args.ops s' := by
  have hapex : (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE).apex s args s' :=
    effect2triple_circuit_full_sound S (queueAtomicTxE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
      (atomicTxRestFrameDecodes S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest) hLog
      (atomicTxGuardDecodes D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s' h
  exact (apex_iff_queueAtomicTxSpec D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s').mp hapex



/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def queueAtomicTxEWire : EffectSpec2Triple RecChainedState AtomicTxArgs where
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
  guardGates   := atomicTxGuardGates
  guardProp    := atomicTxGuardProp
  guardWidth   := 1
  guardEncode  := atomicTxGuardEncode
  guardLocal   := atomicTxGuardLocal
  guardWidth_le := by decide

def queueAtomicTxAAirName : String := "dregg-queueAtomicTxA-v2"

def queueAtomicTxAEmitted : EmittedDescriptor := emittedEffect2Triple queueAtomicTxAAirName queueAtomicTxEWire

#guard queueAtomicTxAEmitted.name == queueAtomicTxAAirName

#assert_axioms atomicTxGuardLocal
#assert_axioms atomicTxGuardProp_iff_atomicTxGuard
#assert_axioms atomicTxGuardDecodes
#assert_axioms atomicTxGuardEncodes
#assert_axioms apex_iff_queueAtomicTxSpec
#assert_axioms queueAtomicTxA_full_sound

end Dregg2.Circuit.Inst.QueueAtomicTxA