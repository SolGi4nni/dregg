/-
# Dregg2.Circuit.WitnessExtractDual — the adversarial-witness EXTRACTOR for the DUAL-component v2 effects.

`WitnessExtract.effect2_extract` closes hostile-witness extraction for the SINGLE-active-component v2
framework (`EffectCommit2`). Some effects touch TWO kernel components at once and route through the DUAL
framework (`EffectCommit2Dual`, `effect2dual_circuit_full_sound`): `cellDestroyA` (lifecycle + death-cert)
and `heapWriteA` (cell record + heap). Their full-state circuit is
`E.guardGates ++ [cE2DRestF, cE2DBind1, cE2DBind2, cE2DLog]` — five EQ gates reading only the eight digest
wires `66..73` (rest 66/67, comp1 68/69, comp2 70/71, log 72/73) plus the guard region.

This module is the EXACT dual analog of `WitnessExtract`: `PIBindsDigestsDual` pins those eight wires +
guard region; `satisfiedE2Dual_of_PIBindsDigestsDual` transports satisfaction; `effect2dual_extract`
forces the apex from an ARBITRARY PI-bound satisfying trace (adversary keeps the un-gated roots `64/65`
and every `w ≥ 74`); the `rejects` teeth refute a forged component-1 / component-2 / log.

ADDITIVE: imports `EffectCommit2Dual` + the two dual Inst effects; edits none.
-/
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Circuit.Inst.cellDestroyA
import Dregg2.Circuit.Inst.heapWriteA

namespace Dregg2.Circuit.WitnessExtractDual

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Exec (RecChainedState CellId AssetId Value)
open Dregg2.Substrate

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the public-input binding on the dual circuit's eight digest wires + guard region. -/

/-- **`PIBindsDigestsDual S E pre args post a`** — the verifier's public-input obligation for the dual
circuit: `a` agrees with `encodeE2Dual S E pre args post` on the guard region `w < guardWidth` and the
eight rest/comp1/comp2/log digest wires `66 .. 73`. STRICTLY WEAKER than `a = encodeE2Dual …`. -/
def PIBindsDigestsDual {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment) : Prop :=
  (∀ w, w < E.guardWidth → a w = E.guardEncode pre args post w)
  ∧ a vE2DRestPre   = encodeE2Dual S E pre args post vE2DRestPre
  ∧ a vE2DRestPost  = encodeE2Dual S E pre args post vE2DRestPost
  ∧ a vE2DComp1Post = encodeE2Dual S E pre args post vE2DComp1Post
  ∧ a vE2DComp1Exp  = encodeE2Dual S E pre args post vE2DComp1Exp
  ∧ a vE2DComp2Post = encodeE2Dual S E pre args post vE2DComp2Post
  ∧ a vE2DComp2Exp  = encodeE2Dual S E pre args post vE2DComp2Exp
  ∧ a vE2DLogPost   = encodeE2Dual S E pre args post vE2DLogPost
  ∧ a vE2DLogExp    = encodeE2Dual S E pre args post vE2DLogExp

theorem encodeE2Dual_PIBindsDigestsDual {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args)
    (pre : St) (args : Args) (post : St) :
    PIBindsDigestsDual S E pre args post (encodeE2Dual S E pre args post) :=
  ⟨fun w hw => encodeE2Dual_agrees_guardEncode S E pre args post w hw,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §2 — locality: a PI-bound `a` satisfies the dual circuit IFF the honest encoding does. -/

theorem satisfiedE2Dual_of_PIBindsDigestsDual {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsDual S E pre args post a) :
    satisfiedE2Dual S E a ↔ satisfiedE2Dual S E (encodeE2Dual S E pre args post) := by
  obtain ⟨hguard, hRPre, hRPost, hC1Post, hC1Exp, hC2Post, hC2Exp, hLPost, hLExp⟩ := hPI
  unfold satisfiedE2Dual effectCircuit2Dual
  constructor
  · intro hsat c hc
    rcases List.mem_append.mp hc with hcg | hc4
    · have hag : satisfied E.guardGates a := fun c' hc' => hsat c' (List.mem_append_left _ hc')
      have hge : satisfied E.guardGates (E.guardEncode pre args post) :=
        (E.guardLocal a _ hguard).mp hag
      exact (E.guardLocal _ _ (fun w hw => encodeE2Dual_agrees_guardEncode S E pre args post w hw)).mpr
        hge c hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4
      have hra := hsat cE2DRestF (by simp [List.mem_append, List.mem_cons])
      have h1a := hsat cE2DBind1 (by simp [List.mem_append, List.mem_cons])
      have h2a := hsat cE2DBind2 (by simp [List.mem_append, List.mem_cons])
      have hla := hsat cE2DLog   (by simp [List.mem_append, List.mem_cons])
      rcases hc4 with rfl | rfl | rfl | rfl
      · unfold Constraint.holds cE2DRestF at hra ⊢
        simp only [Expr.eval] at hra ⊢; rw [hRPre, hRPost] at hra; exact hra
      · unfold Constraint.holds cE2DBind1 at h1a ⊢
        simp only [Expr.eval] at h1a ⊢; rw [hC1Post, hC1Exp] at h1a; exact h1a
      · unfold Constraint.holds cE2DBind2 at h2a ⊢
        simp only [Expr.eval] at h2a ⊢; rw [hC2Post, hC2Exp] at h2a; exact h2a
      · unfold Constraint.holds cE2DLog at hla ⊢
        simp only [Expr.eval] at hla ⊢; rw [hLPost, hLExp] at hla; exact hla
  · intro hsat c hc
    rcases List.mem_append.mp hc with hcg | hc4
    · have hge : satisfied E.guardGates (E.guardEncode pre args post) :=
        (E.guardLocal _ _ (fun w hw => encodeE2Dual_agrees_guardEncode S E pre args post w hw)).mp
          (fun c' hc' => hsat c' (List.mem_append_left _ hc'))
      exact (E.guardLocal a _ hguard).mpr hge c hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4
      have hre := hsat cE2DRestF (by simp [List.mem_append, List.mem_cons])
      have h1e := hsat cE2DBind1 (by simp [List.mem_append, List.mem_cons])
      have h2e := hsat cE2DBind2 (by simp [List.mem_append, List.mem_cons])
      have hle := hsat cE2DLog   (by simp [List.mem_append, List.mem_cons])
      rcases hc4 with rfl | rfl | rfl | rfl
      · unfold Constraint.holds cE2DRestF at hre ⊢
        simp only [Expr.eval] at hre ⊢; rw [hRPre, hRPost]; exact hre
      · unfold Constraint.holds cE2DBind1 at h1e ⊢
        simp only [Expr.eval] at h1e ⊢; rw [hC1Post, hC1Exp]; exact h1e
      · unfold Constraint.holds cE2DBind2 at h2e ⊢
        simp only [Expr.eval] at h2e ⊢; rw [hC2Post, hC2Exp]; exact h2e
      · unfold Constraint.holds cE2DLog at hle ⊢
        simp only [Expr.eval] at hle ⊢; rw [hLPost, hLExp]; exact hle

/-! ## §3 — the dual EXTRACTOR + non-vacuity teeth. -/

/-- **`effect2dual_extract`** — THE dual adversarial-witness extractor. An ARBITRARY assignment `a` that
satisfies the dual effect circuit and is `PIBindsDigestsDual`-pinned forces `E.apex pre args post` —
BOTH touched components and the log determined, the adversary keeping the un-gated roots and `w ≥ 74`. -/
theorem effect2dual_extract {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args)
    (hRestF : RestFrameDecodes2Dual S E) (hLog : logHashInjective S.LH)
    (hGuard : GuardDecodes2Dual E)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hsat : satisfiedE2Dual S E a)
    (hPI : PIBindsDigestsDual S E pre args post a) :
    E.apex pre args post :=
  effect2dual_circuit_full_sound S E hRestF hLog hGuard pre args post
    ((satisfiedE2Dual_of_PIBindsDigestsDual S E pre args post a hPI).mp hsat)

/-- A forged COMPONENT-1 (the first touched component violates its bind/postClause) is refuted. -/
theorem effect2dual_extract_rejects_wrong_component1 {St Args : Type} (S : Surface2)
    (E : EffectSpec2Dual St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsDual S E pre args post a)
    (htamper : ¬ E.active1.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Dual S E a := by
  intro hsat
  exact effectCircuit2Dual_rejects_wrong_component1 S E pre args post htamper
    ((satisfiedE2Dual_of_PIBindsDigestsDual S E pre args post a hPI).mp hsat)

/-- A forged COMPONENT-2 (the second touched component) is refuted. -/
theorem effect2dual_extract_rejects_wrong_component2 {St Args : Type} (S : Surface2)
    (E : EffectSpec2Dual St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsDual S E pre args post a)
    (htamper : ¬ E.active2.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Dual S E a := by
  intro hsat
  exact effectCircuit2Dual_rejects_wrong_component2 S E pre args post htamper
    ((satisfiedE2Dual_of_PIBindsDigestsDual S E pre args post a hPI).mp hsat)

/-- A forged LOG is refuted (`logHashInjective`). -/
theorem effect2dual_extract_rejects_log_forge {St Args : Type} (S : Surface2)
    (E : EffectSpec2Dual St Args) (hLog : logHashInjective S.LH)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsDual S E pre args post a)
    (htamper : E.view.getLog post ≠ E.postLog pre args) :
    ¬ satisfiedE2Dual S E a := by
  intro hsat
  exact effectCircuit2Dual_rejects_log_forge S E hLog pre args post htamper
    ((satisfiedE2Dual_of_PIBindsDigestsDual S E pre args post a hPI).mp hsat)

/-! ## §4 — per-effect instantiation: `cellDestroyA` (lifecycle + death-cert) and `heapWriteA`
(cell record + heap). -/

/-- **`cellDestroyA_extract`** — adversarial extraction for `cellDestroy` (a dual write: the lifecycle
component AND the death-certificate component). A satisfying PI-bound trace forces the COMPLETE
`CellDestroySpec` — a forged destruction (wrong lifecycle OR wrong cert) is refuted. -/
theorem cellDestroyA_extract
    (S : Surface2) (DLif : (CellId → Nat) → ℤ) (hDLif : Function.Injective DLif)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (hRest : Inst.CellDestroyA.RestIffNoLifecycleDeathCert S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.CellDestroyA.CellDestroyArgs) (s' : RecChainedState)
    (a : Assignment)
    (hsat : satisfiedE2Dual S (Inst.CellDestroyA.cellDestroyE DLif hDLif DDC hDDC) a)
    (hPI : PIBindsDigestsDual S (Inst.CellDestroyA.cellDestroyE DLif hDLif DDC hDDC) s args s' a) :
    Spec.CellLifecycle.CellDestroySpec s args.actor args.cell args.certHash s' :=
  (Inst.CellDestroyA.apex_iff_cellDestroySpec DLif hDLif DDC hDDC s args s').mp
    (effect2dual_extract S (Inst.CellDestroyA.cellDestroyE DLif hDLif DDC hDDC)
      (Inst.CellDestroyA.cellDestroyRestFrameDecodes S DLif hDLif DDC hDDC hRest) hLog
      (Inst.CellDestroyA.cellDestroyGuardDecodes DLif hDLif DDC hDDC) s args s' a hsat hPI)

/-- **`heapWriteA_extract`** — adversarial extraction for `heapWrite` (a dual write: the cell record
component AND the heap component). A satisfying PI-bound trace forces the COMPLETE `HeapWriteSpec`. -/
theorem heapWriteA_extract
    (S : Surface2) (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DH : (CellId → Heap.FeltHeap) → ℤ) (hDH : Function.Injective DH)
    (hRest : Inst.HeapWriteA.RestIffNoCellHeaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.HeapWriteA.HeapWriteArgs) (s' : RecChainedState)
    (a : Assignment)
    (hsat : satisfiedE2Dual S (Inst.HeapWriteA.heapWriteE DCell hDCell DH hDH) a)
    (hPI : PIBindsDigestsDual S (Inst.HeapWriteA.heapWriteE DCell hDCell DH hDH) s args s' a) :
    Spec.HeapWrite.HeapWriteSpec s args.actor args.target args.addr args.value args.newRoot s' :=
  (Inst.HeapWriteA.apex_iff_heapWriteSpec DCell hDCell DH hDH s args s').mp
    (effect2dual_extract S (Inst.HeapWriteA.heapWriteE DCell hDCell DH hDH)
      (Inst.HeapWriteA.heapWriteRestFrameDecodes S DCell hDCell DH hDH hRest) hLog
      (Inst.HeapWriteA.heapWriteGuardDecodes DCell hDCell DH hDH) s args s' a hsat hPI)

/-! ## §4b — CONCRETE non-vacuity: the dual gates REJECT a tampered wire (decidable `#guard`s, not `rfl`
on a trivial Prop). A forged component-1 (wire `68 ≠ 69`), component-2 (`70 ≠ 71`), rest (`66 ≠ 67`) or
log (`72 ≠ 73`) FAILS its EQ gate — so the dual extractor's teeth really CONSTRAIN. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

/- comp-1 bind gate rejects a forged first touched component. -/
#guard decide (¬ cE2DBind1.holds (fun w => if w = vE2DComp1Post then 1 else 0))
/- comp-2 bind gate rejects a forged second touched component. -/
#guard decide (¬ cE2DBind2.holds (fun w => if w = vE2DComp2Post then 1 else 0))
/- rest-frame gate rejects a tampered rest digest. -/
#guard decide (¬ cE2DRestF.holds (fun w => if w = vE2DRestPre then 7 else 0))
/- log gate rejects a forged log digest. -/
#guard decide (¬ cE2DLog.holds (fun w => if w = vE2DLogPost then 5 else 0))
/- and the all-equal (honest-shaped) assignment is ACCEPTED by all four (not vacuously false). -/
#guard decide (cE2DBind1.holds (fun _ => 0) ∧ cE2DBind2.holds (fun _ => 0)
  ∧ cE2DRestF.holds (fun _ => 0) ∧ cE2DLog.holds (fun _ => 0))

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms encodeE2Dual_PIBindsDigestsDual
#assert_axioms satisfiedE2Dual_of_PIBindsDigestsDual
#assert_axioms effect2dual_extract
#assert_axioms effect2dual_extract_rejects_wrong_component1
#assert_axioms effect2dual_extract_rejects_wrong_component2
#assert_axioms effect2dual_extract_rejects_log_forge
#assert_axioms cellDestroyA_extract
#assert_axioms heapWriteA_extract

end Dregg2.Circuit.WitnessExtractDual
