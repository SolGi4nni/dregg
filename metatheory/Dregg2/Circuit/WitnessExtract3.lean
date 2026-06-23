/-
# Dregg2.Circuit.WitnessExtract3 — the adversarial-witness EXTRACTOR for the TRIPLE-component v2 effects.

`WitnessExtract.effect2_extract` closes hostile-witness extraction for the SINGLE-active-component v2
framework (`EffectCommit2`); `WitnessExtractDual.effect2dual_extract` for the DUAL framework
(`EffectCommit2Dual`). Some effects touch THREE kernel components at once and route through the TRIPLE
framework (`EffectCommit3`, `effect2triple_circuit_full_sound`): `createCellA` (accounts + bal +
born-empty side tables). Its full-state circuit is
`E.guardGates ++ [cE2TRestF, cE2TBind1, cE2TBind2, cE2TBind3, cE2TLog]` — six EQ gates reading only the
ten digest wires `66..75` (rest 66/67, comp1 68/69, comp2 70/71, comp3 72/73, log 74/75) plus the guard
region.

This module is the EXACT triple analog of `WitnessExtractDual`: `PIBindsDigestsTriple` pins those ten
wires + guard region; `satisfiedE2Triple_of_PIBindsDigestsTriple` transports satisfaction;
`effect2triple_extract` forces the apex from an ARBITRARY PI-bound satisfying trace (adversary keeps the
un-gated roots `64/65` and every `w ≥ 76`); the `rejects` teeth refute a forged component-1 / -2 / -3 /
log.

ADDITIVE: imports `EffectCommit3` + the one triple Inst effect (`createCellA`); edits none.
-/
import Dregg2.Circuit.EffectCommit3
import Dregg2.Circuit.Inst.createCellA

namespace Dregg2.Circuit.WitnessExtract3

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.EffectCommit3
open Dregg2.Circuit.BornEmptyCommit (BornEmptySideTables)
open Dregg2.Circuit.Spec.AccountGrowth (CreateCellSpec)
open Dregg2.Exec (RecChainedState CellId AssetId Value)
open Dregg2.Substrate

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the public-input binding on the triple circuit's ten digest wires + guard region. -/

/-- **`PIBindsDigestsTriple S E pre args post a`** — the verifier's public-input obligation for the
triple circuit: `a` agrees with `encodeE2Triple S E pre args post` on the guard region `w < guardWidth`
and the ten rest/comp1/comp2/comp3/log digest wires `66 .. 75`. STRICTLY WEAKER than
`a = encodeE2Triple …`. -/
def PIBindsDigestsTriple {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment) : Prop :=
  (∀ w, w < E.guardWidth → a w = E.guardEncode pre args post w)
  ∧ a vE2TRestPre   = encodeE2Triple S E pre args post vE2TRestPre
  ∧ a vE2TRestPost  = encodeE2Triple S E pre args post vE2TRestPost
  ∧ a vE2TComp1Post = encodeE2Triple S E pre args post vE2TComp1Post
  ∧ a vE2TComp1Exp  = encodeE2Triple S E pre args post vE2TComp1Exp
  ∧ a vE2TComp2Post = encodeE2Triple S E pre args post vE2TComp2Post
  ∧ a vE2TComp2Exp  = encodeE2Triple S E pre args post vE2TComp2Exp
  ∧ a vE2TComp3Post = encodeE2Triple S E pre args post vE2TComp3Post
  ∧ a vE2TComp3Exp  = encodeE2Triple S E pre args post vE2TComp3Exp
  ∧ a vE2TLogPost   = encodeE2Triple S E pre args post vE2TLogPost
  ∧ a vE2TLogExp    = encodeE2Triple S E pre args post vE2TLogExp

theorem encodeE2Triple_PIBindsDigestsTriple {St Args : Type} (S : Surface2)
    (E : EffectSpec2Triple St Args) (pre : St) (args : Args) (post : St) :
    PIBindsDigestsTriple S E pre args post (encodeE2Triple S E pre args post) :=
  ⟨fun w hw => encodeE2Triple_agrees_guardEncode S E pre args post w hw,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §2 — locality: a PI-bound `a` satisfies the triple circuit IFF the honest encoding does. -/

theorem satisfiedE2Triple_of_PIBindsDigestsTriple {St Args : Type} (S : Surface2)
    (E : EffectSpec2Triple St Args) (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsTriple S E pre args post a) :
    satisfiedE2Triple S E a ↔ satisfiedE2Triple S E (encodeE2Triple S E pre args post) := by
  obtain ⟨hguard, hRPre, hRPost, hC1Post, hC1Exp, hC2Post, hC2Exp, hC3Post, hC3Exp, hLPost, hLExp⟩ := hPI
  unfold satisfiedE2Triple effectCircuit2Triple
  constructor
  · intro hsat c hc
    rcases List.mem_append.mp hc with hcg | hc5
    · have hag : satisfied E.guardGates a := fun c' hc' => hsat c' (List.mem_append_left _ hc')
      have hge : satisfied E.guardGates (E.guardEncode pre args post) :=
        (E.guardLocal a _ hguard).mp hag
      exact (E.guardLocal _ _ (fun w hw => encodeE2Triple_agrees_guardEncode S E pre args post w hw)).mpr
        hge c hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc5
      have hra := hsat cE2TRestF (by simp [List.mem_append, List.mem_cons])
      have h1a := hsat cE2TBind1 (by simp [List.mem_append, List.mem_cons])
      have h2a := hsat cE2TBind2 (by simp [List.mem_append, List.mem_cons])
      have h3a := hsat cE2TBind3 (by simp [List.mem_append, List.mem_cons])
      have hla := hsat cE2TLog   (by simp [List.mem_append, List.mem_cons])
      rcases hc5 with rfl | rfl | rfl | rfl | rfl
      · unfold Constraint.holds cE2TRestF at hra ⊢
        simp only [Expr.eval] at hra ⊢; rw [hRPre, hRPost] at hra; exact hra
      · unfold Constraint.holds cE2TBind1 at h1a ⊢
        simp only [Expr.eval] at h1a ⊢; rw [hC1Post, hC1Exp] at h1a; exact h1a
      · unfold Constraint.holds cE2TBind2 at h2a ⊢
        simp only [Expr.eval] at h2a ⊢; rw [hC2Post, hC2Exp] at h2a; exact h2a
      · unfold Constraint.holds cE2TBind3 at h3a ⊢
        simp only [Expr.eval] at h3a ⊢; rw [hC3Post, hC3Exp] at h3a; exact h3a
      · unfold Constraint.holds cE2TLog at hla ⊢
        simp only [Expr.eval] at hla ⊢; rw [hLPost, hLExp] at hla; exact hla
  · intro hsat c hc
    rcases List.mem_append.mp hc with hcg | hc5
    · have hge : satisfied E.guardGates (E.guardEncode pre args post) :=
        (E.guardLocal _ _ (fun w hw => encodeE2Triple_agrees_guardEncode S E pre args post w hw)).mp
          (fun c' hc' => hsat c' (List.mem_append_left _ hc'))
      exact (E.guardLocal a _ hguard).mpr hge c hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc5
      have hre := hsat cE2TRestF (by simp [List.mem_append, List.mem_cons])
      have h1e := hsat cE2TBind1 (by simp [List.mem_append, List.mem_cons])
      have h2e := hsat cE2TBind2 (by simp [List.mem_append, List.mem_cons])
      have h3e := hsat cE2TBind3 (by simp [List.mem_append, List.mem_cons])
      have hle := hsat cE2TLog   (by simp [List.mem_append, List.mem_cons])
      rcases hc5 with rfl | rfl | rfl | rfl | rfl
      · unfold Constraint.holds cE2TRestF at hre ⊢
        simp only [Expr.eval] at hre ⊢; rw [hRPre, hRPost]; exact hre
      · unfold Constraint.holds cE2TBind1 at h1e ⊢
        simp only [Expr.eval] at h1e ⊢; rw [hC1Post, hC1Exp]; exact h1e
      · unfold Constraint.holds cE2TBind2 at h2e ⊢
        simp only [Expr.eval] at h2e ⊢; rw [hC2Post, hC2Exp]; exact h2e
      · unfold Constraint.holds cE2TBind3 at h3e ⊢
        simp only [Expr.eval] at h3e ⊢; rw [hC3Post, hC3Exp]; exact h3e
      · unfold Constraint.holds cE2TLog at hle ⊢
        simp only [Expr.eval] at hle ⊢; rw [hLPost, hLExp]; exact hle

/-! ## §3 — the triple EXTRACTOR + non-vacuity teeth. -/

/-- **`effect2triple_extract`** — THE triple adversarial-witness extractor. An ARBITRARY assignment `a`
that satisfies the triple effect circuit and is `PIBindsDigestsTriple`-pinned forces
`E.apex pre args post` — ALL THREE touched components and the log determined, the adversary keeping the
un-gated roots and `w ≥ 76`. -/
theorem effect2triple_extract {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args)
    (hRestF : RestFrameDecodes2Triple S E) (hLog : logHashInjective S.LH)
    (hGuard : GuardDecodes2Triple E)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hsat : satisfiedE2Triple S E a)
    (hPI : PIBindsDigestsTriple S E pre args post a) :
    E.apex pre args post :=
  effect2triple_circuit_full_sound S E hRestF hLog hGuard pre args post
    ((satisfiedE2Triple_of_PIBindsDigestsTriple S E pre args post a hPI).mp hsat)

/-- A forged COMPONENT-1 (the first touched component) is refuted. -/
theorem effect2triple_extract_rejects_wrong_component1 {St Args : Type} (S : Surface2)
    (E : EffectSpec2Triple St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsTriple S E pre args post a)
    (htamper : ¬ E.active1.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Triple S E a := by
  intro hsat
  exact effectCircuit2Triple_rejects_wrong_component1 S E pre args post htamper
    ((satisfiedE2Triple_of_PIBindsDigestsTriple S E pre args post a hPI).mp hsat)

/-- A forged COMPONENT-2 (the second touched component) is refuted. -/
theorem effect2triple_extract_rejects_wrong_component2 {St Args : Type} (S : Surface2)
    (E : EffectSpec2Triple St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsTriple S E pre args post a)
    (htamper : ¬ E.active2.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Triple S E a := by
  intro hsat
  exact effectCircuit2Triple_rejects_wrong_component2 S E pre args post htamper
    ((satisfiedE2Triple_of_PIBindsDigestsTriple S E pre args post a hPI).mp hsat)

/-- A forged COMPONENT-3 (the third touched component) is refuted. -/
theorem effect2triple_extract_rejects_wrong_component3 {St Args : Type} (S : Surface2)
    (E : EffectSpec2Triple St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsTriple S E pre args post a)
    (htamper : ¬ E.active3.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Triple S E a := by
  intro hsat
  exact effectCircuit2Triple_rejects_wrong_component3 S E pre args post htamper
    ((satisfiedE2Triple_of_PIBindsDigestsTriple S E pre args post a hPI).mp hsat)

/-- A forged LOG is refuted (`logHashInjective`). -/
theorem effect2triple_extract_rejects_log_forge {St Args : Type} (S : Surface2)
    (E : EffectSpec2Triple St Args) (hLog : logHashInjective S.LH)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsTriple S E pre args post a)
    (htamper : E.view.getLog post ≠ E.postLog pre args) :
    ¬ satisfiedE2Triple S E a := by
  intro hsat
  exact effectCircuit2Triple_rejects_log_forge S E hLog pre args post htamper
    ((satisfiedE2Triple_of_PIBindsDigestsTriple S E pre args post a hPI).mp hsat)

/-! ## §4 — per-effect instantiation: `createCellA` (accounts + bal + born-empty side tables). -/

/-- **`createCellA_extract`** — adversarial extraction for `createCell` (a triple write: the `accounts`
growth, the `bal` reset-at-newCell, AND the born-empty side-table component). A satisfying PI-bound trace
forces the COMPLETE `CreateCellSpec` — a forged creation (wrong accounts / bal / born-empty side) is
refuted. -/
theorem createCellA_extract
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : Inst.CreateCellA.RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.CreateCellA.CreateCellArgs) (s' : RecChainedState)
    (a : Assignment)
    (hsat : satisfiedE2Triple S (Inst.CreateCellA.createCellE LE cN hN hLE DBal hDBal DSide hDSide) a)
    (hPI : PIBindsDigestsTriple S (Inst.CreateCellA.createCellE LE cN hN hLE DBal hDBal DSide hDSide)
      s args s' a) :
    CreateCellSpec s args.actor args.newCell s' :=
  (Inst.CreateCellA.apex_iff_createCellSpec LE cN hN hLE DBal hDBal DSide hDSide s args s').mp
    (effect2triple_extract S (Inst.CreateCellA.createCellE LE cN hN hLE DBal hDBal DSide hDSide)
      (Inst.CreateCellA.createCellRestFrameDecodes S LE cN hN hLE DBal hDBal DSide hDSide hRest) hLog
      (Inst.CreateCellA.createCellGuardDecodes LE cN hN hLE DBal hDBal DSide hDSide) s args s' a hsat hPI)

/-! ## §4b — CONCRETE non-vacuity: the triple gates REJECT a tampered wire (decidable `#guard`s, not
`rfl` on a trivial Prop). A forged component-1 (`68 ≠ 69`), -2 (`70 ≠ 71`), -3 (`72 ≠ 73`), rest
(`66 ≠ 67`) or log (`74 ≠ 75`) FAILS its EQ gate — so the triple extractor's teeth really CONSTRAIN. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

/- comp-1 bind gate rejects a forged first touched component. -/
#guard decide (¬ cE2TBind1.holds (fun w => if w = vE2TComp1Post then 1 else 0))
/- comp-2 bind gate rejects a forged second touched component. -/
#guard decide (¬ cE2TBind2.holds (fun w => if w = vE2TComp2Post then 1 else 0))
/- comp-3 bind gate rejects a forged third touched component. -/
#guard decide (¬ cE2TBind3.holds (fun w => if w = vE2TComp3Post then 1 else 0))
/- rest-frame gate rejects a tampered rest digest. -/
#guard decide (¬ cE2TRestF.holds (fun w => if w = vE2TRestPre then 7 else 0))
/- log gate rejects a forged log digest. -/
#guard decide (¬ cE2TLog.holds (fun w => if w = vE2TLogPost then 5 else 0))
/- and the all-equal (honest-shaped) assignment is ACCEPTED by all five (not vacuously false). -/
#guard decide (cE2TBind1.holds (fun _ => 0) ∧ cE2TBind2.holds (fun _ => 0)
  ∧ cE2TBind3.holds (fun _ => 0) ∧ cE2TRestF.holds (fun _ => 0) ∧ cE2TLog.holds (fun _ => 0))

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms encodeE2Triple_PIBindsDigestsTriple
#assert_axioms satisfiedE2Triple_of_PIBindsDigestsTriple
#assert_axioms effect2triple_extract
#assert_axioms effect2triple_extract_rejects_wrong_component1
#assert_axioms effect2triple_extract_rejects_wrong_component2
#assert_axioms effect2triple_extract_rejects_wrong_component3
#assert_axioms effect2triple_extract_rejects_log_forge
#assert_axioms createCellA_extract

end Dregg2.Circuit.WitnessExtract3
