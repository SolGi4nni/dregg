/-
# Dregg2.Circuit.WitnessExtract5 — the adversarial-witness EXTRACTOR for the QUINT-component v2 effects.

`WitnessExtract.effect2_extract` (single), `WitnessExtractDual.effect2dual_extract` (dual) and
`WitnessExtract3.effect2triple_extract` (triple) close hostile-witness extraction for the smaller
component frameworks. Two effects touch FIVE kernel components at once and route through the QUINT
framework (`EffectCommit5`, `effect2quint_circuit_full_sound`): `spawnA` (accounts + create-leg + caps +
delegate + delegations) and `createCellFromFactoryA` (accounts + bal + cell + slotCaveats + born-empty
authority). Their full-state circuit is
`E.guardGates ++ [cE2URestF, cE2UBind1..5, cE2ULog]` — seven EQ gates reading only the fourteen digest
wires `66..79` (rest 66/67, comp1..5 68..77, log 78/79) plus the guard region.

This module is the EXACT quint analog of `WitnessExtractDual`/`WitnessExtract3`: `PIBindsDigestsQuint`
pins those fourteen wires + guard region; `satisfiedE2Quint_of_PIBindsDigestsQuint` transports
satisfaction; `effect2quint_extract` forces the apex from an ARBITRARY PI-bound satisfying trace
(adversary keeps the un-gated roots `64/65` and every `w ≥ 80`); the `rejects` teeth refute a forged
component-1..5 / log.

ADDITIVE: imports `EffectCommit5` + the two quint Inst effects; edits none.
-/
import Dregg2.Circuit.EffectCommit5
import Dregg2.Circuit.Inst.spawnA
import Dregg2.Circuit.Inst.createCellFromFactoryA

namespace Dregg2.Circuit.WitnessExtract5

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.EffectCommit5
open Dregg2.Circuit.BornEmptyCommit (SpawnCreateLeg BornEmptyAuthorityTables)
open Dregg2.Circuit.Spec.AccountGrowth (SpawnSpec)
open Dregg2.Authority (Caps Cap)
open Dregg2.Exec (RecChainedState CellId AssetId Value SlotCaveat)
open Dregg2.Substrate

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the public-input binding on the quint circuit's fourteen digest wires + guard region. -/

/-- **`PIBindsDigestsQuint S E pre args post a`** — the verifier's public-input obligation for the quint
circuit: `a` agrees with `encodeE2Quint S E pre args post` on the guard region `w < guardWidth` and the
fourteen rest/comp1..5/log digest wires `66 .. 79`. STRICTLY WEAKER than `a = encodeE2Quint …`. -/
def PIBindsDigestsQuint {St Args : Type} (S : Surface2) (E : EffectSpec2Quint St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment) : Prop :=
  (∀ w, w < E.guardWidth → a w = E.guardEncode pre args post w)
  ∧ a vE2URestPre   = encodeE2Quint S E pre args post vE2URestPre
  ∧ a vE2URestPost  = encodeE2Quint S E pre args post vE2URestPost
  ∧ a vE2UComp1Post = encodeE2Quint S E pre args post vE2UComp1Post
  ∧ a vE2UComp1Exp  = encodeE2Quint S E pre args post vE2UComp1Exp
  ∧ a vE2UComp2Post = encodeE2Quint S E pre args post vE2UComp2Post
  ∧ a vE2UComp2Exp  = encodeE2Quint S E pre args post vE2UComp2Exp
  ∧ a vE2UComp3Post = encodeE2Quint S E pre args post vE2UComp3Post
  ∧ a vE2UComp3Exp  = encodeE2Quint S E pre args post vE2UComp3Exp
  ∧ a vE2UComp4Post = encodeE2Quint S E pre args post vE2UComp4Post
  ∧ a vE2UComp4Exp  = encodeE2Quint S E pre args post vE2UComp4Exp
  ∧ a vE2UComp5Post = encodeE2Quint S E pre args post vE2UComp5Post
  ∧ a vE2UComp5Exp  = encodeE2Quint S E pre args post vE2UComp5Exp
  ∧ a vE2ULogPost   = encodeE2Quint S E pre args post vE2ULogPost
  ∧ a vE2ULogExp    = encodeE2Quint S E pre args post vE2ULogExp

theorem encodeE2Quint_PIBindsDigestsQuint {St Args : Type} (S : Surface2)
    (E : EffectSpec2Quint St Args) (pre : St) (args : Args) (post : St) :
    PIBindsDigestsQuint S E pre args post (encodeE2Quint S E pre args post) :=
  ⟨fun w hw => encodeE2Quint_agrees_guardEncode S E pre args post w hw,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §2 — locality: a PI-bound `a` satisfies the quint circuit IFF the honest encoding does. -/

theorem satisfiedE2Quint_of_PIBindsDigestsQuint {St Args : Type} (S : Surface2)
    (E : EffectSpec2Quint St Args) (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsQuint S E pre args post a) :
    satisfiedE2Quint S E a ↔ satisfiedE2Quint S E (encodeE2Quint S E pre args post) := by
  obtain ⟨hguard, hRPre, hRPost, hC1Post, hC1Exp, hC2Post, hC2Exp, hC3Post, hC3Exp,
    hC4Post, hC4Exp, hC5Post, hC5Exp, hLPost, hLExp⟩ := hPI
  unfold satisfiedE2Quint effectCircuit2Quint
  constructor
  · intro hsat c hc
    rcases List.mem_append.mp hc with hcg | hc7
    · have hag : satisfied E.guardGates a := fun c' hc' => hsat c' (List.mem_append_left _ hc')
      have hge : satisfied E.guardGates (E.guardEncode pre args post) :=
        (E.guardLocal a _ hguard).mp hag
      exact (E.guardLocal _ _ (fun w hw => encodeE2Quint_agrees_guardEncode S E pre args post w hw)).mpr
        hge c hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc7
      have hra := hsat cE2URestF (by simp [List.mem_append, List.mem_cons])
      have h1a := hsat cE2UBind1 (by simp [List.mem_append, List.mem_cons])
      have h2a := hsat cE2UBind2 (by simp [List.mem_append, List.mem_cons])
      have h3a := hsat cE2UBind3 (by simp [List.mem_append, List.mem_cons])
      have h4a := hsat cE2UBind4 (by simp [List.mem_append, List.mem_cons])
      have h5a := hsat cE2UBind5 (by simp [List.mem_append, List.mem_cons])
      have hla := hsat cE2ULog   (by simp [List.mem_append, List.mem_cons])
      rcases hc7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · unfold Constraint.holds cE2URestF at hra ⊢
        simp only [Expr.eval] at hra ⊢; rw [hRPre, hRPost] at hra; exact hra
      · unfold Constraint.holds cE2UBind1 at h1a ⊢
        simp only [Expr.eval] at h1a ⊢; rw [hC1Post, hC1Exp] at h1a; exact h1a
      · unfold Constraint.holds cE2UBind2 at h2a ⊢
        simp only [Expr.eval] at h2a ⊢; rw [hC2Post, hC2Exp] at h2a; exact h2a
      · unfold Constraint.holds cE2UBind3 at h3a ⊢
        simp only [Expr.eval] at h3a ⊢; rw [hC3Post, hC3Exp] at h3a; exact h3a
      · unfold Constraint.holds cE2UBind4 at h4a ⊢
        simp only [Expr.eval] at h4a ⊢; rw [hC4Post, hC4Exp] at h4a; exact h4a
      · unfold Constraint.holds cE2UBind5 at h5a ⊢
        simp only [Expr.eval] at h5a ⊢; rw [hC5Post, hC5Exp] at h5a; exact h5a
      · unfold Constraint.holds cE2ULog at hla ⊢
        simp only [Expr.eval] at hla ⊢; rw [hLPost, hLExp] at hla; exact hla
  · intro hsat c hc
    rcases List.mem_append.mp hc with hcg | hc7
    · have hge : satisfied E.guardGates (E.guardEncode pre args post) :=
        (E.guardLocal _ _ (fun w hw => encodeE2Quint_agrees_guardEncode S E pre args post w hw)).mp
          (fun c' hc' => hsat c' (List.mem_append_left _ hc'))
      exact (E.guardLocal a _ hguard).mpr hge c hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc7
      have hre := hsat cE2URestF (by simp [List.mem_append, List.mem_cons])
      have h1e := hsat cE2UBind1 (by simp [List.mem_append, List.mem_cons])
      have h2e := hsat cE2UBind2 (by simp [List.mem_append, List.mem_cons])
      have h3e := hsat cE2UBind3 (by simp [List.mem_append, List.mem_cons])
      have h4e := hsat cE2UBind4 (by simp [List.mem_append, List.mem_cons])
      have h5e := hsat cE2UBind5 (by simp [List.mem_append, List.mem_cons])
      have hle := hsat cE2ULog   (by simp [List.mem_append, List.mem_cons])
      rcases hc7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · unfold Constraint.holds cE2URestF at hre ⊢
        simp only [Expr.eval] at hre ⊢; rw [hRPre, hRPost]; exact hre
      · unfold Constraint.holds cE2UBind1 at h1e ⊢
        simp only [Expr.eval] at h1e ⊢; rw [hC1Post, hC1Exp]; exact h1e
      · unfold Constraint.holds cE2UBind2 at h2e ⊢
        simp only [Expr.eval] at h2e ⊢; rw [hC2Post, hC2Exp]; exact h2e
      · unfold Constraint.holds cE2UBind3 at h3e ⊢
        simp only [Expr.eval] at h3e ⊢; rw [hC3Post, hC3Exp]; exact h3e
      · unfold Constraint.holds cE2UBind4 at h4e ⊢
        simp only [Expr.eval] at h4e ⊢; rw [hC4Post, hC4Exp]; exact h4e
      · unfold Constraint.holds cE2UBind5 at h5e ⊢
        simp only [Expr.eval] at h5e ⊢; rw [hC5Post, hC5Exp]; exact h5e
      · unfold Constraint.holds cE2ULog at hle ⊢
        simp only [Expr.eval] at hle ⊢; rw [hLPost, hLExp]; exact hle

/-! ## §3 — the quint EXTRACTOR + non-vacuity teeth. -/

/-- **`effect2quint_extract`** — THE quint adversarial-witness extractor. An ARBITRARY assignment `a`
that satisfies the quint effect circuit and is `PIBindsDigestsQuint`-pinned forces
`E.apex pre args post` — ALL FIVE touched components and the log determined, the adversary keeping the
un-gated roots and `w ≥ 80`. -/
theorem effect2quint_extract {St Args : Type} (S : Surface2) (E : EffectSpec2Quint St Args)
    (hRestF : RestFrameDecodes2Quint S E) (hLog : logHashInjective S.LH)
    (hGuard : GuardDecodes2Quint E)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hsat : satisfiedE2Quint S E a)
    (hPI : PIBindsDigestsQuint S E pre args post a) :
    E.apex pre args post :=
  effect2quint_circuit_full_sound S E hRestF hLog hGuard pre args post
    ((satisfiedE2Quint_of_PIBindsDigestsQuint S E pre args post a hPI).mp hsat)

/-- A forged COMPONENT-1 is refuted. -/
theorem effect2quint_extract_rejects_wrong_component1 {St Args : Type} (S : Surface2)
    (E : EffectSpec2Quint St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsQuint S E pre args post a)
    (htamper : ¬ E.active1.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quint S E a := by
  intro hsat
  exact effectCircuit2Quint_rejects_wrong_component1 S E pre args post htamper
    ((satisfiedE2Quint_of_PIBindsDigestsQuint S E pre args post a hPI).mp hsat)

/-- A forged COMPONENT-2 is refuted. -/
theorem effect2quint_extract_rejects_wrong_component2 {St Args : Type} (S : Surface2)
    (E : EffectSpec2Quint St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsQuint S E pre args post a)
    (htamper : ¬ E.active2.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quint S E a := by
  intro hsat
  exact effectCircuit2Quint_rejects_wrong_component2 S E pre args post htamper
    ((satisfiedE2Quint_of_PIBindsDigestsQuint S E pre args post a hPI).mp hsat)

/-- A forged COMPONENT-3 is refuted. -/
theorem effect2quint_extract_rejects_wrong_component3 {St Args : Type} (S : Surface2)
    (E : EffectSpec2Quint St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsQuint S E pre args post a)
    (htamper : ¬ E.active3.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quint S E a := by
  intro hsat
  exact effectCircuit2Quint_rejects_wrong_component3 S E pre args post htamper
    ((satisfiedE2Quint_of_PIBindsDigestsQuint S E pre args post a hPI).mp hsat)

/-- A forged COMPONENT-4 is refuted. -/
theorem effect2quint_extract_rejects_wrong_component4 {St Args : Type} (S : Surface2)
    (E : EffectSpec2Quint St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsQuint S E pre args post a)
    (htamper : ¬ E.active4.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quint S E a := by
  intro hsat
  exact effectCircuit2Quint_rejects_wrong_component4 S E pre args post htamper
    ((satisfiedE2Quint_of_PIBindsDigestsQuint S E pre args post a hPI).mp hsat)

/-- A forged COMPONENT-5 is refuted. -/
theorem effect2quint_extract_rejects_wrong_component5 {St Args : Type} (S : Surface2)
    (E : EffectSpec2Quint St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsQuint S E pre args post a)
    (htamper : ¬ E.active5.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quint S E a := by
  intro hsat
  exact effectCircuit2Quint_rejects_wrong_component5 S E pre args post htamper
    ((satisfiedE2Quint_of_PIBindsDigestsQuint S E pre args post a hPI).mp hsat)

/-- A forged LOG is refuted (`logHashInjective`). -/
theorem effect2quint_extract_rejects_log_forge {St Args : Type} (S : Surface2)
    (E : EffectSpec2Quint St Args) (hLog : logHashInjective S.LH)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsQuint S E pre args post a)
    (htamper : E.view.getLog post ≠ E.postLog pre args) :
    ¬ satisfiedE2Quint S E a := by
  intro hsat
  exact effectCircuit2Quint_rejects_log_forge S E hLog pre args post htamper
    ((satisfiedE2Quint_of_PIBindsDigestsQuint S E pre args post a hPI).mp hsat)

/-! ## §4 — per-effect instantiation: `spawnA` (accounts + create-leg + caps + delegate + delegations)
and `createCellFromFactoryA` (accounts + bal + cell + slotCaveats + born-empty authority). -/

/-- **`spawnA_extract`** — adversarial extraction for `spawn` (a quint write: account growth, the
create-leg, AND the full authority handoff — caps/delegate/delegations). A satisfying PI-bound trace
forces the COMPLETE `SpawnSpec` — a forged spawn (wrong account / leg / caps / delegate / delegations) is
refuted. -/
theorem spawnA_extract
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : Inst.SpawnA.RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.SpawnA.SpawnArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2Quint S
      (Inst.SpawnA.spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) a)
    (hPI : PIBindsDigestsQuint S
      (Inst.SpawnA.spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) s args s' a) :
    SpawnSpec s args.actor args.child args.target s' :=
  (Inst.SpawnA.apex_iff_spawnSpec LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s').mp
    (effect2quint_extract S
      (Inst.SpawnA.spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
      (Inst.SpawnA.spawnRestFrameDecodes S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
        hRest) hLog
      (Inst.SpawnA.spawnGuardDecodes LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
      s args s' a hsat hPI)

/-- **`createCellFromFactoryA_extract`** — adversarial extraction for `createCellFromFactory` (a quint
write: accounts + bal + cell + slotCaveats + born-empty authority). A satisfying PI-bound trace forces
the COMPLETE `CreateFromFactoryCircuitSpec` — a forged factory install (wrong cell / caveats / authority)
is refuted. -/
theorem createCellFromFactoryA_extract
    (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRest : Inst.CreateCellFromFactoryA.RestIffNoFactoryTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.CreateCellFromFactoryA.CreateFromFactoryArgs) (s' : RecChainedState)
    (a : Assignment)
    (hsat : satisfiedE2Quint S
      (Inst.CreateCellFromFactoryA.createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC
        DAuth hDAuth) a)
    (hPI : PIBindsDigestsQuint S
      (Inst.CreateCellFromFactoryA.createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC
        DAuth hDAuth) s args s' a) :
    Inst.CreateCellFromFactoryA.CreateFromFactoryCircuitSpec s args.actor args.newCell args.vk s' :=
  (Inst.CreateCellFromFactoryA.apex_iff_createFromFactoryCircuitSpec LE cN hN hLE DBal hDBal DCell hDCell
      DSC hDSC DAuth hDAuth s args s').mp
    (effect2quint_extract S
      (Inst.CreateCellFromFactoryA.createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC
        DAuth hDAuth)
      (Inst.CreateCellFromFactoryA.createFromFactoryRestFrameDecodes S LE cN hN hLE DBal hDBal DCell
        hDCell DSC hDSC DAuth hDAuth hRest) hLog
      (Inst.CreateCellFromFactoryA.createFromFactoryGuardDecodes LE cN hN hLE DBal hDBal DCell hDCell
        DSC hDSC DAuth hDAuth) s args s' a hsat hPI)

/-! ## §4b — CONCRETE non-vacuity: the quint gates REJECT a tampered wire (decidable `#guard`s). A forged
component-1..5 (`68≠69` .. `76≠77`), rest (`66≠67`) or log (`78≠79`) FAILS its EQ gate. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

#guard decide (¬ cE2UBind1.holds (fun w => if w = vE2UComp1Post then 1 else 0))
#guard decide (¬ cE2UBind2.holds (fun w => if w = vE2UComp2Post then 1 else 0))
#guard decide (¬ cE2UBind3.holds (fun w => if w = vE2UComp3Post then 1 else 0))
#guard decide (¬ cE2UBind4.holds (fun w => if w = vE2UComp4Post then 1 else 0))
#guard decide (¬ cE2UBind5.holds (fun w => if w = vE2UComp5Post then 1 else 0))
#guard decide (¬ cE2URestF.holds (fun w => if w = vE2URestPre then 7 else 0))
#guard decide (¬ cE2ULog.holds (fun w => if w = vE2ULogPost then 5 else 0))
/- and the all-equal (honest-shaped) assignment is ACCEPTED by all seven (not vacuously false). -/
#guard decide (cE2UBind1.holds (fun _ => 0) ∧ cE2UBind2.holds (fun _ => 0)
  ∧ cE2UBind3.holds (fun _ => 0) ∧ cE2UBind4.holds (fun _ => 0) ∧ cE2UBind5.holds (fun _ => 0)
  ∧ cE2URestF.holds (fun _ => 0) ∧ cE2ULog.holds (fun _ => 0))

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms encodeE2Quint_PIBindsDigestsQuint
#assert_axioms satisfiedE2Quint_of_PIBindsDigestsQuint
#assert_axioms effect2quint_extract
#assert_axioms effect2quint_extract_rejects_wrong_component1
#assert_axioms effect2quint_extract_rejects_wrong_component2
#assert_axioms effect2quint_extract_rejects_wrong_component3
#assert_axioms effect2quint_extract_rejects_wrong_component4
#assert_axioms effect2quint_extract_rejects_wrong_component5
#assert_axioms effect2quint_extract_rejects_log_forge
#assert_axioms spawnA_extract
#assert_axioms createCellFromFactoryA_extract

end Dregg2.Circuit.WitnessExtract5
