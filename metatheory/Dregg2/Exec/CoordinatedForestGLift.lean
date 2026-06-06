/-
# Dregg2.Exec.CoordinatedForestGLift — lift coordinated/bilateral caveats to `RecChainedState`.

`FullForestAuth.GatedCaveat.holds` correctly fail-closes `.coordinated` on a **single-cell**
`execFullForestG` node — a cross-cell read cannot be faked on one cell. This module supplies the
**honest positive path** at the gated-forest layer: a **pair** of `RecChainedState` snapshots
(`BilateralForestPairG`) routed through `execCoordinatedForestG` / `execCoordinatedForestCredG`,
projecting each leg's `RecordKernelState` to the proved joint `KernelState` view for covenant
checks, then committing record-level bilateral half-edges (logs unchanged — receipt routing is
per-leg).

  * intra-cell `.coordinated` on one snapshot still fail-closes (`coordinated_intra_gate_failclosed`);
  * bilateral coordinated discharge refines `CoordinatedForestGate.execBilateralCoordinated`;
  * charter commits refine coordinated-forest commits (`charter_refines_coordinated_forest`).

Discipline: no `sorry`/`admit`/`axiom`. Keystones `#assert_axioms`-pinned.
-/
import Dregg2.Exec.CoordinatedForestGate
import Dregg2.Exec.JointCharterBridge
import Dregg2.Exec.RecordKernel

namespace Dregg2.Exec.CoordinatedForestGLift

open Dregg2.Exec
open Dregg2.Exec.CoordinatedForestGate
open Dregg2.Exec.JointCharterBridge
open Dregg2.Exec.CoordinatedCaveat
open Dregg2.Exec.CrossCaveat
open Dregg2.Exec.CrossVatCharter
open Dregg2.Exec.JointCell
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.FullForestAuth

/-! ## §1 — Honest `RecordKernelState` projection (scalar `balance`-field view). -/

/-- **`recordKernelView`** — project a record kernel to the joint-layer `KernelState` carrier.
Reads each live cell's `balance` field via `balOf`; does NOT fabricate cross-cell reads on one cell. -/
def recordKernelView (k : RecordKernelState) : KernelState :=
  { accounts := k.accounts
  , bal := fun c => balOf (k.cell c)
  , caps := k.caps }

/-- **`recChainedKernelView`** — project one `RecChainedState` leg (kernel only). -/
def recChainedKernelView (s : RecChainedState) : KernelState :=
  recordKernelView s.kernel

@[simp] theorem recordKernelView_bal (k : RecordKernelState) (c : CellId) :
    (recordKernelView k).bal c = balOf (k.cell c) := rfl

@[simp] theorem recChainedKernelView_bal (s : RecChainedState) (c : CellId) :
    (recChainedKernelView s).bal c = balOf (s.kernel.cell c) := rfl

/-! ## §2 — Record-level bilateral half-edges (lift of `JointCell.applyHalfOut/In`). -/

/-- A-side debit on the record `balance` field (the lift of `applyHalfOut`). -/
def applyRecHalfOut (k : RecordKernelState) (bt : BiTurn) : Option RecordKernelState :=
  if authorizedB k.caps { actor := bt.actorA, src := bt.srcA, dst := bt.srcA, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.amt ≤ balOf (k.cell bt.srcA) ∧ bt.srcA ∈ k.accounts then
    some { k with cell := recDebit k.cell bt.srcA bt.amt }
  else
    none

/-- B-side credit on the record `balance` field (the lift of `applyHalfIn`). -/
def applyRecHalfIn (k : RecordKernelState) (bt : BiTurn) : Option RecordKernelState :=
  if authorizedB k.caps { actor := bt.actorB, src := bt.dstB, dst := bt.dstB, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.dstB ∈ k.accounts then
    some { k with cell := recCredit k.cell bt.dstB bt.amt }
  else
    none

/-- Atomic bilateral commit on two record kernels (the lift of `jointApply`). -/
def jointApplyRec (kA kB : RecordKernelState) (bt : BiTurn) :
    Option (RecordKernelState × RecordKernelState) :=
  match applyRecHalfOut kA bt, applyRecHalfIn kB bt with
  | some A', some B' => some (A', B')
  | _, _ => none

/-! ## §3 — Bilateral routing carriers at the `RecChainedState` layer. -/

/-- **Two `RecChainedState` snapshots** — the honest routing carrier for coordinated caveats
(no cross-cell reads on a single cell). -/
structure BilateralForestPairG where
  sA : RecChainedState
  sB : RecChainedState

/-- A **coordinated bilateral forest step** — pair + equalizer payload. -/
structure BilateralForestStepG where
  pair : BilateralForestPairG
  step : BilateralStep

/-- A **credential-gated** coordinated bilateral forest step. -/
structure BilateralForestCredStepG where
  pair : BilateralForestPairG
  step : BilateralCredStep

/-- Project a credential forest step to its equalizer forest step. -/
def BilateralForestCredStepG.bilateral (s : BilateralForestCredStepG) : BilateralForestStepG :=
  { pair := s.pair, step := s.step.bilateral }

/-! ## §4 — `execCoordinatedForestG` (the production routing hook). -/

/-- **`execCoordinatedForestG`** — coordinated covenant + bilateral turn over a **pair** of
`RecChainedState` snapshots. Kernel halves commit via `jointApplyRec`; receipt logs are unchanged
(honest per-leg routing — this layer does not splice one cell's log into another). -/
def execCoordinatedForestG (g : BilateralForestStepG) : Option (RecChainedState × RecChainedState) :=
  if g.step.covenant.φ (recChainedKernelView g.pair.sA) (recChainedKernelView g.pair.sB) = true then
    match jointApplyRec g.pair.sA.kernel g.pair.sB.kernel g.step.bt with
    | some (kA', kB') =>
        some ({ kernel := kA', log := g.pair.sA.log }, { kernel := kB', log := g.pair.sB.log })
    | none => none
  else
    none

/-- **`execCoordinatedForestCredG`** — portal credentials ∧ coordinated forest equalizer. -/
def execCoordinatedForestCredG (g : BilateralForestCredStepG) :
    Option (RecChainedState × RecChainedState) :=
  if bilateralCredAdmits g.step then execCoordinatedForestG g.bilateral else none

/-! ## §5 — Projection bridge (`recordKernelView` commutes with bilateral apply). -/

theorem kernelExt_iff {A B : KernelState} :
    A = B ↔ A.accounts = B.accounts ∧ A.bal = B.bal ∧ A.caps = B.caps := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨ha, hb, hc⟩
    rcases A with ⟨a1, b1, c1⟩
    rcases B with ⟨a2, b2, c2⟩
    subst ha hb hc
    rfl

theorem balOf_recDebit (cell : CellId → Value) (src cid : CellId) (amt : ℤ) :
    balOf (recDebit cell src amt cid) =
      if cid = src then balOf (cell cid) - amt else balOf (cell cid) := by
  unfold recDebit; by_cases hc : cid = src <;> simp [hc, setBalance_balOf]

theorem balOf_recCredit (cell : CellId → Value) (dst cid : CellId) (amt : ℤ) :
    balOf (recCredit cell dst amt cid) =
      if cid = dst then balOf (cell cid) + amt else balOf (cell cid) := by
  unfold recCredit; by_cases hc : cid = dst <;> simp [hc, setBalance_balOf]

theorem recordKernelView_applyRecHalfOut {k k' : RecordKernelState} {bt : BiTurn}
    (h : applyRecHalfOut k bt = some k') :
    applyHalfOut (recordKernelView k) bt = some (recordKernelView k') := by
  unfold applyRecHalfOut at h
  split_ifs at h with hg
  · simp only [Option.some.injEq] at h
    subst h
    unfold applyHalfOut recordKernelView
    rw [if_pos hg]
    simp only [recordKernelView_bal, Option.some.injEq]
    refine (kernelExt_iff).mpr ?_
    refine ⟨rfl, ?_, rfl⟩
    funext c
    simp [balOf_recDebit]

theorem recordKernelView_applyRecHalfIn {k k' : RecordKernelState} {bt : BiTurn}
    (h : applyRecHalfIn k bt = some k') :
    applyHalfIn (recordKernelView k) bt = some (recordKernelView k') := by
  unfold applyRecHalfIn at h
  split_ifs at h with hg
  · simp only [Option.some.injEq] at h
    subst h
    unfold applyHalfIn recordKernelView
    rw [if_pos hg]
    simp only [recordKernelView_bal, Option.some.injEq]
    refine (kernelExt_iff).mpr ?_
    refine ⟨rfl, ?_, rfl⟩
    funext c
    simp [balOf_recCredit]

theorem recordKernelView_jointApplyRec {kA kB kA' kB' : RecordKernelState} {bt : BiTurn}
    (h : jointApplyRec kA kB bt = some (kA', kB')) :
    jointApply (recordKernelView kA) (recordKernelView kB) bt
      = some (recordKernelView kA', recordKernelView kB') := by
  unfold jointApplyRec jointApply at *
  rcases hoa : applyRecHalfOut kA bt with _ | kA'' <;> rw [hoa] at h
  · cases h
  · rcases hib : applyRecHalfIn kB bt with _ | kB'' <;> rw [hib] at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [hoa, hib, recordKernelView_applyRecHalfOut hoa, recordKernelView_applyRecHalfIn hib]

/-! ## §6 — Keystones (intra fail-closed, bilateral refinement, charter bridge). -/

/-- Re-export: `.coordinated` tier fail-closes on a single `RecChainedState` (unchanged). -/
theorem coordinated_intra_gate_failclosed (c : GatedCaveat) (s : RecChainedState)
    (h : c.tier = .coordinated) : c.holds s = false :=
  CoordinatedForestGate.coordinated_intra_gate_failclosed c s h

/-- **`coordinated_forest_refines_bilateral`** — every committed coordinated-forest step is ALSO a
committed `execBilateralCoordinated` on the projected kernel views. -/
theorem coordinated_forest_refines_bilateral (g : BilateralForestStepG)
    {sA' sB' : RecChainedState}
    (h : execCoordinatedForestG g = some (sA', sB')) :
    execBilateralCoordinated (recChainedKernelView g.pair.sA) (recChainedKernelView g.pair.sB) g.step
      = some (recChainedKernelView sA', recChainedKernelView sB') := by
  unfold execCoordinatedForestG execBilateralCoordinated dischargeCoordinated at *
  by_cases hφ : g.step.covenant.φ (recChainedKernelView g.pair.sA) (recChainedKernelView g.pair.sB) = true
  · rw [if_pos hφ] at h
    rcases hrec : jointApplyRec g.pair.sA.kernel g.pair.sB.kernel g.step.bt with _ | ⟨kA', kB'⟩ <;> rw [hrec] at h
    · exact absurd h (by simp)
    · have hview :
        recChainedKernelView sA' = recordKernelView kA' ∧
          recChainedKernelView sB' = recordKernelView kB' := by
        have hk : sA'.kernel = kA' ∧ sB'.kernel = kB' := by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, ⟨rfl, _⟩⟩ := h
          exact ⟨rfl, rfl⟩
        constructor <;> simp [recChainedKernelView, hk.1, hk.2]
      rw [jointApplyCaveated, if_pos hφ, hview.1, hview.2]
      exact recordKernelView_jointApplyRec hrec
  · rw [if_neg hφ] at h
    exact absurd h (by simp)

/-- **`coordinated_forest_joint_conserves`** — committed coordinated forest preserves the joint
scalar-total over the projected views (CG-5, via `bilateral_coordinated_sound`). -/
theorem coordinated_forest_joint_conserves (g : BilateralForestStepG)
    {sA' sB' : RecChainedState}
    (h : execCoordinatedForestG g = some (sA', sB')) :
    jointTotal (recChainedKernelView sA') (recChainedKernelView sB')
      = jointTotal (recChainedKernelView g.pair.sA) (recChainedKernelView g.pair.sB) :=
  (bilateral_coordinated_sound g.step
    (coordinated_forest_refines_bilateral g h)).1

/-- **`recordKernelView_total`** — the scalar projection matches the record `balance`-field total. -/
theorem recordKernelView_total (k : RecordKernelState) :
    total (recordKernelView k) = recTotal k := by
  simp [total, recTotal, recordKernelView]

theorem recChainedKernelView_total (s : RecChainedState) :
    total (recChainedKernelView s) = recTotal s.kernel :=
  recordKernelView_total s.kernel

/-- **`coordinated_forest_joint_recTotal_conserves`** — the SUM of record `balance`-field totals
across both legs is conserved (the CG-5 lift to `recTotal`). -/
theorem coordinated_forest_joint_recTotal_conserves (g : BilateralForestStepG)
    {sA' sB' : RecChainedState}
    (h : execCoordinatedForestG g = some (sA', sB')) :
    recTotal sA'.kernel + recTotal sB'.kernel
      = recTotal g.pair.sA.kernel + recTotal g.pair.sB.kernel := by
  have hcg5 := coordinated_forest_joint_conserves g h
  simpa [jointTotal, recChainedKernelView_total] using hcg5

/-- Credential-gated coordinated forest rejects forged credentials (reuses bilateral gate). -/
theorem coordinated_forest_cred_forged_fails (g : BilateralForestCredStepG)
    (h : bilateralCredAdmits g.step = false) :
    execCoordinatedForestCredG g = none := by
  unfold execCoordinatedForestCredG
  by_cases hc : bilateralCredAdmits g.step
  · have hadm : bilateralCredAdmits g.step = true := by simp [hc]
    rw [hadm] at h; cases h
  · simp [hc]

/-! ## §7 — Demo fixtures (`RecChainedState` legs mirroring `JointCell.sA`/`sB`). -/

def demoRecA : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

def demoRecB : RecChainedState :=
  { kernel :=
      { accounts := {7}
        cell := fun c => if c = 7 then .record [("balance", .int 20)] else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

def demoRecBhigh : RecChainedState :=
  { kernel :=
      { accounts := {7}
        cell := fun c => if c = 7 then .record [("balance", .int 200)] else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

def demoPair : BilateralForestPairG :=
  { sA := demoRecA, sB := demoRecB }

def demoPairHigh : BilateralForestPairG :=
  { sA := demoRecA, sB := demoRecBhigh }

def demoForestStep : BilateralForestStepG :=
  { pair := demoPair, step := demoStep }

def demoForestCredStep : BilateralForestCredStepG :=
  { pair := demoPair, step := demoCredStep }

def demoForestForgedCredStep : BilateralForestCredStepG :=
  { pair := demoPair
  , step := { covenant := covenantCoord, bt := goodBi, bind := demoBind
            , credA := forgedCred, credB := goodCred } }

theorem demoRec_view_eq_sA : recChainedKernelView demoRecA = sA := by
  apply (kernelExt_iff).mpr
  refine And.intro rfl (And.intro ?_ rfl)
  funext c
  simp only [recChainedKernelView, recordKernelView, demoRecA, sA, balOf]
  split_ifs <;> rfl

theorem demoRec_view_eq_sB : recChainedKernelView demoRecB = sB := by
  apply (kernelExt_iff).mpr
  refine And.intro rfl (And.intro ?_ rfl)
  funext c
  simp only [recChainedKernelView, recordKernelView, demoRecB, sB, balOf]
  split_ifs <;> rfl

theorem demoRec_view_eq_sBhigh : recChainedKernelView demoRecBhigh = sBhigh := by
  apply (kernelExt_iff).mpr
  refine And.intro rfl (And.intro ?_ rfl)
  funext c
  simp only [recChainedKernelView, recordKernelView, demoRecBhigh, sBhigh, balOf]
  split_ifs <;> rfl

/-- Covenant check fails on the high-`B` demo pair (reuses the proved `covenant` computation). -/
theorem covenant_sA_sBhigh_false : covenant sA sBhigh = false := by
  unfold covenant; decide

/-- Fail-closed when the bilateral covenant is false (honest single-pair routing). -/
theorem coordinated_forest_none_of_covenant_false (g : BilateralForestStepG)
    (hφ : g.step.covenant.φ (recChainedKernelView g.pair.sA) (recChainedKernelView g.pair.sB) = false) :
    execCoordinatedForestG g = none := by
  unfold execCoordinatedForestG; simp [hφ]

theorem demoPairHigh_covenant_false :
    demoStep.covenant.φ (recChainedKernelView demoRecA) (recChainedKernelView demoRecBhigh) = false := by
  rw [demoRec_view_eq_sA, demoRec_view_eq_sBhigh]
  exact covenant_sA_sBhigh_false

theorem demo_coordinated_forest_covenant_teeth :
    execCoordinatedForestG { pair := demoPairHigh, step := demoStep } = none :=
  coordinated_forest_none_of_covenant_false _ demoPairHigh_covenant_false

/-- **`charter_refines_coordinated_forest`** — a committed charter discharge AND a committed
`execCoordinatedForestG` on the matching `RecChainedState` pair project to the same post-states.
Forest existence on demo fixtures is `#guard`-witnessed below. -/
theorem charter_refines_coordinated_forest
    {A' B' : KernelState} {sApost sBpost : RecChainedState}
    (h : charterDischarge demoCharter sA sB 0 0 noDischarges noDischarges = some (A', B'))
    (hexec : execCoordinatedForestG
        { pair := demoPair, step := charterBilateral demoCharter } = some (sApost, sBpost)) :
    recChainedKernelView sApost = A' ∧ recChainedKernelView sBpost = B' := by
  have href := coordinated_forest_refines_bilateral { pair := demoPair, step := charterBilateral demoCharter } hexec
  have hbil := charter_refines_bilateral_coordinated demoCharter 0 0 noDischarges noDischarges h
  rw [demoPair, demoRec_view_eq_sA, demoRec_view_eq_sB] at href
  have heq : (recChainedKernelView sApost, recChainedKernelView sBpost) = (A', B') :=
    Option.some_inj.mp (href.symm.trans hbil)
  rcases Prod.ext_iff.mp heq with ⟨hA, hB⟩
  exact ⟨hA, hB⟩

/-! ## §8 — `#guard` demos. -/

#guard GatedCaveat.requiresBilateral { tier := .coordinated, check := fun _ => true }  --  true
#guard (GatedCaveat.holds { tier := .coordinated, check := fun _ => true } demoRecA) == false  --  intra fail-closed
#guard (recChainedKernelView demoRecA).bal 0 == 100  --  matches sA
#guard ((execCoordinatedForestG demoForestStep).isSome)  --  covenant + pair ⇒ commits
#guard ((execCoordinatedForestG { pair := demoPairHigh, step := demoStep }).isSome) == false  --  teeth
#guard ((execCoordinatedForestCredG demoForestCredStep).isSome)  --  creds + covenant
#guard ((execCoordinatedForestCredG demoForestForgedCredStep).isSome) == false  --  forged
#guard ((execCoordinatedForestG { pair := demoPair, step := charterBilateral demoCharter }).isSome)  --  charter⇒forest

/-! ## §9 — Axiom hygiene. -/

#assert_axioms coordinated_intra_gate_failclosed
#assert_axioms recordKernelView_applyRecHalfOut
#assert_axioms recordKernelView_applyRecHalfIn
#assert_axioms recordKernelView_jointApplyRec
#assert_axioms coordinated_forest_refines_bilateral
#assert_axioms coordinated_forest_joint_conserves
#assert_axioms recordKernelView_total
#assert_axioms coordinated_forest_joint_recTotal_conserves
#assert_axioms coordinated_forest_cred_forged_fails
#assert_axioms covenant_sA_sBhigh_false
#assert_axioms coordinated_forest_none_of_covenant_false
#assert_axioms demoPairHigh_covenant_false
#assert_axioms demo_coordinated_forest_covenant_teeth
#assert_axioms charter_refines_coordinated_forest

end Dregg2.Exec.CoordinatedForestGLift