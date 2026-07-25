/-
# Dregg2.Circuit.EffectCommit3 — the v2 GENERIC full-state circuit⟺spec framework for TRIPLE non-`cell`
components.

Gate 3: effects touching THREE non-`cell` components (typically `queues` + `bal` + `escrows` for
`queueEnqueueA` / `queueDequeueA`). Literal product of `EffectCommit2Dual` with a third bind gate.

Wire layout (`traceWidth = 76`, guard `< 64`):

  `64 preRoot · 65 postRoot · 66 restPre · 67 restPost · 68..73 comp1..3 post/exp · 74 logPost · 75 logExp`

ADDITIVE: imports `EffectCommit2Dual` (reuses `ActiveComponent`, `Surface2`, `StateView`); edits none.
-/
import Dregg2.Circuit.EffectCommit2Dual

namespace Dregg2.Circuit.EffectCommit3

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit

set_option linter.dupNamespace false

/-! ## §1 — `EffectSpec2Triple`. -/

structure EffectSpec2Triple (St Args : Type) where
  view         : StateView St
  active1      : ActiveComponent St Args
  active2      : ActiveComponent St Args
  active3      : ActiveComponent St Args
  logUpdate    : Option (St → Args → List Turn)
  restFrame    : RecordKernelState → RecordKernelState → Prop
  guardGates   : ConstraintSystem
  guardProp    : St → Args → Prop
  guardWidth   : Nat
  guardEncode  : St → Args → St → Assignment
  guardLocal   : ∀ (a b : Assignment), (∀ w, w < guardWidth → a w = b w) →
                   (satisfied guardGates a ↔ satisfied guardGates b)
  guardWidth_le : guardWidth ≤ 64

def EffectSpec2Triple.postLog {St Args : Type} (E : EffectSpec2Triple St Args) (pre : St) (args : Args) :
    List Turn :=
  match E.logUpdate with
  | none   => E.view.getLog pre
  | some f => f pre args

def EffectSpec2Triple.apex {St Args : Type} (E : EffectSpec2Triple St Args) (pre : St) (args : Args)
    (post : St) : Prop :=
  E.guardProp pre args
  ∧ E.active1.postClause pre args (E.view.toKernel post)
  ∧ E.active2.postClause pre args (E.view.toKernel post)
  ∧ E.active3.postClause pre args (E.view.toKernel post)
  ∧ E.view.getLog post = E.postLog pre args
  ∧ E.restFrame (E.view.toKernel pre) (E.view.toKernel post)

/-! ## §2 — digest wires + encoder (`traceWidth = 76`). -/

abbrev vE2TPreRoot   : Var := 64
abbrev vE2TPostRoot  : Var := 65
abbrev vE2TRestPre   : Var := 66
abbrev vE2TRestPost  : Var := 67
abbrev vE2TComp1Post : Var := 68
abbrev vE2TComp1Exp  : Var := 69
abbrev vE2TComp2Post : Var := 70
abbrev vE2TComp2Exp  : Var := 71
abbrev vE2TComp3Post : Var := 72
abbrev vE2TComp3Exp  : Var := 73
abbrev vE2TLogPost   : Var := 74
abbrev vE2TLogExp    : Var := 75

def EffectSpec2Triple.traceWidth {St Args : Type} (_E : EffectSpec2Triple St Args) : Nat := 76

def effectStateCommit2Triple {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args)
    (k : RecordKernelState) (log : List Turn) : ℤ :=
  E.active1.digest k + E.active2.digest k + E.active3.digest k + S.RH k + S.LH log

def encodeE2Triple {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args)
    (pre : St) (args : Args) (post : St) : Assignment :=
  fun w =>
    if      w = vE2TPreRoot   then
      effectStateCommit2Triple S E (E.view.toKernel pre) (E.view.getLog pre)
    else if w = vE2TPostRoot  then
      effectStateCommit2Triple S E (E.view.toKernel post) (E.view.getLog post)
    else if w = vE2TRestPre   then S.RH (E.view.toKernel pre)
    else if w = vE2TRestPost  then S.RH (E.view.toKernel post)
    else if w = vE2TComp1Post then E.active1.digest (E.view.toKernel post)
    else if w = vE2TComp1Exp  then E.active1.expected pre args
    else if w = vE2TComp2Post then E.active2.digest (E.view.toKernel post)
    else if w = vE2TComp2Exp  then E.active2.expected pre args
    else if w = vE2TComp3Post then E.active3.digest (E.view.toKernel post)
    else if w = vE2TComp3Exp  then E.active3.expected pre args
    else if w = vE2TLogPost   then S.LH (E.view.getLog post)
    else if w = vE2TLogExp    then S.LH (E.postLog pre args)
    else E.guardEncode pre args post w

theorem encodeE2Triple_agrees_guardEncode {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args)
    (pre : St) (args : Args) (post : St) (w : Var) (hw : w < E.guardWidth) :
    encodeE2Triple S E pre args post w = E.guardEncode pre args post w := by
  have hlt : w < 64 := Nat.lt_of_lt_of_le hw E.guardWidth_le
  have hn64 : w ≠ 64 := ne_of_lt hlt
  have hn65 : w ≠ 65 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 65))
  have hn66 : w ≠ 66 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 66))
  have hn67 : w ≠ 67 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 67))
  have hn68 : w ≠ 68 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 68))
  have hn69 : w ≠ 69 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 69))
  have hn70 : w ≠ 70 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 70))
  have hn71 : w ≠ 71 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 71))
  have hn72 : w ≠ 72 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 72))
  have hn73 : w ≠ 73 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 73))
  have hn74 : w ≠ 74 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 74))
  have hn75 : w ≠ 75 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 75))
  unfold encodeE2Triple
  simp only [vE2TPreRoot, vE2TPostRoot, vE2TRestPre, vE2TRestPost, vE2TComp1Post, vE2TComp1Exp,
    vE2TComp2Post, vE2TComp2Exp, vE2TComp3Post, vE2TComp3Exp, vE2TLogPost, vE2TLogExp,
    if_neg hn64, if_neg hn65, if_neg hn66, if_neg hn67, if_neg hn68, if_neg hn69, if_neg hn70,
    if_neg hn71, if_neg hn72, if_neg hn73, if_neg hn74, if_neg hn75]

macro "ec2t_lookup" : tactic =>
  `(tactic| simp [encodeE2Triple, vE2TPreRoot, vE2TPostRoot, vE2TRestPre, vE2TRestPost, vE2TComp1Post,
      vE2TComp1Exp, vE2TComp2Post, vE2TComp2Exp, vE2TComp3Post, vE2TComp3Exp, vE2TLogPost, vE2TLogExp])

section Lookups
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args) (pre : St) (args : Args)
  (post : St)

theorem enc2t_restPre :
    encodeE2Triple S E pre args post vE2TRestPre = S.RH (E.view.toKernel pre) := by ec2t_lookup
theorem enc2t_restPost :
    encodeE2Triple S E pre args post vE2TRestPost = S.RH (E.view.toKernel post) := by ec2t_lookup
theorem enc2t_comp1Post :
    encodeE2Triple S E pre args post vE2TComp1Post = E.active1.digest (E.view.toKernel post) := by ec2t_lookup
theorem enc2t_comp1Exp :
    encodeE2Triple S E pre args post vE2TComp1Exp = E.active1.expected pre args := by ec2t_lookup
theorem enc2t_comp2Post :
    encodeE2Triple S E pre args post vE2TComp2Post = E.active2.digest (E.view.toKernel post) := by ec2t_lookup
theorem enc2t_comp2Exp :
    encodeE2Triple S E pre args post vE2TComp2Exp = E.active2.expected pre args := by ec2t_lookup
theorem enc2t_comp3Post :
    encodeE2Triple S E pre args post vE2TComp3Post = E.active3.digest (E.view.toKernel post) := by ec2t_lookup
theorem enc2t_comp3Exp :
    encodeE2Triple S E pre args post vE2TComp3Exp = E.active3.expected pre args := by ec2t_lookup
theorem enc2t_logPost :
    encodeE2Triple S E pre args post vE2TLogPost = S.LH (E.view.getLog post) := by ec2t_lookup
theorem enc2t_logExp :
    encodeE2Triple S E pre args post vE2TLogExp = S.LH (E.postLog pre args) := by ec2t_lookup

end Lookups

/-! ## §3 — circuit + satisfaction. -/

def cE2TRestF : Constraint := { lhs := .var vE2TRestPre, rhs := .var vE2TRestPost }
def cE2TBind1 : Constraint := { lhs := .var vE2TComp1Post, rhs := .var vE2TComp1Exp }
def cE2TBind2 : Constraint := { lhs := .var vE2TComp2Post, rhs := .var vE2TComp2Exp }
def cE2TBind3 : Constraint := { lhs := .var vE2TComp3Post, rhs := .var vE2TComp3Exp }
def cE2TLog   : Constraint := { lhs := .var vE2TLogPost, rhs := .var vE2TLogExp }

def effectCircuit2Triple {St Args : Type} (E : EffectSpec2Triple St Args) : ConstraintSystem :=
  E.guardGates ++ [cE2TRestF, cE2TBind1, cE2TBind2, cE2TBind3, cE2TLog]

def satisfiedE2Triple {St Args : Type} (_S : Surface2) (E : EffectSpec2Triple St Args) (a : Assignment) :
    Prop :=
  satisfied (effectCircuit2Triple E) a

section GateIff
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args) (pre : St) (args : Args)
  (post : St)

theorem e2trest_iff :
    cE2TRestF.holds (encodeE2Triple S E pre args post)
      ↔ S.RH (E.view.toKernel pre) = S.RH (E.view.toKernel post) := by
  unfold Constraint.holds cE2TRestF
  simp only [Expr.eval, enc2t_restPre, enc2t_restPost]

theorem e2tbind1_iff :
    cE2TBind1.holds (encodeE2Triple S E pre args post)
      ↔ E.active1.digest (E.view.toKernel post) = E.active1.expected pre args := by
  unfold Constraint.holds cE2TBind1
  simp only [Expr.eval, enc2t_comp1Post, enc2t_comp1Exp]

theorem e2tbind2_iff :
    cE2TBind2.holds (encodeE2Triple S E pre args post)
      ↔ E.active2.digest (E.view.toKernel post) = E.active2.expected pre args := by
  unfold Constraint.holds cE2TBind2
  simp only [Expr.eval, enc2t_comp2Post, enc2t_comp2Exp]

theorem e2tbind3_iff :
    cE2TBind3.holds (encodeE2Triple S E pre args post)
      ↔ E.active3.digest (E.view.toKernel post) = E.active3.expected pre args := by
  unfold Constraint.holds cE2TBind3
  simp only [Expr.eval, enc2t_comp3Post, enc2t_comp3Exp]

theorem e2tlog_iff :
    cE2TLog.holds (encodeE2Triple S E pre args post)
      ↔ S.LH (E.view.getLog post) = S.LH (E.postLog pre args) := by
  unfold Constraint.holds cE2TLog
  simp only [Expr.eval, enc2t_logPost, enc2t_logExp]

end GateIff

/-! ## §4 — per-effect obligations. -/

def GuardDecodes2Triple {St Args : Type} (E : EffectSpec2Triple St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    satisfied E.guardGates (E.guardEncode pre args post) → E.guardProp pre args

def GuardEncodes2Triple {St Args : Type} (E : EffectSpec2Triple St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    E.guardProp pre args → satisfied E.guardGates (E.guardEncode pre args post)

def RestFrameDecodes2Triple {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args) : Prop :=
  ∀ k k' : RecordKernelState, S.RH k = S.RH k' → E.restFrame k k'

def RestFrameEncodes2Triple {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args) : Prop :=
  ∀ k k' : RecordKernelState, E.restFrame k k' → S.RH k = S.RH k'

/-! ## §5 — generic crown-jewel theorems. -/

section Sound
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args)

theorem effect2triple_circuit_full_sound
    (hRestF : RestFrameDecodes2Triple S E)
    (hGuard : GuardDecodes2Triple E)
    (pre : St) (args : Args) (post : St)
    (hno : ¬ Dregg2.Circuit.LogCommitRegrounded.LogColl S.LH (E.view.getLog post) (E.postLog pre args))
    (h : satisfiedE2Triple S E (encodeE2Triple S E pre args post)) :
    E.apex pre args post := by
  have hArith : satisfied (effectCircuit2Triple E) (encodeE2Triple S E pre args post) := h
  have hguardSat : satisfied E.guardGates (encodeE2Triple S E pre args post) := by
    intro c hc; exact hArith c (by unfold effectCircuit2Triple; exact List.mem_append_left _ hc)
  have hguardSat' : satisfied E.guardGates (E.guardEncode pre args post) :=
    (E.guardLocal _ _ (fun w hw => encodeE2Triple_agrees_guardEncode S E pre args post w hw)).mp hguardSat
  have hguard : E.guardProp pre args := hGuard pre args post hguardSat'
  have hrest := hArith cE2TRestF (by simp [effectCircuit2Triple])
  have hbind1 := hArith cE2TBind1 (by simp [effectCircuit2Triple])
  have hbind2 := hArith cE2TBind2 (by simp [effectCircuit2Triple])
  have hbind3 := hArith cE2TBind3 (by simp [effectCircuit2Triple])
  have hlog := hArith cE2TLog (by simp [effectCircuit2Triple])
  have hframe : E.restFrame (E.view.toKernel pre) (E.view.toKernel post) :=
    hRestF _ _ ((e2trest_iff S E pre args post).mp hrest)
  have hcomp1 := E.active1.binds pre args (E.view.toKernel post) ((e2tbind1_iff S E pre args post).mp hbind1)
  have hcomp2 := E.active2.binds pre args (E.view.toKernel post) ((e2tbind2_iff S E pre args post).mp hbind2)
  have hcomp3 := E.active3.binds pre args (E.view.toKernel post) ((e2tbind3_iff S E pre args post).mp hbind3)
  have hlogVal : E.view.getLog post = E.postLog pre args :=
    Dregg2.Circuit.LogCommitRegrounded.logHash_binds_of_noLogColl S.LH _ _ hno
      ((e2tlog_iff S E pre args post).mp hlog)
  exact ⟨hguard, hcomp1, hcomp2, hcomp3, hlogVal, hframe⟩

theorem effect2triple_circuit_full_complete
    (hRestF : RestFrameEncodes2Triple S E) (hGuardEnc : GuardEncodes2Triple E)
    (pre : St) (args : Args) (post : St) (hspec : E.apex pre args post) :
    satisfiedE2Triple S E (encodeE2Triple S E pre args post) := by
  obtain ⟨hguard, hcomp1, hcomp2, hcomp3, hlogVal, hframe⟩ := hspec
  show satisfied (effectCircuit2Triple E) (encodeE2Triple S E pre args post)
  intro c hc
  rcases List.mem_append.mp hc with hcg | hc5
  · have hge : satisfied E.guardGates (encodeE2Triple S E pre args post) :=
      (E.guardLocal _ _ (fun w hw => encodeE2Triple_agrees_guardEncode S E pre args post w hw)).mpr
        (hGuardEnc pre args post hguard)
    exact hge c hcg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc5
    rcases hc5 with rfl | rfl | rfl | rfl | rfl
    · exact (e2trest_iff S E pre args post).mpr (hRestF _ _ hframe)
    · exact (e2tbind1_iff S E pre args post).mpr
        (E.active1.encodes pre args (E.view.toKernel post) hcomp1)
    · exact (e2tbind2_iff S E pre args post).mpr
        (E.active2.encodes pre args (E.view.toKernel post) hcomp2)
    · exact (e2tbind3_iff S E pre args post).mpr
        (E.active3.encodes pre args (E.view.toKernel post) hcomp3)
    · exact (e2tlog_iff S E pre args post).mpr (by rw [hlogVal])

theorem effectCircuit2Triple_rejects_frame_tamper (hRestF : RestFrameDecodes2Triple S E)
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.restFrame (E.view.toKernel pre) (E.view.toKernel post)) :
    ¬ satisfiedE2Triple S E (encodeE2Triple S E pre args post) := by
  intro h
  have hrest := h cE2TRestF (by simp [effectCircuit2Triple])
  exact htamper (hRestF _ _ ((e2trest_iff S E pre args post).mp hrest))

theorem effectCircuit2Triple_rejects_wrong_component1
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active1.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Triple S E (encodeE2Triple S E pre args post) := by
  intro h
  have hbind := h cE2TBind1 (by simp [effectCircuit2Triple])
  exact htamper (E.active1.binds pre args (E.view.toKernel post) ((e2tbind1_iff S E pre args post).mp hbind))

theorem effectCircuit2Triple_rejects_wrong_component2
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active2.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Triple S E (encodeE2Triple S E pre args post) := by
  intro h
  have hbind := h cE2TBind2 (by simp [effectCircuit2Triple])
  exact htamper (E.active2.binds pre args (E.view.toKernel post) ((e2tbind2_iff S E pre args post).mp hbind))

theorem effectCircuit2Triple_rejects_wrong_component3
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active3.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Triple S E (encodeE2Triple S E pre args post) := by
  intro h
  have hbind := h cE2TBind3 (by simp [effectCircuit2Triple])
  exact htamper (E.active3.binds pre args (E.view.toKernel post) ((e2tbind3_iff S E pre args post).mp hbind))

theorem effectCircuit2Triple_rejects_log_forge
    (pre : St) (args : Args) (post : St) (htamper : E.view.getLog post ≠ E.postLog pre args)
    (hno : ¬ Dregg2.Circuit.LogCommitRegrounded.LogColl S.LH (E.view.getLog post) (E.postLog pre args)) :
    ¬ satisfiedE2Triple S E (encodeE2Triple S E pre args post) := by
  intro h
  have hlog := h cE2TLog (by simp [effectCircuit2Triple])
  exact htamper (Dregg2.Circuit.LogCommitRegrounded.logHash_binds_of_noLogColl S.LH _ _ hno
    ((e2tlog_iff S E pre args post).mp hlog))

end Sound

/-! ## §6 — emission. -/

def emittedEffect2Triple {St Args : Type} (name : String) (E : EffectSpec2Triple St Args) :
    EmittedDescriptor :=
  emit name E.traceWidth (effectCircuit2Triple E)

theorem emitEffect2TripleFaithful {St Args : Type} (name : String) (E : EffectSpec2Triple St Args)
    (a : Assignment) :
    satisfied (effectCircuit2Triple E) a ↔ satisfiedEmitted (emittedEffect2Triple name E) a :=
  emit_faithful name E.traceWidth (effectCircuit2Triple E) a

#assert_axioms encodeE2Triple_agrees_guardEncode
#assert_axioms e2trest_iff
#assert_axioms e2tbind1_iff
#assert_axioms e2tbind2_iff
#assert_axioms e2tbind3_iff
#assert_axioms e2tlog_iff
#assert_axioms effect2triple_circuit_full_sound
#assert_axioms effect2triple_circuit_full_complete
#assert_axioms effectCircuit2Triple_rejects_frame_tamper
#assert_axioms effectCircuit2Triple_rejects_wrong_component1
#assert_axioms effectCircuit2Triple_rejects_wrong_component2
#assert_axioms effectCircuit2Triple_rejects_wrong_component3
#assert_axioms effectCircuit2Triple_rejects_log_forge
#assert_axioms emitEffect2TripleFaithful

end Dregg2.Circuit.EffectCommit3