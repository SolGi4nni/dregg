/-
# Dregg2.Circuit.EffectCommit4 — the v2 GENERIC full-state circuit⟺spec framework for QUAD non-`cell`
components.

Gate 3: effects touching FOUR non-`cell` components (typically `queues` + `bal` + `escrows` for
`queueEnqueueA` / `queueDequeueA`). Literal product of `EffectCommit2Dual` with a third bind gate.

Wire layout (`traceWidth = 78`, guard `< 64`):

  `64 preRoot · 65 postRoot · 66 restPre · 67 restPost · 68..73 comp1..3 post/exp · 74 logPost · 75 logExp`

ADDITIVE: imports `EffectCommit2Dual` (reuses `ActiveComponent`, `Surface2`, `StateView`); edits none.
-/
import Dregg2.Circuit.EffectCommit2Dual

namespace Dregg2.Circuit.EffectCommit4

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit

set_option linter.dupNamespace false

/-! ## §1 — `EffectSpec2Quad`. -/

structure EffectSpec2Quad (St Args : Type) where
  view         : StateView St
  active1      : ActiveComponent St Args
  active2      : ActiveComponent St Args
  active3      : ActiveComponent St Args
  active4      : ActiveComponent St Args
  logUpdate    : Option (St → Args → List Turn)
  restFrame    : RecordKernelState → RecordKernelState → Prop
  guardGates   : ConstraintSystem
  guardProp    : St → Args → Prop
  guardWidth   : Nat
  guardEncode  : St → Args → St → Assignment
  guardLocal   : ∀ (a b : Assignment), (∀ w, w < guardWidth → a w = b w) →
                   (satisfied guardGates a ↔ satisfied guardGates b)
  guardWidth_le : guardWidth ≤ 64

def EffectSpec2Quad.postLog {St Args : Type} (E : EffectSpec2Quad St Args) (pre : St) (args : Args) :
    List Turn :=
  match E.logUpdate with
  | none   => E.view.getLog pre
  | some f => f pre args

def EffectSpec2Quad.apex {St Args : Type} (E : EffectSpec2Quad St Args) (pre : St) (args : Args)
    (post : St) : Prop :=
  E.guardProp pre args
  ∧ E.active1.postClause pre args (E.view.toKernel post)
  ∧ E.active2.postClause pre args (E.view.toKernel post)
  ∧ E.active3.postClause pre args (E.view.toKernel post)
  ∧ E.active4.postClause pre args (E.view.toKernel post)
  ∧ E.view.getLog post = E.postLog pre args
  ∧ E.restFrame (E.view.toKernel pre) (E.view.toKernel post)

/-! ## §2 — digest wires + encoder (`traceWidth = 78`). -/

abbrev vE2QPreRoot   : Var := 64
abbrev vE2QPostRoot  : Var := 65
abbrev vE2QRestPre   : Var := 66
abbrev vE2QRestPost  : Var := 67
abbrev vE2QComp1Post : Var := 68
abbrev vE2QComp1Exp  : Var := 69
abbrev vE2QComp2Post : Var := 70
abbrev vE2QComp2Exp  : Var := 71
abbrev vE2QComp3Post : Var := 72
abbrev vE2QComp3Exp  : Var := 73
abbrev vE2QComp4Post : Var := 74
abbrev vE2QComp4Exp  : Var := 75
abbrev vE2QLogPost   : Var := 76
abbrev vE2QLogExp    : Var := 77

def EffectSpec2Quad.traceWidth {St Args : Type} (_E : EffectSpec2Quad St Args) : Nat := 78

def effectStateCommit2Quad {St Args : Type} (S : Surface2) (E : EffectSpec2Quad St Args)
    (k : RecordKernelState) (log : List Turn) : ℤ :=
  E.active1.digest k + E.active2.digest k + E.active3.digest k + E.active4.digest k + S.RH k + S.LH log

def encodeE2Quad {St Args : Type} (S : Surface2) (E : EffectSpec2Quad St Args)
    (pre : St) (args : Args) (post : St) : Assignment :=
  fun w =>
    if      w = vE2QPreRoot   then
      effectStateCommit2Quad S E (E.view.toKernel pre) (E.view.getLog pre)
    else if w = vE2QPostRoot  then
      effectStateCommit2Quad S E (E.view.toKernel post) (E.view.getLog post)
    else if w = vE2QRestPre   then S.RH (E.view.toKernel pre)
    else if w = vE2QRestPost  then S.RH (E.view.toKernel post)
    else if w = vE2QComp1Post then E.active1.digest (E.view.toKernel post)
    else if w = vE2QComp1Exp  then E.active1.expected pre args
    else if w = vE2QComp2Post then E.active2.digest (E.view.toKernel post)
    else if w = vE2QComp2Exp  then E.active2.expected pre args
    else if w = vE2QComp3Post then E.active3.digest (E.view.toKernel post)
    else if w = vE2QComp3Exp  then E.active3.expected pre args
    else if w = vE2QComp4Post then E.active4.digest (E.view.toKernel post)
    else if w = vE2QComp4Exp  then E.active4.expected pre args
    else if w = vE2QLogPost   then S.LH (E.view.getLog post)
    else if w = vE2QLogExp    then S.LH (E.postLog pre args)
    else E.guardEncode pre args post w

theorem encodeE2Quad_agrees_guardEncode {St Args : Type} (S : Surface2) (E : EffectSpec2Quad St Args)
    (pre : St) (args : Args) (post : St) (w : Var) (hw : w < E.guardWidth) :
    encodeE2Quad S E pre args post w = E.guardEncode pre args post w := by
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
  have hn76 : w ≠ 76 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 76))
  have hn77 : w ≠ 77 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 77))
  unfold encodeE2Quad
  simp only [vE2QPreRoot, vE2QPostRoot, vE2QRestPre, vE2QRestPost, vE2QComp1Post, vE2QComp1Exp,
    vE2QComp2Post, vE2QComp2Exp, vE2QComp3Post, vE2QComp3Exp, vE2QComp4Post, vE2QComp4Exp,
    vE2QLogPost, vE2QLogExp, if_neg hn64, if_neg hn65, if_neg hn66, if_neg hn67, if_neg hn68,
    if_neg hn69, if_neg hn70, if_neg hn71, if_neg hn72, if_neg hn73, if_neg hn74, if_neg hn75,
    if_neg hn76, if_neg hn77]

macro "ec2q_lookup" : tactic =>
  `(tactic| simp [encodeE2Quad, vE2QPreRoot, vE2QPostRoot, vE2QRestPre, vE2QRestPost, vE2QComp1Post,
      vE2QComp1Exp, vE2QComp2Post, vE2QComp2Exp, vE2QComp3Post, vE2QComp3Exp, vE2QComp4Post, vE2QComp4Exp,
      vE2QLogPost, vE2QLogExp])

section Lookups
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Quad St Args) (pre : St) (args : Args)
  (post : St)

theorem enc2q_restPre :
    encodeE2Quad S E pre args post vE2QRestPre = S.RH (E.view.toKernel pre) := by ec2q_lookup
theorem enc2q_restPost :
    encodeE2Quad S E pre args post vE2QRestPost = S.RH (E.view.toKernel post) := by ec2q_lookup
theorem enc2q_comp1Post :
    encodeE2Quad S E pre args post vE2QComp1Post = E.active1.digest (E.view.toKernel post) := by ec2q_lookup
theorem enc2q_comp1Exp :
    encodeE2Quad S E pre args post vE2QComp1Exp = E.active1.expected pre args := by ec2q_lookup
theorem enc2q_comp2Post :
    encodeE2Quad S E pre args post vE2QComp2Post = E.active2.digest (E.view.toKernel post) := by ec2q_lookup
theorem enc2q_comp2Exp :
    encodeE2Quad S E pre args post vE2QComp2Exp = E.active2.expected pre args := by ec2q_lookup
theorem enc2q_comp3Post :
    encodeE2Quad S E pre args post vE2QComp3Post = E.active3.digest (E.view.toKernel post) := by ec2q_lookup
theorem enc2q_comp3Exp :
    encodeE2Quad S E pre args post vE2QComp3Exp = E.active3.expected pre args := by ec2q_lookup
theorem enc2q_comp4Post :
    encodeE2Quad S E pre args post vE2QComp4Post = E.active4.digest (E.view.toKernel post) := by ec2q_lookup
theorem enc2q_comp4Exp :
    encodeE2Quad S E pre args post vE2QComp4Exp = E.active4.expected pre args := by ec2q_lookup
theorem enc2q_logPost :
    encodeE2Quad S E pre args post vE2QLogPost = S.LH (E.view.getLog post) := by ec2q_lookup
theorem enc2q_logExp :
    encodeE2Quad S E pre args post vE2QLogExp = S.LH (E.postLog pre args) := by ec2q_lookup

end Lookups

/-! ## §3 — circuit + satisfaction. -/

def cE2QRestF : Constraint := { lhs := .var vE2QRestPre, rhs := .var vE2QRestPost }
def cE2QBind1 : Constraint := { lhs := .var vE2QComp1Post, rhs := .var vE2QComp1Exp }
def cE2QBind2 : Constraint := { lhs := .var vE2QComp2Post, rhs := .var vE2QComp2Exp }
def cE2QBind3 : Constraint := { lhs := .var vE2QComp3Post, rhs := .var vE2QComp3Exp }
def cE2QBind4 : Constraint := { lhs := .var vE2QComp4Post, rhs := .var vE2QComp4Exp }
def cE2QLog   : Constraint := { lhs := .var vE2QLogPost, rhs := .var vE2QLogExp }

def effectCircuit2Quad {St Args : Type} (E : EffectSpec2Quad St Args) : ConstraintSystem :=
  E.guardGates ++ [cE2QRestF, cE2QBind1, cE2QBind2, cE2QBind3, cE2QBind4, cE2QLog]

def satisfiedE2Quad {St Args : Type} (_S : Surface2) (E : EffectSpec2Quad St Args) (a : Assignment) :
    Prop :=
  satisfied (effectCircuit2Quad E) a

section GateIff
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Quad St Args) (pre : St) (args : Args)
  (post : St)

theorem e2qrest_iff :
    cE2QRestF.holds (encodeE2Quad S E pre args post)
      ↔ S.RH (E.view.toKernel pre) = S.RH (E.view.toKernel post) := by
  unfold Constraint.holds cE2QRestF
  simp only [Expr.eval, enc2q_restPre, enc2q_restPost]

theorem e2qbind1_iff :
    cE2QBind1.holds (encodeE2Quad S E pre args post)
      ↔ E.active1.digest (E.view.toKernel post) = E.active1.expected pre args := by
  unfold Constraint.holds cE2QBind1
  simp only [Expr.eval, enc2q_comp1Post, enc2q_comp1Exp]

theorem e2qbind2_iff :
    cE2QBind2.holds (encodeE2Quad S E pre args post)
      ↔ E.active2.digest (E.view.toKernel post) = E.active2.expected pre args := by
  unfold Constraint.holds cE2QBind2
  simp only [Expr.eval, enc2q_comp2Post, enc2q_comp2Exp]

theorem e2qbind3_iff :
    cE2QBind3.holds (encodeE2Quad S E pre args post)
      ↔ E.active3.digest (E.view.toKernel post) = E.active3.expected pre args := by
  unfold Constraint.holds cE2QBind3
  simp only [Expr.eval, enc2q_comp3Post, enc2q_comp3Exp]

theorem e2qbind4_iff :
    cE2QBind4.holds (encodeE2Quad S E pre args post)
      ↔ E.active4.digest (E.view.toKernel post) = E.active4.expected pre args := by
  unfold Constraint.holds cE2QBind4
  simp only [Expr.eval, enc2q_comp4Post, enc2q_comp4Exp]

theorem e2qlog_iff :
    cE2QLog.holds (encodeE2Quad S E pre args post)
      ↔ S.LH (E.view.getLog post) = S.LH (E.postLog pre args) := by
  unfold Constraint.holds cE2QLog
  simp only [Expr.eval, enc2q_logPost, enc2q_logExp]

end GateIff

/-! ## §4 — per-effect obligations. -/

def GuardDecodes2Quad {St Args : Type} (E : EffectSpec2Quad St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    satisfied E.guardGates (E.guardEncode pre args post) → E.guardProp pre args

def GuardEncodes2Quad {St Args : Type} (E : EffectSpec2Quad St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    E.guardProp pre args → satisfied E.guardGates (E.guardEncode pre args post)

def RestFrameDecodes2Quad {St Args : Type} (S : Surface2) (E : EffectSpec2Quad St Args) : Prop :=
  ∀ k k' : RecordKernelState, S.RH k = S.RH k' → E.restFrame k k'

def RestFrameEncodes2Quad {St Args : Type} (S : Surface2) (E : EffectSpec2Quad St Args) : Prop :=
  ∀ k k' : RecordKernelState, E.restFrame k k' → S.RH k = S.RH k'

/-! ## §5 — generic crown-jewel theorems. -/

section Sound
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Quad St Args)

theorem effect2quad_circuit_full_sound
    (hRestF : RestFrameDecodes2Quad S E)
    (hGuard : GuardDecodes2Quad E)
    (pre : St) (args : Args) (post : St)
    (hno : ¬ Dregg2.Circuit.LogCommitRegrounded.LogColl S.LH (E.view.getLog post) (E.postLog pre args))
    (h : satisfiedE2Quad S E (encodeE2Quad S E pre args post)) :
    E.apex pre args post := by
  have hArith : satisfied (effectCircuit2Quad E) (encodeE2Quad S E pre args post) := h
  have hguardSat : satisfied E.guardGates (encodeE2Quad S E pre args post) := by
    intro c hc; exact hArith c (by unfold effectCircuit2Quad; exact List.mem_append_left _ hc)
  have hguardSat' : satisfied E.guardGates (E.guardEncode pre args post) :=
    (E.guardLocal _ _ (fun w hw => encodeE2Quad_agrees_guardEncode S E pre args post w hw)).mp hguardSat
  have hguard : E.guardProp pre args := hGuard pre args post hguardSat'
  have hrest := hArith cE2QRestF (by simp [effectCircuit2Quad])
  have hbind1 := hArith cE2QBind1 (by simp [effectCircuit2Quad])
  have hbind2 := hArith cE2QBind2 (by simp [effectCircuit2Quad])
  have hbind3 := hArith cE2QBind3 (by simp [effectCircuit2Quad])
  have hbind4 := hArith cE2QBind4 (by simp [effectCircuit2Quad])
  have hlog := hArith cE2QLog (by simp [effectCircuit2Quad])
  have hframe : E.restFrame (E.view.toKernel pre) (E.view.toKernel post) :=
    hRestF _ _ ((e2qrest_iff S E pre args post).mp hrest)
  have hcomp1 := E.active1.binds pre args (E.view.toKernel post) ((e2qbind1_iff S E pre args post).mp hbind1)
  have hcomp2 := E.active2.binds pre args (E.view.toKernel post) ((e2qbind2_iff S E pre args post).mp hbind2)
  have hcomp3 := E.active3.binds pre args (E.view.toKernel post) ((e2qbind3_iff S E pre args post).mp hbind3)
  have hcomp4 := E.active4.binds pre args (E.view.toKernel post) ((e2qbind4_iff S E pre args post).mp hbind4)
  have hlogVal : E.view.getLog post = E.postLog pre args :=
    Dregg2.Circuit.LogCommitRegrounded.logHash_binds_of_noLogColl S.LH _ _ hno
      ((e2qlog_iff S E pre args post).mp hlog)
  exact ⟨hguard, hcomp1, hcomp2, hcomp3, hcomp4, hlogVal, hframe⟩

theorem effect2quad_circuit_full_complete
    (hRestF : RestFrameEncodes2Quad S E) (hGuardEnc : GuardEncodes2Quad E)
    (pre : St) (args : Args) (post : St) (hspec : E.apex pre args post) :
    satisfiedE2Quad S E (encodeE2Quad S E pre args post) := by
  obtain ⟨hguard, hcomp1, hcomp2, hcomp3, hcomp4, hlogVal, hframe⟩ := hspec
  show satisfied (effectCircuit2Quad E) (encodeE2Quad S E pre args post)
  intro c hc
  rcases List.mem_append.mp hc with hcg | hc6
  · have hge : satisfied E.guardGates (encodeE2Quad S E pre args post) :=
      (E.guardLocal _ _ (fun w hw => encodeE2Quad_agrees_guardEncode S E pre args post w hw)).mpr
        (hGuardEnc pre args post hguard)
    exact hge c hcg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc6
    rcases hc6 with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (e2qrest_iff S E pre args post).mpr (hRestF _ _ hframe)
    · exact (e2qbind1_iff S E pre args post).mpr
        (E.active1.encodes pre args (E.view.toKernel post) hcomp1)
    · exact (e2qbind2_iff S E pre args post).mpr
        (E.active2.encodes pre args (E.view.toKernel post) hcomp2)
    · exact (e2qbind3_iff S E pre args post).mpr
        (E.active3.encodes pre args (E.view.toKernel post) hcomp3)
    · exact (e2qbind4_iff S E pre args post).mpr
        (E.active4.encodes pre args (E.view.toKernel post) hcomp4)
    · exact (e2qlog_iff S E pre args post).mpr (by rw [hlogVal])

theorem effectCircuit2Quad_rejects_frame_tamper (hRestF : RestFrameDecodes2Quad S E)
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.restFrame (E.view.toKernel pre) (E.view.toKernel post)) :
    ¬ satisfiedE2Quad S E (encodeE2Quad S E pre args post) := by
  intro h
  have hrest := h cE2QRestF (by simp [effectCircuit2Quad])
  exact htamper (hRestF _ _ ((e2qrest_iff S E pre args post).mp hrest))

theorem effectCircuit2Quad_rejects_wrong_component1
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active1.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quad S E (encodeE2Quad S E pre args post) := by
  intro h
  have hbind := h cE2QBind1 (by simp [effectCircuit2Quad])
  exact htamper (E.active1.binds pre args (E.view.toKernel post) ((e2qbind1_iff S E pre args post).mp hbind))

theorem effectCircuit2Quad_rejects_wrong_component2
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active2.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quad S E (encodeE2Quad S E pre args post) := by
  intro h
  have hbind := h cE2QBind2 (by simp [effectCircuit2Quad])
  exact htamper (E.active2.binds pre args (E.view.toKernel post) ((e2qbind2_iff S E pre args post).mp hbind))

theorem effectCircuit2Quad_rejects_wrong_component3
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active3.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quad S E (encodeE2Quad S E pre args post) := by
  intro h
  have hbind := h cE2QBind3 (by simp [effectCircuit2Quad])
  exact htamper (E.active3.binds pre args (E.view.toKernel post) ((e2qbind3_iff S E pre args post).mp hbind))

theorem effectCircuit2Quad_rejects_wrong_component4
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active4.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quad S E (encodeE2Quad S E pre args post) := by
  intro h
  have hbind := h cE2QBind4 (by simp [effectCircuit2Quad])
  exact htamper (E.active4.binds pre args (E.view.toKernel post) ((e2qbind4_iff S E pre args post).mp hbind))

theorem effectCircuit2Quad_rejects_log_forge
    (pre : St) (args : Args) (post : St) (htamper : E.view.getLog post ≠ E.postLog pre args)
    (hno : ¬ Dregg2.Circuit.LogCommitRegrounded.LogColl S.LH (E.view.getLog post) (E.postLog pre args)) :
    ¬ satisfiedE2Quad S E (encodeE2Quad S E pre args post) := by
  intro h
  have hlog := h cE2QLog (by simp [effectCircuit2Quad])
  exact htamper (Dregg2.Circuit.LogCommitRegrounded.logHash_binds_of_noLogColl S.LH _ _ hno
    ((e2qlog_iff S E pre args post).mp hlog))

end Sound

/-! ## §6 — emission. -/

def emittedEffect2Quad {St Args : Type} (name : String) (E : EffectSpec2Quad St Args) :
    EmittedDescriptor :=
  emit name E.traceWidth (effectCircuit2Quad E)

theorem emitEffect2QuadFaithful {St Args : Type} (name : String) (E : EffectSpec2Quad St Args)
    (a : Assignment) :
    satisfied (effectCircuit2Quad E) a ↔ satisfiedEmitted (emittedEffect2Quad name E) a :=
  emit_faithful name E.traceWidth (effectCircuit2Quad E) a

#assert_axioms encodeE2Quad_agrees_guardEncode
#assert_axioms e2qrest_iff
#assert_axioms e2qbind1_iff
#assert_axioms e2qbind2_iff
#assert_axioms e2qbind3_iff
#assert_axioms e2qbind4_iff
#assert_axioms e2qlog_iff
#assert_axioms effect2quad_circuit_full_sound
#assert_axioms effect2quad_circuit_full_complete
#assert_axioms effectCircuit2Quad_rejects_frame_tamper
#assert_axioms effectCircuit2Quad_rejects_wrong_component1
#assert_axioms effectCircuit2Quad_rejects_wrong_component2
#assert_axioms effectCircuit2Quad_rejects_wrong_component3
#assert_axioms effectCircuit2Quad_rejects_wrong_component4
#assert_axioms effectCircuit2Quad_rejects_log_forge
#assert_axioms emitEffect2QuadFaithful

end Dregg2.Circuit.EffectCommit4