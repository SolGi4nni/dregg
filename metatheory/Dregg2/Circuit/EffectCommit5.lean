/-
# Dregg2.Circuit.EffectCommit5 — the v2 GENERIC full-state circuit⟺spec framework for QUINT non-`cell`
components.

Gate 3: effects touching FIVE non-`cell` components (typically `accounts` + `bal` + `caps` +
`delegate` + `delegations` for `spawnA`). Literal product of `EffectCommit2Dual` with four extra bind
gates.

Wire layout (`traceWidth = 80`, guard `< 64`):

  `64 preRoot · 65 postRoot · 66 restPre · 67 restPost · 68..77 comp1..5 post/exp · 78 logPost · 79 logExp`

ADDITIVE: imports `EffectCommit2Dual` (reuses `ActiveComponent`, `Surface2`, `StateView`); edits none.
-/
import Dregg2.Circuit.EffectCommit2Dual

namespace Dregg2.Circuit.EffectCommit5

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit

set_option linter.dupNamespace false

/-! ## §1 — `EffectSpec2Quint`. -/

structure EffectSpec2Quint (St Args : Type) where
  view         : StateView St
  active1      : ActiveComponent St Args
  active2      : ActiveComponent St Args
  active3      : ActiveComponent St Args
  active4      : ActiveComponent St Args
  active5      : ActiveComponent St Args
  logUpdate    : Option (St → Args → List Turn)
  restFrame    : RecordKernelState → RecordKernelState → Prop
  guardGates   : ConstraintSystem
  guardProp    : St → Args → Prop
  guardWidth   : Nat
  guardEncode  : St → Args → St → Assignment
  guardLocal   : ∀ (a b : Assignment), (∀ w, w < guardWidth → a w = b w) →
                   (satisfied guardGates a ↔ satisfied guardGates b)
  guardWidth_le : guardWidth ≤ 64

def EffectSpec2Quint.postLog {St Args : Type} (E : EffectSpec2Quint St Args) (pre : St) (args : Args) :
    List Turn :=
  match E.logUpdate with
  | none   => E.view.getLog pre
  | some f => f pre args

def EffectSpec2Quint.apex {St Args : Type} (E : EffectSpec2Quint St Args) (pre : St) (args : Args)
    (post : St) : Prop :=
  E.guardProp pre args
  ∧ E.active1.postClause pre args (E.view.toKernel post)
  ∧ E.active2.postClause pre args (E.view.toKernel post)
  ∧ E.active3.postClause pre args (E.view.toKernel post)
  ∧ E.active4.postClause pre args (E.view.toKernel post)
  ∧ E.active5.postClause pre args (E.view.toKernel post)
  ∧ E.view.getLog post = E.postLog pre args
  ∧ E.restFrame (E.view.toKernel pre) (E.view.toKernel post)

/-! ## §2 — digest wires + encoder (`traceWidth = 80`). -/

abbrev vE2UPreRoot   : Var := 64
abbrev vE2UPostRoot  : Var := 65
abbrev vE2URestPre   : Var := 66
abbrev vE2URestPost  : Var := 67
abbrev vE2UComp1Post : Var := 68
abbrev vE2UComp1Exp  : Var := 69
abbrev vE2UComp2Post : Var := 70
abbrev vE2UComp2Exp  : Var := 71
abbrev vE2UComp3Post : Var := 72
abbrev vE2UComp3Exp  : Var := 73
abbrev vE2UComp4Post : Var := 74
abbrev vE2UComp4Exp  : Var := 75
abbrev vE2UComp5Post : Var := 76
abbrev vE2UComp5Exp  : Var := 77
abbrev vE2ULogPost   : Var := 78
abbrev vE2ULogExp    : Var := 79

def EffectSpec2Quint.traceWidth {St Args : Type} (_E : EffectSpec2Quint St Args) : Nat := 80

def effectStateCommit2Quint {St Args : Type} (S : Surface2) (E : EffectSpec2Quint St Args)
    (k : RecordKernelState) (log : List Turn) : ℤ :=
  E.active1.digest k + E.active2.digest k + E.active3.digest k + E.active4.digest k
    + E.active5.digest k + S.RH k + S.LH log

def encodeE2Quint {St Args : Type} (S : Surface2) (E : EffectSpec2Quint St Args)
    (pre : St) (args : Args) (post : St) : Assignment :=
  fun w =>
    if      w = vE2UPreRoot   then
      effectStateCommit2Quint S E (E.view.toKernel pre) (E.view.getLog pre)
    else if w = vE2UPostRoot  then
      effectStateCommit2Quint S E (E.view.toKernel post) (E.view.getLog post)
    else if w = vE2URestPre   then S.RH (E.view.toKernel pre)
    else if w = vE2URestPost  then S.RH (E.view.toKernel post)
    else if w = vE2UComp1Post then E.active1.digest (E.view.toKernel post)
    else if w = vE2UComp1Exp  then E.active1.expected pre args
    else if w = vE2UComp2Post then E.active2.digest (E.view.toKernel post)
    else if w = vE2UComp2Exp  then E.active2.expected pre args
    else if w = vE2UComp3Post then E.active3.digest (E.view.toKernel post)
    else if w = vE2UComp3Exp  then E.active3.expected pre args
    else if w = vE2UComp4Post then E.active4.digest (E.view.toKernel post)
    else if w = vE2UComp4Exp  then E.active4.expected pre args
    else if w = vE2UComp5Post then E.active5.digest (E.view.toKernel post)
    else if w = vE2UComp5Exp  then E.active5.expected pre args
    else if w = vE2ULogPost   then S.LH (E.view.getLog post)
    else if w = vE2ULogExp    then S.LH (E.postLog pre args)
    else E.guardEncode pre args post w

theorem encodeE2Quint_agrees_guardEncode {St Args : Type} (S : Surface2) (E : EffectSpec2Quint St Args)
    (pre : St) (args : Args) (post : St) (w : Var) (hw : w < E.guardWidth) :
    encodeE2Quint S E pre args post w = E.guardEncode pre args post w := by
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
  have hn78 : w ≠ 78 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 78))
  have hn79 : w ≠ 79 := ne_of_lt (Nat.lt_trans hlt (by decide : 64 < 79))
  unfold encodeE2Quint
  simp only [vE2UPreRoot, vE2UPostRoot, vE2URestPre, vE2URestPost, vE2UComp1Post, vE2UComp1Exp,
    vE2UComp2Post, vE2UComp2Exp, vE2UComp3Post, vE2UComp3Exp, vE2UComp4Post, vE2UComp4Exp,
    vE2UComp5Post, vE2UComp5Exp, vE2ULogPost, vE2ULogExp,
    if_neg hn64, if_neg hn65, if_neg hn66, if_neg hn67, if_neg hn68, if_neg hn69, if_neg hn70,
    if_neg hn71, if_neg hn72, if_neg hn73, if_neg hn74, if_neg hn75, if_neg hn76, if_neg hn77,
    if_neg hn78, if_neg hn79]

macro "ec2u_lookup" : tactic =>
  `(tactic| simp [encodeE2Quint, vE2UPreRoot, vE2UPostRoot, vE2URestPre, vE2URestPost, vE2UComp1Post,
      vE2UComp1Exp, vE2UComp2Post, vE2UComp2Exp, vE2UComp3Post, vE2UComp3Exp, vE2UComp4Post,
      vE2UComp4Exp, vE2UComp5Post, vE2UComp5Exp, vE2ULogPost, vE2ULogExp])

section Lookups
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Quint St Args) (pre : St) (args : Args)
  (post : St)

theorem enc2u_restPre :
    encodeE2Quint S E pre args post vE2URestPre = S.RH (E.view.toKernel pre) := by ec2u_lookup
theorem enc2u_restPost :
    encodeE2Quint S E pre args post vE2URestPost = S.RH (E.view.toKernel post) := by ec2u_lookup
theorem enc2u_comp1Post :
    encodeE2Quint S E pre args post vE2UComp1Post = E.active1.digest (E.view.toKernel post) := by ec2u_lookup
theorem enc2u_comp1Exp :
    encodeE2Quint S E pre args post vE2UComp1Exp = E.active1.expected pre args := by ec2u_lookup
theorem enc2u_comp2Post :
    encodeE2Quint S E pre args post vE2UComp2Post = E.active2.digest (E.view.toKernel post) := by ec2u_lookup
theorem enc2u_comp2Exp :
    encodeE2Quint S E pre args post vE2UComp2Exp = E.active2.expected pre args := by ec2u_lookup
theorem enc2u_comp3Post :
    encodeE2Quint S E pre args post vE2UComp3Post = E.active3.digest (E.view.toKernel post) := by ec2u_lookup
theorem enc2u_comp3Exp :
    encodeE2Quint S E pre args post vE2UComp3Exp = E.active3.expected pre args := by ec2u_lookup
theorem enc2u_comp4Post :
    encodeE2Quint S E pre args post vE2UComp4Post = E.active4.digest (E.view.toKernel post) := by ec2u_lookup
theorem enc2u_comp4Exp :
    encodeE2Quint S E pre args post vE2UComp4Exp = E.active4.expected pre args := by ec2u_lookup
theorem enc2u_comp5Post :
    encodeE2Quint S E pre args post vE2UComp5Post = E.active5.digest (E.view.toKernel post) := by ec2u_lookup
theorem enc2u_comp5Exp :
    encodeE2Quint S E pre args post vE2UComp5Exp = E.active5.expected pre args := by ec2u_lookup
theorem enc2u_logPost :
    encodeE2Quint S E pre args post vE2ULogPost = S.LH (E.view.getLog post) := by ec2u_lookup
theorem enc2u_logExp :
    encodeE2Quint S E pre args post vE2ULogExp = S.LH (E.postLog pre args) := by ec2u_lookup

end Lookups

/-! ## §3 — circuit + satisfaction. -/

def cE2URestF : Constraint := { lhs := .var vE2URestPre, rhs := .var vE2URestPost }
def cE2UBind1 : Constraint := { lhs := .var vE2UComp1Post, rhs := .var vE2UComp1Exp }
def cE2UBind2 : Constraint := { lhs := .var vE2UComp2Post, rhs := .var vE2UComp2Exp }
def cE2UBind3 : Constraint := { lhs := .var vE2UComp3Post, rhs := .var vE2UComp3Exp }
def cE2UBind4 : Constraint := { lhs := .var vE2UComp4Post, rhs := .var vE2UComp4Exp }
def cE2UBind5 : Constraint := { lhs := .var vE2UComp5Post, rhs := .var vE2UComp5Exp }
def cE2ULog   : Constraint := { lhs := .var vE2ULogPost, rhs := .var vE2ULogExp }

def effectCircuit2Quint {St Args : Type} (E : EffectSpec2Quint St Args) : ConstraintSystem :=
  E.guardGates ++ [cE2URestF, cE2UBind1, cE2UBind2, cE2UBind3, cE2UBind4, cE2UBind5, cE2ULog]

def satisfiedE2Quint {St Args : Type} (_S : Surface2) (E : EffectSpec2Quint St Args) (a : Assignment) :
    Prop :=
  satisfied (effectCircuit2Quint E) a

section GateIff
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Quint St Args) (pre : St) (args : Args)
  (post : St)

theorem e2urest_iff :
    cE2URestF.holds (encodeE2Quint S E pre args post)
      ↔ S.RH (E.view.toKernel pre) = S.RH (E.view.toKernel post) := by
  unfold Constraint.holds cE2URestF
  simp only [Expr.eval, enc2u_restPre, enc2u_restPost]

theorem e2ubind1_iff :
    cE2UBind1.holds (encodeE2Quint S E pre args post)
      ↔ E.active1.digest (E.view.toKernel post) = E.active1.expected pre args := by
  unfold Constraint.holds cE2UBind1
  simp only [Expr.eval, enc2u_comp1Post, enc2u_comp1Exp]

theorem e2ubind2_iff :
    cE2UBind2.holds (encodeE2Quint S E pre args post)
      ↔ E.active2.digest (E.view.toKernel post) = E.active2.expected pre args := by
  unfold Constraint.holds cE2UBind2
  simp only [Expr.eval, enc2u_comp2Post, enc2u_comp2Exp]

theorem e2ubind3_iff :
    cE2UBind3.holds (encodeE2Quint S E pre args post)
      ↔ E.active3.digest (E.view.toKernel post) = E.active3.expected pre args := by
  unfold Constraint.holds cE2UBind3
  simp only [Expr.eval, enc2u_comp3Post, enc2u_comp3Exp]

theorem e2ubind4_iff :
    cE2UBind4.holds (encodeE2Quint S E pre args post)
      ↔ E.active4.digest (E.view.toKernel post) = E.active4.expected pre args := by
  unfold Constraint.holds cE2UBind4
  simp only [Expr.eval, enc2u_comp4Post, enc2u_comp4Exp]

theorem e2ubind5_iff :
    cE2UBind5.holds (encodeE2Quint S E pre args post)
      ↔ E.active5.digest (E.view.toKernel post) = E.active5.expected pre args := by
  unfold Constraint.holds cE2UBind5
  simp only [Expr.eval, enc2u_comp5Post, enc2u_comp5Exp]

theorem e2ulog_iff :
    cE2ULog.holds (encodeE2Quint S E pre args post)
      ↔ S.LH (E.view.getLog post) = S.LH (E.postLog pre args) := by
  unfold Constraint.holds cE2ULog
  simp only [Expr.eval, enc2u_logPost, enc2u_logExp]

end GateIff

/-! ## §4 — per-effect obligations. -/

def GuardDecodes2Quint {St Args : Type} (E : EffectSpec2Quint St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    satisfied E.guardGates (E.guardEncode pre args post) → E.guardProp pre args

def GuardEncodes2Quint {St Args : Type} (E : EffectSpec2Quint St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    E.guardProp pre args → satisfied E.guardGates (E.guardEncode pre args post)

def RestFrameDecodes2Quint {St Args : Type} (S : Surface2) (E : EffectSpec2Quint St Args) : Prop :=
  ∀ k k' : RecordKernelState, S.RH k = S.RH k' → E.restFrame k k'

def RestFrameEncodes2Quint {St Args : Type} (S : Surface2) (E : EffectSpec2Quint St Args) : Prop :=
  ∀ k k' : RecordKernelState, E.restFrame k k' → S.RH k = S.RH k'

/-! ## §5 — generic crown-jewel theorems. -/

section Sound
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Quint St Args)

theorem effect2quint_circuit_full_sound
    (hRestF : RestFrameDecodes2Quint S E)
    (hGuard : GuardDecodes2Quint E)
    (pre : St) (args : Args) (post : St)
    (hno : ¬ Dregg2.Circuit.LogCommitRegrounded.LogColl S.LH (E.view.getLog post) (E.postLog pre args))
    (h : satisfiedE2Quint S E (encodeE2Quint S E pre args post)) :
    E.apex pre args post := by
  have hArith : satisfied (effectCircuit2Quint E) (encodeE2Quint S E pre args post) := h
  have hguardSat : satisfied E.guardGates (encodeE2Quint S E pre args post) := by
    intro c hc; exact hArith c (by unfold effectCircuit2Quint; exact List.mem_append_left _ hc)
  have hguardSat' : satisfied E.guardGates (E.guardEncode pre args post) :=
    (E.guardLocal _ _ (fun w hw => encodeE2Quint_agrees_guardEncode S E pre args post w hw)).mp hguardSat
  have hguard : E.guardProp pre args := hGuard pre args post hguardSat'
  have hrest := hArith cE2URestF (by simp [effectCircuit2Quint])
  have hbind1 := hArith cE2UBind1 (by simp [effectCircuit2Quint])
  have hbind2 := hArith cE2UBind2 (by simp [effectCircuit2Quint])
  have hbind3 := hArith cE2UBind3 (by simp [effectCircuit2Quint])
  have hbind4 := hArith cE2UBind4 (by simp [effectCircuit2Quint])
  have hbind5 := hArith cE2UBind5 (by simp [effectCircuit2Quint])
  have hlog := hArith cE2ULog (by simp [effectCircuit2Quint])
  have hframe : E.restFrame (E.view.toKernel pre) (E.view.toKernel post) :=
    hRestF _ _ ((e2urest_iff S E pre args post).mp hrest)
  have hcomp1 := E.active1.binds pre args (E.view.toKernel post) ((e2ubind1_iff S E pre args post).mp hbind1)
  have hcomp2 := E.active2.binds pre args (E.view.toKernel post) ((e2ubind2_iff S E pre args post).mp hbind2)
  have hcomp3 := E.active3.binds pre args (E.view.toKernel post) ((e2ubind3_iff S E pre args post).mp hbind3)
  have hcomp4 := E.active4.binds pre args (E.view.toKernel post) ((e2ubind4_iff S E pre args post).mp hbind4)
  have hcomp5 := E.active5.binds pre args (E.view.toKernel post) ((e2ubind5_iff S E pre args post).mp hbind5)
  have hlogVal : E.view.getLog post = E.postLog pre args :=
    Dregg2.Circuit.LogCommitRegrounded.logHash_binds_of_noLogColl S.LH _ _ hno
      ((e2ulog_iff S E pre args post).mp hlog)
  exact ⟨hguard, hcomp1, hcomp2, hcomp3, hcomp4, hcomp5, hlogVal, hframe⟩

theorem effect2quint_circuit_full_complete
    (hRestF : RestFrameEncodes2Quint S E) (hGuardEnc : GuardEncodes2Quint E)
    (pre : St) (args : Args) (post : St) (hspec : E.apex pre args post) :
    satisfiedE2Quint S E (encodeE2Quint S E pre args post) := by
  obtain ⟨hguard, hcomp1, hcomp2, hcomp3, hcomp4, hcomp5, hlogVal, hframe⟩ := hspec
  show satisfied (effectCircuit2Quint E) (encodeE2Quint S E pre args post)
  intro c hc
  rcases List.mem_append.mp hc with hcg | hc7
  · have hge : satisfied E.guardGates (encodeE2Quint S E pre args post) :=
      (E.guardLocal _ _ (fun w hw => encodeE2Quint_agrees_guardEncode S E pre args post w hw)).mpr
        (hGuardEnc pre args post hguard)
    exact hge c hcg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc7
    rcases hc7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (e2urest_iff S E pre args post).mpr (hRestF _ _ hframe)
    · exact (e2ubind1_iff S E pre args post).mpr
        (E.active1.encodes pre args (E.view.toKernel post) hcomp1)
    · exact (e2ubind2_iff S E pre args post).mpr
        (E.active2.encodes pre args (E.view.toKernel post) hcomp2)
    · exact (e2ubind3_iff S E pre args post).mpr
        (E.active3.encodes pre args (E.view.toKernel post) hcomp3)
    · exact (e2ubind4_iff S E pre args post).mpr
        (E.active4.encodes pre args (E.view.toKernel post) hcomp4)
    · exact (e2ubind5_iff S E pre args post).mpr
        (E.active5.encodes pre args (E.view.toKernel post) hcomp5)
    · exact (e2ulog_iff S E pre args post).mpr (by rw [hlogVal])

theorem effectCircuit2Quint_rejects_frame_tamper (hRestF : RestFrameDecodes2Quint S E)
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.restFrame (E.view.toKernel pre) (E.view.toKernel post)) :
    ¬ satisfiedE2Quint S E (encodeE2Quint S E pre args post) := by
  intro h
  have hrest := h cE2URestF (by simp [effectCircuit2Quint])
  exact htamper (hRestF _ _ ((e2urest_iff S E pre args post).mp hrest))

theorem effectCircuit2Quint_rejects_wrong_component1
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active1.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quint S E (encodeE2Quint S E pre args post) := by
  intro h
  have hbind := h cE2UBind1 (by simp [effectCircuit2Quint])
  exact htamper (E.active1.binds pre args (E.view.toKernel post) ((e2ubind1_iff S E pre args post).mp hbind))

theorem effectCircuit2Quint_rejects_wrong_component2
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active2.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quint S E (encodeE2Quint S E pre args post) := by
  intro h
  have hbind := h cE2UBind2 (by simp [effectCircuit2Quint])
  exact htamper (E.active2.binds pre args (E.view.toKernel post) ((e2ubind2_iff S E pre args post).mp hbind))

theorem effectCircuit2Quint_rejects_wrong_component3
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active3.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quint S E (encodeE2Quint S E pre args post) := by
  intro h
  have hbind := h cE2UBind3 (by simp [effectCircuit2Quint])
  exact htamper (E.active3.binds pre args (E.view.toKernel post) ((e2ubind3_iff S E pre args post).mp hbind))

theorem effectCircuit2Quint_rejects_wrong_component4
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active4.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quint S E (encodeE2Quint S E pre args post) := by
  intro h
  have hbind := h cE2UBind4 (by simp [effectCircuit2Quint])
  exact htamper (E.active4.binds pre args (E.view.toKernel post) ((e2ubind4_iff S E pre args post).mp hbind))

theorem effectCircuit2Quint_rejects_wrong_component5
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active5.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Quint S E (encodeE2Quint S E pre args post) := by
  intro h
  have hbind := h cE2UBind5 (by simp [effectCircuit2Quint])
  exact htamper (E.active5.binds pre args (E.view.toKernel post) ((e2ubind5_iff S E pre args post).mp hbind))

theorem effectCircuit2Quint_rejects_log_forge
    (pre : St) (args : Args) (post : St) (htamper : E.view.getLog post ≠ E.postLog pre args)
    (hno : ¬ Dregg2.Circuit.LogCommitRegrounded.LogColl S.LH (E.view.getLog post) (E.postLog pre args)) :
    ¬ satisfiedE2Quint S E (encodeE2Quint S E pre args post) := by
  intro h
  have hlog := h cE2ULog (by simp [effectCircuit2Quint])
  exact htamper (Dregg2.Circuit.LogCommitRegrounded.logHash_binds_of_noLogColl S.LH _ _ hno
    ((e2ulog_iff S E pre args post).mp hlog))

end Sound

/-! ## §6 — emission. -/

def emittedEffect2Quint {St Args : Type} (name : String) (E : EffectSpec2Quint St Args) :
    EmittedDescriptor :=
  emit name E.traceWidth (effectCircuit2Quint E)

theorem emitEffect2QuintFaithful {St Args : Type} (name : String) (E : EffectSpec2Quint St Args)
    (a : Assignment) :
    satisfied (effectCircuit2Quint E) a ↔ satisfiedEmitted (emittedEffect2Quint name E) a :=
  emit_faithful name E.traceWidth (effectCircuit2Quint E) a

#assert_axioms encodeE2Quint_agrees_guardEncode
#assert_axioms e2urest_iff
#assert_axioms e2ubind1_iff
#assert_axioms e2ubind2_iff
#assert_axioms e2ubind3_iff
#assert_axioms e2ubind4_iff
#assert_axioms e2ubind5_iff
#assert_axioms e2ulog_iff
#assert_axioms effect2quint_circuit_full_sound
#assert_axioms effect2quint_circuit_full_complete
#assert_axioms effectCircuit2Quint_rejects_frame_tamper
#assert_axioms effectCircuit2Quint_rejects_wrong_component1
#assert_axioms effectCircuit2Quint_rejects_wrong_component2
#assert_axioms effectCircuit2Quint_rejects_wrong_component3
#assert_axioms effectCircuit2Quint_rejects_wrong_component4
#assert_axioms effectCircuit2Quint_rejects_wrong_component5
#assert_axioms effectCircuit2Quint_rejects_log_forge
#assert_axioms emitEffect2QuintFaithful

end Dregg2.Circuit.EffectCommit5