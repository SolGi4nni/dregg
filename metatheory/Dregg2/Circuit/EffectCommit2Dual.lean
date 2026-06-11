/-
# Dregg2.Circuit.EffectCommit2Dual — the v2 GENERIC full-state circuit⟺spec framework for DUAL non-`cell`
components.

`EffectCommit2` covers effects touching ONE non-`cell` component (`bal`, a `List` side-table, or `caps`).
Escrow, bridge-outbound, and queue-enqueue/dequeue touch TWO (typically `bal` + `escrows`, or `queues` +
`bal` + `escrows` in Gate 3). This module is Gate 1: exactly TWO `ActiveComponent`s, proved ONCE.

## The design (literal product of v2)

  * `EffectSpec2Dual` — two `ActiveComponent`s (`active1`, `active2`), shared guard/log/`restFrame`.
  * Four EQ gates: `cE2RestF`, `cE2Bind1`, `cE2Bind2`, `cE2Log`.
  * `effect2dual_circuit_full_sound` — both bind gates fire ⇒ both `postClause`s ⇒ apex.
  * `restFrame` omits BOTH touched fields (carried per-effect via `RestIffNo*` portal).

Wire layout (`traceWidth = 74`, guard `< 64`):

  `64 preRoot · 65 postRoot · 66 restPre · 67 restPost · 68 comp1Post · 69 comp1Exp · 70 comp2Post ·
   71 comp2Exp · 72 logPost · 73 logExp`

ADDITIVE: imports `EffectCommit2` (reuses `ActiveComponent`, smart constructors, `Surface2`,
`StateView`); edits none of the v1/v2 keystones.
-/
import Dregg2.Circuit.EffectCommit2

namespace Dregg2.Circuit.EffectCommit2Dual

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit

set_option linter.dupNamespace false

/-! ## §0b — shared `RestIffNoBalEscrows` portal (the bal+escrows dual family). -/

/-- **`RestIffNoBalEscrows RH`** — the rest hash binds the 15 non-`bal`-non-`escrows` components
(BIDIRECTIONAL). Frame order matches the escrow/bridge dual specs. -/
def RestIffNoBalEscrows (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments ∧ k'.slotCaveats = k.slotCaveats
      ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps)

/-! ## §1 — `EffectSpec2Dual` (two touched non-`cell` components). -/

/-- **`EffectSpec2Dual St Args`** — per-effect data for a DUAL-component non-`cell` effect. -/
structure EffectSpec2Dual (St Args : Type) where
  view         : StateView St
  active1      : ActiveComponent St Args
  active2      : ActiveComponent St Args
  logUpdate    : Option (St → Args → List Turn)
  restFrame    : RecordKernelState → RecordKernelState → Prop
  guardGates   : ConstraintSystem
  guardProp    : St → Args → Prop
  guardWidth   : Nat
  guardEncode  : St → Args → St → Assignment
  guardLocal   : ∀ (a b : Assignment), (∀ w, w < guardWidth → a w = b w) →
                   (satisfied guardGates a ↔ satisfied guardGates b)
  guardWidth_le : guardWidth ≤ 64

/-- The post log the apex predicts. -/
def EffectSpec2Dual.postLog {St Args : Type} (E : EffectSpec2Dual St Args) (pre : St) (args : Args) :
    List Turn :=
  match E.logUpdate with
  | none   => E.view.getLog pre
  | some f => f pre args

/-- **`EffectSpec2Dual.apex`** — guard ∧ both component `postClause`s ∧ log ∧ `restFrame`. -/
def EffectSpec2Dual.apex {St Args : Type} (E : EffectSpec2Dual St Args) (pre : St) (args : Args)
    (post : St) : Prop :=
  E.guardProp pre args
  ∧ E.active1.postClause pre args (E.view.toKernel post)
  ∧ E.active2.postClause pre args (E.view.toKernel post)
  ∧ E.view.getLog post = E.postLog pre args
  ∧ E.restFrame (E.view.toKernel pre) (E.view.toKernel post)

/-! ## §2 — digest wires + encoder (concrete indices, `traceWidth = 74`). -/

abbrev vE2DPreRoot   : Var := 64
abbrev vE2DPostRoot  : Var := 65
abbrev vE2DRestPre   : Var := 66
abbrev vE2DRestPost  : Var := 67
abbrev vE2DComp1Post : Var := 68
abbrev vE2DComp1Exp  : Var := 69
abbrev vE2DComp2Post : Var := 70
abbrev vE2DComp2Exp  : Var := 71
abbrev vE2DLogPost   : Var := 72
abbrev vE2DLogExp    : Var := 73

def EffectSpec2Dual.traceWidth {St Args : Type} (_E : EffectSpec2Dual St Args) : Nat := 74

def effectStateCommit2Dual {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args)
    (k : RecordKernelState) (log : List Turn) : ℤ :=
  E.active1.digest k + E.active2.digest k + S.RH k + S.LH log

def encodeE2Dual {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args)
    (pre : St) (args : Args) (post : St) : Assignment :=
  fun w =>
    if      w = vE2DPreRoot   then
      effectStateCommit2Dual S E (E.view.toKernel pre) (E.view.getLog pre)
    else if w = vE2DPostRoot  then
      effectStateCommit2Dual S E (E.view.toKernel post) (E.view.getLog post)
    else if w = vE2DRestPre   then S.RH (E.view.toKernel pre)
    else if w = vE2DRestPost  then S.RH (E.view.toKernel post)
    else if w = vE2DComp1Post then E.active1.digest (E.view.toKernel post)
    else if w = vE2DComp1Exp  then E.active1.expected pre args
    else if w = vE2DComp2Post then E.active2.digest (E.view.toKernel post)
    else if w = vE2DComp2Exp  then E.active2.expected pre args
    else if w = vE2DLogPost   then S.LH (E.view.getLog post)
    else if w = vE2DLogExp    then S.LH (E.postLog pre args)
    else E.guardEncode pre args post w

theorem encodeE2Dual_agrees_guardEncode {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args)
    (pre : St) (args : Args) (post : St) (w : Var) (hw : w < E.guardWidth) :
    encodeE2Dual S E pre args post w = E.guardEncode pre args post w := by
  have hle := E.guardWidth_le
  unfold encodeE2Dual Var at *
  simp only [vE2DPreRoot, vE2DPostRoot, vE2DRestPre, vE2DRestPost, vE2DComp1Post, vE2DComp1Exp,
    vE2DComp2Post, vE2DComp2Exp, vE2DLogPost, vE2DLogExp]
  split_ifs <;> first | rfl | (exfalso; omega)

macro "ec2d_lookup" : tactic =>
  `(tactic| simp [encodeE2Dual, vE2DPreRoot, vE2DPostRoot, vE2DRestPre, vE2DRestPost, vE2DComp1Post,
      vE2DComp1Exp, vE2DComp2Post, vE2DComp2Exp, vE2DLogPost, vE2DLogExp])

section Lookups
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args) (pre : St) (args : Args)
  (post : St)

theorem enc2d_restPre :
    encodeE2Dual S E pre args post vE2DRestPre = S.RH (E.view.toKernel pre) := by ec2d_lookup
theorem enc2d_restPost :
    encodeE2Dual S E pre args post vE2DRestPost = S.RH (E.view.toKernel post) := by ec2d_lookup
theorem enc2d_comp1Post :
    encodeE2Dual S E pre args post vE2DComp1Post = E.active1.digest (E.view.toKernel post) := by ec2d_lookup
theorem enc2d_comp1Exp :
    encodeE2Dual S E pre args post vE2DComp1Exp = E.active1.expected pre args := by ec2d_lookup
theorem enc2d_comp2Post :
    encodeE2Dual S E pre args post vE2DComp2Post = E.active2.digest (E.view.toKernel post) := by ec2d_lookup
theorem enc2d_comp2Exp :
    encodeE2Dual S E pre args post vE2DComp2Exp = E.active2.expected pre args := by ec2d_lookup
theorem enc2d_logPost :
    encodeE2Dual S E pre args post vE2DLogPost = S.LH (E.view.getLog post) := by ec2d_lookup
theorem enc2d_logExp :
    encodeE2Dual S E pre args post vE2DLogExp = S.LH (E.postLog pre args) := by ec2d_lookup

end Lookups

/-! ## §3 — circuit + satisfaction. -/

def cE2DRestF : Constraint := { lhs := .var vE2DRestPre, rhs := .var vE2DRestPost }
def cE2DBind1 : Constraint := { lhs := .var vE2DComp1Post, rhs := .var vE2DComp1Exp }
def cE2DBind2 : Constraint := { lhs := .var vE2DComp2Post, rhs := .var vE2DComp2Exp }
def cE2DLog   : Constraint := { lhs := .var vE2DLogPost, rhs := .var vE2DLogExp }

def effectCircuit2Dual {St Args : Type} (E : EffectSpec2Dual St Args) : ConstraintSystem :=
  E.guardGates ++ [cE2DRestF, cE2DBind1, cE2DBind2, cE2DLog]

def satisfiedE2Dual {St Args : Type} (_S : Surface2) (E : EffectSpec2Dual St Args) (a : Assignment) :
    Prop :=
  satisfied (effectCircuit2Dual E) a

section GateIff
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args) (pre : St) (args : Args)
  (post : St)

theorem e2drest_iff :
    cE2DRestF.holds (encodeE2Dual S E pre args post)
      ↔ S.RH (E.view.toKernel pre) = S.RH (E.view.toKernel post) := by
  unfold Constraint.holds cE2DRestF
  simp only [Expr.eval, enc2d_restPre, enc2d_restPost]

theorem e2dbind1_iff :
    cE2DBind1.holds (encodeE2Dual S E pre args post)
      ↔ E.active1.digest (E.view.toKernel post) = E.active1.expected pre args := by
  unfold Constraint.holds cE2DBind1
  simp only [Expr.eval, enc2d_comp1Post, enc2d_comp1Exp]

theorem e2dbind2_iff :
    cE2DBind2.holds (encodeE2Dual S E pre args post)
      ↔ E.active2.digest (E.view.toKernel post) = E.active2.expected pre args := by
  unfold Constraint.holds cE2DBind2
  simp only [Expr.eval, enc2d_comp2Post, enc2d_comp2Exp]

theorem e2dlog_iff :
    cE2DLog.holds (encodeE2Dual S E pre args post)
      ↔ S.LH (E.view.getLog post) = S.LH (E.postLog pre args) := by
  unfold Constraint.holds cE2DLog
  simp only [Expr.eval, enc2d_logPost, enc2d_logExp]

end GateIff

/-! ## §4 — per-effect obligations (guard + rest-frame portals). -/

def GuardDecodes2Dual {St Args : Type} (E : EffectSpec2Dual St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    satisfied E.guardGates (E.guardEncode pre args post) → E.guardProp pre args

def GuardEncodes2Dual {St Args : Type} (E : EffectSpec2Dual St Args) : Prop :=
  ∀ (pre : St) (args : Args) (post : St),
    E.guardProp pre args → satisfied E.guardGates (E.guardEncode pre args post)

def RestFrameDecodes2Dual {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args) : Prop :=
  ∀ k k' : RecordKernelState, S.RH k = S.RH k' → E.restFrame k k'

def RestFrameEncodes2Dual {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args) : Prop :=
  ∀ k k' : RecordKernelState, E.restFrame k k' → S.RH k = S.RH k'

/-! ## §5 — the generic crown-jewel theorems (proved ONCE). -/

section Sound
variable {St Args : Type} (S : Surface2) (E : EffectSpec2Dual St Args)

theorem effect2dual_circuit_full_sound
    (hRestF : RestFrameDecodes2Dual S E) (hLog : logHashInjective S.LH)
    (hGuard : GuardDecodes2Dual E)
    (pre : St) (args : Args) (post : St)
    (h : satisfiedE2Dual S E (encodeE2Dual S E pre args post)) :
    E.apex pre args post := by
  have hArith : satisfied (effectCircuit2Dual E) (encodeE2Dual S E pre args post) := h
  have hguardSat : satisfied E.guardGates (encodeE2Dual S E pre args post) := by
    intro c hc; exact hArith c (by unfold effectCircuit2Dual; exact List.mem_append_left _ hc)
  have hguardSat' : satisfied E.guardGates (E.guardEncode pre args post) :=
    (E.guardLocal _ _ (fun w hw => encodeE2Dual_agrees_guardEncode S E pre args post w hw)).mp hguardSat
  have hguard : E.guardProp pre args := hGuard pre args post hguardSat'
  have hrest : cE2DRestF.holds (encodeE2Dual S E pre args post) :=
    hArith cE2DRestF (by simp [effectCircuit2Dual])
  have hbind1 : cE2DBind1.holds (encodeE2Dual S E pre args post) :=
    hArith cE2DBind1 (by simp [effectCircuit2Dual])
  have hbind2 : cE2DBind2.holds (encodeE2Dual S E pre args post) :=
    hArith cE2DBind2 (by simp [effectCircuit2Dual])
  have hlog : cE2DLog.holds (encodeE2Dual S E pre args post) :=
    hArith cE2DLog (by simp [effectCircuit2Dual])
  have hframe : E.restFrame (E.view.toKernel pre) (E.view.toKernel post) :=
    hRestF _ _ ((e2drest_iff S E pre args post).mp hrest)
  have hcomp1 : E.active1.postClause pre args (E.view.toKernel post) :=
    E.active1.binds pre args (E.view.toKernel post) ((e2dbind1_iff S E pre args post).mp hbind1)
  have hcomp2 : E.active2.postClause pre args (E.view.toKernel post) :=
    E.active2.binds pre args (E.view.toKernel post) ((e2dbind2_iff S E pre args post).mp hbind2)
  have hlogVal : E.view.getLog post = E.postLog pre args :=
    hLog _ _ ((e2dlog_iff S E pre args post).mp hlog)
  exact ⟨hguard, hcomp1, hcomp2, hlogVal, hframe⟩

theorem effect2dual_circuit_full_complete
    (hRestF : RestFrameEncodes2Dual S E) (hGuardEnc : GuardEncodes2Dual E)
    (pre : St) (args : Args) (post : St)
    (hspec : E.apex pre args post) :
    satisfiedE2Dual S E (encodeE2Dual S E pre args post) := by
  obtain ⟨hguard, hcomp1, hcomp2, hlogVal, hframe⟩ := hspec
  show satisfied (effectCircuit2Dual E) (encodeE2Dual S E pre args post)
  intro c hc
  rcases List.mem_append.mp hc with hcg | hc4
  · have hge : satisfied E.guardGates (encodeE2Dual S E pre args post) :=
      (E.guardLocal _ _ (fun w hw => encodeE2Dual_agrees_guardEncode S E pre args post w hw)).mpr
        (hGuardEnc pre args post hguard)
    exact hge c hcg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4
    rcases hc4 with rfl | rfl | rfl | rfl
    · exact (e2drest_iff S E pre args post).mpr (hRestF _ _ hframe)
    · exact (e2dbind1_iff S E pre args post).mpr
        (E.active1.encodes pre args (E.view.toKernel post) hcomp1)
    · exact (e2dbind2_iff S E pre args post).mpr
        (E.active2.encodes pre args (E.view.toKernel post) hcomp2)
    · exact (e2dlog_iff S E pre args post).mpr (by rw [hlogVal])

theorem effectCircuit2Dual_rejects_frame_tamper (hRestF : RestFrameDecodes2Dual S E)
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.restFrame (E.view.toKernel pre) (E.view.toKernel post)) :
    ¬ satisfiedE2Dual S E (encodeE2Dual S E pre args post) := by
  intro h
  have hrest := h cE2DRestF (by simp [effectCircuit2Dual])
  exact htamper (hRestF _ _ ((e2drest_iff S E pre args post).mp hrest))

theorem effectCircuit2Dual_rejects_wrong_component1
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active1.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Dual S E (encodeE2Dual S E pre args post) := by
  intro h
  have hbind := h cE2DBind1 (by simp [effectCircuit2Dual])
  exact htamper (E.active1.binds pre args (E.view.toKernel post) ((e2dbind1_iff S E pre args post).mp hbind))

theorem effectCircuit2Dual_rejects_wrong_component2
    (pre : St) (args : Args) (post : St)
    (htamper : ¬ E.active2.postClause pre args (E.view.toKernel post)) :
    ¬ satisfiedE2Dual S E (encodeE2Dual S E pre args post) := by
  intro h
  have hbind := h cE2DBind2 (by simp [effectCircuit2Dual])
  exact htamper (E.active2.binds pre args (E.view.toKernel post) ((e2dbind2_iff S E pre args post).mp hbind))

theorem effectCircuit2Dual_rejects_log_forge (hLog : logHashInjective S.LH)
    (pre : St) (args : Args) (post : St)
    (htamper : E.view.getLog post ≠ E.postLog pre args) :
    ¬ satisfiedE2Dual S E (encodeE2Dual S E pre args post) := by
  intro h
  have hlog := h cE2DLog (by simp [effectCircuit2Dual])
  exact htamper (hLog _ _ ((e2dlog_iff S E pre args post).mp hlog))

end Sound

/-! ## §6 — emission. -/

def emittedEffect2Dual {St Args : Type} (name : String) (E : EffectSpec2Dual St Args) :
    EmittedDescriptor :=
  emit name E.traceWidth (effectCircuit2Dual E)

theorem emitEffect2DualFaithful {St Args : Type} (name : String) (E : EffectSpec2Dual St Args)
    (a : Assignment) :
    satisfied (effectCircuit2Dual E) a ↔ satisfiedEmitted (emittedEffect2Dual name E) a :=
  emit_faithful name E.traceWidth (effectCircuit2Dual E) a

#assert_axioms encodeE2Dual_agrees_guardEncode
#assert_axioms e2drest_iff
#assert_axioms e2dbind1_iff
#assert_axioms e2dbind2_iff
#assert_axioms e2dlog_iff
#assert_axioms effect2dual_circuit_full_sound
#assert_axioms effect2dual_circuit_full_complete
#assert_axioms effectCircuit2Dual_rejects_frame_tamper
#assert_axioms effectCircuit2Dual_rejects_wrong_component1
#assert_axioms effectCircuit2Dual_rejects_wrong_component2
#assert_axioms effectCircuit2Dual_rejects_log_forge
#assert_axioms emitEffect2DualFaithful

end Dregg2.Circuit.EffectCommit2Dual