import Reactor.Pipeline
import Reactor.Stage.ContentLanguage

/-!
# Reactor.Stage.NotAcceptable — the language `406` (RFC 9110 §12.5.4 / §15.5.7)

A byte-driving request GATE closing the negotiated route's named residual: the
deployed `GET /welcome` negotiation (`Reactor.Stage.ContentLanguage`) picks the
maximal-q representation, but a request whose `Accept-Language` assigns `q=0`
to EVERY served representation — "not acceptable" by RFC 9110 §12.4.2 ("a
weight of 0 means 'not acceptable'") — was served the default anyway (wire
capture 2026-07-13: `Accept-Language: de;q=0, en;q=0` on `/welcome` is answered
the full `200 en`). RFC 9110 §15.5.7 names the honest refusal: `406 (Not
Acceptable)`, with a body that "SHOULD generate content containing a list of
available representation characteristics" — the body here lists the served
language tags, one per line.

The gate fires exactly when (a) the request is the negotiated route's
(`GET /welcome`), (b) an `Accept-Language` is present, and (c) EVERY served
representation scores `q = 0` under the PROVEN negotiation scorer (`qFor` — the
same function the deployed argmax rides, so gate and negotiation can never
disagree about acceptability). Everything else passes through untouched; a
request with no `Accept-Language` is the §12.5.4 "no preference" case and is
served the default, as before.

## What is proven here (pure kernel; no `native_decide`, no `ofReduceBool`)

* `naGate_fires` / `naGate_passes` — the exact firing condition.
* `allUnacceptable_sound` — a firing condition really does score EVERY served
  language 0, including the one the deployed argmax would have picked
  (`negotiated_scores_zero` — the refusal and the negotiation are consistent).
* `notAcceptable_lists_tags` — the refusal body carries every served tag.
* Status-stability; non-vacuous witnesses by `decide`.
-/

namespace Reactor.Stage.NotAcceptable

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)
open Reactor.Stage.ContentLanguage (Lang hasAl qFor tagOf negotiate inScope
  welcomeTarget getBytes)

/-- Does the request score EVERY served representation `q = 0` (with an
`Accept-Language` present — no header means "no preference", not refusal)? -/
def allUnacceptable (req : Proto.Request) : Bool :=
  hasAl req && (qFor req (tagOf .en) == 0) && (qFor req (tagOf .de) == 0)
    && (qFor req (tagOf .fr) == 0)

/-- The refusal body: the available representation characteristics (RFC 9110
§15.5.7) — one served language tag per line. -/
def naBody : Bytes := [101, 110, 10, 100, 101, 10, 102, 114, 10]

-- The literal is the string it claims to be (`en\nde\nfr\n`).
#guard naBody == "en\nde\nfr\n".toUTF8.toList

/-- The `406 (Not Acceptable)` refusal. -/
def notAcceptableResp : Response :=
  { status := 406
    reason := "Not Acceptable".toUTF8.toList
    headers := []
    body := naBody }

/-- **The firing condition**: the negotiated route, all representations
unacceptable. -/
def fires (c : Ctx) : Bool :=
  inScope c && allUnacceptable c.req

/-- **The language `406` gate.** A firing request is refused the `406`;
everything else passes through UNTOUCHED. -/
def naGateStage : Stage where
  name := "language-not-acceptable-406"
  onRequest := fun c => if fires c then .respond notAcceptableResp else .continue c
  onResponse := fun _ b => b

theorem naGate_fires (c : Ctx) (h : fires c = true) :
    naGateStage.onRequest c = .respond notAcceptableResp := by
  show (if fires c then StageStep.respond notAcceptableResp
        else StageStep.continue c) = _
  rw [h]
  rfl

theorem naGate_passes (c : Ctx) (h : fires c = false) :
    naGateStage.onRequest c = .continue c := by
  show (if fires c then StageStep.respond notAcceptableResp
        else StageStep.continue c) = _
  rw [h]
  rfl

/-- The gate's response phase is the identity. -/
theorem naGate_onResponse_id (c : Ctx) (b : ResponseBuilder) :
    naGateStage.onResponse c b = b := rfl

theorem naGate_statusStable : Stage.statusStable naGateStage :=
  fun _ _ => rfl

theorem notAcceptable_status : notAcceptableResp.status = 406 := rfl

/-- Off the negotiated route the gate NEVER fires. -/
theorem fires_off_welcome (c : Ctx) (hw : ¬ c.req.target = welcomeTarget) :
    fires c = false := by
  unfold fires inScope
  have ht : (c.req.target == welcomeTarget) = false := by
    cases h : c.req.target == welcomeTarget
    · rfl
    · exact absurd (eq_of_beq h) hw
  rw [ht, Bool.and_false, Bool.false_and]

/-- **Soundness**: a firing condition scores EVERY served language `0` — the
refusal is genuinely "no acceptable representation". -/
theorem allUnacceptable_sound (req : Proto.Request)
    (h : allUnacceptable req = true) :
    ∀ l : Lang, qFor req (tagOf l) = 0 := by
  unfold allUnacceptable at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, hen⟩, hde⟩, hfr⟩ := h
  intro l
  cases l
  · exact eq_of_beq hen
  · exact eq_of_beq hde
  · exact eq_of_beq hfr

/-- Even the representation the deployed argmax would have picked scores `0` —
the refusal and the negotiation are consistent (rides `allUnacceptable_sound`
at the negotiated point). -/
theorem negotiated_scores_zero (req : Proto.Request)
    (h : allUnacceptable req = true) :
    qFor req (tagOf (negotiate req)) = 0 :=
  allUnacceptable_sound req h (negotiate req)

/-- The refusal body carries every served tag (RFC 9110 §15.5.7). -/
theorem notAcceptable_lists_tags :
    ∀ l : Lang, ∃ pre post, notAcceptableResp.body = pre ++ tagOf l ++ post := by
  intro l
  cases l
  · exact ⟨[], [10, 100, 101, 10, 102, 114, 10], by decide⟩
  · exact ⟨[101, 110, 10], [10, 102, 114, 10], by decide⟩
  · exact ⟨[101, 110, 10, 100, 101, 10], [10], by decide⟩

/-! ## Non-vacuity (kernel `decide` on concrete bytes) -/

/-- `GET /welcome` scoring every representation `q=0` — the gate fires. -/
def q0Ctx : Ctx :=
  { input := []
    req := { method := [71, 69, 84]
             target := [47, 119, 101, 108, 99, 111, 109, 101]
             version := []
             headers := [([65, 99, 99, 101, 112, 116, 45, 76, 97, 110, 103,
               117, 97, 103, 101],
               [100, 101, 59, 113, 61, 48, 44, 32, 101, 110, 59, 113, 61, 48,
                44, 32, 102, 114, 59, 113, 61, 48])] }
    attrs := [] }

example : fires q0Ctx = true := by decide

/-- A wholly-unsupported range (`xx`) scores every representation 0 too. -/
def xxCtx : Ctx :=
  { q0Ctx with
    req := { q0Ctx.req with
      headers := [([65, 99, 99, 101, 112, 116, 45, 76, 97, 110, 103, 117,
        97, 103, 101], [120, 120])] } }

example : fires xxCtx = true := by decide

/-- Any positive q on a served tag negotiates as before — the gate passes. -/
def deCtx : Ctx :=
  { q0Ctx with
    req := { q0Ctx.req with
      headers := [([65, 99, 99, 101, 112, 116, 45, 76, 97, 110, 103, 117,
        97, 103, 101], [100, 101, 44, 32, 101, 110, 59, 113, 61, 48])] } }

example : fires deCtx = false := by decide

/-- No `Accept-Language` at all — "no preference", served the default. -/
def bareCtx : Ctx :=
  { q0Ctx with req := { q0Ctx.req with headers := [] } }

example : fires bareCtx = false := by decide

/-- Off the route (`/bulk` with the all-`q=0` header): passes. -/
def q0BulkCtx : Ctx :=
  { q0Ctx with req := { q0Ctx.req with target := [47, 98, 117, 108, 107] } }

example : fires q0BulkCtx = false := by decide

end Reactor.Stage.NotAcceptable

#print axioms Reactor.Stage.NotAcceptable.naGate_fires
#print axioms Reactor.Stage.NotAcceptable.allUnacceptable_sound
#print axioms Reactor.Stage.NotAcceptable.negotiated_scores_zero
