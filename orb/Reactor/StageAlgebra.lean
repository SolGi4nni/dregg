import Reactor.Pipeline
import Reactor.Stage.DateHeader
import Reactor.Stage.SecurityHeaders
import Reactor.Stage.CrossOriginResource
import Reactor.Stage.TimingAllowOrigin
import Reactor.Stage.PermissionsPolicy
import Reactor.Stage.Via
import Reactor.Stage.MethodFilter
import Reactor.Stage.Cors

/-!
# Reactor.StageAlgebra — deployed middleware stages re-expressed as DSL DATA

The deployed serve builds each middleware stage as a `Stage` VALUE — a pair of
`onRequest`/`onResponse` FUNCTIONS living in `Reactor/Stage/*.lean`. This module
introduces a small deep embedding, `StageProg`, whose terms are DATA describing a
stage, and a reference interpretation `denote : StageProg → Stage` that IS the
deployed serve semantics. For each re-expressed stage we prove that `denote <term>`
equals the deployed `Stage` (its `onRequest` and its `onResponse`), so the DSL term
is a faithful, data-level description of the running stage.

## The shared syntax (one algebra)

`StageProg` is the shared stage syntax; `denote` is ONE interpretation of it (the
deployed serve). A second interpretation — a byte-level lowering into the translator
IR — targets the SAME syntax, so a single keystone (compile p byte-equals denote p)
covers every stage at once. The constructors are:

* `skip`                          — the identity stage (the unit of `seq`).
* `addHeader (name val)`          — append a response header.
* `addHeaderOnce (name val)`      — append a header unless one with the same
  (case-insensitive) field name is already present (the idempotent stamp the
  deployed security/representation stages use).
* `setStatus (code reason)`       — overwrite the status line.
* `gate (c : ReqPred) (code)`     — short-circuit with a status when the
  request-predicate holds.
* `rewriteBody (t : BodyLoop)`    — a bounded body transform.
* `seq (a b)`                     — sequential composition.
* `condR (c : ReqPred) (a b)`     — branch on the request.

`skip` and `addHeaderOnce` are refinements this lane proposes to the shared algebra:
`skip` is the unit of `seq` (needed for the `condR` deny branch and as the base of a
header fold); `addHeaderOnce` is the idempotent-stamp leaf that the four
security/representation stamp stages actually run (their `onResponse` de-duplicates a
pre-existing field, which `addHeader`'s unconditional append cannot express). Both
are flagged in the residual notes.

## What is proved (pure kernel; `#print axioms` ⊆ {propext, Quot.sound})

Fully faithful (both phases equal the deployed stage, for ALL contexts):
* `dateHeader_*`               — `dateStage now` = `addHeader Date now`.
* `securityHeaders_*`          — `securityheadersStage` = a `seq`-fold of `addHeader`s.
* `corp_* / tao_* / pp_* / via_*` — the four stamp stages = `addHeaderOnce`.
* `headStrip_*`                — `headStripStage` = `condR (method = HEAD) (rewriteBody _) skip`.

Partial (control-flow / predicate faithful; refusal payload named as residual):
* `methodFilter_gate_*`        — `methodFilterStage` = `gate (¬allowed) 405` up to the
  405's `Allow` header / reason / body (which the status-only `gate` elides).
* `cors_*`                     — `corsStage` = `condR (originAllowed) (addHeader ACAO _) skip`
  on the deployed fixed-origin policy (witnessed allow/deny) + the general predicate
  alignment; the ctx-dependent ACAO echo is named as a residual.

## Residuals (named)

* `gate` carries only a status `code`; the deployed refusals (405 `Allow`, 403/429
  body/reason) need a richer `gate' (c : ReqPred) (r : Response)` to be BYTE-faithful,
  not merely status-faithful.
* `condR`/`addHeader` capture `cors` exactly for the deployed single fixed allowed
  origin (the ACAO value is then constant); a wildcard / credentialed / multi-origin
  policy echoes the request origin, needing an `addHeaderF (name) (val : Ctx → Bytes)`
  ctx-dependent-value leaf.
* Response-state predicates: the stamp de-dup keys on the RESPONSE headers, captured
  here by the dedicated `addHeaderOnce` leaf rather than a general response predicate.
-/

namespace Reactor.StageAlgebra

open Reactor (Response error4xx)
open Reactor.Pipeline
open Proto (Bytes)

/-! ## Field-name normalisation (the stamp stages' duplicate-detection key) -/

/-- ASCII-lowercase one byte — the exact normaliser the deployed stamp stages use. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a field name. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-! ## The syntax -/

/-- A request predicate — the shape `gate`/`condR` branch on. -/
abbrev ReqPred := Ctx → Bool

/-- A bounded body transform. -/
abbrev BodyLoop := Bytes → Bytes

/-- The shared stage syntax (deep embedding); its terms are DATA describing a
middleware stage. -/
inductive StageProg where
  | skip
  | addHeader (name val : Bytes)
  | addHeaderOnce (name val : Bytes)
  | setStatus (code : Nat) (reason : Bytes)
  | gate (c : ReqPred) (code : Nat)
  | rewriteBody (t : BodyLoop)
  | seq (a b : StageProg)
  | condR (c : ReqPred) (a b : StageProg)

/-- The idempotent append the stamp stages run: add `(name, val)` unless a field with
the same (case-insensitive) name is already present. -/
def stampOnce (name val : Bytes) (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if hs.any (fun nv => lower nv.1 == lower name) then hs else hs ++ [(name, val)]

/-! ## The reference interpretation — the deployed serve semantics -/

/-- `denote p` is the deployed serve's `Stage` for the program `p`: exactly the
`onRequest`/`onResponse` a `Reactor/Stage/*.lean` stage runs. The `name` field is
diagnostic (Pipeline notes it is not load-bearing), so faithfulness is stated on the
two semantic fields. -/
def denote : StageProg → Stage
  | .skip =>
      { name := "skip", onRequest := fun c => .continue c, onResponse := fun _ b => b }
  | .addHeader name val =>
      { name := "addHeader", onRequest := fun c => .continue c,
        onResponse := fun _ b => b.addHeader (name, val) }
  | .addHeaderOnce name val =>
      { name := "addHeaderOnce", onRequest := fun c => .continue c,
        onResponse := fun _ b =>
          b.mapResp (fun r => { r with headers := stampOnce name val r.headers }) }
  | .setStatus code reason =>
      { name := "setStatus", onRequest := fun c => .continue c,
        onResponse := fun _ b => (b.setStatus code).setReason reason }
  | .gate p code =>
      { name := "gate",
        onRequest := fun c => if p c then .respond (error4xx code [] []) else .continue c,
        onResponse := fun _ b => b }
  | .rewriteBody t =>
      { name := "rewriteBody", onRequest := fun c => .continue c,
        onResponse := fun _ b => b.mapResp (fun r => { r with body := t r.body }) }
  | .seq a b =>
      { name := "seq",
        onRequest := fun c =>
          match (denote a).onRequest c with
          | .continue c' => (denote b).onRequest c'
          | .respond r => .respond r,
        onResponse := fun c bld => (denote b).onResponse c ((denote a).onResponse c bld) }
  | .condR p a b =>
      { name := "condR",
        onRequest := fun c => if p c then (denote a).onRequest c else (denote b).onRequest c,
        onResponse := fun c bld =>
          if p c then (denote a).onResponse c bld else (denote b).onResponse c bld }

/-! ## 1. DateHeader — `dateStage now` = `addHeader Date now` (FULL) -/

open Reactor.Stage.DateHeader (dateStage dateName mHEAD stripBody headStripStage)

/-- The `Date` stage re-expressed as a term (`now` the current HTTP-date bytes). -/
def dateHeaderProg (now : Bytes) : StageProg := .addHeader dateName now

/-- Faithful response phase: identical single header append. -/
theorem dateHeader_onResponse (now : Bytes) (c : Ctx) (b : ResponseBuilder) :
    (denote (dateHeaderProg now)).onResponse c b = (dateStage now).onResponse c b := rfl

/-- Faithful request phase: both pass through. -/
theorem dateHeader_onRequest (now : Bytes) (c : Ctx) :
    (denote (dateHeaderProg now)).onRequest c = (dateStage now).onRequest c := rfl

/-! ## 2. SecurityHeaders — `securityheadersStage` = a `seq`-fold of `addHeader`s (FULL) -/

/-- Fold a header list into a right-nested `seq` of `addHeader` leaves (the base is
`skip`). This is the term form of the deployed `foldl addHeader` response phase. -/
def addHeadersProg : List (Bytes × Bytes) → StageProg
  | [] => .skip
  | h :: t => .seq (.addHeader h.1 h.2) (addHeadersProg t)

/-- The `seq`-fold's response phase is exactly `List.foldl addHeader` — the deployed
security-header response phase, for ANY header list. -/
theorem denote_addHeadersProg_onResponse (L : List (Bytes × Bytes)) (c : Ctx)
    (b : ResponseBuilder) :
    (denote (addHeadersProg L)).onResponse c b = L.foldl ResponseBuilder.addHeader b := by
  induction L generalizing b with
  | nil => rfl
  | cons h t ih =>
    show (denote (addHeadersProg t)).onResponse c
          ((denote (StageProg.addHeader h.1 h.2)).onResponse c b)
        = (h :: t).foldl ResponseBuilder.addHeader b
    rw [ih]; rfl

/-- The `seq`-fold's request phase passes through, for ANY header list. -/
theorem denote_addHeadersProg_onRequest (L : List (Bytes × Bytes)) (c : Ctx) :
    (denote (addHeadersProg L)).onRequest c = .continue c := by
  induction L generalizing c with
  | nil => rfl
  | cons h t ih =>
    show (denote (addHeadersProg t)).onRequest c = .continue c
    exact ih c

open Reactor.Stage.SecurityHeaders (securityheadersStage wireHeaders policy)

/-- The security-header stage re-expressed as the `seq`-fold over its REAL rendered
header set (`wireHeaders policy`). -/
def securityHeadersProg : StageProg := addHeadersProg (wireHeaders policy)

/-- **Faithful (response).** The term's response phase equals the deployed
`securityheadersStage.onResponse` exactly, for ALL contexts — both fold the real
rendered security-header set onto the affine builder. -/
theorem securityHeaders_onResponse (c : Ctx) (b : ResponseBuilder) :
    (denote securityHeadersProg).onResponse c b = securityheadersStage.onResponse c b := by
  rw [securityHeadersProg, denote_addHeadersProg_onResponse]; rfl

/-- **Faithful (request).** Both pass the request phase. -/
theorem securityHeaders_onRequest (c : Ctx) :
    (denote securityHeadersProg).onRequest c = securityheadersStage.onRequest c :=
  denote_addHeadersProg_onRequest _ c

/-! ## 3–6. The four stamp stages — `addHeaderOnce` (FULL)

Each deployed stamp stage runs `onResponse := b.mapResp (r ↦ {r with headers := stampX
r.headers})` where `stampX` appends `(name,val)` unless a field whose lowercased name
equals the field token is already present. `stampOnce name val` is definitionally that
same idempotent append (its lowercasing and the stage's coincide, and `lower name`
computes to the stage's lowercase token), so `denote (addHeaderOnce name val)` equals
the deployed stage's `onResponse` by reduction. -/

open Reactor.Stage.CrossOriginResource (corpStage corpName corpVal)
open Reactor.Stage.TimingAllowOrigin (taoStage taoName taoVal)
open Reactor.Stage.PermissionsPolicy (ppStage ppName ppVal)
open Reactor.Stage.Via (viaStage viaName viaVal)

/-- Cross-Origin-Resource-Policy stamp. -/
def corpProg : StageProg := .addHeaderOnce corpName corpVal
theorem corp_onResponse (c : Ctx) (b : ResponseBuilder) :
    (denote corpProg).onResponse c b = corpStage.onResponse c b := rfl
theorem corp_onRequest (c : Ctx) :
    (denote corpProg).onRequest c = corpStage.onRequest c := rfl

/-- Timing-Allow-Origin stamp. -/
def taoProg : StageProg := .addHeaderOnce taoName taoVal
theorem tao_onResponse (c : Ctx) (b : ResponseBuilder) :
    (denote taoProg).onResponse c b = taoStage.onResponse c b := rfl
theorem tao_onRequest (c : Ctx) :
    (denote taoProg).onRequest c = taoStage.onRequest c := rfl

/-- Permissions-Policy stamp. -/
def ppProg : StageProg := .addHeaderOnce ppName ppVal
theorem pp_onResponse (c : Ctx) (b : ResponseBuilder) :
    (denote ppProg).onResponse c b = ppStage.onResponse c b := rfl
theorem pp_onRequest (c : Ctx) :
    (denote ppProg).onRequest c = ppStage.onRequest c := rfl

/-- Via stamp. -/
def viaProg : StageProg := .addHeaderOnce viaName viaVal
theorem via_onResponse (c : Ctx) (b : ResponseBuilder) :
    (denote viaProg).onResponse c b = viaStage.onResponse c b := rfl
theorem via_onRequest (c : Ctx) :
    (denote viaProg).onRequest c = viaStage.onRequest c := rfl

/-! ## 7. headStrip — `condR (method = HEAD) (rewriteBody _) skip` (FULL) -/

/-- The HEAD body-strip stage re-expressed: on a HEAD request rewrite the body to
empty, else pass through. -/
def headStripProg : StageProg :=
  .condR (fun c => c.req.method == mHEAD) (.rewriteBody (fun _ => [])) .skip

/-- **Faithful (response).** The term's response phase equals `headStripStage`'s
exactly — on HEAD it wipes the body (`stripBody`), else identity — for ALL contexts. -/
theorem headStrip_onResponse (c : Ctx) (b : ResponseBuilder) :
    (denote headStripProg).onResponse c b = headStripStage.onResponse c b := rfl

/-- **Faithful (request).** Both pass the request phase (`condR` on a response-only
pair collapses to a pass-through). -/
theorem headStrip_onRequest (c : Ctx) :
    (denote headStripProg).onRequest c = headStripStage.onRequest c := by
  show (if c.req.method == mHEAD then StageStep.continue c else StageStep.continue c)
      = StageStep.continue c
  split <;> rfl

/-! ## 8. MethodFilter — `gate (¬allowed) 405` (control-flow / status faithful) -/

open Reactor.Stage.MethodFilter (methodFilterStage isAllowed methodNotAllowed)

/-- The predicate the gate fires on: a method NOT in the allow-list. -/
def methodFilterFires : ReqPred := fun c => ! isAllowed c.req.method

/-- The method-filter gate re-expressed (status-only refusal; the `Allow` header and
reason/body are the named residual of the status-only `gate`). -/
def methodFilterProg : StageProg := .gate methodFilterFires 405

/-- **Faithful control-flow.** The gate `.respond`s exactly when the deployed stage
refuses and `.continue`s exactly when it passes — the abstract gate tracks the real
admission decision for ALL contexts (the emitted refusal status is `405` either way;
see `methodFilter_gate_status`). -/
theorem methodFilter_gate_control (c : Ctx) :
    (denote methodFilterProg).onRequest c
      = (match methodFilterStage.onRequest c with
         | .respond _ => .respond (error4xx 405 [] [])
         | .continue c' => .continue c') := by
  show (if methodFilterFires c then StageStep.respond (error4xx 405 [] []) else .continue c)
      = (match (if isAllowed c.req.method then StageStep.continue c
                else .respond methodNotAllowed) with
         | .respond _ => .respond (error4xx 405 [] [])
         | .continue c' => .continue c')
  unfold methodFilterFires
  cases h : isAllowed c.req.method <;> simp [h]

/-- **Status agreement.** When the gate refuses, its status is exactly the deployed
`405`'s status. (The `405`'s `Allow` header / reason / body are elided by the
status-only `gate` — the named residual.) -/
theorem methodFilter_gate_status : (error4xx 405 [] []).status = methodNotAllowed.status := rfl

/-! ## 9. Cors — `condR (originAllowed) (addHeader ACAO _) skip` (witnessed + aligned)

For the deployed single fixed allowed origin the ACAO value is constant, so `condR` +
`addHeader` reproduce the stage. Below: the allow and the deny both match the deployed
`onResponse` byte-for-byte, and the general predicate alignment shows the `condR`
guard IS the deployed grant condition. The ctx-dependent ACAO ECHO (needed for a
wildcard / credentialed / multi-origin policy) is the named residual. -/

open Reactor.Stage.Cors
  (corsStage corsPolicy originOf acaoName strBytes allowedCtx allowedCtx_origin)

/-- The allowed origin's ACAO value bytes (constant for the deployed single-origin
policy). -/
def corsAllowedValue : Bytes := strBytes "https://app.example.com"

/-- The CORS stage re-expressed for the deployed fixed-origin policy. -/
def corsProg : StageProg :=
  .condR (fun c => _root_.Cors.originAllowed corsPolicy (originOf c))
         (.addHeader acaoName corsAllowedValue) .skip

/-- **Predicate alignment (ALL contexts).** The `condR` guard `originAllowed` is
exactly the deployed grant condition: the stage emits an ACAO iff the guard holds
(`acaoValue` is `some` iff `originAllowed`, for this non-credentialed non-wildcard
policy). -/
theorem cors_guard_aligned (c : Ctx) :
    (_root_.Cors.acaoValue corsPolicy (originOf c)).isSome
      = _root_.Cors.originAllowed corsPolicy (originOf c) := by
  unfold _root_.Cors.acaoValue corsPolicy
  cases _root_.Cors.originAllowed _ (originOf c) <;> rfl

/-- **Faithful on the allow witness.** For the allowed origin the term's response phase
stamps exactly the deployed ACAO header. -/
theorem cors_allowed_onResponse (b : ResponseBuilder) :
    (denote corsProg).onResponse allowedCtx b = corsStage.onResponse allowedCtx b := by
  have hp : _root_.Cors.originAllowed corsPolicy (originOf allowedCtx) = true := by
    rw [allowedCtx_origin]; decide
  have hv : _root_.Cors.acaoValue corsPolicy (originOf allowedCtx)
      = some "https://app.example.com" := by rw [allowedCtx_origin]; decide
  show (if _root_.Cors.originAllowed corsPolicy (originOf allowedCtx)
        then b.addHeader (acaoName, corsAllowedValue) else b)
      = (match _root_.Cors.acaoValue corsPolicy (originOf allowedCtx) with
         | some v => b.addHeader (acaoName, strBytes v)
         | none => b)
  simp [hp, hv, corsAllowedValue]

/-- A request carrying no `Origin` — the deny witness (empty origin is on no
allow-list). -/
def deniedCtx : Ctx := { input := [], req := {} }

/-- **Faithful on the deny witness.** A disallowed origin adds nothing — both the term
and the deployed stage return the builder untouched. -/
theorem cors_denied_onResponse (b : ResponseBuilder) :
    (denote corsProg).onResponse deniedCtx b = corsStage.onResponse deniedCtx b := by
  have hp : _root_.Cors.originAllowed corsPolicy (originOf deniedCtx) = false := by decide
  have hv : _root_.Cors.acaoValue corsPolicy (originOf deniedCtx) = none := by decide
  show (if _root_.Cors.originAllowed corsPolicy (originOf deniedCtx)
        then b.addHeader (acaoName, corsAllowedValue) else b)
      = (match _root_.Cors.acaoValue corsPolicy (originOf deniedCtx) with
         | some v => b.addHeader (acaoName, strBytes v)
         | none => b)
  simp [hp, hv]

/-- **Faithful (request).** Both pass the request phase. -/
theorem cors_onRequest (c : Ctx) :
    (denote corsProg).onRequest c = corsStage.onRequest c := by
  show (if _root_.Cors.originAllowed corsPolicy (originOf c)
        then StageStep.continue c else StageStep.continue c) = .continue c
  split <;> rfl

/-! ## Axiom audit -/

#print axioms dateHeader_onResponse
#print axioms securityHeaders_onResponse
#print axioms corp_onResponse
#print axioms tao_onResponse
#print axioms pp_onResponse
#print axioms via_onResponse
#print axioms headStrip_onResponse
#print axioms methodFilter_gate_control
#print axioms cors_guard_aligned
#print axioms cors_allowed_onResponse
#print axioms cors_denied_onResponse

end Reactor.StageAlgebra
