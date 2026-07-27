/-
  Pancake/StageLift2Inst.lean — THE PER-STAGE INSTANTIATION LAYER, ON THE CORRECT
  INTERPRETER.

  WHY THIS FILE EXISTS. `StageLift2.lean` migrated the stage SHAPE lemmas onto the
  two-phase onion (`StageProg2`'s `RespProg`/`denoteR`, `StageSpec`, `runChain`) — the
  denotation that actually matches the deployed serve, where a fired gate does NOT
  absorb the other stages' response phases. But the migration stopped at the shapes:
  the PER-STAGE instantiations still existed only against the OLD flat
  `StageProg.denote`. This file re-instantiates the deployed stages through the NEW
  lemmas, so the per-stage pins say something true about the REAL whole-chain serve.

  WHAT IS RE-INSTANTIATED HERE, AND WHAT IS NOT — the honest split.

  A stamp stage ports through `denoteR_stampProg` / `runChain_stampSpec` iff its
  DECISION reads only the CONTEXT. `RespProg.condR`'s predicate is `ReqPred = Ctx →
  Bool`; it cannot read the response threaded up from the inner onion. So:

   * CTX-DECIDED stamps (§3) port EXACTLY — one line each. Their decision is a
     function of the request/route alone (`inScope c`, an attribute lookup, an origin
     policy), and their value, where computed, is CONSTANT once the context is fixed,
     so it is carried as a `val` witness (`hval : valOf ctx = val`) exactly as the
     shape lemma's `val` argument.

   * RESPONSE-DECIDED stamps (§6) DO NOT PORT, and are NOT forced. Every one of them
     keys on the ARRIVING response — `r.status == 200`, `!hasX r.headers`,
     `isTransformed r.headers`. The old lift pre-baked those at `ctx.base`, which
     under the true onion is NOT the response the stage sees (the arriving response is
     the inner result, after every inner stage's response phase). Pinning them through
     a `Ctx → Bool` decision would be a FALSE pin — the claim would be about a serve
     the deployed stage does not perform. They are listed, counted, and left blocked
     on a `condResp` constructor, whose required shape is specified in §6.

  A gate stage ports through `runChain_gateSpec` / `runChain_gateChainSpec` iff its
  REFUSAL is a constant record (or a record family over an explicit parameter). Every
  deployed gate is of that shape — the refusal is written by the stage, not read off
  the response — so ALL of them port (§4, §5), including the multi-status if-chains.

  CURRENCY. The pins are stated in `StageLift2`'s builder-erased currency (`stampFn`,
  `gateEmitH`, `gateChainEmitH`) — the deployed response phase's functional effect,
  with the affine builder erased through its own faithfulness equations. That is the
  same currency the shape lemmas are proven in, and it is what composes under
  `runChain`.

  DECISIONS AS PARAMETERS. Every deployed decision (`inScope`, a CIDR match, a token
  bucket, a signature check, an origin policy) enters as a universally quantified
  parameter named for what it computes. This package cannot import the deployed
  libraries; the lift is about the stage SHAPE, and the decisions are the deployed
  libraries' own proven cores. The pins therefore hold for the REAL decision, whatever
  it computes.

  Own file. Imports `StageLift2` and edits nothing — no other file is touched.
  Axiom audit at the end: expect ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx.
-/
import Pancake.StageLift2

namespace Pancake.StageLift2Inst

open Pancake Pancake.SerializeCompile Pancake.StageProg Pancake.StageOnion Pancake.StageLift2

/-! ## 1. The conditional-SET shape — a `condR` over a whole header list

One deployed stamp (the content-language stage) appends a PAIR of headers under a
single ctx decision. The single-header shape (`stampProg2`) does not cover it and the
multi-header shape (`addHeadersR`) is unconditional, so the conditional-set shape is
derived HERE, from `denoteR_addHeadersR` — a genuine shape lemma, not a special case.
Everything else in this file goes through `StageLift2`'s lemmas unchanged. -/

/-- **The conditional-set program** — `condR p (addHeadersR nvs) skip`. -/
def condSetProg (p : ReqPred) (nvs : List (Bytes × Bytes)) : RespProg :=
  .condR p (addHeadersR nvs) .skip

/-- **The deployed conditional-set's functional response effect**: append the whole
list exactly when the decision fires at this context. -/
def condSetFn (p : ReqPred) (nvs : List (Bytes × Bytes)) (ctx : Ctx) (r : Response) : Response :=
  if p ctx then { r with headers := r.headers ++ nvs } else r

/-- **`denoteR_condSetProg`.** The conditional-set program's `denoteR` computes the
deployed conditional whole-list append, for ANY decision, ANY list and ANY arriving
response. Both branches are discharged, so it is not vacuous. -/
theorem denoteR_condSetProg (p : ReqPred) (nvs : List (Bytes × Bytes))
    (ctx : Ctx) (r : Response) :
    denoteR ctx (condSetProg p nvs) r = condSetFn p nvs ctx r := by
  show (if p ctx then denoteR ctx (addHeadersR nvs) r else denoteR ctx .skip r)
      = condSetFn p nvs ctx r
  unfold condSetFn
  cases h : p ctx with
  | true => exact denoteR_addHeadersR ctx nvs r
  | false => rfl

/-- **The conditional-set STAGE** — passes the request, appends the set on its own
decision. -/
def condSetSpec (p : ReqPred) (nvs : List (Bytes × Bytes)) : StageSpec :=
  { guard := fun _ => false, refusal := .skip, onResp := condSetProg p nvs }

/-- **`runChain_condSetSpec`.** A single conditional-set stage over a handler passes to
the handler and appends its set under its decision. -/
theorem runChain_condSetSpec (p : ReqPred) (nvs : List (Bytes × Bytes))
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [condSetSpec p nvs] = condSetFn p nvs ctx (handler ctx) := by
  rw [runChain_stage_effect ctx handler (condSetSpec p nvs) [] rfl, runChain_nil]
  show denoteR ctx (condSetProg p nvs) (handler ctx) = _
  rw [denoteR_condSetProg]

/-! ## 2. The stamp field bytes — the exact ASCII the deployed stages render -/

/-- `Content-Type` field name. -/
def ctName : Bytes := str "Content-Type"
/-- The deployed HTML media type. -/
def htmlVal : Bytes := str "text/html"
/-- The deployed server-sent-events media type. -/
def sseVal : Bytes := str "text/event-stream"
/-- `Set-Cookie` field name. -/
def setCookieName : Bytes := str "Set-Cookie"
/-- The deployed session cookie value. -/
def sessionCookieVal : Bytes := str "sid=1; Path=/"
/-- `X-Request-Id` field name. -/
def ridName : Bytes := str "X-Request-Id"
/-- `X-Forwarded-For` field name. -/
def xffName : Bytes := str "X-Forwarded-For"
/-- `Access-Control-Allow-Origin` field name. -/
def acaoName : Bytes := str "Access-Control-Allow-Origin"
/-- `Date` field name. -/
def dateName : Bytes := str "Date"
/-- `Content-Language` field name. -/
def clHdrName : Bytes := str "Content-Language"
/-- `Vary` field name. -/
def varyName : Bytes := str "Vary"
/-- The deployed language-negotiation `Vary` value. -/
def langVaryVal : Bytes := str "Accept-Language"

/-! ## 3. THE CTX-DECIDED STAMP INSTANTIATIONS — one line each, on the correct interpreter

Each stage below gets TWO pins:

 * a `denoteR` pin — the stage's RESPONSE PHASE over ANY arriving response `r`. This is
   the onion-composable statement: `r` is the true inner result, not a pre-baked
   `ctx.base`. It is what carries the stamp onto an inner gate's refusal (§7).
 * a `runChain` pin — the stage's whole single-stage SERVE, over ANY handler.

Both go through `StageLift2`'s lemmas (`denoteR_stampProg` / `runChain_stampSpec` /
`denoteR_condSetProg` / `runChain_stampSetSpec`), one line each. -/

/-! ### 3.1 The route-scoped media-type / cookie stamps (decision: `inScope c`) -/

/-- **The dashboard content-type stage** (deployed: `if inScope c then b.addHeader
(ctName, htmlVal) else b`) — the decision is the route test, a pure ctx predicate. -/
def dashTypeSpec (inScope : ReqPred) : StageSpec := stampSpec inScope ctName htmlVal

/-- **`denoteR_dashType`** — the response phase, over ANY arriving response. -/
theorem denoteR_dashType (inScope : ReqPred) (ctx : Ctx) (r : Response) :
    denoteR ctx (dashTypeSpec inScope).onResp r = stampFn inScope ctName htmlVal ctx r :=
  denoteR_stampProg inScope ctName htmlVal ctx r

/-- **`runChain_dashType`** — the single-stage serve, over ANY handler. -/
theorem runChain_dashType (inScope : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [dashTypeSpec inScope]
      = stampFn inScope ctName htmlVal ctx (handler ctx) :=
  runChain_stampSpec inScope ctName htmlVal handler ctx

/-- **The single-page-app content-type stage** — same shape, same route-test decision. -/
def spaTypeSpec (inScope : ReqPred) : StageSpec := stampSpec inScope ctName htmlVal

/-- **`denoteR_spaType`** — the response phase, over ANY arriving response. -/
theorem denoteR_spaType (inScope : ReqPred) (ctx : Ctx) (r : Response) :
    denoteR ctx (spaTypeSpec inScope).onResp r = stampFn inScope ctName htmlVal ctx r :=
  denoteR_stampProg inScope ctName htmlVal ctx r

/-- **`runChain_spaType`** — the single-stage serve, over ANY handler. -/
theorem runChain_spaType (inScope : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [spaTypeSpec inScope]
      = stampFn inScope ctName htmlVal ctx (handler ctx) :=
  runChain_stampSpec inScope ctName htmlVal handler ctx

/-- **The server-sent-events content-type stage** (deployed `text/event-stream`). -/
def sseHeadSpec (inScope : ReqPred) : StageSpec := stampSpec inScope ctName sseVal

/-- **`denoteR_sseHead`** — the response phase, over ANY arriving response. -/
theorem denoteR_sseHead (inScope : ReqPred) (ctx : Ctx) (r : Response) :
    denoteR ctx (sseHeadSpec inScope).onResp r = stampFn inScope ctName sseVal ctx r :=
  denoteR_stampProg inScope ctName sseVal ctx r

/-- **`runChain_sseHead`** — the single-stage serve, over ANY handler. -/
theorem runChain_sseHead (inScope : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [sseHeadSpec inScope]
      = stampFn inScope ctName sseVal ctx (handler ctx) :=
  runChain_stampSpec inScope ctName sseVal handler ctx

/-- **The session-cookie stage** (deployed: `if inScope c then b.addHeader
(setCookieName, weakCookie) else b`). -/
def setCookieSpec (inScope : ReqPred) : StageSpec :=
  stampSpec inScope setCookieName sessionCookieVal

/-- **`denoteR_setCookie`** — the response phase, over ANY arriving response. -/
theorem denoteR_setCookie (inScope : ReqPred) (ctx : Ctx) (r : Response) :
    denoteR ctx (setCookieSpec inScope).onResp r
      = stampFn inScope setCookieName sessionCookieVal ctx r :=
  denoteR_stampProg inScope setCookieName sessionCookieVal ctx r

/-- **`runChain_setCookie`** — the single-stage serve, over ANY handler. -/
theorem runChain_setCookie (inScope : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [setCookieSpec inScope]
      = stampFn inScope setCookieName sessionCookieVal ctx (handler ctx) :=
  runChain_stampSpec inScope setCookieName sessionCookieVal handler ctx

/-! ### 3.2 The ctx-COMPUTED-value stamps

The value is a function of the CONTEXT only (an attribute lookup, an origin policy, a
clock reading already fixed in the context). Once the context is fixed the value is a
constant, so it is carried as the shape lemma's `val` argument under an explicit
witness `hval : valOf ctx = val` — the value is the deployed stage's own, not invented
here. NOTE the witness type: `valOf : Ctx → Bytes`, NOT `Ctx → Response → Bytes`. A
value that had to read the arriving response would be response-decided and would
belong in §6. -/

/-- **The request-id stage** (deployed: appends on BOTH branches — the correlation id
from the attribute lookup if present, else the context's own id — i.e. an
UNCONDITIONAL append at a ctx-chosen value). -/
def ridSpec (val : Bytes) : StageSpec := stampSpec (fun _ => true) ridName val

/-- **`denoteR_rid`** — the response phase appends the stage's own chosen id to ANY
arriving response, unconditionally. -/
theorem denoteR_rid (idOf : Ctx → Bytes) (val : Bytes) (ctx : Ctx) (r : Response)
    (hval : idOf ctx = val) :
    denoteR ctx (ridSpec val).onResp r
      = { r with headers := r.headers ++ [(ridName, idOf ctx)] } := by
  subst hval
  exact denoteR_alwaysStamp ridName (idOf ctx) ctx r

/-- **`runChain_rid`** — the single-stage serve, over ANY handler. -/
theorem runChain_rid (idOf : Ctx → Bytes) (val : Bytes) (handler : Ctx → Response) (ctx : Ctx)
    (hval : idOf ctx = val) :
    runChain ctx handler [ridSpec val]
      = { handler ctx with headers := (handler ctx).headers ++ [(ridName, idOf ctx)] } := by
  subst hval
  rw [runChain_stage_effect ctx handler (ridSpec (idOf ctx)) [] rfl, runChain_nil]
  exact denoteR_alwaysStamp ridName (idOf ctx) ctx (handler ctx)

/-- **The proxy-protocol stage** (deployed: `match c.attrs.find? … | some p =>
b.addHeader (xffName, p.2) | none => b`) — a conditional append; BOTH the decision
(the recovered client address is present or it is not) and the value are read off the
CONTEXT's attributes. `present` is that lookup's success. -/
def proxyProtoSpec (present : ReqPred) (val : Bytes) : StageSpec :=
  stampSpec present xffName val

/-- **`denoteR_proxyProto`** — the response phase, over ANY arriving response. -/
theorem denoteR_proxyProto (present : ReqPred) (addrOf : Ctx → Bytes) (val : Bytes)
    (ctx : Ctx) (r : Response) (hval : addrOf ctx = val) :
    denoteR ctx (proxyProtoSpec present val).onResp r
      = stampFn present xffName (addrOf ctx) ctx r := by
  subst hval
  exact denoteR_stampProg present xffName (addrOf ctx) ctx r

/-- **`runChain_proxyProto`** — the single-stage serve, over ANY handler. -/
theorem runChain_proxyProto (present : ReqPred) (addrOf : Ctx → Bytes) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) (hval : addrOf ctx = val) :
    runChain ctx handler [proxyProtoSpec present val]
      = stampFn present xffName (addrOf ctx) ctx (handler ctx) := by
  subst hval
  exact runChain_stampSpec present xffName (addrOf ctx) handler ctx

/-- **The cross-origin stage** (deployed: `match acaoValue policy (originOf c) with |
some v => b.addHeader (acaoName, strBytes v) | none => b`) — the policy admits this
context's origin or it does not, and the admitted value is the policy's. Both read the
CONTEXT only. -/
def corsSpec (admits : ReqPred) (val : Bytes) : StageSpec := stampSpec admits acaoName val

/-- **`denoteR_cors`** — the response phase, over ANY arriving response. -/
theorem denoteR_cors (admits : ReqPred) (valOf : Ctx → Bytes) (val : Bytes)
    (ctx : Ctx) (r : Response) (hval : valOf ctx = val) :
    denoteR ctx (corsSpec admits val).onResp r = stampFn admits acaoName (valOf ctx) ctx r := by
  subst hval
  exact denoteR_stampProg admits acaoName (valOf ctx) ctx r

/-- **`runChain_cors`** — the single-stage serve, over ANY handler. -/
theorem runChain_cors (admits : ReqPred) (valOf : Ctx → Bytes) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) (hval : valOf ctx = val) :
    runChain ctx handler [corsSpec admits val]
      = stampFn admits acaoName (valOf ctx) ctx (handler ctx) := by
  subst hval
  exact runChain_stampSpec admits acaoName (valOf ctx) handler ctx

/-! ### 3.3 The unconditional stamp -/

/-- **The date stage** (deployed: `fun _ b => b.addHeader (dateName, now)`) — the bare
unconditional append at the serve instant fixed for this response. -/
def dateSpec (now : Bytes) : StageSpec := stampSpec (fun _ => true) dateName now

/-- **`denoteR_date`** — the response phase appends `Date` to ANY arriving response. -/
theorem denoteR_date (now : Bytes) (ctx : Ctx) (r : Response) :
    denoteR ctx (dateSpec now).onResp r = { r with headers := r.headers ++ [(dateName, now)] } :=
  denoteR_alwaysStamp dateName now ctx r

/-- **`runChain_date`** — the single-stage serve, over ANY handler. -/
theorem runChain_date (now : Bytes) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [dateSpec now]
      = { handler ctx with headers := (handler ctx).headers ++ [(dateName, now)] } := by
  rw [runChain_stage_effect ctx handler (dateSpec now) [] rfl, runChain_nil]
  exact denoteR_alwaysStamp dateName now ctx (handler ctx)

/-! ### 3.4 The multi-header stamps -/

/-- **The security-header stage** (deployed: `fun _ b => (wireHeaders policy).foldl
ResponseBuilder.addHeader b`) — the WHOLE rendered policy set, at ANY size, in one
term. The set is a parameter: the pin holds for whatever the policy renders. -/
def securityHeadersSpec (wireHeaders : List (Bytes × Bytes)) : StageSpec :=
  stampSetSpec wireHeaders

/-- **`denoteR_securityHeaders`** — the response phase appends the whole rendered set,
in order, to ANY arriving response. -/
theorem denoteR_securityHeaders (wireHeaders : List (Bytes × Bytes)) (ctx : Ctx) (r : Response) :
    denoteR ctx (securityHeadersSpec wireHeaders).onResp r
      = { r with headers := r.headers ++ wireHeaders } :=
  denoteR_addHeadersR ctx wireHeaders r

/-- **`runChain_securityHeaders`** — the single-stage serve, over ANY handler. -/
theorem runChain_securityHeaders (wireHeaders : List (Bytes × Bytes))
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [securityHeadersSpec wireHeaders]
      = { handler ctx with headers := (handler ctx).headers ++ wireHeaders } :=
  runChain_stampSetSpec wireHeaders handler ctx

/-- **The content-language stage** (deployed: `if inScope c then (b.addHeader
(clHdrName, tagOf (negotiate c.req))).addHeader (varyName, varyVal) else b`) — a
CONDITIONAL PAIR of appends. The decision is the route test and the negotiated tag is a
function of the request, so both are ctx-only: it ports through the conditional-set
shape (§1) at the tag witness. -/
def langStampSpec (inScope : ReqPred) (tag : Bytes) : StageSpec :=
  condSetSpec inScope [(clHdrName, tag), (varyName, langVaryVal)]

/-- **`denoteR_langStamp`** — the response phase over ANY arriving response: on the
stage's route, the negotiated tag and the negotiation cache key are appended as a pair;
off it, the response passes untouched. Both branches live in `condSetFn`. -/
theorem denoteR_langStamp (inScope : ReqPred) (tagOf : Ctx → Bytes) (tag : Bytes)
    (ctx : Ctx) (r : Response) (htag : tagOf ctx = tag) :
    denoteR ctx (langStampSpec inScope tag).onResp r
      = condSetFn inScope [(clHdrName, tagOf ctx), (varyName, langVaryVal)] ctx r := by
  subst htag
  exact denoteR_condSetProg inScope [(clHdrName, tagOf ctx), (varyName, langVaryVal)] ctx r

/-- **`runChain_langStamp`** — the single-stage serve, over ANY handler. -/
theorem runChain_langStamp (inScope : ReqPred) (tagOf : Ctx → Bytes) (tag : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) (htag : tagOf ctx = tag) :
    runChain ctx handler [langStampSpec inScope tag]
      = condSetFn inScope [(clHdrName, tagOf ctx), (varyName, langVaryVal)] ctx (handler ctx) := by
  subst htag
  exact runChain_condSetSpec inScope [(clHdrName, tagOf ctx), (varyName, langVaryVal)] handler ctx

/-! ## 4. The gate refusal records — transcribed field for field

Each record is the deployed stage's OWN refusal (status / reason phrase / headers /
body). The generically-constructed refusals carry an EMPTY header list by that
constructor's definition; the record-built ones carry the headers the stage writes.
`methodNotAllowed` and `forbidden403` are reused from `StageLift2` (§5.1 there). -/

/-- `413` — body-size cap refusal. -/
def contentTooLarge : Response :=
  { status := 413, reason := str "Content Too Large", headers := [],
    body := str "content too large\n" }

/-- `503` — per-source connection-cap refusal. -/
def resp503 : Response :=
  { status := 503, reason := str "Service Unavailable", headers := [],
    body := str "per-source connection limit reached\n" }

/-- `431` — request-head byte-cap refusal. -/
def requestHeaderFieldsTooLarge : Response :=
  { status := 431, reason := str "Request Header Fields Too Large", headers := [],
    body := str "request header fields too large\n" }

/-- `414` — request-target length refusal. -/
def uriTooLong : Response :=
  { status := 414, reason := str "URI Too Long", headers := [],
    body := str "uri too long\n" }

/-- `429` — aggregated stick-counter threshold refusal. -/
def stickResp429 : Response :=
  { status := 429, reason := str "Too Many Requests", headers := [],
    body := str "aggregated request limit exceeded\n" }

/-- `429` — token-bucket rate refusal. -/
def rateResp429 : Response :=
  { status := 429, reason := str "Too Many Requests", headers := [],
    body := str "rate limit exceeded\n" }

/-- `408` — header-dribble timeout refusal. -/
def resp408 : Response :=
  { status := 408, reason := str "Request Timeout", headers := [],
    body := str "request header timeout\n" }

/-- `304` — conditional-request hit: carries the validator instant, empty body by
definition of a `304`. -/
def notModified304 : Response :=
  { status := 304, reason := str "Not Modified",
    headers := [(str "Last-Modified", str "Mon, 01 Jan 2024 00:00:00 GMT")],
    body := [] }

/-- `400` — malformed-request refusal (shared by the framing and validation gates). -/
def badRequest400 : Response :=
  { status := 400, reason := str "Bad Request", headers := [],
    body := str "bad request\n" }

/-- `417` — unsatisfiable `Expect` refusal. -/
def expectationFailed417 : Response :=
  { status := 417, reason := str "Expectation Failed", headers := [],
    body := str "expectation failed\n" }

/-- `501` — unrecognized method refusal. -/
def notImplemented501 : Response :=
  { status := 501, reason := str "Not Implemented", headers := [],
    body := str "not implemented\n" }

/-- `505` — unsupported protocol version refusal. -/
def badVersion505 : Response :=
  { status := 505, reason := str "HTTP Version Not Supported", headers := [],
    body := str "http version not supported\n" }

/-- `421` — `Host` allow-list refusal. -/
def misdirected421 : Response :=
  { status := 421, reason := str "Misdirected Request", headers := [],
    body := str "misdirected request\n" }

/-- `401` — bearer-token refusal: carries the challenge. -/
def bearerUnauthorized : Response :=
  { status := 401, reason := str "Unauthorized",
    headers := [(str "WWW-Authenticate", str "Bearer")],
    body := str "invalid or missing bearer token" }

/-- `401` — credential refusal carrying EXACTLY the challenge value the real
authenticator produced (a family over the challenge, one gate per value). -/
def basicUnauthorized (www : Bytes) : Response :=
  { status := 401, reason := str "Unauthorized",
    headers := [(str "WWW-Authenticate", www)],
    body := str "authentication required" }

/-- `401` — auth-subrequest deny. -/
def authResp401 : Response :=
  { status := 401, reason := str "Unauthorized", headers := [],
    body := str "auth subrequest denied\n" }

/-- `403` — auth-subrequest deny. -/
def authResp403 : Response :=
  { status := 403, reason := str "Forbidden", headers := [],
    body := str "auth subrequest denied\n" }

/-- `500` — auth-subrequest fail-closed. -/
def authResp500 : Response :=
  { status := 500, reason := str "Internal Server Error", headers := [],
    body := str "auth subrequest failed\n" }

/-- `500` — forwarded-auth fail-closed. -/
def forwardResp500 : Response :=
  { status := 500, reason := str "Internal Server Error", headers := [],
    body := str "auth subrequest failed\n" }

/-- The forwarded-auth deny reason phrase table (`401` ⇒ `Unauthorized`, anything else
⇒ `Forbidden`). -/
def forwardReasonOf : Nat → Bytes
  | 401 => str "Unauthorized"
  | _   => str "Forbidden"

/-- `4xx` — forwarded-auth deny, a family over the carried status. -/
def forwardDenyResp (status : Nat) : Response :=
  { status := status, reason := forwardReasonOf status, headers := [],
    body := str "auth subrequest denied\n" }

/-! ## 5. THE GATE INSTANTIATIONS — one line each, on the correct interpreter

Every deployed gate's refusal is a CONSTANT record written by the stage (or a record
family over an explicit parameter), so every one ports through `runChain_gateSpec` /
`runChain_gateChainSpec` unchanged. `fire` stays universally quantified: it is whatever
the deployed stage computes.

WHAT THE NEW PIN BUYS over the old one. The old `denote_gateWith` pins needed a side
condition `ctx.base.headers = []` (the flat gate appended onto the base's headers) and
leaked the base body. The new pins are HYPOTHESIS-FREE — the refusal is built over the
fresh `blankResp` seed, so it reaches the wire exactly as the stage wrote it — and the
PASS branch yields the HANDLER, not a fixed `ctx.base`. -/

/-! ### 5.1 The single-refusal gates -/

/-- **Method allow-list gate (`405`).** -/
theorem runChain_methodFilter (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire methodNotAllowed]
      = gateEmitH fire methodNotAllowed handler ctx :=
  runChain_gateSpec fire methodNotAllowed handler ctx

/-- **CIDR admission gate (`403`).** -/
theorem runChain_ipFilter (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire forbidden403] = gateEmitH fire forbidden403 handler ctx :=
  runChain_gateSpec fire forbidden403 handler ctx

/-- **Body-size cap gate (`413`).** -/
theorem runChain_bodyLimit (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire contentTooLarge]
      = gateEmitH fire contentTooLarge handler ctx :=
  runChain_gateSpec fire contentTooLarge handler ctx

/-- **Per-source connection-cap gate (`503`).** -/
theorem runChain_connLimit (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire resp503] = gateEmitH fire resp503 handler ctx :=
  runChain_gateSpec fire resp503 handler ctx

/-- **Request-head byte-cap gate (`431`).** -/
theorem runChain_requestHeadLimit (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire requestHeaderFieldsTooLarge]
      = gateEmitH fire requestHeaderFieldsTooLarge handler ctx :=
  runChain_gateSpec fire requestHeaderFieldsTooLarge handler ctx

/-- **Request-target length gate (`414`).** -/
theorem runChain_uriTooLong (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire uriTooLong] = gateEmitH fire uriTooLong handler ctx :=
  runChain_gateSpec fire uriTooLong handler ctx

/-- **Aggregated stick-counter gate (`429`).** -/
theorem runChain_stickTable (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire stickResp429] = gateEmitH fire stickResp429 handler ctx :=
  runChain_gateSpec fire stickResp429 handler ctx

/-- **Token-bucket rate gate (`429`).** -/
theorem runChain_rate (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire rateResp429] = gateEmitH fire rateResp429 handler ctx :=
  runChain_gateSpec fire rateResp429 handler ctx

/-- **Header-dribble timeout gate (`408`).** -/
theorem runChain_slowloris (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire resp408] = gateEmitH fire resp408 handler ctx :=
  runChain_gateSpec fire resp408 handler ctx

/-- **Conditional-request gate (`304` + the validator instant).** -/
theorem runChain_modifiedSince (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire notModified304]
      = gateEmitH fire notModified304 handler ctx :=
  runChain_gateSpec fire notModified304 handler ctx

/-- **`Host` allow-list gate (`421`).** -/
theorem runChain_hostAllowlist (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire misdirected421]
      = gateEmitH fire misdirected421 handler ctx :=
  runChain_gateSpec fire misdirected421 handler ctx

/-- **Bearer-token gate (`401` + the challenge).** -/
theorem runChain_jwt (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire bearerUnauthorized]
      = gateEmitH fire bearerUnauthorized handler ctx :=
  runChain_gateSpec fire bearerUnauthorized handler ctx

/-- **Credential gate (`401` + the authenticator's own challenge).** A FAMILY: one gate
per challenge value the real authenticator produces. -/
theorem runChain_basicAuth (fire : ReqPred) (www : Bytes) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire (basicUnauthorized www)]
      = gateEmitH fire (basicUnauthorized www) handler ctx :=
  runChain_gateSpec fire (basicUnauthorized www) handler ctx

/-! ### 5.2 The multi-status if-chain gates — ONE stage, ordered branches -/

/-- **Auth-subrequest gate — the three-outcome if-chain (`401` / `403` / `500`).** -/
theorem runChain_authRequest (f401 f403 f500 : ReqPred) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler
        [gateChainSpec [(f401, authResp401), (f403, authResp403), (f500, authResp500)]]
      = gateChainEmitH [(f401, authResp401), (f403, authResp403), (f500, authResp500)]
          handler ctx :=
  runChain_gateChainSpec _ handler ctx

/-- **Forwarded-auth gate — deny at a carried status, else fail-closed `500`.** A FAMILY
over the carried deny status. -/
theorem runChain_forwardAuth (fdeny f500 : ReqPred) (status : Nat)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler
        [gateChainSpec [(fdeny, forwardDenyResp status), (f500, forwardResp500)]]
      = gateChainEmitH [(fdeny, forwardDenyResp status), (f500, forwardResp500)] handler ctx :=
  runChain_gateChainSpec _ handler ctx

/-- **Framing-validation gate — the ordered three-branch chain (`400` field-name, `400`
transfer-coding, `417` `Expect`).** -/
theorem runChain_framingValidation (fname fte fexp : ReqPred)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler
        [gateChainSpec [(fname, badRequest400), (fte, badRequest400),
                        (fexp, expectationFailed417)]]
      = gateChainEmitH [(fname, badRequest400), (fte, badRequest400),
                        (fexp, expectationFailed417)] handler ctx :=
  runChain_gateChainSpec _ handler ctx

/-- **Request-validation gate — the ordered three-branch chain (`505` version, `501`
method, `400` host).** The deployed nesting tests version first, then method, then host;
the chain's branch order is that order. -/
theorem runChain_requestValidation (fver fmeth fhost : ReqPred)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler
        [gateChainSpec [(fver, badVersion505), (fmeth, notImplemented501),
                        (fhost, badRequest400)]]
      = gateChainEmitH [(fver, badVersion505), (fmeth, notImplemented501),
                        (fhost, badRequest400)] handler ctx :=
  runChain_gateChainSpec _ handler ctx

/-! ## 6. THE `condResp`-BLOCKED SET — named, counted, NOT forced

The stamps below are RESPONSE-DECIDED: the deployed decision reads the response that
ARRIVES at the stage's response phase. Under the two-phase onion that response is the
INNER result — every inner stage's response phase has already run on it, and if an
inner gate fired it is the REFUSAL, not the handler's `ctx.base` at all. `condR`'s
predicate is `ReqPred = Ctx → Bool`, so none of these is expressible, and pinning them
at `ctx.base` (what the old lift did) would assert a serve the deployed stage does not
perform. They are left blocked rather than falsely pinned.

  §8.1 unless-present family — decision `!hasX r.headers` on the ARRIVING response:
    1. alt-svc            `Alt-Svc`
    2. permissions-policy `Permissions-Policy`
    3. resource-policy    `Cross-Origin-Resource-Policy`
    4. timing-allow       `Timing-Allow-Origin`
    5. via                `Via`
    6. vary-encoding      `Vary`
    7. vary-excluded      `Vary` with a ctx route exclusion — the EXCLUSION is
                          ctx-decided, but it wraps a response-decided inner stamp, so
                          the composite is blocked on the inner decision alone.
  §8.2 positive-polarity / status-keyed family:
    8. warning            `Warning`      — `isTransformed r.headers && !hasWarning r.headers`
    9. link-preload       `Link`         — `r.status == 200 && !hasLink r.headers`
   10. cache-status       `Cache-Status` — `!hasCS r.headers`, AND a value computed from
                          `r.headers` (`isHit`): needs a response-reading VALUE too.
  §8.3 status-keyed conditional-append family:
   11. cache-control      `Cache-Control`    — `r.status == 200 && isStaticGet c`
   12. asset-expires      `Expires`          — same decision
   13. asset-immutable    `Cache-Control`    — same decision
   14. last-modified      `Last-Modified`    — `r.status == 200 && isStaticGet c &&
                                               !hasLm r.headers`
   15. retry-after        `Retry-After`      — `needsRetryAfter r.status`
   16. content-location   `Content-Location` — `r.status == 200 && isStaticGet c`
                          (its VALUE is ctx-only; only the decision blocks it)

DESIGN NOTE — WHAT `condResp` MUST BE (the next `StageProg2` extension).

A response-reading conditional constructor on `RespProg`:

    | condResp (c : Ctx → Response → Bool) (a b : RespProg)

with the denotation clause

    | .condResp c a b, r => if c ctx r then denoteR ctx a r else denoteR ctx b r

The predicate MUST be applied to the ARRIVING `r` — the `denoteR` argument — and not to
`ctx.base`. That is the whole content of the extension: it is what makes the decision
see the inner onion's result. Note `denoteR` stays a plain fold (no `halted` flag, no
gate) — `condResp` is a response TRANSFORM, so the gate/response split that
`StageProg2` is built on is preserved, and `runChain`/`respFold` need no change at all.

Consequences to discharge with it:
 * The stamp shape generalizes: `stampProgR c name val = condResp c (addHeader name
   val) skip`, with `denoteR_stampProgR : denoteR ctx (stampProgR c name val) r =
   (if c ctx r then { r with headers := r.headers ++ [(name, val)] } else r)` — the
   same two-branch proof as `denoteR_stampProg`, one `cases` on `c ctx r`. All 16
   stages above then instantiate it one line each, exactly as §3 does.
 * `condR` becomes derivable (`condR c a b = condResp (fun ctx _ => c ctx) a b`), so
   §3's ctx-decided pins survive unchanged — the extension is CONSERVATIVE over this
   file.
 * The COMPILER side is the real work, and is where the extension must be paid for:
   `compileR` (StageProg2 §6) compiles `condR c a b` by naming the decision through
   `nm : ReqPred → String`. A `condResp` decision reads the response, which at the
   machine level lives in the encoded cells (`Enc3`'s `aStat`/`aCnt`/`aBody`) — so its
   compiled test must READ those cells rather than call a named ctx oracle. The
   status-keyed decisions (`r.status == 200`, `needsRetryAfter r.status`) are the
   tractable first case: the status IS `aStat`, so they compile to a comparison against
   a live cell, and `compileR_correct`'s `condR` case extends by the same `Enc3`
   framing argument already used there. The `!hasX r.headers` decisions are HARDER —
   the header list is not in `Enc3` (only its COUNT, `aCnt`, is), so they need a header
   representation on the machine side first. That is a separate, larger piece of work
   and should not be smuggled in with `condResp`.
 * Cache-status additionally needs a response-reading VALUE (`valOf : Ctx → Response →
   Bytes`), which `addHeader`'s constant `val` cannot express — a strictly further
   extension (`addHeaderOf`), not covered by `condResp` alone.

RECOMMENDED ORDER: `condResp` + the status-keyed subset (items 9, 11–16, and the
decision half of 8) first — they are 8 of the 16 and need only `aStat`. The
header-list-reading subset (1–7, 8's `hasWarning`, 10) waits on a machine-side header
representation. -/

/-! ## 7. THE PAYOFF — the re-instantiated stages compose under the true onion

The point of re-instantiating on the correct interpreter: these stages now compose with
a firing gate the way the deployed serve does. Under the OLD flat `denote` a fired gate
ABSORBED every later op, so a refusal went out bare. Here the security-header set and
the date stamp CARRY onto a real gate's refusal — through the proven keystone, at the
real refusal records. -/

/-- **Security headers carry onto a method refusal.** The deployed policy set, at ANY
size, lands on the `405` — for ANY handler (which never runs). -/
theorem securityHeaders_on_methodRefusal (wireHeaders : List (Bytes × Bytes))
    (fire : ReqPred) (handler : Ctx → Response) (ctx : Ctx) (hfire : fire ctx = true) :
    runChain ctx handler [securityHeadersSpec wireHeaders, gateSpec fire methodNotAllowed]
      = { methodNotAllowed with headers := methodNotAllowed.headers ++ wireHeaders } :=
  stampSet_carries_on_gate_refusal wireHeaders fire methodNotAllowed handler ctx hfire

/-- **The date stamp carries onto an auth refusal.** A `401` still gets its `Date`. -/
theorem date_on_authRefusal (now : Bytes) (fire : ReqPred)
    (handler : Ctx → Response) (ctx : Ctx) (hfire : fire ctx = true) :
    runChain ctx handler [dateSpec now, gateSpec fire bearerUnauthorized]
      = { bearerUnauthorized with
            headers := bearerUnauthorized.headers ++ [(dateName, now)] } :=
  stamp_carries_on_gate_refusal dateName now fire bearerUnauthorized handler ctx hfire

/-! ## 8. Non-vacuity — the instantiations genuinely compute, both branches live

Kernel `#guard`s on the re-instantiated stages, at the real field bytes. A pin that
held only vacuously could not decide these. -/

/-- A rendered two-element policy set, for the concrete checks. -/
def demoPolicy : List (Bytes × Bytes) :=
  [(str "X-Frame-Options", str "DENY"), (str "X-Content-Type-Options", str "nosniff")]

/-- The route test used in the concrete checks: this demo scopes on the `GET` route. -/
def demoInScope : ReqPred := fun c => c.req.method = str "GET"

-- the ctx-decided stamp fires ON its route and does NOT off it (both branches live):
#guard (runChain ctxGet (fun c => c.base) [dashTypeSpec demoInScope]).headers
        = baseOk.headers ++ [(ctName, htmlVal)]
#guard (runChain ctxPost (fun c => c.base) [dashTypeSpec demoInScope]).headers = baseOk.headers
-- the media types are genuinely distinct stages (SSE is not HTML):
#guard (runChain ctxGet (fun c => c.base) [sseHeadSpec demoInScope]).headers
        = baseOk.headers ++ [(ctName, sseVal)]
-- the unconditional stamps always land:
#guard (runChain ctxPost (fun c => c.base) [dateSpec (str "Mon, 01 Jan 2024 00:00:00 GMT")]).headers
        = baseOk.headers ++ [(dateName, str "Mon, 01 Jan 2024 00:00:00 GMT")]
#guard (runChain ctxPost (fun c => c.base) [ridSpec (str "abc123")]).headers
        = baseOk.headers ++ [(ridName, str "abc123")]
-- the multi-header stage appends the WHOLE set, in order:
#guard (runChain ctxGet (fun c => c.base) [securityHeadersSpec demoPolicy]).headers
        = baseOk.headers ++ demoPolicy
-- the conditional PAIR lands as a pair on-route, and nothing off-route:
#guard (runChain ctxGet (fun c => c.base) [langStampSpec demoInScope (str "en")]).headers
        = baseOk.headers ++ [(clHdrName, str "en"), (varyName, langVaryVal)]
#guard (runChain ctxPost (fun c => c.base) [langStampSpec demoInScope (str "en")]).headers
        = baseOk.headers

-- the gates land their REAL refusal records on fire (status, reason and body all fresh):
#guard (runChain ctxPost (fun c => c.base) [gateSpec (fun _ => true) uriTooLong]).status = 414
#guard (runChain ctxPost (fun c => c.base) [gateSpec (fun _ => true) uriTooLong]).body
        = str "uri too long\n"
#guard (runChain ctxPost (fun c => c.base) [gateSpec (fun _ => true) bearerUnauthorized]).headers
        = [(str "WWW-Authenticate", str "Bearer")]
-- and the HANDLER on pass (not a fixed base — the handler genuinely runs):
#guard serialize (runChain ctxGet (fun c => c.base) [gateSpec (fun _ => false) uriTooLong])
        = serialize baseOk
-- distinct gates drive distinct wire bytes (the pins are not collapsing):
#guard serialize (runChain ctxPost (fun c => c.base) [gateSpec (fun _ => true) uriTooLong])
        ≠ serialize (runChain ctxPost (fun c => c.base) [gateSpec (fun _ => true) resp408])

-- the if-chain picks the FIRST firing branch, in the deployed order:
#guard (runChain ctxPost (fun c => c.base)
          [gateChainSpec [(fun _ => true, badVersion505), (fun _ => true, notImplemented501),
                          (fun _ => false, badRequest400)]]).status = 505
#guard (runChain ctxPost (fun c => c.base)
          [gateChainSpec [(fun _ => false, badVersion505), (fun _ => true, notImplemented501),
                          (fun _ => false, badRequest400)]]).status = 501
#guard (runChain ctxPost (fun c => c.base)
          [gateChainSpec [(fun _ => false, badVersion505), (fun _ => false, notImplemented501),
                          (fun _ => true, badRequest400)]]).status = 400
-- a request clearing every branch reaches the handler:
#guard serialize (runChain ctxGet (fun c => c.base)
          [gateChainSpec [(fun _ => false, badVersion505), (fun _ => false, notImplemented501),
                          (fun _ => false, badRequest400)]])
        = serialize baseOk
-- the forwarded-auth family carries its status AND the reason table:
#guard (runChain ctxPost (fun c => c.base)
          [gateChainSpec [(fun _ => true, forwardDenyResp 401),
                          (fun _ => false, forwardResp500)]]).reason = str "Unauthorized"
#guard (runChain ctxPost (fun c => c.base)
          [gateChainSpec [(fun _ => true, forwardDenyResp 403),
                          (fun _ => false, forwardResp500)]]).reason = str "Forbidden"

-- THE PAYOFF, concretely: the policy set CARRIES onto a fired gate's refusal, and the
-- refusal record stays fresh underneath it (this is what the old flat denote got wrong):
#guard (runChain ctxPost (fun c => c.base)
          [securityHeadersSpec demoPolicy, gateSpec (fun _ => true) methodNotAllowed]).headers
        = methodNotAllowed.headers ++ demoPolicy
#guard (runChain ctxPost (fun c => c.base)
          [securityHeadersSpec demoPolicy, gateSpec (fun _ => true) methodNotAllowed]).status = 405
#guard (runChain ctxPost (fun c => c.base)
          [securityHeadersSpec demoPolicy, gateSpec (fun _ => true) methodNotAllowed]).body
        = str "method not allowed\n"

/-! ## 9. Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx. -/

#print axioms denoteR_condSetProg
#print axioms runChain_condSetSpec
#print axioms denoteR_dashType
#print axioms runChain_dashType
#print axioms denoteR_spaType
#print axioms runChain_spaType
#print axioms denoteR_sseHead
#print axioms runChain_sseHead
#print axioms denoteR_setCookie
#print axioms runChain_setCookie
#print axioms denoteR_rid
#print axioms runChain_rid
#print axioms denoteR_proxyProto
#print axioms runChain_proxyProto
#print axioms denoteR_cors
#print axioms runChain_cors
#print axioms denoteR_date
#print axioms runChain_date
#print axioms denoteR_securityHeaders
#print axioms runChain_securityHeaders
#print axioms denoteR_langStamp
#print axioms runChain_langStamp
#print axioms runChain_methodFilter
#print axioms runChain_ipFilter
#print axioms runChain_bodyLimit
#print axioms runChain_connLimit
#print axioms runChain_requestHeadLimit
#print axioms runChain_uriTooLong
#print axioms runChain_stickTable
#print axioms runChain_rate
#print axioms runChain_slowloris
#print axioms runChain_modifiedSince
#print axioms runChain_hostAllowlist
#print axioms runChain_jwt
#print axioms runChain_basicAuth
#print axioms runChain_authRequest
#print axioms runChain_forwardAuth
#print axioms runChain_framingValidation
#print axioms runChain_requestValidation
#print axioms securityHeaders_on_methodRefusal
#print axioms date_on_authRefusal

end Pancake.StageLift2Inst
