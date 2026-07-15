import Reactor.DeployPlus4
import Reactor.Stage.CookieSecure
import Reactor.Stage.SessionCookie
import Reactor.Stage.SseServe
import Reactor.Stage.SpaServe

/-!
# Reactor.DeployPlus5 — three PARTIAL parity rows deepened into the DEFAULT serve

Wires the deployed-serve halves of three previously PARTIAL parity rows onto the
EXACT `Reactor.DeployPlus4.deployStagesPlus4` fold the running default serves —
`deployStagesPlus4` is referenced read-only, so every existing deployed proof
stands:

* **ck.1** (`Reactor.Stage.SessionCookie` + the previously-INERT
  `Reactor.Stage.CookieSecure`): `GET /login` issues a session cookie and the
  deployed hardener repairs it — the wire carries
  `Set-Cookie: sid=…; Secure; HttpOnly; SameSite=Lax`.
* **sse.1** (`Reactor.Stage.SseServe`): `GET /events` — previously a deployed
  `404` under a fully proven framing library — serves a
  `200 text/event-stream` whose body is the PROVEN SSE encoder's bytes, with the
  encode/decode inversion instantiated on the deployed events.
* **rt.7** (`Reactor.Stage.SpaServe`): `GET /app/…` — previously a deployed
  `404` under a proven-but-inert fallback model — serves the SPA shell selected
  by the PROVEN `spaServedPath`, its filesystem hypothesis DISCHARGED against
  the real embedded FS; prefix-scoped, so every other route (including the
  conformance suites' `404` probes) is untouched.

## Stage geometry

`deployStagesPlus5` puts the three method+target-scoped GATES just ahead of the
deployed plus4 fold (their answers still traverse the ENTIRE deployed response
onion — TAO, Via, CORP, Permissions-Policy, Alt-Svc, Cache-Status, security
headers, CORS, hop-strip, the header rewrite — via the gate-carries-transforms
semantics) and the representation STAMPS + the cookie hardener OUTSIDE the
onion, so their pairs reach the wire without a survival argument through the
header-map rewrites.

## Composition theorems (pure kernel — no `native_decide`, no `ofReduceBool`)

* `plus4_onion_status` / `plus4_onion_body` — the deployed plus4 response onion
  is status-stable (rides `deployStagesPlus4_statusStable`) and, for a
  header-less gate seed on a non-gzip-negotiating request, body-preserving: the
  content-type-gated body rewrite is a PROVEN passthrough
  (`bareOnionHeaders_not_html`, kernel-decided through the
  `Proto.Kernel.Shortcuts.ba_toList_eq` bridge), and every other response phase
  is header-only (`stagesA_bodyStable`).
* `plus5_login` — ANY `GET /login` is answered `200` carrying the HARDENED
  `Set-Cookie`, body `ok`.
* `plus5_events` — ANY `GET /events` is answered `200` with
  `Content-Type: text/event-stream` and body EXACTLY the proven encoder's two
  frames (`frame1_parses`/`frame2_parses` round-trip those bytes).
* `plus5_app` — ANY `GET /app/…` is answered `200 text/html` with body EXACTLY
  the shell the proven fallback selects.
* `witness_*` — concrete non-vacuous instantiations.

## Deployment

`drorb_serve_metered_plus5_conformant` — the RFC-conformant metered serve over
the extended fold (`conformantServe`, same ABI as
`drorb_serve_metered_plus4_conformant`). The host's default crossing re-points
here — NOT behind any env lever; `DRORB_PLUS5=0` reverts to the plus4 fold.

Named residuals (honest): the three new gates sit ahead of the metered
IP-filter/rate gates (the plus4 `mfStage` precedent), so the three new paths are
not rate-metered; `/events` is a one-shot proven-framed burst per request, not a
held-open push stream; the deployed onion's default caching-policy stamp applies
to `/events` like any other `200`.
-/

namespace Reactor.DeployPlus5

open Reactor.Pipeline
open Reactor (Response serialize)
open Reactor.Deploy (deployStagesFull2 appHandler ctxOf ctxOfMetered)
open Reactor.DeployPlus4 (deployStagesPlus4 deployStagesPlus4_statusStable)
open Reactor.ServeConformant (conformantServe)
open Reactor.Stage.CookieSecure (cookieSecureStage hardenHeader harden)
open Reactor.Stage.SessionCookie (sessionGateStage setCookieStage loginTarget
  setCookieName weakCookie loginResp loginBody sessionGate_fires sessionGate_passes
  setCookieStage_effect setCookieStage_noop hardenHeader_weak)
open Reactor.Stage.SseServe (sseGateStage sseHeadStage eventsTarget sseResp sseBody
  sseGate_fires sseGate_passes sseHeadStage_effect sseHeadStage_noop)
open Reactor.Stage.SpaServe (spaGateStage spaTypeStage spaPrefix spaRespOf
  spaRespOf_body htmlVal spaGate_fires spaGate_passes spaTypeStage_effect
  spaTypeStage_noop)

/-- **The extended deployed chain.** The hardener + three stamps outermost, the
three scoped gates next, then the EXACT deployed `deployStagesPlus4` fold
(read-only). -/
def deployStagesPlus5 : List Stage :=
  [ cookieSecureStage, setCookieStage, sseHeadStage, spaTypeStage,
    sseGateStage, spaGateStage, sessionGateStage ] ++ deployStagesPlus4

/-- The built response of the extended fold on a directly-supplied context. -/
def deployRespPlus5Of (c : Ctx) : Response :=
  (runPipeline deployStagesPlus5 appHandler c).build

/-- The built response of the extended METERED fold — the connection-aware
peer/seq context the dataplane threads in. -/
def deployRespPlus5Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Response :=
  (runPipeline deployStagesPlus5 appHandler (ctxOfMetered clientIp connSeq input)).build

/-- The extended metered serve as wire bytes. -/
def servePipelinePlus5Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Proto.Bytes :=
  serialize (deployRespPlus5Metered clientIp connSeq input)

/-! ## Builder helpers -/

/-- `addHeader` keeps the built body. -/
theorem addHeader_body (b : ResponseBuilder) (nv : Proto.Bytes × Proto.Bytes) :
    ((b.addHeader nv).build).body = b.build.body := rfl

/-- `addHeader` keeps the built status. -/
theorem addHeader_status (b : ResponseBuilder) (nv : Proto.Bytes × Proto.Bytes) :
    ((b.addHeader nv).build).status = b.build.status := rfl

/-- A header fold builds to a headers-append (body/status untouched). -/
theorem foldl_addHeader_build (l : List (Proto.Bytes × Proto.Bytes)) :
    ∀ b : ResponseBuilder, (l.foldl ResponseBuilder.addHeader b).build
      = { b.build with headers := b.build.headers ++ l } := by
  induction l with
  | nil => intro b; simp
  | cons x t ih =>
    intro b
    rw [List.foldl_cons, ih (b.addHeader x), build_addHeader]
    simp

/-- `runResp` distributes over list append. -/
theorem runResp_append (l1 l2 : List Stage) (c : Ctx) (b : ResponseBuilder) :
    runResp (l1 ++ l2) c b = runResp l1 c (runResp l2 c b) := by
  induction l1 with
  | nil => rfl
  | cons s t ih => rw [List.cons_append, runResp_cons, runResp_cons, ih]

/-! ## Body stability of the deployed response onion -/

/-- A stage's response phase is BODY-STABLE at a context when it never changes
the built body there. -/
def BodyStableAt (c : Ctx) (s : Stage) : Prop :=
  ∀ b : ResponseBuilder, ((s.onResponse c b).build).body = b.build.body

/-- The response-only fold preserves the built body over body-stable stages. -/
theorem runResp_bodyStable (l : List Stage) (c : Ctx)
    (h : ∀ s ∈ l, BodyStableAt c s) (b : ResponseBuilder) :
    ((runResp l c b).build).body = b.build.body := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    have hs : BodyStableAt c s := h s (List.mem_cons_self _ _)
    have hr : ∀ t ∈ rest, BodyStableAt c t := fun t ht => h t (List.mem_cons_of_mem _ ht)
    rw [runResp_cons, hs (runResp rest c b), ih hr]

/-- The plus4 onion OUTSIDE the content-type-gated body rewrite: every response
phase here is header-only (or gzip, disabled by negotiation). -/
def stagesA : List Stage :=
  [ Reactor.Stage.TimingAllowOrigin.taoStage
  , Reactor.Stage.ContentLocation.contentLocationStage
  , Reactor.Stage.MaxForwards.mfStage
  , Reactor.Stage.AltSvc.altStage
  , Reactor.Stage.PermissionsPolicy.ppStage
  , Reactor.Stage.CrossOriginResource.corpStage
  , Reactor.Stage.Via.viaStage
  , Reactor.Stage.CacheStatus.csStage
  , Reactor.Stage.WarningTransform.warningStage
  , Reactor.Stage.LinkPreload.linkStage
  , Reactor.Stage.ProxyProtocol.proxyProtoStage
  , Reactor.Stage.StaleWhileRevalidate.swrStage
  , Reactor.Deploy.jwtAdminStage
  , Reactor.Stage.BasicAuth.basicStage
  , Reactor.Stage.IpFilter.ipfilterStage
  , Reactor.Stage.Rate.rateStage
  , Reactor.Deploy.cacheEmptyStage
  , Reactor.Stage.Redirect.redirectStage
  , Reactor.Deploy.traversalStage
  , Reactor.Deploy.policyStage
  , Reactor.Deploy.headerRewriteStage
  , Reactor.Deploy.deployCorsStage
  , Reactor.Stage.Gzip.gzipStage ]

/-- The innermost two header stages (below the body rewrite). -/
def stagesB : List Stage :=
  [ Reactor.Stage.SecurityHeaders.securityheadersStage
  , Reactor.Stage.Header.headerStage ]

/-- The deployed plus4 chain splits around the body rewrite (definitional). -/
theorem plus4_split :
    deployStagesPlus4
      = stagesA ++ (Reactor.Stage.HtmlRewrite.htmlrewriteStage :: stagesB) := rfl

/-- **Every `stagesA` response phase is body-stable** (given the request does not
negotiate gzip). -/
theorem stagesA_bodyStable (c : Ctx)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false) :
    ∀ s ∈ stagesA, BodyStableAt c s := by
  intro s hs
  simp only [stagesA, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
  · exact fun b => rfl
  · intro b
    show ((if b.acc.status == 200 && Reactor.Stage.ContentLocation.isStaticGet c
           then b.addHeader (Reactor.Stage.ContentLocation.contentLocationName,
                  Reactor.Stage.ContentLocation.canonicalResourcePath c.req.target)
           else b).build).body = b.build.body
    by_cases h : (b.acc.status == 200 && Reactor.Stage.ContentLocation.isStaticGet c) = true
    · rw [if_pos h]; rfl
    · rw [if_neg h]
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · intro b
    show ((match c.attrs.find?
             (fun (p : String × Proto.Bytes) =>
               p.1 == Reactor.Stage.ProxyProtocol.clientKey) with
           | some p => b.addHeader (Reactor.Stage.ProxyProtocol.xffName, p.2)
           | none => b).build).body = b.build.body
    cases c.attrs.find?
      (fun (p : String × Proto.Bytes) =>
        p.1 == Reactor.Stage.ProxyProtocol.clientKey) <;> rfl
  · intro b
    show ((b.mapResp Reactor.Stage.StaleWhileRevalidate.applyCc).build).body = b.build.body
    rw [build_mapResp]
    unfold Reactor.Stage.StaleWhileRevalidate.applyCc
    split <;> rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · exact fun b => rfl
  · intro b
    show ((match _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy
             (Reactor.Deploy.corsOriginOf c) with
           | some v => b.addHeader (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
           | none => b).build).body = b.build.body
    cases _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy
      (Reactor.Deploy.corsOriginOf c) <;> rfl
  · intro b
    show ((match Reactor.Stage.Gzip.acceptsGzip c.req with
           | true => ((b.mapResp Reactor.Stage.Gzip.gzipBody).addHeader
               (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal))
           | false => b).build).body = b.build.body
    rw [hgz]

/-! ## The bare-seed header set at the body-rewrite point -/

/-- The header set the two innermost stages produce over a header-LESS seed: the
deployed `Server` rewrite followed by the security-header set. Closed
(seed-independent), so the content-type gate on it is kernel-decidable. -/
def bareOnionHeaders : List (Proto.Bytes × Proto.Bytes) :=
  Reactor.Stage.Header.fromFields
    (_root_.Header.run Reactor.Stage.Header.rewriteProg (Reactor.Stage.Header.toFields []))
  ++ Reactor.Stage.SecurityHeaders.wireHeaders Reactor.Stage.SecurityHeaders.policy

/-- **The content-type gate is closed on the bare onion headers**: none of the
deployed rewrite/security headers declares `text/html`, so a header-less gate
seed's body is a PROVEN passthrough of the deployed body rewrite. Kernel-decided
through the `ba_toList_eq` bridge. -/
theorem bareOnionHeaders_not_html :
    Reactor.Stage.HtmlRewrite.isHtmlCT bareOnionHeaders = false := by
  simp only [bareOnionHeaders, Reactor.Stage.SecurityHeaders.wireHeaders,
    Reactor.Stage.SecurityHeaders.policy, Reactor.Stage.SecurityHeaders.hstsPolicy,
    Reactor.Stage.SecurityHeaders.toWireHeader,
    _root_.SecurityHeaders.render, _root_.SecurityHeaders.hstsRender,
    _root_.SecurityHeaders.cspRender, _root_.SecurityHeaders.xfoValue,
    ite_true, ite_false,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
    Reactor.Stage.HtmlRewrite.isHtmlCT, Reactor.Stage.HtmlRewrite.ctName,
    Reactor.Stage.HtmlRewrite.isHtmlValue, Reactor.Stage.HtmlRewrite.htmlPrefix,
    Proto.Kernel.Shortcuts.ba_toList_eq]
  decide

/-- The two innermost header stages build a header-less seed to exactly the bare
onion header set (body/status/reason untouched). -/
theorem stagesB_build (c : Ctx) (r : Response) (hh : r.headers = []) :
    (runResp stagesB c (ResponseBuilder.ofResponse r)).build
      = { r with headers := bareOnionHeaders } := by
  show ((Reactor.Stage.SecurityHeaders.wireHeaders
      Reactor.Stage.SecurityHeaders.policy).foldl ResponseBuilder.addHeader
      ((ResponseBuilder.ofResponse r).mapResp Reactor.Stage.Header.rewriteResp)).build = _
  rw [foldl_addHeader_build, build_mapResp, build_ofResponse]
  unfold Reactor.Stage.Header.rewriteResp bareOnionHeaders
  rw [hh]

/-! ## The deployed onion: status- and body-preservation -/

/-- **The deployed plus4 onion is status-stable** (a gate's `200` stays `200`
through every response transform). -/
theorem plus4_onion_status (c : Ctx) (b : ResponseBuilder) :
    ((runResp deployStagesPlus4 c b).build).status = b.build.status :=
  runResp_build_status deployStagesPlus4 c b deployStagesPlus4_statusStable

/-- **The deployed plus4 onion preserves a header-less seed's body** on a request
that does not negotiate gzip: every response phase outside the body rewrite is
header-only, and the body rewrite's content-type gate is a proven passthrough on
the bare seed. -/
theorem plus4_onion_body (c : Ctx) (r : Response)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false)
    (hh : r.headers = []) :
    ((runResp deployStagesPlus4 c (ResponseBuilder.ofResponse r)).build).body
      = r.body := by
  rw [plus4_split, runResp_append,
      runResp_bodyStable stagesA c (stagesA_bodyStable c hgz), runResp_cons]
  show (((runResp stagesB c (ResponseBuilder.ofResponse r)).mapResp
      Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp).build).body = r.body
  rw [build_mapResp, stagesB_build c r hh,
      Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp_body]
  show (if Reactor.Stage.HtmlRewrite.isHtmlCT bareOnionHeaders then _ else _) = r.body
  rw [bareOnionHeaders_not_html]
  rfl

/-! ## ck.1 — the login route issues a HARDENED session cookie -/

/-- **ANY `GET /login` through the extended deployed fold is answered `200`
carrying the hardened `Set-Cookie`** (`Secure`/`HttpOnly`/`SameSite=Lax` present
via `harden_has_*`), body `ok`. The previously-inert hardener fires on the wire
pair the new route stamps. -/
theorem plus5_login (c : Ctx)
    (hm : c.req.method = Reactor.Stage.SessionCookie.getBytes)
    (ht : c.req.target = loginTarget)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false) :
    (deployRespPlus5Of c).status = 200
  ∧ (setCookieName, harden weakCookie) ∈ (deployRespPlus5Of c).headers
  ∧ (deployRespPlus5Of c).body = loginBody := by
  have hne_ev : ¬ c.req.target = eventsTarget := by rw [ht]; decide
  have hpre : spaPrefix.isPrefixOf c.req.target = false := by rw [ht]; rfl
  have hout : deployRespPlus5Of c
      = (((runResp deployStagesPlus4 c
            (ResponseBuilder.ofResponse loginResp)).addHeader
              (setCookieName, weakCookie)).mapResp
          (fun resp => { resp with
            headers := resp.headers.map hardenHeader })).build := by
    show (runPipeline (cookieSecureStage :: setCookieStage :: sseHeadStage
      :: spaTypeStage :: sseGateStage :: spaGateStage :: sessionGateStage
      :: deployStagesPlus4) appHandler c).build = _
    rw [pipeline_stage_effect cookieSecureStage _ appHandler c c rfl,
        setCookieStage_effect _ appHandler c hm ht,
        sseHeadStage_noop _ appHandler c hne_ev,
        spaTypeStage_noop _ appHandler c hpre,
        pipeline_stage_effect sseGateStage _ appHandler c c (sseGate_passes c hne_ev),
        pipeline_stage_effect spaGateStage _ appHandler c c (spaGate_passes c hpre),
        pipeline_gate_short_circuits sessionGateStage _ appHandler c loginResp
          (sessionGate_fires c hm ht)]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hout, build_mapResp]
    show (((runResp deployStagesPlus4 c (ResponseBuilder.ofResponse loginResp)).addHeader
      (setCookieName, weakCookie)).build).status = 200
    rw [addHeader_status, plus4_onion_status]
    rfl
  · rw [hout, build_mapResp]
    show (setCookieName, harden weakCookie)
      ∈ ((((runResp deployStagesPlus4 c (ResponseBuilder.ofResponse loginResp)).addHeader
        (setCookieName, weakCookie)).build).headers.map hardenHeader)
    rw [build_addHeader]
    show _ ∈ (_ ++ [(setCookieName, weakCookie)]).map hardenHeader
    rw [List.map_append, List.map_cons, List.map_nil, hardenHeader_weak]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · rw [hout, build_mapResp]
    show (((runResp deployStagesPlus4 c (ResponseBuilder.ofResponse loginResp)).addHeader
      (setCookieName, weakCookie)).build).body = loginBody
    rw [addHeader_body, plus4_onion_body c loginResp hgz rfl]
    rfl

/-! ## sse.1 — the events endpoint serves the proven framing -/

/-- **ANY `GET /events` through the extended deployed fold is answered
`200 text/event-stream` whose body is EXACTLY the proven encoder's two frames**
(`frame1_parses`/`frame2_parses` are the round-trip on these bytes). -/
theorem plus5_events (c : Ctx)
    (hm : c.req.method = Reactor.Stage.SessionCookie.getBytes)
    (ht : c.req.target = eventsTarget)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false) :
    (deployRespPlus5Of c).status = 200
  ∧ (Reactor.Stage.SseServe.ctName, Reactor.Stage.SseServe.ctVal)
      ∈ (deployRespPlus5Of c).headers
  ∧ (deployRespPlus5Of c).body = sseBody := by
  have hne_login : ¬ c.req.target = loginTarget := by rw [ht]; decide
  have hpre : spaPrefix.isPrefixOf c.req.target = false := by rw [ht]; rfl
  have hout : deployRespPlus5Of c
      = (((runResp deployStagesPlus4 c
            (ResponseBuilder.ofResponse sseResp)).addHeader
              (Reactor.Stage.SseServe.ctName, Reactor.Stage.SseServe.ctVal)).mapResp
          (fun resp => { resp with
            headers := resp.headers.map hardenHeader })).build := by
    show (runPipeline (cookieSecureStage :: setCookieStage :: sseHeadStage
      :: spaTypeStage :: sseGateStage :: spaGateStage :: sessionGateStage
      :: deployStagesPlus4) appHandler c).build = _
    rw [pipeline_stage_effect cookieSecureStage _ appHandler c c rfl,
        setCookieStage_noop _ appHandler c hne_login,
        sseHeadStage_effect _ appHandler c hm ht,
        spaTypeStage_noop _ appHandler c hpre,
        pipeline_gate_short_circuits sseGateStage _ appHandler c sseResp
          (sseGate_fires c hm ht)]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hout, build_mapResp]
    show (((runResp deployStagesPlus4 c (ResponseBuilder.ofResponse sseResp)).addHeader
      (Reactor.Stage.SseServe.ctName, Reactor.Stage.SseServe.ctVal)).build).status = 200
    rw [addHeader_status, plus4_onion_status]
    rfl
  · rw [hout, build_mapResp]
    show (Reactor.Stage.SseServe.ctName, Reactor.Stage.SseServe.ctVal)
      ∈ ((((runResp deployStagesPlus4 c (ResponseBuilder.ofResponse sseResp)).addHeader
        (Reactor.Stage.SseServe.ctName, Reactor.Stage.SseServe.ctVal)).build).headers.map
        hardenHeader)
    rw [build_addHeader]
    show _ ∈ (_ ++ [(Reactor.Stage.SseServe.ctName, Reactor.Stage.SseServe.ctVal)]).map
      hardenHeader
    rw [List.map_append, List.map_cons, List.map_nil,
        show hardenHeader (Reactor.Stage.SseServe.ctName, Reactor.Stage.SseServe.ctVal)
          = (Reactor.Stage.SseServe.ctName, Reactor.Stage.SseServe.ctVal) from by decide]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · rw [hout, build_mapResp]
    show (((runResp deployStagesPlus4 c (ResponseBuilder.ofResponse sseResp)).addHeader
      (Reactor.Stage.SseServe.ctName, Reactor.Stage.SseServe.ctVal)).build).body = sseBody
    rw [addHeader_body, plus4_onion_body c sseResp hgz rfl]
    rfl

/-! ## rt.7 — the SPA prefix serves the model-selected shell -/

/-- **ANY `GET /app/…` through the extended deployed fold is answered
`200 text/html` whose body is EXACTLY the shell the proven fallback selects**
(the model's `spa_fallback_serves_index` with its FS hypothesis discharged). -/
theorem plus5_app (c : Ctx)
    (hm : c.req.method = Reactor.Stage.SessionCookie.getBytes)
    (ht : spaPrefix.isPrefixOf c.req.target = true)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false) :
    (deployRespPlus5Of c).status = 200
  ∧ (Reactor.Stage.SpaServe.ctName, htmlVal) ∈ (deployRespPlus5Of c).headers
  ∧ (deployRespPlus5Of c).body = Reactor.Stage.SpaServe.shellBytes := by
  have hne_ev : ¬ c.req.target = eventsTarget := by
    intro h; rw [h] at ht; exact absurd ht (by decide)
  have hne_login : ¬ c.req.target = loginTarget := by
    intro h; rw [h] at ht; exact absurd ht (by decide)
  have hout : deployRespPlus5Of c
      = (((runResp deployStagesPlus4 c
            (ResponseBuilder.ofResponse (spaRespOf c))).addHeader
              (Reactor.Stage.SpaServe.ctName, htmlVal)).mapResp
          (fun resp => { resp with
            headers := resp.headers.map hardenHeader })).build := by
    show (runPipeline (cookieSecureStage :: setCookieStage :: sseHeadStage
      :: spaTypeStage :: sseGateStage :: spaGateStage :: sessionGateStage
      :: deployStagesPlus4) appHandler c).build = _
    rw [pipeline_stage_effect cookieSecureStage _ appHandler c c rfl,
        setCookieStage_noop _ appHandler c hne_login,
        sseHeadStage_noop _ appHandler c hne_ev,
        spaTypeStage_effect _ appHandler c hm ht,
        pipeline_stage_effect sseGateStage _ appHandler c c (sseGate_passes c hne_ev),
        pipeline_gate_short_circuits spaGateStage _ appHandler c (spaRespOf c)
          (spaGate_fires c hm ht)]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hout, build_mapResp]
    show (((runResp deployStagesPlus4 c
      (ResponseBuilder.ofResponse (spaRespOf c))).addHeader
      (Reactor.Stage.SpaServe.ctName, htmlVal)).build).status = 200
    rw [addHeader_status, plus4_onion_status]
    rfl
  · rw [hout, build_mapResp]
    show (Reactor.Stage.SpaServe.ctName, htmlVal)
      ∈ ((((runResp deployStagesPlus4 c
        (ResponseBuilder.ofResponse (spaRespOf c))).addHeader
        (Reactor.Stage.SpaServe.ctName, htmlVal)).build).headers.map hardenHeader)
    rw [build_addHeader]
    show _ ∈ (_ ++ [(Reactor.Stage.SpaServe.ctName, htmlVal)]).map hardenHeader
    rw [List.map_append, List.map_cons, List.map_nil,
        show hardenHeader (Reactor.Stage.SpaServe.ctName, htmlVal)
          = (Reactor.Stage.SpaServe.ctName, htmlVal) from by decide]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · rw [hout, build_mapResp]
    show (((runResp deployStagesPlus4 c
      (ResponseBuilder.ofResponse (spaRespOf c))).addHeader
      (Reactor.Stage.SpaServe.ctName, htmlVal)).build).body
      = Reactor.Stage.SpaServe.shellBytes
    rw [addHeader_body, plus4_onion_body c (spaRespOf c) hgz rfl, spaRespOf_body]

/-! ## Concrete non-vacuous witnesses -/

/-- A bare `GET` request context for a target (no headers — no gzip negotiation). -/
def ctxOfTarget (tgt : Proto.Bytes) : Ctx :=
  { input := []
    req := { method := [71, 69, 84], target := tgt, version := [], headers := [] }
    attrs := [] }

theorem witness_login :
    (deployRespPlus5Of (ctxOfTarget loginTarget)).status = 200
  ∧ (setCookieName, harden weakCookie)
      ∈ (deployRespPlus5Of (ctxOfTarget loginTarget)).headers
  ∧ (deployRespPlus5Of (ctxOfTarget loginTarget)).body = loginBody :=
  plus5_login (ctxOfTarget loginTarget) rfl rfl rfl

theorem witness_events :
    (deployRespPlus5Of (ctxOfTarget eventsTarget)).status = 200
  ∧ (Reactor.Stage.SseServe.ctName, Reactor.Stage.SseServe.ctVal)
      ∈ (deployRespPlus5Of (ctxOfTarget eventsTarget)).headers
  ∧ (deployRespPlus5Of (ctxOfTarget eventsTarget)).body = sseBody :=
  plus5_events (ctxOfTarget eventsTarget) rfl rfl rfl

/-- ASCII `"/app/dashboard"` — a navigable client route. -/
def dashTarget : Proto.Bytes :=
  [47, 97, 112, 112, 47, 100, 97, 115, 104, 98, 111, 97, 114, 100]

theorem witness_app :
    (deployRespPlus5Of (ctxOfTarget dashTarget)).status = 200
  ∧ (Reactor.Stage.SpaServe.ctName, htmlVal)
      ∈ (deployRespPlus5Of (ctxOfTarget dashTarget)).headers
  ∧ (deployRespPlus5Of (ctxOfTarget dashTarget)).body
      = Reactor.Stage.SpaServe.shellBytes :=
  plus5_app (ctxOfTarget dashTarget) rfl (by decide) rfl

/-! ## The (retired) exports — the `@[export]`s were removed in the consolidation; the single default is `drorb_serve_pipeline_conformant` -/

/-- **The extended metered serve seam** (`drorb_serve_metered_plus5`) — the
`drorb_serve_metered` ABI sibling over `deployStagesPlus5`. -/
def drorbServeMeteredPlus5 (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  ByteArray.mk (servePipelinePlus5Metered peer.toList seq.toNat input.toList).toArray

/-- What the export folds is definitionally the extended pipeline (totality: a
plain `def`). -/
theorem drorbServeMeteredPlus5_serves (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    drorbServeMeteredPlus5 peer seq input
      = ByteArray.mk (servePipelinePlus5Metered peer.toList seq.toNat input.toList).toArray :=
  rfl

/-- **A retired conformance-wrapped extended metered serve** (formerly the C
export `drorb_serve_metered_plus5_conformant`): the proven conformance wrapper
over the extended metered fold `deployStagesPlus5`. RETIRED experimental seam — the `@[export]` was removed in the consolidation, so this def is no longer a host crossing; it is retained only for the byte-identity derivation chain. The single deployed default is `drorb_serve_pipeline_conformant`. -/
def drorbServeMeteredPlus5Conformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  conformantServe (fun i => drorbServeMeteredPlus5 peer seq i) input

/-- The export is definitionally the conformance wrapper over the extended fold. -/
theorem drorbServeMeteredPlus5Conformant_serves (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    drorbServeMeteredPlus5Conformant peer seq input
      = conformantServe (fun i => drorbServeMeteredPlus5 peer seq i) input := rfl

end Reactor.DeployPlus5

#print axioms Reactor.DeployPlus5.bareOnionHeaders_not_html
#print axioms Reactor.DeployPlus5.plus4_onion_status
#print axioms Reactor.DeployPlus5.plus4_onion_body
#print axioms Reactor.DeployPlus5.plus5_login
#print axioms Reactor.DeployPlus5.plus5_events
#print axioms Reactor.DeployPlus5.plus5_app
#print axioms Reactor.DeployPlus5.witness_login
#print axioms Reactor.DeployPlus5.witness_events
#print axioms Reactor.DeployPlus5.witness_app
#print axioms Reactor.DeployPlus5.drorbServeMeteredPlus5Conformant_serves
