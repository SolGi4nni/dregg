import Reactor.DeployPlus5
import Proto.Kernel.Shortcuts
import Reactor.Stage.MultiRange
import Reactor.Stage.MethodFilter
import Reactor.Stage.BodyLimit
import Reactor.Stage.ClTeGuard
import Reactor.Stage.ContentLanguage
import Reactor.Stage.Dashboard

/-!
# Reactor.DeployPlus6 — three proven-inert stages un-inerted + three missing
features built, onto the DEFAULT serve

Extends the EXACT `Reactor.DeployPlus5.deployStagesPlus5` fold the running
default serves — referenced read-only, so every existing deployed proof stands.

## Un-inerted (proven-in-isolation, never deployed until now)

* **`Reactor.Stage.MethodFilter`** — the RFC 9110 §15.5.6 method allow-list:
  a `DELETE`/`PUT`/`TRACE`/`PATCH` is refused a pristine `405` carrying the
  §10.2.1-required `Allow` list. Previously the fold served such methods `404`.
* **`Reactor.Stage.MultiRange`** — the RFC 9110 §14.6 `multipart/byteranges`
  response transform: a MULTI-range `Range` request against a `200` becomes a
  genuine multipart `206` (per-part `Content-Range` + terminated boundary);
  single-range and range-less requests are proven untouched. Deployed reality
  (wire-discovered): the deployed static handler consumes `Range` itself and
  emits its own (still non-conformant, concatenated) `206`, so this transform
  fires on the RANGE-IGNORING `200` routes — the five gate routes (`/welcome`,
  `/dashboard`, `/login`, `/events`, `/app/…`) now answer a multi-range GET
  with a conformant multipart `206`; the static handler's own multi-range arm
  is a NAMED residual (its rewrite needs the concatenated-`206`-splitting
  transform, a follow-up).

## Built (the reference had them; the engine had NOTHING)

* **`Reactor.Stage.ClTeGuard`** — the `Content-Length`+`Transfer-Encoding`
  conflict `400` (RFC 7230 §3.3.3(3), the request-smuggling defense's missing
  half; the deployed framing gate only checked the final coding).
* **`Reactor.Stage.ContentLanguage`** — the i18n surface: `GET /welcome`
  negotiates `Accept-Language` (real q-values, wildcard, region ranges — with
  the proven argmax fact `negotiate_maximal`) and answers the localized body
  with `Content-Language` + `Vary: Accept-Language` on the wire.
* **`Reactor.Stage.Dashboard`** — the ops dashboard: `GET /dashboard` serves a
  self-refreshing, script-less (CSP-clean) HTML page that live-embeds the
  `/health` and `/events` probes and links every deployed route.

## Stage geometry

`deployStagesPlus6` puts the multipart-`206` transform OUTERMOST (so it
observes the final built response and its rewrite survives the header maps),
the two representation stamps next (outside the rewrite onion, the plus5
precedent), then the two request gates, then the two scoped route gates,
then the EXACT `deployStagesPlus5` fold (read-only). Gate answers still
traverse the ENTIRE deployed response onion via the gate-carries-transforms
semantics.

The method gate is DISPATCH-SCOPED (`methodGate6`): the fold's reject path
carries a default (empty-method) request context, and an unscoped allow-list
would shadow the deployed `431`/`400` reject responses with a bogus `405`
(wire-discovered on an over-cap input); the gate therefore passes any
non-dispatched context through untouched.

UN-INERT ATTEMPT WITHDRAWN (honest): `Reactor.Stage.BodyLimit` (the `413`
declared-size gate) was composed and proven here, then REMOVED — on this host
it can never fire: the host framing layer caps whole requests (8 MiB, close)
and the fold's parse cap (64 KiB) rejects any larger input BEFORE the stages
run, so every announced size a ≥-1-digit budget could refuse is already
refused upstream. Deploying it would be proven-inert-in-place theater. A
budget under the 64 KiB parse cap is not a defensible upload default; the
wire-visible `413` needs a host-side respond-before-body seam (owned
elsewhere). Named residual.

## Composition theorems (pure kernel — no `native_decide`, no `ofReduceBool`)

* `plus6_factor` — **the conservation theorem**: off the two new routes, with
  the three gates passing, the plus6 response IS `MultiRange.transform` of the
  plus5 response; `plus6_collapse` — with no `Range` header it IS the plus5
  response, byte-for-byte. Every deployed behaviour off the new edges is
  UNCHANGED, provably.
* `plus6_clte_400` / `plus6_405` — each gate's refusal status reaches the
  wire through the whole status-stable response onion. (The CL+TE `400` is
  defense-in-depth: the proven framing seam already refuses the shape at the
  host by close — `frameRaw_no_smuggle` — so on this host the fold gate is
  shadowed; it fires for any embedding that delivers the shape.)
* `plus6_welcome` — ANY `GET /welcome` (off the other edges) is answered `200`
  with body EXACTLY the negotiated representation and the
  `Content-Language`/`Vary` pair on the wire.
* `plus6_dashboard` — ANY `GET /dashboard` is answered `200 text/html` with
  body EXACTLY the dashboard shell (which provably embeds the live probes).
* `witness_*` — concrete non-vacuous instantiations.

## Deployment

`drorb_serve_metered_plus6` / `drorb_serve_metered_plus6_conformant` — the
extended metered serve and its RFC-conformant wrapper (same ABI as the plus5
pair). The host's default crossing reaches this fold through the dense twin
(`Datapath.DenseStampsPlus6`) — default-on, NOT behind any env lever;
`DRORB_PLUS5=0` still reverts the host to the plus4 fold.

Named residuals (honest): the two new route gates sit ahead of the metered
IP-filter/rate gates (the plus5 precedent — `/welcome` and `/dashboard` are
not rate-metered); the `405` carries its `Allow` in the gate seed (stage-level
`methodNotAllowed_advertises`), its fold-level survival through the header
rewrite is wire-verified rather than proven; an all-`q=0` `Accept-Language`
serves the default rather than `406`.
-/

namespace Reactor.DeployPlus6

open Reactor.Pipeline
open Reactor (Response serialize)
open Reactor.Deploy (appHandler ctxOf ctxOfMetered)
open Reactor.DeployPlus4 (deployStagesPlus4 deployStagesPlus4_statusStable)
open Reactor.DeployPlus5 (deployStagesPlus5 deployRespPlus5Of
  plus4_onion_status plus4_onion_body BodyStableAt runResp_append
  runResp_bodyStable addHeader_status addHeader_body)
open Reactor.ServeConformant (conformantServe)
open Reactor.Stage.MultiRange (multiRangeStage transform rangesOf
  transform_no_range transform_non200)
open Reactor.Stage.MethodFilter (methodFilterStage methodNotAllowed isAllowed
  method_allows method_denies methodFilterStage_statusStable)
open Reactor.Stage.ClTeGuard (clTeGuardStage clTeConflict clte_allows
  clte_denies clTeGuardStage_statusStable)
open Reactor.Stage.RequestValidation (badRequestResp)
open Reactor.Stage.ContentLanguage (welcomeGateStage langStampStage
  welcomeTarget welcomeRespOf negotiate tagOf bodyOf clHdrName varyName varyVal
  welcomeGate_fires welcomeGate_passes langStamp_effect langStamp_noop
  welcomeGate_statusStable langStamp_statusStable)
open Reactor.Stage.Dashboard (dashGateStage dashTypeStage dashTarget dashResp
  shellBytes ctName htmlVal dashGate_fires dashGate_passes dashTypeStage_effect
  dashTypeStage_noop dashGate_statusStable dashTypeStage_statusStable)

/-- **The dispatch-scoped method allow-list gate.** The fold's reject path
(an input the deployed parse refuses — over-cap, unparsable) carries a
DEFAULT request context (empty method); an unscoped allow-list would answer
it `405` and shadow the deployed reject response. This gate passes any
non-dispatched (empty-method) context through and runs the proven
`methodFilterStage` decision on genuine dispatches only. -/
def methodGate6 : Stage where
  name := "method-filter-dispatched"
  onRequest := fun c =>
    if c.req.method.isEmpty then .continue c else methodFilterStage.onRequest c
  onResponse := fun _ b => b

theorem methodGate6_statusStable : Stage.statusStable methodGate6 :=
  fun _ _ => rfl

/-- An allowed method passes through UNCHANGED (an allowed method is in the
allow-list, hence nonempty, so the dispatch scope is genuine). -/
theorem methodGate6_allows (c : Ctx) (h : isAllowed c.req.method = true) :
    methodGate6.onRequest c = .continue c := by
  have hne : c.req.method.isEmpty = false := by
    cases hm : c.req.method with
    | nil => rw [hm] at h; exact absurd h (by decide)
    | cons b t => rfl
  show (if c.req.method.isEmpty then StageStep.continue c
        else methodFilterStage.onRequest c) = _
  rw [hne]
  exact method_allows c h

/-- A DISPATCHED disallowed method is refused the proven `405`. -/
theorem methodGate6_denies (c : Ctx) (hne : c.req.method.isEmpty = false)
    (h : isAllowed c.req.method = false) :
    methodGate6.onRequest c = .respond methodNotAllowed := by
  show (if c.req.method.isEmpty then StageStep.continue c
        else methodFilterStage.onRequest c) = _
  rw [hne]
  exact method_denies c h

/-- A non-dispatched (empty-method) context passes through UNCHANGED — the
deployed reject responses stay owned by the handler. -/
theorem methodGate6_skips_reject_path (c : Ctx)
    (h : c.req.method.isEmpty = true) :
    methodGate6.onRequest c = .continue c := by
  show (if c.req.method.isEmpty then StageStep.continue c
        else methodFilterStage.onRequest c) = _
  rw [h]
  rfl

/-- **The extended deployed chain.** The multipart-`206` transform outermost,
the two stamps, the three gates, the two route gates, then the EXACT deployed
`deployStagesPlus5` fold (read-only). -/
def deployStagesPlus6 : List Stage :=
  [ multiRangeStage, langStampStage, dashTypeStage,
    clTeGuardStage, methodGate6,
    welcomeGateStage, dashGateStage ] ++ deployStagesPlus5

/-- The built response of the extended fold on a directly-supplied context. -/
def deployRespPlus6Of (c : Ctx) : Response :=
  (runPipeline deployStagesPlus6 appHandler c).build

/-- The built response of the extended METERED fold — the connection-aware
peer/seq context the dataplane threads in. -/
def deployRespPlus6Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Response :=
  (runPipeline deployStagesPlus6 appHandler
    (ctxOfMetered clientIp connSeq input)).build

/-- The extended metered serve as wire bytes. -/
def servePipelinePlus6Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Proto.Bytes :=
  serialize (deployRespPlus6Metered clientIp connSeq input)

/-! ## The plus5 onion, packaged (status- and body-preservation) -/

/-- The seven plus5 head stages (the plus5 fold splits as these ++ plus4 —
definitional). -/
def plus5Head : List Stage :=
  [ Reactor.Stage.CookieSecure.cookieSecureStage
  , Reactor.Stage.SessionCookie.setCookieStage
  , Reactor.Stage.SseServe.sseHeadStage
  , Reactor.Stage.SpaServe.spaTypeStage
  , Reactor.Stage.SseServe.sseGateStage
  , Reactor.Stage.SpaServe.spaGateStage
  , Reactor.Stage.SessionCookie.sessionGateStage ]

theorem plus5_split : deployStagesPlus5 = plus5Head ++ deployStagesPlus4 := rfl

/-- Every plus5 head stage is status-stable. -/
theorem plus5Head_statusStable : ∀ s ∈ plus5Head, Stage.statusStable s := by
  intro s hs
  simp only [plus5Head, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h|h|h|h|h|h|h <;> subst h
  · exact fun _ _ => rfl
  · exact Reactor.Stage.SessionCookie.setCookieStage_statusStable
  · exact Reactor.Stage.SseServe.sseHeadStage_statusStable
  · exact Reactor.Stage.SpaServe.spaTypeStage_statusStable
  · exact Reactor.Stage.SseServe.sseGate_statusStable
  · exact Reactor.Stage.SpaServe.spaGate_statusStable
  · exact Reactor.Stage.SessionCookie.sessionGate_statusStable

/-- Every plus5 stage is status-stable. -/
theorem plus5_statusStable : ∀ s ∈ deployStagesPlus5, Stage.statusStable s := by
  intro s hs
  rw [plus5_split, List.mem_append] at hs
  rcases hs with hs | hs
  · exact plus5Head_statusStable s hs
  · exact deployStagesPlus4_statusStable s hs

/-- **The plus5 onion is status-stable**: a gate's status survives the entire
deployed response-transform fold. -/
theorem plus5_onion_status (c : Ctx) (b : ResponseBuilder) :
    ((runResp deployStagesPlus5 c b).build).status = b.build.status :=
  runResp_build_status deployStagesPlus5 c b plus5_statusStable

/-- Every plus5 head stage is body-stable (they only add or map headers). -/
theorem plus5Head_bodyStable (c : Ctx) : ∀ s ∈ plus5Head, BodyStableAt c s := by
  intro s hs
  simp only [plus5Head, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h|h|h|h|h|h|h <;> subst h
  · exact fun _ => rfl
  · intro b
    show ((if Reactor.Stage.SessionCookie.inScope c then
            b.addHeader (Reactor.Stage.SessionCookie.setCookieName,
              Reactor.Stage.SessionCookie.weakCookie)
          else b).build).body = b.build.body
    by_cases h : Reactor.Stage.SessionCookie.inScope c = true
    · rw [if_pos h]; rfl
    · rw [if_neg h]
  · intro b
    show ((if Reactor.Stage.SseServe.inScope c then
            b.addHeader (Reactor.Stage.SseServe.ctName,
              Reactor.Stage.SseServe.ctVal)
          else b).build).body = b.build.body
    by_cases h : Reactor.Stage.SseServe.inScope c = true
    · rw [if_pos h]; rfl
    · rw [if_neg h]
  · intro b
    show ((if Reactor.Stage.SpaServe.inScope c then
            b.addHeader (Reactor.Stage.SpaServe.ctName,
              Reactor.Stage.SpaServe.htmlVal)
          else b).build).body = b.build.body
    by_cases h : Reactor.Stage.SpaServe.inScope c = true
    · rw [if_pos h]; rfl
    · rw [if_neg h]
  · exact fun _ => rfl
  · exact fun _ => rfl
  · exact fun _ => rfl

/-- **The plus5 onion preserves a header-less seed's body** on a request that
does not negotiate gzip (rides `plus4_onion_body`). -/
theorem plus5_onion_body (c : Ctx) (r : Response)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false)
    (hh : r.headers = []) :
    ((runResp deployStagesPlus5 c (ResponseBuilder.ofResponse r)).build).body
      = r.body := by
  rw [plus5_split, runResp_append,
      runResp_bodyStable plus5Head c (plus5Head_bodyStable c),
      plus4_onion_body c r hgz hh]

/-! ## The new outermost transform, characterized at the builder -/

/-- With no `Range` header the multipart transform is the identity ON THE
BUILDER. -/
theorem multiRange_noop_at (c : Ctx) (hr : rangesOf c.req = none)
    (b : ResponseBuilder) : multiRangeStage.onResponse c b = b := by
  show b.mapResp (transform c.req) = b
  unfold ResponseBuilder.mapResp
  rw [transform_no_range c.req b.acc hr]

/-- On a non-`200` builder the multipart transform preserves the status (a
refusal is never rewritten). -/
theorem multiRange_status_at (c : Ctx) (b : ResponseBuilder)
    (h : (b.build.status == 200) = false) :
    ((multiRangeStage.onResponse c b).build).status = b.build.status := by
  show ((b.mapResp (transform c.req)).build).status = b.build.status
  rw [build_mapResp, transform_non200 c.req b.build h]

/-! ## The conservation theorems -/

/-- **The off-routes peel**: off the two new routes the two stamps vanish and
the plus6 fold is the multipart transform over the gate chain. -/
theorem plus6_peel (c : Ctx)
    (hw : ¬ c.req.target = welcomeTarget)
    (hd : ¬ c.req.target = dashTarget) :
    deployRespPlus6Of c
      = (multiRangeStage.onResponse c
          (runPipeline (clTeGuardStage :: methodGate6 ::
            welcomeGateStage :: dashGateStage :: deployStagesPlus5)
            appHandler c)).build := by
  show (runPipeline (multiRangeStage :: langStampStage :: dashTypeStage ::
      clTeGuardStage :: methodGate6 ::
      welcomeGateStage :: dashGateStage :: deployStagesPlus5)
      appHandler c).build = _
  rw [pipeline_stage_effect multiRangeStage _ appHandler c c rfl,
      langStamp_noop _ appHandler c hw,
      dashTypeStage_noop _ appHandler c hd]

/-- **The conservation/factoring theorem.** Off the two new routes, with the
three new gates passing, the plus6 response IS the multipart transform of the
plus5 response — every deployed behaviour is either UNCHANGED or the proven
`206` rewrite. -/
theorem plus6_factor (c : Ctx)
    (hw : ¬ c.req.target = welcomeTarget)
    (hd : ¬ c.req.target = dashTarget)
    (hclte : clTeConflict c.req = false)
    (hmf : isAllowed c.req.method = true) :
    deployRespPlus6Of c = transform c.req (deployRespPlus5Of c) := by
  rw [plus6_peel c hw hd,
      pipeline_stage_effect clTeGuardStage _ appHandler c c (clte_allows c hclte),
      pipeline_stage_effect methodGate6 _ appHandler c c (methodGate6_allows c hmf),
      pipeline_stage_effect welcomeGateStage _ appHandler c c (welcomeGate_passes c hw),
      pipeline_stage_effect dashGateStage _ appHandler c c (dashGate_passes c hd)]
  show (((runPipeline deployStagesPlus5 appHandler c).mapResp
      (transform c.req)).build) = _
  rw [build_mapResp]
  rfl

/-- **The collapse.** Additionally range-less ⇒ the plus6 response IS the plus5
response, byte-for-byte. This is the theorem the dense-arm byte-identity rides. -/
theorem plus6_collapse (c : Ctx)
    (hw : ¬ c.req.target = welcomeTarget)
    (hd : ¬ c.req.target = dashTarget)
    (hclte : clTeConflict c.req = false)
    (hmf : isAllowed c.req.method = true)
    (hr : rangesOf c.req = none) :
    deployRespPlus6Of c = deployRespPlus5Of c := by
  rw [plus6_factor c hw hd hclte hmf, transform_no_range c.req _ hr]

/-! ## The gate refusals reach the wire -/

/-- The three inner stages after the CL/TE gate are status-stable, and so is
the whole tail (used by every refusal theorem). -/
theorem tail3_statusStable :
    ∀ s ∈ (methodGate6 :: welcomeGateStage ::
      dashGateStage :: deployStagesPlus5), Stage.statusStable s := by
  intro s hs
  simp only [List.mem_cons] at hs
  rcases hs with h|h|h|hs
  · subst h; exact methodGate6_statusStable
  · subst h; exact welcomeGate_statusStable
  · subst h; exact dashGate_statusStable
  · exact plus5_statusStable s hs

theorem tail2_statusStable :
    ∀ s ∈ (welcomeGateStage :: dashGateStage :: deployStagesPlus5),
      Stage.statusStable s := by
  intro s hs
  simp only [List.mem_cons] at hs
  rcases hs with h|h|hs
  · subst h; exact welcomeGate_statusStable
  · subst h; exact dashGate_statusStable
  · exact plus5_statusStable s hs

/-- **h1.5's missing half, deployed: the CL+TE conflict is answered `400`**
through the entire deployed response onion. -/
theorem plus6_clte_400 (c : Ctx)
    (hconf : clTeConflict c.req = true)
    (hw : ¬ c.req.target = welcomeTarget)
    (hd : ¬ c.req.target = dashTarget) :
    (deployRespPlus6Of c).status = 400 := by
  rw [plus6_peel c hw hd,
      pipeline_gate_short_circuits clTeGuardStage _ appHandler c badRequestResp
        (clte_denies c hconf)]
  have hin : ((runResp (methodGate6 :: welcomeGateStage ::
      dashGateStage :: deployStagesPlus5) c
      (ResponseBuilder.ofResponse badRequestResp)).build).status = 400 := by
    rw [runResp_build_status _ c _ tail3_statusStable]
    rfl
  rw [multiRange_status_at c _ (by rw [hin]; rfl), hin]

/-- **mw: the method allow-list, deployed: a DISPATCHED disallowed method is
answered `405`** through the entire deployed response onion. -/
theorem plus6_405 (c : Ctx)
    (hclte : clTeConflict c.req = false)
    (hne : c.req.method.isEmpty = false)
    (hm : isAllowed c.req.method = false)
    (hw : ¬ c.req.target = welcomeTarget)
    (hd : ¬ c.req.target = dashTarget) :
    (deployRespPlus6Of c).status = 405 := by
  rw [plus6_peel c hw hd,
      pipeline_stage_effect clTeGuardStage _ appHandler c c (clte_allows c hclte),
      pipeline_gate_short_circuits methodGate6 _ appHandler c
        methodNotAllowed (methodGate6_denies c hne hm)]
  have hin : ((runResp (welcomeGateStage :: dashGateStage ::
      deployStagesPlus5) c
      (ResponseBuilder.ofResponse methodNotAllowed)).build).status = 405 := by
    rw [runResp_build_status _ c _ tail2_statusStable]
    rfl
  rw [show clTeGuardStage.onResponse c
        (runResp (welcomeGateStage :: dashGateStage ::
          deployStagesPlus5) c (ResponseBuilder.ofResponse methodNotAllowed))
      = runResp (welcomeGateStage :: dashGateStage ::
          deployStagesPlus5) c (ResponseBuilder.ofResponse methodNotAllowed)
      from rfl,
      multiRange_status_at c _ (by rw [hin]; rfl), hin]

/-! ## bc: the i18n surface — the negotiated route on the wire -/

/-- **ANY `GET /welcome` through the extended deployed fold is answered `200`
with body EXACTLY the negotiated representation and the
`Content-Language`/`Vary: Accept-Language` pair on the wire.** -/
theorem plus6_welcome (c : Ctx)
    (hm : c.req.method = Reactor.Stage.ContentLanguage.getBytes)
    (ht : c.req.target = welcomeTarget)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false)
    (hr : rangesOf c.req = none)
    (hclte : clTeConflict c.req = false) :
    (deployRespPlus6Of c).status = 200
  ∧ (clHdrName, tagOf (negotiate c.req)) ∈ (deployRespPlus6Of c).headers
  ∧ (varyName, varyVal) ∈ (deployRespPlus6Of c).headers
  ∧ (deployRespPlus6Of c).body = bodyOf (negotiate c.req) := by
  have hd : ¬ c.req.target = dashTarget := by rw [ht]; decide
  have hmf : isAllowed c.req.method = true := by rw [hm]; decide
  have hout : deployRespPlus6Of c
      = (((runResp (dashGateStage :: deployStagesPlus5) c
            (ResponseBuilder.ofResponse (welcomeRespOf c))).addHeader
              (clHdrName, tagOf (negotiate c.req))).addHeader
            (varyName, varyVal)).build := by
    show (runPipeline (multiRangeStage :: langStampStage :: dashTypeStage ::
        clTeGuardStage :: methodGate6 ::
        welcomeGateStage :: dashGateStage :: deployStagesPlus5)
        appHandler c).build = _
    rw [pipeline_stage_effect multiRangeStage _ appHandler c c rfl,
        multiRange_noop_at c hr,
        langStamp_effect _ appHandler c hm ht,
        dashTypeStage_noop _ appHandler c hd,
        pipeline_stage_effect clTeGuardStage _ appHandler c c (clte_allows c hclte),
        pipeline_stage_effect methodGate6 _ appHandler c c (methodGate6_allows c hmf),
        pipeline_gate_short_circuits welcomeGateStage _ appHandler c
          (welcomeRespOf c) (welcomeGate_fires c hm ht)]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hout, addHeader_status, addHeader_status]
    show ((runResp (dashGateStage :: deployStagesPlus5) c
      (ResponseBuilder.ofResponse (welcomeRespOf c))).build).status = 200
    rw [runResp_cons]
    show ((runResp deployStagesPlus5 c
      (ResponseBuilder.ofResponse (welcomeRespOf c))).build).status = 200
    rw [plus5_onion_status]
    rfl
  · rw [hout]
    show (clHdrName, tagOf (negotiate c.req))
      ∈ ((((runResp (dashGateStage :: deployStagesPlus5) c
        (ResponseBuilder.ofResponse (welcomeRespOf c))).addHeader
          (clHdrName, tagOf (negotiate c.req))).addHeader
          (varyName, varyVal)).build).headers
    rw [build_addHeader, build_addHeader]
    exact List.mem_append_left _
      (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  · rw [hout]
    rw [build_addHeader]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · rw [hout, addHeader_body, addHeader_body]
    show ((runResp (dashGateStage :: deployStagesPlus5) c
      (ResponseBuilder.ofResponse (welcomeRespOf c))).build).body
        = bodyOf (negotiate c.req)
    rw [runResp_cons]
    show ((runResp deployStagesPlus5 c
      (ResponseBuilder.ofResponse (welcomeRespOf c))).build).body
        = bodyOf (negotiate c.req)
    rw [plus5_onion_body c (welcomeRespOf c) hgz rfl]
    rfl

/-! ## ad: the dashboard — the ops page on the wire -/

/-- **ANY `GET /dashboard` through the extended deployed fold is answered
`200 text/html` with body EXACTLY the dashboard shell** (which provably embeds
the live `/health` and `/events` probes — `shell_embeds_health`/`_events`). -/
theorem plus6_dashboard (c : Ctx)
    (hm : c.req.method = Reactor.Stage.Dashboard.getBytes)
    (ht : c.req.target = dashTarget)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false)
    (hr : rangesOf c.req = none)
    (hclte : clTeConflict c.req = false) :
    (deployRespPlus6Of c).status = 200
  ∧ (ctName, htmlVal) ∈ (deployRespPlus6Of c).headers
  ∧ (deployRespPlus6Of c).body = shellBytes := by
  have hw : ¬ c.req.target = welcomeTarget := by rw [ht]; decide
  have hmf : isAllowed c.req.method = true := by rw [hm]; decide
  have hout : deployRespPlus6Of c
      = ((runResp deployStagesPlus5 c
            (ResponseBuilder.ofResponse dashResp)).addHeader
              (ctName, htmlVal)).build := by
    show (runPipeline (multiRangeStage :: langStampStage :: dashTypeStage ::
        clTeGuardStage :: methodGate6 ::
        welcomeGateStage :: dashGateStage :: deployStagesPlus5)
        appHandler c).build = _
    rw [pipeline_stage_effect multiRangeStage _ appHandler c c rfl,
        multiRange_noop_at c hr,
        langStamp_noop _ appHandler c hw,
        dashTypeStage_effect _ appHandler c hm ht,
        pipeline_stage_effect clTeGuardStage _ appHandler c c (clte_allows c hclte),
        pipeline_stage_effect methodGate6 _ appHandler c c (methodGate6_allows c hmf),
        pipeline_stage_effect welcomeGateStage _ appHandler c c
          (welcomeGate_passes c hw),
        pipeline_gate_short_circuits dashGateStage _ appHandler c dashResp
          (dashGate_fires c hm ht)]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hout, addHeader_status, plus5_onion_status]
    rfl
  · rw [hout, build_addHeader]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · rw [hout, addHeader_body, plus5_onion_body c dashResp hgz rfl]
    rfl

/-! ## Concrete non-vacuous witnesses -/

/-- A bare request context: method, target, headers. -/
def ctxOfShape (m tgt : Proto.Bytes)
    (hs : List (Proto.Bytes × Proto.Bytes)) : Ctx :=
  { input := []
    req := { method := m, target := tgt, version := [], headers := hs }
    attrs := [] }

/-- `DELETE /health` — refused `405` on the deployed fold. -/
theorem witness_405 :
    (deployRespPlus6Of (ctxOfShape [68, 69, 76, 69, 84, 69]
      [47, 104, 101, 97, 108, 116, 104] [])).status = 405 :=
  plus6_405 _ (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `POST /echo` with BOTH `Content-Length` and `Transfer-Encoding` — the
smuggling shape, refused `400`. -/
theorem witness_clte_400 :
    (deployRespPlus6Of (ctxOfShape [80, 79, 83, 84] [47, 101, 99, 104, 111]
      [([67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104], [53]),
       ([84, 114, 97, 110, 115, 102, 101, 114, 45, 69, 110, 99, 111, 100, 105,
         110, 103], [99, 104, 117, 110, 107, 101, 100])])).status = 400 :=
  plus6_clte_400 _ (by decide) (by decide) (by decide)

/-- `GET /welcome` with `Accept-Language: de` — the negotiated German
representation with the `Content-Language`/`Vary` pair. -/
theorem witness_welcome_de :
    (deployRespPlus6Of (ctxOfShape [71, 69, 84] welcomeTarget
        [(varyVal, [100, 101])])).status = 200
  ∧ (clHdrName, tagOf .de)
      ∈ (deployRespPlus6Of (ctxOfShape [71, 69, 84] welcomeTarget
          [(varyVal, [100, 101])])).headers
  ∧ (deployRespPlus6Of (ctxOfShape [71, 69, 84] welcomeTarget
        [(varyVal, [100, 101])])).body = bodyOf .de := by
  have h := plus6_welcome (ctxOfShape [71, 69, 84] welcomeTarget
    [(varyVal, [100, 101])]) rfl rfl
    (by
      simp only [Reactor.Stage.Gzip.acceptsGzip, Reactor.Stage.Gzip.aeName,
        Reactor.Stage.Gzip.gzipTok, Proto.Kernel.Shortcuts.ba_toList_eq]
      decide)
    (by decide) (by decide)
  have hneg : negotiate (ctxOfShape [71, 69, 84] welcomeTarget
      [(varyVal, [100, 101])]).req = .de := by decide
  rw [hneg] at h
  exact ⟨h.1, h.2.1, h.2.2.2⟩

/-- `GET /dashboard` — the live dashboard shell, typed HTML. -/
theorem witness_dashboard :
    (deployRespPlus6Of (ctxOfShape [71, 69, 84] dashTarget [])).status = 200
  ∧ (ctName, htmlVal)
      ∈ (deployRespPlus6Of (ctxOfShape [71, 69, 84] dashTarget [])).headers
  ∧ (deployRespPlus6Of (ctxOfShape [71, 69, 84] dashTarget [])).body
      = shellBytes :=
  plus6_dashboard _ rfl rfl rfl (by decide) (by decide)

/-! ## The exports (the DEFAULT crossing reaches this fold via the dense twin) -/

/-- **The extended metered serve seam** (`drorb_serve_metered_plus6`) — the
`drorb_serve_metered_plus5` ABI sibling over `deployStagesPlus6`. -/
@[export drorb_serve_metered_plus6]
def drorbServeMeteredPlus6 (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  ByteArray.mk (servePipelinePlus6Metered peer.toList seq.toNat input.toList).toArray

/-- What the export folds is definitionally the extended pipeline. -/
theorem drorbServeMeteredPlus6_serves (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    drorbServeMeteredPlus6 peer seq input
      = ByteArray.mk (servePipelinePlus6Metered peer.toList seq.toNat
          input.toList).toArray := rfl

/-- **The extended metered serve, RFC-conformant**
(`drorb_serve_metered_plus6_conformant`): the proven conformance wrapper over
`deployStagesPlus6`. Same `(peer, seq, input)` ABI as the plus5 sibling. -/
@[export drorb_serve_metered_plus6_conformant]
def drorbServeMeteredPlus6Conformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  conformantServe (fun i => drorbServeMeteredPlus6 peer seq i) input

/-- The export is definitionally the conformance wrapper over the extended fold. -/
theorem drorbServeMeteredPlus6Conformant_serves (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    drorbServeMeteredPlus6Conformant peer seq input
      = conformantServe (fun i => drorbServeMeteredPlus6 peer seq i) input := rfl

end Reactor.DeployPlus6

#print axioms Reactor.DeployPlus6.plus5_onion_status
#print axioms Reactor.DeployPlus6.plus5_onion_body
#print axioms Reactor.DeployPlus6.plus6_factor
#print axioms Reactor.DeployPlus6.plus6_collapse
#print axioms Reactor.DeployPlus6.plus6_clte_400
#print axioms Reactor.DeployPlus6.plus6_405
#print axioms Reactor.DeployPlus6.methodGate6_allows
#print axioms Reactor.DeployPlus6.methodGate6_skips_reject_path
#print axioms Reactor.DeployPlus6.plus6_welcome
#print axioms Reactor.DeployPlus6.plus6_dashboard
#print axioms Reactor.DeployPlus6.witness_405
#print axioms Reactor.DeployPlus6.witness_clte_400
#print axioms Reactor.DeployPlus6.witness_welcome_de
#print axioms Reactor.DeployPlus6.witness_dashboard
#print axioms Reactor.DeployPlus6.drorbServeMeteredPlus6Conformant_serves
