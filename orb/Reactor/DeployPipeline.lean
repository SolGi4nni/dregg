import Datapath.DenseStampsPlus8
import Reactor.ServeConformant
import Reactor.Stage.RangeUnveil
import Reactor.Stage.CacheControl
import Reactor.Stage.ModifiedSince
import Reactor.Stage.AssetExpires
import Reactor.Stage.AssetImmutable
import Reactor.Stage.ErrorPage
import Reactor.Stage.ConnLimit
import Reactor.Stage.Slowloris
import Reactor.Stage.BodyLimit
import Reactor.RateMeteredCorrect
import Datapath.DenseStampsPlus5
import Datapath.ServeDenseReal
import Datapath.ServeMeteredHeadIdx

/-!
# Reactor.DeployPipeline — the ONE consolidated deployed pipeline

The deployed default serve was assembled by a CHAIN of extension folds spread
across six files: `deployStagesFull2` (base) was wrapped by `deployStagesPlus2`,
then `…Plus4`, `…Plus5`, `…Plus6`, `…Plus8`, each defined as `newEdges ++
priorList` in its own module. The running list was therefore only visible by
mentally unrolling six `::`/`++` splices across six files — the confusing chain
the debt-paydown targets.

This module states that SAME list ONCE, FLAT: `deployPipelineStages` is the full
ordered registry, outermost stage first. Each entry is a fully-qualified
reference to the stage's OWN proof module (it is proven and imported, never
inlined here) — so the pipeline GROWS by adding one line + one import, with no
giant file to recompile and no fold-of-folds to unroll.

## This wave — the status-keyed error-page layer (RFC 9110 §15.5)

One proven stage is prepended OUTERMOST of the whole onion, the FIRST outermost
stage that genuinely FIRES on a general dynamic request rather than staying inert
on it:

  * `Reactor.Stage.ErrorPage.errorStage` — when the built response status has a
    configured custom error page (here `404`), its body is REPLACED by the
    rendered page (the template with the request path spliced in, HTML-escaped so
    a crafted URL cannot inject) — RFC 9110 §15.5. A dynamic `404` (`GET /nope`)
    now serves the rendered error body instead of the bare handler body; a `/bulk`
    `200` (and every other non-404 shape) is left byte-for-byte untouched.

### The `/bulk` fast path stays byte-identical — the un-inert hook, USED

The dense-arm off-condition `newStagesOffB` was previously narrowed to the LITERAL
`/bulk` datapath shape (`armB8`), leaving the `armB8 ⇒ /bulk arm` fact bound but
DISCARDED. This wave USES it: `armB8` pins the request to the `/bulk` route, whose
deployed fold answers a `200` (the handler) or a gate refusal (`403`/`429`), NEVER
a `404` — so `errorStage` is the identity on the whole `/bulk` arm regardless of
the peer/rate gates (`bulkFull2_notPage` proves the fold status is never a
configured page code). The dense-arm bytes therefore stay byte-identical
(`drorbServePipelineMetered_eq_plus8_off`, `serveMeteredPipelineDenseIdx_eq`),
while every non-`/bulk` dynamic request flows through the full consolidated fold,
so `errorStage` fires on its `404`s.

The off-condition additionally carries the `noPreambleB` probe (the raw head is a
plain HTTP request, no PROXY preamble). This is redundant with `armB8` (a preamble
would make the raw head parse as `PROXY …`, not `GET /bulk`, failing the arm) and
is exactly the dense arm's own firing condition — it makes the preamble-free fact
(`recoverClient = none`) available to the collapse so the `/bulk` fold's status
reduces cleanly through the stamp layers to the base fold.

### Named residual — RetryAfter / RequestId are NOT deployed here

`Reactor.Stage.RetryAfter.retryAfterStage` (stamps `Retry-After` on `429`/`503`)
is a status-keyed edge like `errorStage`, but a rate-limited `/bulk` request DOES
answer `429`, on which `retryAfterStage` genuinely fires — it would change the
`/bulk` gate-refusal bytes and break the dense-arm byte-identity this lane
guarantees. `Reactor.Stage.RequestId.ridStage` stamps on EVERY request
unconditionally (not status-keyed), so it fires on the `/bulk` `200` and breaks it
outright. Both stay out of this outermost layer; their correct home is a layer
INSIDE the dense-arm split (where the `/bulk` refusal bytes are produced), a
change out of this lane.

## The range / freshness layer (RFC 9110 §14, RFC 9111 §5) — from the prior wave

Five proven stages sit between `errorStage` and the plus8 onion, each the identity
off its surface (so the dense `/bulk` arm stays byte-identical):

  * `Reactor.Stage.RangeUnveil.rangeUnveilStage` — the two mishandled range
    shapes (multi-range `206`, `If-Range`) unveiled on the handler's full `200`.
  * `Reactor.Stage.CacheControl.cacheControlStage` — the origin freshness
    directive on a cacheable static `200`.
  * the static-asset validation stamps (`Last-Modified`, `Expires`, immutable).

## The dense `/bulk` fast path is preserved (the perf lever)

`newStages_collapse` proves the five range/freshness stages collapse to the
identity under the off-facts (still true on the `/bulk` shape), and `errorStage`
is inert there by `bulkFull2_notPage`, so the consolidated fold equals the plus8
fold on `/bulk` and the deployed OUTPUT is unchanged — the fold and the fast path
agree on `/bulk`.
-/

namespace Reactor.DeployPipeline

open Proto (Bytes)
open Reactor (Response serialize)
open Reactor.Pipeline (Ctx Stage StageStep runPipeline runResp ResponseBuilder pipeline_cons
  pipeline_stage_effect pipeline_gate_status)
open Reactor.Deploy (appHandler ctxOfMetered ctxOf ctxOfMeteredConn ctxOfMeteredConn_req
  activeOf_ctxOfMeteredConn capOf_ctxOfMeteredConn nowOf_ctxOfMeteredConn
  startedOf_ctxOfMeteredConn countOf_ctxOfMeteredConn)
open Reactor.ServeConformant (conformantServe)
open Reactor.DeployPlus8 (deployStagesPlus8 drorbServeMeteredPlus8
  servePipelinePlus8Metered deployRespPlus8Of)
open Datapath.DenseStampsPlus8 (serveMeteredPlus8HeadIdx serveMeteredPlus8HeadIdx_eq
  armB8 armB8_sound reqArm_bulkSegs)
open Datapath.ServeHeadIdx (noPreambleB noPreambleB_sound)

/-- **THE consolidated deployed pipeline** — the full ordered stage registry the
running default folds, flat in one list, outermost stage first. The status-keyed
`errorStage` of this wave is prepended OUTERMOST, then the prior wave's five
range/freshness stages, then the plus8 onion stated flat (definitionally
`deployStagesPlus8`, so every existing proof about the deployed fold transfers to
the tail via `deployPipelineStages_tail_eq`). -/
def deployPipelineStages : List Stage :=
  -- DoS admission gates, OUTERMOST of everything (pre-parse-ish): the per-source
  -- concurrent-connection cap (503) and the slow-header-arrival timeout (408).
  -- Both are pure request-phase gates keyed on accept-path state the host threads
  -- into the attribute bag (`conn-active` / `hdr-now`); off their surface (no attr,
  -- e.g. the plain `ctxOfMetered` context) each is the identity, so every existing
  -- deployed proof transfers through them (`connStage_pass` / `slowStage_pass`).
  [ Reactor.Stage.ConnLimit.connStage
  -- the per-source request-ARRIVAL limit (429), immediately inside the connection
  -- cap: the same precedence the accept path uses (connection-resource 503 first,
  -- then request-rate 429). Off its surface (no `stick-limit` attr ⇒ limit 0) it is
  -- the identity, so every existing deployed proof transfers through it.
  , Reactor.Stage.StickTable.stickStage
  , Reactor.Stage.Slowloris.slowStage
  -- this wave: the status-keyed custom error page (outermost of everything)
  , Reactor.Stage.ErrorPage.errorStage
  -- DoS gate: the body-size 413 (declared Content-Length OR streamed-byte over-cap);
  -- inert on the /bulk arm (no oversized body), so the dense fast path is preserved.
  , Reactor.Stage.BodyLimit.bodyLimitStage
  -- prior wave: range unveil (outermost of the tail) → static freshness
  , Reactor.Stage.RangeUnveil.rangeUnveilStage
  , Reactor.Stage.CacheControl.cacheControlStage
  -- prior wave: the static-asset validation / caching completeness stamps
  , Reactor.Stage.ModifiedSince.lmStampStage
  , Reactor.Stage.AssetExpires.assetExpiresStage
  , Reactor.Stage.AssetImmutable.assetImmutableStage
  -- plus8 edges (outermost of the tail): Vary stamp, then the 414 / 406 gates
  , Reactor.DeployPlus8.varyGate8
  , Reactor.Stage.UriTooLong.uriTooLongStage
  , Reactor.Stage.NotAcceptable.naGateStage
  -- plus6 edges: multi-range 206, language stamp, dashboard type, CL/TE guard,
  -- method gate, welcome/dashboard route gates
  , Reactor.Stage.MultiRange.multiRangeStage
  , Reactor.Stage.ContentLanguage.langStampStage
  , Reactor.Stage.Dashboard.dashTypeStage
  , Reactor.Stage.ClTeGuard.clTeGuardStage
  , Reactor.DeployPlus6.methodGate6
  , Reactor.Stage.ContentLanguage.welcomeGateStage
  , Reactor.Stage.Dashboard.dashGateStage
  -- plus5 layer: cookie hardening, session set-cookie, SSE + SPA heads/gates
  , Reactor.Stage.CookieSecure.cookieSecureStage
  , Reactor.Stage.SessionCookie.setCookieStage
  , Reactor.Stage.SseServe.sseHeadStage
  , Reactor.Stage.SpaServe.spaTypeStage
  , Reactor.Stage.SseServe.sseGateStage
  , Reactor.Stage.SpaServe.spaGateStage
  , Reactor.Stage.SessionCookie.sessionGateStage
  -- plus4 layer: Timing-Allow-Origin, Content-Location, Max-Forwards hop gate
  , Reactor.Stage.TimingAllowOrigin.taoStage
  , Reactor.Stage.ContentLocation.contentLocationStage
  , Reactor.Stage.MaxForwards.mfStage
  -- plus2 layer: the nine response-stamp edges
  , Reactor.Stage.AltSvc.altStage
  , Reactor.Stage.PermissionsPolicy.ppStage
  , Reactor.Stage.CrossOriginResource.corpStage
  , Reactor.Stage.Via.viaStage
  , Reactor.Stage.CacheStatus.csStage
  , Reactor.Stage.WarningTransform.warningStage
  , Reactor.Stage.LinkPreload.linkStage
  , Reactor.Stage.ProxyProtocol.proxyProtoStage
  , Reactor.Stage.StaleWhileRevalidate.swrStage
  -- base serve (deployStagesFull2): auth, gates, route, transform, headers
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
  , Reactor.Stage.Gzip.gzipStage
  , Reactor.Stage.HtmlRewrite.htmlrewriteStage
  , Reactor.Stage.SecurityHeaders.securityheadersStage
  , Reactor.Stage.Header.headerStage ]

/-- **The consolidation identity for the tail.** Dropping the six outermost stages
(the custom error page, range unveil, cache-control freshness, and this wave's
Last-Modified / Expires / immutable static-asset stamps), the flat registry tail
IS the deployed `deployStagesPlus8` onion, definitionally. Every proof about the
deployed fold therefore transfers to the tail. -/
theorem deployPipelineStages_tail_eq :
    deployPipelineStages.drop 10 = Reactor.DeployPlus8.deployStagesPlus8 := rfl

/-- The consolidated registry is exactly fifty-three stages (43 plus8 + 6 new of the
prior waves: custom error page, range unveil, cache-control freshness,
Last-Modified, Expires, immutable + 4 DoS admission gates: conn-limit, arrival-rate,
slowloris, body-size). -/
theorem deployPipelineStages_length : deployPipelineStages.length = 53 := rfl

/-! ## The two DoS gates are the identity on the plain metered context

`ctxOfMetered` stashes only the client IP and the rate sequence — never the
`conn-active` / `hdr-now` / `hdr-started` keys the two admission gates read. So on
that context the reconstructed active count and header span are both `0`: the
conn-limit gate admits (`0 < defaultConnCap`, the cap an unconfigured context
reads) and the slowloris gate is in time
(`¬ 0 + headerTimeout ≤ 0`). Each gate is therefore the pass-through identity on
every plain metered context, so the whole existing byte-identity chain (the `/bulk`
dense-arm collapse below) transfers through the two prepended stages untouched. -/

/-- The plain metered context carries no `conn-active` attr, so its reconstructed
active-connection count is `0`. -/
theorem activeOf_ctxOfMetered (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.ConnLimit.activeOf (ctxOfMetered clientIp connSeq input) = 0 := by
  have h : Reactor.Stage.ConnLimit.lookupBytes
      (ctxOfMetered clientIp connSeq input) Reactor.Stage.ConnLimit.activeKey = [] := by
    show (match (ctxOfMetered clientIp connSeq input).attrs.find?
        (fun p => p.1 == Reactor.Stage.ConnLimit.activeKey) with
      | some p => p.2 | none => []) = []
    rw [Reactor.Deploy.ctxOfMetered_find_none clientIp connSeq input
      Reactor.Stage.ConnLimit.activeKey (by decide) (by decide)]
  simp [Reactor.Stage.ConnLimit.activeOf, h]

/-- The plain metered context carries no `hdr-now` attr, so its reconstructed
current header clock is `0`. -/
theorem nowOf_ctxOfMetered (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.Slowloris.nowOf (ctxOfMetered clientIp connSeq input) = 0 := by
  have h : Reactor.Stage.Slowloris.lookupBytes
      (ctxOfMetered clientIp connSeq input) Reactor.Stage.Slowloris.nowKey = [] := by
    show (match (ctxOfMetered clientIp connSeq input).attrs.find?
        (fun p => p.1 == Reactor.Stage.Slowloris.nowKey) with
      | some p => p.2 | none => []) = []
    rw [Reactor.Deploy.ctxOfMetered_find_none clientIp connSeq input
      Reactor.Stage.Slowloris.nowKey (by decide) (by decide)]
  simp [Reactor.Stage.Slowloris.nowOf, h]

/-- The plain metered context carries no `stick-limit` attr, so the arrival-rate
gate reads limit `0` — OFF — and admits whatever the count is. This is what carries
every pre-threading byte-identity proof through the newly prepended stage. -/
theorem stickStage_ctxOfMetered_admits (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.StickTable.ctxAdmits (ctxOfMetered clientIp connSeq input) = true := by
  refine Reactor.Stage.StickTable.unlimited_by_default ?_
  show (match (ctxOfMetered clientIp connSeq input).attrs.find?
      (fun p => p.1 == Reactor.Stage.StickTable.limitKey) with
    | some p => p.2 | none => []) = []
  rw [Reactor.Deploy.ctxOfMetered_find_none clientIp connSeq input
    Reactor.Stage.StickTable.limitKey (by decide) (by decide)]

/-- The plain metered context carries no `conn-cap` attr either, so it reads the
DEFAULT per-source cap — the knob is additive, nothing that predates it moves. -/
theorem capOf_ctxOfMetered (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.ConnLimit.capOf (ctxOfMetered clientIp connSeq input)
      = Reactor.Stage.ConnLimit.defaultConnCap := by
  have h : Reactor.Stage.ConnLimit.lookupBytes
      (ctxOfMetered clientIp connSeq input) Reactor.Stage.ConnLimit.capKey = [] := by
    show (match (ctxOfMetered clientIp connSeq input).attrs.find?
        (fun p => p.1 == Reactor.Stage.ConnLimit.capKey) with
      | some p => p.2 | none => []) = []
    rw [Reactor.Deploy.ctxOfMetered_find_none clientIp connSeq input
      Reactor.Stage.ConnLimit.capKey (by decide) (by decide)]
  exact Reactor.Stage.ConnLimit.capOf_absent h

/-- **The conn-limit gate admits every plain metered context** (active count `0`,
strictly under the default cap). -/
theorem connStage_ctxOfMetered_admits (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.ConnLimit.ctxAdmits (ctxOfMetered clientIp connSeq input) = true := by
  simp [Reactor.Stage.ConnLimit.ctxAdmits, activeOf_ctxOfMetered, capOf_ctxOfMetered,
    Reactor.Stage.ConnLimit.admits, Reactor.Stage.ConnLimit.defaultConnCap]

/-- **The slowloris gate is in time on every plain metered context** (header span
`0`, well under the timeout). -/
theorem slowStage_ctxOfMetered_ok (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.Slowloris.ctxExpired (ctxOfMetered clientIp connSeq input) = false := by
  simp [Reactor.Stage.Slowloris.ctxExpired, nowOf_ctxOfMetered,
    Reactor.Stage.Slowloris.expired, Reactor.Stage.Slowloris.headerTimeout]

/-- The streamed-byte accumulator slot of a metered context is empty: the sans-IO fold
never stashes a streamed count (that enforcement lives in the dataplane body-read
loop), so the fold's body-size gate reduces to the declared-`Content-Length` gate. -/
theorem streamedOf_ctxOfMetered (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.BodyLimit.streamedOf (ctxOfMetered clientIp connSeq input) = 0 := by
  simp [Reactor.Stage.BodyLimit.streamedOf, ctxOfMetered,
        Reactor.Stage.BodyLimit.streamedKey,
        Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey, Reactor.Stage.Rate.clockKey]

/-- On a metered context the body-size gate IS the declared-`Content-Length` gate
(`oversized`), since no streamed count is stashed. -/
theorem oversizedCtx_ctxOfMetered (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.BodyLimit.oversizedCtx (ctxOfMetered clientIp connSeq input)
      = Reactor.Stage.BodyLimit.oversized (ctxOfMetered clientIp connSeq input).req :=
  Reactor.Stage.BodyLimit.oversizedCtx_of_no_stream _
    (streamedOf_ctxOfMetered clientIp connSeq input)

/-- On a bare (unmetered) context the body-size gate IS the declared gate too. -/
theorem oversizedCtx_ctxOf (input : Bytes) :
    Reactor.Stage.BodyLimit.oversizedCtx (ctxOf input)
      = Reactor.Stage.BodyLimit.oversized (ctxOf input).req :=
  Reactor.Stage.BodyLimit.oversizedCtx_of_no_stream _ (by
    simp [Reactor.Stage.BodyLimit.streamedOf, ctxOf, Reactor.Stage.BodyLimit.streamedKey])

/-! ## The consolidated serve (folds the full registry, new stages included) -/

/-- The built response of the consolidated fold on a directly-supplied context. -/
def deployPipelineRespOf (c : Ctx) : Response :=
  (runPipeline deployPipelineStages appHandler c).build

/-- The consolidated metered serve as wire bytes: the flat-registry fold over the
connection-aware peer/seq context the dataplane threads in. -/
def servePipelineMetered (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Bytes :=
  serialize ((runPipeline deployPipelineStages appHandler
    (ctxOfMetered clientIp connSeq input)).build)

/-- The consolidated metered serve at the host ABI (`ByteArray → UInt64 →
ByteArray`). -/
def drorbServePipelineMetered (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  ByteArray.mk (servePipelineMetered peer.toList seq.toNat input.toList).toArray

/-! ## The range/freshness collapse — the five range stamps are the identity off
their surface (unchanged from the prior wave; stated about the tail AFTER the
outermost `errorStage`). -/

/-- The body-size gate + the five range/freshness stages, over the plus8 onion — the
tail of the consolidated registry after the outermost `errorStage`. The body-size
`413` gate leads (outermost of the tail); the five range/freshness stamps follow. -/
def rangeFreshTail : List Stage :=
  Reactor.Stage.BodyLimit.bodyLimitStage
    :: Reactor.Stage.RangeUnveil.rangeUnveilStage
    :: Reactor.Stage.CacheControl.cacheControlStage
    :: Reactor.Stage.ModifiedSince.lmStampStage
    :: Reactor.Stage.AssetExpires.assetExpiresStage
    :: Reactor.Stage.AssetImmutable.assetImmutableStage
    :: Reactor.DeployPlus8.deployStagesPlus8

/-- **The two DoS gates peel off the front of the metered fold.** When both gates
pass (conn-limit admits, slowloris in time — true on every plain metered context by
`connStage_ctxOfMetered_admits` / `slowStage_ctxOfMetered_ok`), the fifty-one-stage
fold equals the forty-nine-stage `errorStage :: rangeFreshTail` fold the existing
`/bulk` collapse reasons about, so that whole chain transfers through the two
prepended admission gates untouched. -/
theorem deployPipelineStages_peel_dos (c : Ctx)
    (hconn : Reactor.Stage.ConnLimit.ctxAdmits c = true)
    (hstick : Reactor.Stage.StickTable.ctxAdmits c = true)
    (hslow : Reactor.Stage.Slowloris.ctxExpired c = false) :
    runPipeline deployPipelineStages appHandler c
      = runPipeline (Reactor.Stage.ErrorPage.errorStage :: rangeFreshTail) appHandler c := by
  rw [show deployPipelineStages
        = Reactor.Stage.ConnLimit.connStage
          :: Reactor.Stage.StickTable.stickStage
          :: Reactor.Stage.Slowloris.slowStage
          :: Reactor.Stage.ErrorPage.errorStage :: rangeFreshTail from rfl,
      Reactor.Stage.ConnLimit.connStage_pass _ appHandler c hconn,
      Reactor.Stage.StickTable.stickStage_pass _ appHandler c hstick,
      Reactor.Stage.Slowloris.slowStage_pass _ appHandler c hslow]

/-- **The five range/freshness stages collapse to the identity on the fold** when
the request carries no range and is not a static `GET` (and the context has no
stashed range). Each stage passes the request phase and is builder-identical on
the response phase under its off-fact — so the fold over `rangeFreshTail` equals
the plus8 fold, builder-for-builder. -/
theorem newStages_collapse (c : Ctx)
    (hbody : Reactor.Stage.BodyLimit.oversizedCtx c = false)
    (hu : Reactor.Stage.RangeUnveil.unveils c.req = false)
    (hs : Reactor.Stage.CacheControl.isStaticGet c = false)
    (hstash : Reactor.Stage.RangeUnveil.stashOf c = none) :
    runPipeline rangeFreshTail appHandler c
      = runPipeline Reactor.DeployPlus8.deployStagesPlus8 appHandler c := by
  -- generic peel: a stage whose request phase continues on `c` and whose
  -- response phase is `c`-identical drops off the front of the fold.
  have peel : ∀ (s : Stage) (rest : List Stage),
      s.onRequest c = StageStep.continue c → (∀ b, s.onResponse c b = b) →
      runPipeline (s :: rest) appHandler c = runPipeline rest appHandler c := by
    intro s rest hReq hResp
    rw [pipeline_cons, hReq]
    exact hResp _
  -- cacheControl's response phase is builder-identical off the static surface
  have hccResp : ∀ b, Reactor.Stage.CacheControl.cacheControlStage.onResponse c b = b := by
    intro b
    show (if b.acc.status == 200 && Reactor.Stage.CacheControl.isStaticGet c
          then b.addHeader (Reactor.Stage.CacheControl.cacheControlName,
                            Reactor.Stage.CacheControl.cacheControlVal)
          else b) = b
    rw [hs]; simp
  -- the three static-asset stamps of this wave are each the identity off static
  have hlmResp : ∀ b, Reactor.Stage.ModifiedSince.lmStampStage.onResponse c b = b :=
    fun b => Reactor.Stage.ModifiedSince.lmStamp_noop_nonstatic c b hs
  have hexpResp : ∀ b, Reactor.Stage.AssetExpires.assetExpiresStage.onResponse c b = b :=
    fun b => Reactor.Stage.AssetExpires.assetExpiresStage_resp_off_static c b hs
  have himmResp : ∀ b, Reactor.Stage.AssetImmutable.assetImmutableStage.onResponse c b = b :=
    fun b => Reactor.Stage.AssetImmutable.assetImmutableStage_resp_off_static c b hs
  show runPipeline (Reactor.Stage.BodyLimit.bodyLimitStage
      :: Reactor.Stage.RangeUnveil.rangeUnveilStage
      :: Reactor.Stage.CacheControl.cacheControlStage
      :: Reactor.Stage.ModifiedSince.lmStampStage
      :: Reactor.Stage.AssetExpires.assetExpiresStage
      :: Reactor.Stage.AssetImmutable.assetImmutableStage
      :: Reactor.DeployPlus8.deployStagesPlus8) appHandler c
    = runPipeline Reactor.DeployPlus8.deployStagesPlus8 appHandler c
  rw [peel _ _ (Reactor.Stage.BodyLimit.body_allows c hbody) (fun _ => rfl),
      peel _ _ (Reactor.Stage.RangeUnveil.unveil_off_id c hu)
        (fun b => Reactor.Stage.RangeUnveil.unveil_noStash_id c b hstash),
      peel _ _ rfl hccResp,
      peel _ _ rfl hlmResp,
      peel _ _ rfl hexpResp,
      peel _ _ rfl himmResp]

/-- The stashed-range slot of a metered context is empty (its attribute bag holds
only the client IP and rate sequence — never the range-unveil key). -/
theorem stashOf_ctxOfMetered (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.RangeUnveil.stashOf (ctxOfMetered clientIp connSeq input) = none := by
  simp [Reactor.Stage.RangeUnveil.stashOf, ctxOfMetered,
        Reactor.Stage.RangeUnveil.ruRangeKey,
        Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey, Reactor.Stage.Rate.clockKey]

/-! ## The status stamp preserves the built status -/

/-- The nine-edge response-level stamp chain never touches the status (every step
is a `headers`-only record update; the Cache-Control apply is status-preserving). -/
theorem stampResp_status (r : Response) :
    (Datapath.DenseStamps.stampResp r).status = r.status := by
  unfold Datapath.DenseStamps.stampResp
  exact Reactor.Stage.StaleWhileRevalidate.applyCc_status r

/-! ## The IP-filter refusal reaches the wire as a `403` -/

/-- **The deployed IP-filter gate fires `403` through the full fold.** For a
context off `/admin` (JWT) and `/private` (basic-auth) whose client address the
deployed ruleset DENIES, the built response of the whole `deployStagesFull2` fold
has status `403`: the two preceding gates pass, the IP-filter short-circuits, and
the inner onion (rate gate + positions 5–14) is status-stable so the `403` is
preserved outward. The status sibling of `full2_rate_gate_status`. -/
theorem full2_ip_gate_status (c : Ctx)
    (hadmin : Reactor.Deploy.isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hipdeny : Reactor.Stage.IpFilter.deployAdmits (Reactor.Stage.IpFilter.ctxAddr c) = false) :
    ((runPipeline Reactor.Deploy.deployStagesFull2 appHandler c).build).status = 403 := by
  have hipc : Reactor.Stage.IpFilter.ipfilterStage.onRequest c
      = StageStep.respond Reactor.Stage.IpFilter.forbidden403 := by
    show (match Reactor.Stage.IpFilter.deployAdmits (Reactor.Stage.IpFilter.ctxAddr c) with
          | true  => StageStep.continue c
          | false => StageStep.respond Reactor.Stage.IpFilter.forbidden403) = _
    rw [hipdeny]
  have hstable : ∀ s ∈ (Reactor.Stage.Rate.rateStage
      :: Reactor.RateMeteredCorrect.full2AfterRate), Stage.statusStable s := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | h
    · intro _ _; rfl
    · exact Reactor.RateMeteredCorrect.full2AfterRate_statusStable s h
  rw [Reactor.RateMeteredCorrect.deployStagesFull2_eq_rate,
      pipeline_stage_effect Reactor.Deploy.jwtAdminStage _ appHandler c c
        (Reactor.Deploy.jwtAdminStage_pass c hadmin),
      Reactor.Deploy.jwtAdminStage_statusStable c _,
      pipeline_stage_effect Reactor.Stage.BasicAuth.basicStage _ appHandler c c
        (Reactor.Stage.BasicAuth.basicStage_pass c hpriv),
      Reactor.Deploy.basicStage_statusStable c _]
  exact pipeline_gate_status Reactor.Stage.IpFilter.ipfilterStage
    (Reactor.Stage.Rate.rateStage :: Reactor.RateMeteredCorrect.full2AfterRate)
    appHandler c Reactor.Stage.IpFilter.forbidden403 hipc hstable

/-! ## The `/bulk` fold never answers a configured error-page status -/

/-- **`errorStage` is inert on the `/bulk` arm.** On the literal `/bulk` datapath
shape (`armB8`, preamble-free) the deployed plus8 metered fold answers a `200` (the
handler), a `403` (IP-filter deny) or a `429` (rate deny) — never a `404` — so its
built status has no configured custom error page. `errorStage` (keyed on `404`)
therefore leaves the `/bulk` bytes byte-identical, regardless of the peer/rate
gates. The plus8 status is bridged to the base `deployStagesFull2` status through
the range/freshness (`plus8`→`plus6`→`plus5`) collapse and the status-preserving
stamp chain, then the base status is pinned by a three-way gate split. -/
theorem bulkFull2_notPage (peer : ByteArray) (seq : UInt64) (input : ByteArray)
    (harm8 : armB8 input = true) (hnp : noPreambleB input = true) :
    Reactor.Stage.ErrorPage.hasPage
      ((runPipeline deployStagesPlus8 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build).status = false := by
  -- unpack the arm: the dispatched request, the plus6/plus8 off-edges …
  obtain ⟨harm5, req, rest, hsub, harm, hoff6, hoff8⟩ := armB8_sound input harm8
  obtain ⟨hmf, hclte, hr, hwt, hdt⟩ := hoff6
  -- … and the plus5 off-edges (from the plus5 arm on the same dispatch)
  obtain ⟨reqA, restA, hsubA, harmA, hoffE⟩ :=
    Datapath.DenseStampsPlus5.armB5_dispatch input harm5
  have hreq : (ctxOfMetered peer.toList seq.toNat input.toList).req = req :=
    Reactor.Deploy.ctxOf_req input.toList req rest hsub
  have hAeqReq : reqA = req :=
    (Reactor.Deploy.ctxOf_req input.toList reqA restA hsubA).symm.trans hreq
  rw [hAeqReq] at hsubA harmA hoffE
  obtain ⟨hmeth, hstat, hlog, hev, hpre⟩ := hoffE
  -- the bulk-arm facts on the BARE ctx (its req is the same dispatch)
  have hreqBare : (ctxOf input.toList).req = req :=
    Reactor.Deploy.ctxOf_req input.toList req restA hsubA
  have harmBare : Datapath.ServeDenseReal.BulkArm (ctxOf input.toList) :=
    Datapath.ServeDenseIdx.bulkArm_of_reqArm input.toList req hreqBare harmA
  obtain ⟨hadmin, hpriv, hrate0, hredir, htrav, hpol, hgz, hcors, hseg, hna, hnb⟩ := harmBare
  -- ============ plus8 status = base full2 status (no gate facts needed) ============
  have hb : Reactor.DeployPlus8.isBulkTarget
      (ctxOfMetered peer.toList seq.toNat input.toList) = true := by
    apply Reactor.DeployPlus8.isBulkTarget_of_segs
    rw [hreq]; exact reqArm_bulkSegs req harm
  have hlen : Reactor.Stage.UriTooLong.overCap
      (ctxOfMetered peer.toList seq.toNat input.toList).req = false := by
    rw [hreq]; exact hoff8
  have hwC : ¬ (ctxOfMetered peer.toList seq.toNat input.toList).req.target
      = Reactor.Stage.ContentLanguage.welcomeTarget := by rw [hreq]; exact hwt
  have hdC : ¬ (ctxOfMetered peer.toList seq.toNat input.toList).req.target
      = Reactor.Stage.Dashboard.dashTarget := by rw [hreq]; exact hdt
  have hclteC : Reactor.Stage.ClTeGuard.clTeConflict
      (ctxOfMetered peer.toList seq.toNat input.toList).req = false := by
    rw [hreq]; exact hclte
  have hmfC : Reactor.Stage.MethodFilter.isAllowed
      (ctxOfMetered peer.toList seq.toNat input.toList).req.method = true := by
    rw [hreq]; exact hmf
  have hrC : Reactor.Stage.MultiRange.rangesOf
      (ctxOfMetered peer.toList seq.toNat input.toList).req = none := by
    rw [hreq]; exact hr
  -- the plus5 stamp facts on the metered ctx
  have hrec : Reactor.Stage.ProxyProtocol.recoverClient
      (ctxOfMetered peer.toList seq.toNat input.toList).input = none :=
    noPreambleB_sound input hnp
  have hfind : (ctxOfMetered peer.toList seq.toNat input.toList).attrs.find?
      (fun p => p.1 == Reactor.Stage.ProxyProtocol.clientKey) = none :=
    Datapath.DenseStamps.meteredAttrs_no_client peer.toList seq.toNat input.toList
  have hmethC : (Reactor.Stage.MaxForwards.isOPTIONS
        (ctxOfMetered peer.toList seq.toNat input.toList).req
      || Reactor.Stage.MaxForwards.isTRACE
        (ctxOfMetered peer.toList seq.toNat input.toList).req) = false := by
    rw [hreq]; exact hmeth
  have hnsC : Reactor.Stage.ContentLocation.isStaticGet
      (ctxOfMetered peer.toList seq.toNat input.toList) = false := by
    show ((ctxOfMetered peer.toList seq.toNat input.toList).req.method
          == Reactor.Stage.ContentLocation.getMethod
        && Reactor.Stage.ContentLocation.staticPrefix.isPrefixOf
            (ctxOfMetered peer.toList seq.toNat input.toList).req.target) = false
    rw [hreq, hstat, Bool.and_false]
  have hlogC : ¬ (ctxOfMetered peer.toList seq.toNat input.toList).req.target
      = Reactor.Stage.SessionCookie.loginTarget := by rw [hreq]; exact hlog
  have hevC : ¬ (ctxOfMetered peer.toList seq.toNat input.toList).req.target
      = Reactor.Stage.SseServe.eventsTarget := by rw [hreq]; exact hev
  have hpreC : Reactor.Stage.SpaServe.spaPrefix.isPrefixOf
      (ctxOfMetered peer.toList seq.toNat input.toList).req.target = false := by
    rw [hreq]; exact hpre
  -- plus8 build = plus5 build (response equality; needs no preamble / gate facts)
  have e1 : (runPipeline deployStagesPlus8 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build
      = (runPipeline Reactor.DeployPlus5.deployStagesPlus5 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build :=
    (Reactor.DeployPlus8.plus8_collapse _ hb hlen hwC).trans
      (Reactor.DeployPlus6.plus6_collapse _ hwC hdC hclteC hmfC hrC)
  -- plus5 build = stamped base build ⇒ status = base status
  have hstatus : ((runPipeline deployStagesPlus8 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build).status
      = ((runPipeline Reactor.Deploy.deployStagesFull2 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build).status := by
    rw [e1, Datapath.DenseStampsPlus5.plus5_build_stamped _ hrec hfind hmethC hnsC
          hlogC hevC hpreC]
    exact stampResp_status ((runPipeline Reactor.Deploy.deployStagesFull2 appHandler
      (ctxOfMetered peer.toList seq.toNat input.toList)).build)
  rw [hstatus]
  -- ============ the base full2 status on `/bulk` is 200 / 403 / 429 ============
  by_cases hip : Reactor.Stage.IpFilter.deployAdmits
      (Reactor.Stage.IpFilter.ctxAddr
        (ctxOfMetered peer.toList seq.toNat input.toList)) = true
  · by_cases hrate : Reactor.Stage.Rate.admits
        (ctxOfMetered peer.toList seq.toNat input.toList) = true
    · -- both gates admit ⇒ the metered fold is the bare fold ⇒ 200
      have happ : appHandler (ctxOf input.toList)
          = { status := 200, reason := Reactor.App.reasonFor 200,
              headers := [], body := Reactor.App.bulkBody } :=
        Datapath.ServeDenseReal.appHandler_bulk (ctxOf input.toList) hseg hna hnb
      obtain ⟨hst, _, _⟩ := Datapath.ServeDenseReal.builtScalars (ctxOf input.toList)
        hadmin hpriv rfl hrate0 hredir htrav hpol hgz hcors happ
      have hin : (ctxOfMetered peer.toList seq.toNat input.toList).input
          = (ctxOf input.toList).input := rfl
      have hkey : runPipeline Reactor.Deploy.deployStagesFull2 appHandler
            (ctxOfMetered peer.toList seq.toNat input.toList)
          = runPipeline Reactor.Deploy.deployStagesFull2 appHandler (ctxOf input.toList) := by
        rw [Datapath.ServeMeteredHeadIdx.full2_reduces_unknown_pass
              (ctxOfMetered peer.toList seq.toNat input.toList) hadmin hpriv
              (Datapath.ServeMeteredHeadIdx.ipfilterStage_pass_admit _ hip) hrate
              hredir htrav hpol,
            Reactor.Deploy.full2_reduces_unknown (ctxOf input.toList) hadmin hpriv rfl
              hrate0 hredir htrav hpol,
            Datapath.ServeMeteredHeadIdx.innerFold_ctxOfMetered peer.toList seq.toNat
              input.toList, hin]
      rw [hkey, hst]; exact Reactor.Stage.ErrorPage.hasPage_200
    · -- IP admits, rate denies ⇒ 429
      have h429 := Reactor.RateMeteredCorrect.full2_rate_gate_status
        (ctxOfMetered peer.toList seq.toNat input.toList) hadmin hpriv hip
        (by rw [← Bool.not_eq_true]; exact hrate)
      rw [h429]; decide
  · -- IP denies ⇒ 403
    have h403 := full2_ip_gate_status
      (ctxOfMetered peer.toList seq.toNat input.toList) hadmin hpriv
      (by rw [← Bool.not_eq_true]; exact hip)
    rw [h403]; decide

/-! ## The new-stage collapse — the outermost stamps are the identity off their surface -/

/-- **The dense-arm off-condition — the LITERAL `/bulk` dense shape.** Four
conjuncts, each load-bearing:

  * `armB8 input` — the request IS the dense `/bulk` datapath shape (the
    index-native `/bulk`-arm guard). A non-`/bulk` dynamic request (`GET /`, a
    `404`, `/health`, `/welcome`, …) fails this conjunct and so leaves the dense
    fast path for the FULL consolidated fold — every outermost registry stage
    (`errorStage` included) runs on it.
  * `!unveils req` and `!isStaticGet` — the two facts the range/freshness collapse
    needs (`newStages_collapse`): those five outermost stamps are the identity
    exactly here.
  * `noPreambleB input` — the raw head is a plain HTTP request (no PROXY preamble).
    Redundant with `armB8` (a preamble would parse the head as `PROXY …`, not
    `GET /bulk`, and fail the arm) and is the dense arm's OWN firing condition; it
    surfaces `recoverClient = none` for the `errorStage` inertness collapse
    (`bulkFull2_notPage`).

Decided on the parsed request of the raw input (attribute-independent, so it
agrees with the metered context). -/
def newStagesOffB (input : ByteArray) : Bool :=
  armB8 input
    && !Reactor.Stage.RangeUnveil.unveils (ctxOf input.toList).req
    && !Reactor.Stage.CacheControl.isStaticGet (ctxOf input.toList)
    && noPreambleB input
    && !Reactor.Stage.BodyLimit.oversizedCtx (ctxOf input.toList)

/-- **On the dense-arm off-condition, the consolidated fold IS the plus8 fold.**
The outermost `errorStage` is the identity on the `/bulk` arm (`bulkFull2_notPage`
— the fold never answers a configured error-page status there) and the five
range/freshness stages are the identity there (`newStages_collapse`), so their
serve bytes agree — this is the bridge that keeps the dense `/bulk` arm
byte-identical. -/
theorem drorbServePipelineMetered_eq_plus8_off (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) (hoff : newStagesOffB input = true) :
    drorbServePipelineMetered peer seq input
      = drorbServeMeteredPlus8 peer seq input := by
  simp only [newStagesOffB, Bool.and_eq_true, Bool.not_eq_true'] at hoff
  obtain ⟨⟨⟨⟨harm8, hu⟩, hstatic⟩, hnp⟩, hbody⟩ := hoff
  show ByteArray.mk (servePipelineMetered peer.toList seq.toNat input.toList).toArray
      = ByteArray.mk (servePipelinePlus8Metered peer.toList seq.toNat input.toList).toArray
  -- the body-size gate is inert (no over-cap body), transported to the metered ctx.
  have hbodyM : Reactor.Stage.BodyLimit.oversizedCtx
      (ctxOfMetered peer.toList seq.toNat input.toList) = false := by
    rw [oversizedCtx_ctxOfMetered]
    rw [oversizedCtx_ctxOf] at hbody
    exact hbody
  -- the outermost `errorStage` is inert on `/bulk`, then the body-size + range/freshness
  -- tail collapses to the plus8 fold.
  have hcol := newStages_collapse (ctxOfMetered peer.toList seq.toNat input.toList)
    hbodyM hu hstatic (stashOf_ctxOfMetered peer.toList seq.toNat input.toList)
  have hno : Reactor.Stage.ErrorPage.hasPage
      ((runPipeline rangeFreshTail appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build).status = false := by
    rw [hcol]; exact bulkFull2_notPage peer seq input harm8 hnp
  have hbuild : (runPipeline deployPipelineStages appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build
      = (runPipeline Reactor.DeployPlus8.deployStagesPlus8 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build := by
    rw [deployPipelineStages_peel_dos (ctxOfMetered peer.toList seq.toNat input.toList)
          (connStage_ctxOfMetered_admits peer.toList seq.toNat input.toList)
          (stickStage_ctxOfMetered_admits peer.toList seq.toNat input.toList)
          (slowStage_ctxOfMetered_ok peer.toList seq.toNat input.toList),
        Reactor.Stage.ErrorPage.errorStage_passthrough rangeFreshTail appHandler
          (ctxOfMetered peer.toList seq.toNat input.toList) hno, hcol]
  show ByteArray.mk (serialize ((runPipeline deployPipelineStages appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build)).toArray = _
  rw [hbuild]
  rfl

/-! ## The re-homed deployed default — dense `/bulk` arm, consolidated fold elsewhere -/

/-- **The consolidated dense-arm metered serve.** On the dense-arm off-condition
(the `/bulk` datapath shape) it reuses the plus8 dense assembly verbatim
(`serveMeteredPlus8HeadIdx`); on every other shape it is the consolidated fold,
which applies the outermost `errorStage` and the range/freshness stages. -/
def serveMeteredPipelineDenseIdx (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  if newStagesOffB input then
    serveMeteredPlus8HeadIdx peer seq input
  else
    drorbServePipelineMetered peer seq input

/-- **Byte-identity to the consolidated fold.** For EVERY `(peer, seq, input)` the
dense-arm serve equals the plain consolidated fold `drorbServePipelineMetered`: on
the off-condition the dense assembly is the plus8 fold
(`serveMeteredPlus8HeadIdx_eq`) which is the consolidated fold there
(`drorbServePipelineMetered_eq_plus8_off`); off the condition it IS the fold. -/
theorem serveMeteredPipelineDenseIdx_eq (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    serveMeteredPipelineDenseIdx peer seq input
      = drorbServePipelineMetered peer seq input := by
  unfold serveMeteredPipelineDenseIdx
  cases hoff : newStagesOffB input with
  | false => rw [if_neg Bool.false_ne_true]
  | true =>
    rw [if_pos rfl]
    rw [serveMeteredPlus8HeadIdx_eq,
        ← drorbServePipelineMetered_eq_plus8_off peer seq input hoff]

/-- **The consolidated default metered serve BODY.** The RFC-conformance wrapper
(`conformantServe`) over the consolidated dense-arm serve: the `/bulk` arm emits
the fully-stamped dense head + the dense 1 MiB body with no per-byte `List` cons;
every other shape is the consolidated `List` fold, which now applies the
outermost `errorStage` (its `404` custom page) and the range / freshness stages.

HOST-SYMBOL NOTE (honest): this def is NOT exported directly. The single host
serve symbol is `drorb_serve_pipeline_conformant`
(`Dataplane.drorbServePipelineConformant`), which is definitionally this function
— so the deployed default IS this serve, by construction. -/
def serveMeteredPipelineConformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  conformantServe (fun i => serveMeteredPipelineDenseIdx peer seq i) input

/-- **The consolidation's core claim: the deployed executable = the conformance
wrapper over the consolidated registry fold.** The dense arm is byte-identical to
the plain consolidated fold (`serveMeteredPipelineDenseIdx_eq`), so the bytes the
host emits are exactly the consolidated pipeline's bytes, conformance-wrapped. -/
theorem serveMeteredPipelineConformant_eq_stages (peer : ByteArray)
    (seq : UInt64) (input : ByteArray) :
    serveMeteredPipelineConformant peer seq input
      = conformantServe (fun i => drorbServePipelineMetered peer seq i) input := by
  show conformantServe (fun i => serveMeteredPipelineDenseIdx peer seq i) input
    = conformantServe (fun i => drorbServePipelineMetered peer seq i) input
  have h : (fun i => serveMeteredPipelineDenseIdx peer seq i)
         = (fun i => drorbServePipelineMetered peer seq i) := by
    funext i; exact serveMeteredPipelineDenseIdx_eq peer seq i
  rw [h]

/-! ## The DoS-metered serve — the accept-path admission state threaded into the fold

The plain metered context (`ctxOfMetered`) supplies only the client IP + rate
sequence, so the two prepended DoS gates are inert on it (proven above). The
DEPLOYED serve threads two further accept-path readings into the attribute bag: the
source's standing active-connection count (`conn-active`) and the header-arrival
span (`hdr-now`, against a zero `hdr-started` base) — plus the OPERATOR's per-source
cap (`conn-cap`, from `max-connections`). The conn-limit gate reads the count against
that CONFIGURED cap (→ `503` at/over it), the slowloris gate reads the span (→ `408`
at/over `headerTimeout`).

The cap is threaded, not baked: it used to be the module constant
`Reactor.Stage.ConnLimit.connCap := 4`, which no operator directive could move, so a
default deployment refused any source at five concurrent connections — under what a
browser opens. `defaultConnCap` (512) applies when the host threads nothing. -/

-- The DoS-metered context, its four projection lemmas and the stick-table hole
-- theorem live in `Reactor.Deploy` (opened above): ONE representation of the
-- accept-path admission readings, shared by this consolidated seam and the
-- config-driven `drorb_serve_metered_cfg_conformant` seam, proven once.

/-! ### The gates FIRE through the deployed fold on the DoS-metered context -/

/-- **Conn-limit FIRES at the CONFIGURED cap.** At/over the cap the operator
configured, the deployed fold's outermost stage short-circuits the whole
fifty-two-stage onion to the proven `503`: the built response is the tail folded over
`resp503`, never the handler. Stated over an ARBITRARY live cap (`0 < cap`, any cap
the host can cross), so the refusal point is the configured one — this is the
restatement of the old `connCap`-literal theorem over the configured value. -/
theorem connLimit_fires_deployed (clientIp : Bytes) (connSeq span rateCount rateLimit burstCap burstRate : Nat)
    {active cap : Nat}
    (input : Bytes) (hcap : cap < 2 ^ 64) (hpos : 0 < cap) (hover : cap ≤ active) :
    runPipeline deployPipelineStages appHandler
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = runResp (deployPipelineStages.tail)
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
          (ResponseBuilder.ofResponse Reactor.Stage.ConnLimit.resp503) := by
  have hover' : Reactor.Stage.ConnLimit.ctxAdmits
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) = false := by
    show Reactor.Stage.ConnLimit.admits
        (Reactor.Stage.ConnLimit.capOf
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input))
        (Reactor.Stage.ConnLimit.activeOf
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)) = false
    rw [activeOf_ctxOfMeteredConn,
        capOf_ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input hcap]
    exact Reactor.Stage.ConnLimit.admits_over hpos hover
  exact Reactor.Stage.ConnLimit.connStage_gate_build (deployPipelineStages.tail) appHandler
    (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) hover'

/-- **Conn-limit does NOT fire below the configured cap** — the dual, and the fact the
regression violated: strictly under the operator's cap the gate is TRANSPARENT and the
whole fold runs. -/
theorem connLimit_passes_deployed (clientIp : Bytes) (connSeq span rateCount rateLimit burstCap burstRate : Nat)
    {active cap : Nat}
    (input : Bytes) (hcap : cap < 2 ^ 64) (hunder : active < cap) :
    runPipeline deployPipelineStages appHandler
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = runPipeline (deployPipelineStages.tail) appHandler
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) := by
  have hadmit : Reactor.Stage.ConnLimit.ctxAdmits
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) = true := by
    show Reactor.Stage.ConnLimit.admits
        (Reactor.Stage.ConnLimit.capOf
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input))
        (Reactor.Stage.ConnLimit.activeOf
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)) = true
    rw [activeOf_ctxOfMeteredConn,
        capOf_ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input hcap]
    exact Reactor.Stage.ConnLimit.admits_under (Nat.lt_of_le_of_lt (Nat.zero_le _) hunder) hunder
  exact Reactor.Stage.ConnLimit.connStage_pass (deployPipelineStages.tail) appHandler
    (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) hadmit

/-- **A browser burst is admitted by the DEPLOYED fold under the DEFAULT cap.** A
source holding EIGHT concurrent connections — more than a browser opens per origin —
passes the deployed pipeline's outermost gate with no config at all. This is exactly
the case the hardcoded `4` answered `503` to. -/
theorem browserBurst_admitted_deployed (clientIp : Bytes)
    (connSeq span rateCount rateLimit burstCap burstRate : Nat) (input : Bytes) :
    runPipeline deployPipelineStages appHandler
        (ctxOfMeteredConn clientIp connSeq 8 span Reactor.Stage.ConnLimit.defaultConnCap
          rateCount rateLimit burstCap burstRate input)
      = runPipeline (deployPipelineStages.tail) appHandler
          (ctxOfMeteredConn clientIp connSeq 8 span
            Reactor.Stage.ConnLimit.defaultConnCap rateCount rateLimit burstCap burstRate input) :=
  connLimit_passes_deployed clientIp connSeq span rateCount rateLimit burstCap burstRate input
    (by decide) (by decide)

/-- **★ THE ARRIVAL-RATE GATE FIRES ON THE DEPLOYED FOLD, at the CONFIGURED limit.**
Under the connection cap but at/over the operator's threaded `rate-limit`, the deployed
fold's second stage short-circuits the whole fifty-three-stage onion to the proven
`429`: the built response is the tail folded over `resp429`, never the handler.

Stated over an ARBITRARY live limit and an ARBITRARY count (any pair the host can
cross), so the refusal point is the CONFIGURED one. This is the theorem the fold could
not have before: `rateCount` had no producer, because the reactor's rate window
returned a bool and not a count. -/
theorem rateLimit_fires_deployed (clientIp : Bytes) (connSeq active span cap : Nat)
    {rateCount rateLimit burstCap burstRate : Nat}
    (input : Bytes) (hcap : cap < 2 ^ 64)
    (hadmitConn : Reactor.Stage.ConnLimit.admits cap active = true)
    (hc : rateCount < 2 ^ 64) (hl : rateLimit < 2 ^ 64)
    (hpos : 0 < rateLimit) (hover : rateLimit ≤ rateCount) :
    runPipeline deployPipelineStages appHandler
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = runResp ((deployPipelineStages.tail))
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
          (ResponseBuilder.ofResponse Reactor.Stage.StickTable.resp429) := by
  have hconn : Reactor.Stage.ConnLimit.ctxAdmits
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) = true := by
    show Reactor.Stage.ConnLimit.admits (Reactor.Stage.ConnLimit.capOf _)
        (Reactor.Stage.ConnLimit.activeOf _) = true
    rw [activeOf_ctxOfMeteredConn,
        capOf_ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input hcap]
    exact hadmitConn
  have hstick : Reactor.Stage.StickTable.ctxAdmits
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) = false := by
    rw [Reactor.Deploy.ctxAdmits_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ hc hl]
    exact Reactor.Stage.StickTable.admitsAt_over hpos hover
  rw [show deployPipelineStages
        = Reactor.Stage.ConnLimit.connStage :: deployPipelineStages.tail from rfl,
      Reactor.Stage.ConnLimit.connStage_pass (deployPipelineStages.tail) appHandler _ hconn,
      show deployPipelineStages.tail
        = Reactor.Stage.StickTable.stickStage :: (deployPipelineStages.tail).tail from rfl]
  exact Reactor.Stage.StickTable.stickStage_gate_build ((deployPipelineStages.tail).tail)
    appHandler _ hstick

/-- **The refusal is a real `429` on the wire** — the status carried out through the
status-stable inner onion, not merely a builder the fold discards. -/
theorem rateLimit_fires_deployed_status (clientIp : Bytes) (connSeq active span cap : Nat)
    {rateCount rateLimit burstCap burstRate : Nat}
    (input : Bytes) (hcap : cap < 2 ^ 64)
    (hadmitConn : Reactor.Stage.ConnLimit.admits cap active = true)
    (hc : rateCount < 2 ^ 64) (hl : rateLimit < 2 ^ 64)
    (hpos : 0 < rateLimit) (hover : rateLimit ≤ rateCount)
    (hst : ∀ t ∈ (deployPipelineStages.tail).tail, Stage.statusStable t) :
    ((runPipeline deployPipelineStages appHandler
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)).build).status
      = 429 := by
  have hconn : Reactor.Stage.ConnLimit.ctxAdmits
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) = true := by
    show Reactor.Stage.ConnLimit.admits (Reactor.Stage.ConnLimit.capOf _)
        (Reactor.Stage.ConnLimit.activeOf _) = true
    rw [activeOf_ctxOfMeteredConn,
        capOf_ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input hcap]
    exact hadmitConn
  have hstick : Reactor.Stage.StickTable.ctxAdmits
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) = false := by
    rw [Reactor.Deploy.ctxAdmits_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ hc hl]
    exact Reactor.Stage.StickTable.admitsAt_over hpos hover
  rw [show deployPipelineStages
        = Reactor.Stage.ConnLimit.connStage :: deployPipelineStages.tail from rfl,
      Reactor.Stage.ConnLimit.connStage_pass (deployPipelineStages.tail) appHandler _ hconn,
      show deployPipelineStages.tail
        = Reactor.Stage.StickTable.stickStage :: (deployPipelineStages.tail).tail from rfl]
  exact Reactor.Stage.StickTable.stickStage_over_status ((deployPipelineStages.tail).tail)
    appHandler _ hstick hst

/-- **The arrival-rate gate does NOT fire below the configured limit** — the dual, and
the property every normal request depends on: strictly under the operator's limit the
gate is TRANSPARENT and the whole fold runs. -/
theorem rateLimit_passes_deployed (clientIp : Bytes) (connSeq active span cap : Nat)
    {rateCount rateLimit burstCap burstRate : Nat}
    (input : Bytes) (hc : rateCount < 2 ^ 64) (hl : rateLimit < 2 ^ 64)
    (hunder : rateCount < rateLimit) :
    runPipeline (deployPipelineStages.tail) appHandler
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = runPipeline ((deployPipelineStages.tail).tail) appHandler
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) := by
  have hstick : Reactor.Stage.StickTable.ctxAdmits
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) = true := by
    rw [Reactor.Deploy.ctxAdmits_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ hc hl]
    exact Reactor.Stage.StickTable.admitsAt_under (Nat.lt_of_le_of_lt (Nat.zero_le _) hunder) hunder
  rw [show deployPipelineStages.tail
        = Reactor.Stage.StickTable.stickStage :: (deployPipelineStages.tail).tail from rfl]
  exact Reactor.Stage.StickTable.stickStage_pass ((deployPipelineStages.tail).tail)
    appHandler _ hstick

/-- **A threaded limit of `0` leaves the deployed rate gate OFF** — for EVERY count,
including one far past any plausible limit. `0` is what an operator who disables
`rate-limit` crosses, and it is also what every context that predates this threading
reads; this is the statement that arming the gate is the operator's decision. -/
theorem rateLimit_zero_off_deployed (clientIp : Bytes) (connSeq active span cap : Nat)
    {rateCount : Nat} (input : Bytes) (hc : rateCount < 2 ^ 64) :
    runPipeline (deployPipelineStages.tail) appHandler
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount 0 burstCap burstRate input)
      = runPipeline ((deployPipelineStages.tail).tail) appHandler
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount 0 burstCap burstRate input) := by
  have hstick : Reactor.Stage.StickTable.ctxAdmits
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount 0 burstCap burstRate input) = true := by
    rw [Reactor.Deploy.ctxAdmits_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ hc (by decide)]
    exact Reactor.Stage.StickTable.admitsAt_unlimited _
  rw [show deployPipelineStages.tail
        = Reactor.Stage.StickTable.stickStage :: (deployPipelineStages.tail).tail from rfl]
  exact Reactor.Stage.StickTable.stickStage_pass ((deployPipelineStages.tail).tail)
    appHandler _ hstick

/-- **Slowloris FIRES.** Under the connection cap but at/over the header timeout, the
conn-limit gate passes and the slowloris gate short-circuits the onion to the proven
`408`. Non-vacuous — a header drip whose span reaches `headerTimeout` is dropped. -/
theorem slowloris_fires_deployed (clientIp : Bytes)
    (connSeq active cap rateCount rateLimit burstCap burstRate : Nat) {span : Nat}
    (input : Bytes)
    (hcap : cap < 2 ^ 64)
    (hunder : Reactor.Stage.ConnLimit.admits cap active = true)
    (hrc : rateCount < 2 ^ 64) (hrl : rateLimit < 2 ^ 64)
    (hrate : Reactor.Stage.StickTable.admitsAt rateLimit rateCount = true)
    (hexp : Reactor.Stage.Slowloris.headerTimeout ≤ span) :
    runPipeline deployPipelineStages appHandler
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = runResp (((deployPipelineStages.tail).tail).tail)
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
          (ResponseBuilder.ofResponse Reactor.Stage.Slowloris.resp408) := by
  have hadmit : Reactor.Stage.ConnLimit.ctxAdmits
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) = true := by
    show Reactor.Stage.ConnLimit.admits
        (Reactor.Stage.ConnLimit.capOf
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input))
        (Reactor.Stage.ConnLimit.activeOf
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)) = true
    rw [activeOf_ctxOfMeteredConn,
        capOf_ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input hcap]
    exact hunder
  have hexp' : Reactor.Stage.Slowloris.ctxExpired
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) = true := by
    show Reactor.Stage.Slowloris.expired Reactor.Stage.Slowloris.headerTimeout
        (Reactor.Stage.Slowloris.startedOf
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input))
        (Reactor.Stage.Slowloris.nowOf
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input))
        = true
    rw [startedOf_ctxOfMeteredConn, nowOf_ctxOfMeteredConn]
    exact Reactor.Stage.Slowloris.expired_over (by decide) (by simpa using hexp)
  -- peel the passing conn-limit gate, then the passing arrival-rate gate, then the
  -- slowloris gate short-circuits
  have hstick : Reactor.Stage.StickTable.ctxAdmits
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) = true := by
    rw [Reactor.Deploy.ctxAdmits_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ hrc hrl]
    exact hrate
  rw [show deployPipelineStages
        = Reactor.Stage.ConnLimit.connStage :: deployPipelineStages.tail from rfl,
      Reactor.Stage.ConnLimit.connStage_pass (deployPipelineStages.tail) appHandler
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) hadmit,
      show deployPipelineStages.tail
        = Reactor.Stage.StickTable.stickStage :: (deployPipelineStages.tail).tail from rfl,
      Reactor.Stage.StickTable.stickStage_pass ((deployPipelineStages.tail).tail) appHandler
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) hstick,
      show (deployPipelineStages.tail).tail
        = Reactor.Stage.Slowloris.slowStage :: ((deployPipelineStages.tail).tail).tail from rfl]
  exact Reactor.Stage.Slowloris.slowStage_gate_build (((deployPipelineStages.tail).tail).tail)
    appHandler
    (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) hexp'

/-! ### The deployed DoS-metered serve object -/

/-- The DoS-metered fold as wire bytes. -/
def servePipelineMeteredConn (clientIp : Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) : Bytes :=
  serialize ((runPipeline deployPipelineStages appHandler
    (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)).build)

/-- The DoS-metered serve at the host ABI. `cap` is the operator's configured
per-source `max-connections`, crossed as a `UInt64` (`0` = unlimited, as `admits`
already reads it); the host SUPPLIES the number, the proven `admits` MAKES the
decision. -/
def drorbServePipelineMeteredConn (peer : ByteArray) (seq active span cap rateCount rateLimit burstCap burstRate : UInt64)
    (input : ByteArray) : ByteArray :=
  ByteArray.mk (servePipelineMeteredConn peer.toList seq.toNat active.toNat span.toNat
    cap.toNat rateCount.toNat rateLimit.toNat burstCap.toNat burstRate.toNat input.toList).toArray

/-- **The DoS-metered dense-arm serve.** The `/bulk` datapath shape keeps the plus8
dense fast path verbatim (the DoS gates are enforced accept-path-side for that arm);
every other shape flows through the fifty-one-stage fold, where the two admission
gates decide on the threaded accept-path state. On `/bulk` this is byte-identical to
the baseline dense serve regardless of the admission readings. -/
def serveMeteredPipelineConnDenseIdx (peer : ByteArray) (seq active span cap rateCount rateLimit burstCap burstRate : UInt64)
    (input : ByteArray) : ByteArray :=
  if newStagesOffB input then
    serveMeteredPlus8HeadIdx peer seq input
  else
    drorbServePipelineMeteredConn peer seq active span cap rateCount rateLimit burstCap burstRate input

/-- On the `/bulk` dense arm the DoS-metered serve equals the baseline dense serve,
for ANY admission readings — the `/bulk` fast path is untouched. -/
theorem serveMeteredPipelineConnDenseIdx_bulk_eq (peer : ByteArray)
    (seq active span cap rateCount rateLimit burstCap burstRate : UInt64)
    (input : ByteArray) (hoff : newStagesOffB input = true) :
    serveMeteredPipelineConnDenseIdx peer seq active span cap rateCount rateLimit burstCap burstRate input
      = serveMeteredPipelineDenseIdx peer seq input := by
  unfold serveMeteredPipelineConnDenseIdx serveMeteredPipelineDenseIdx
  rw [if_pos hoff, if_pos hoff]

/-- **The deployed DoS-metered default serve BODY** — the RFC-conformance wrapper
over the DoS-metered dense-arm serve. This is the function the host symbol
`drorb_serve_pipeline_conformant` is definitionally equal to. -/
def serveMeteredPipelineConnConformant (peer : ByteArray) (seq active span cap rateCount rateLimit burstCap burstRate : UInt64)
    (input : ByteArray) : ByteArray :=
  conformantServe (fun i => serveMeteredPipelineConnDenseIdx peer seq active span cap rateCount rateLimit burstCap burstRate i) input

/-! ## Non-vacuity — the narrowed off-condition routes `/bulk` dense, dynamic full,
and `errorStage` genuinely FIRES on a dynamic `404`. -/

/-- A plain dynamic `GET /` (root): not `/bulk`, no range, not a static asset. -/
def rootReq : ByteArray := "GET / HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

/-- A `404` dynamic shape (`GET /nope`): not `/bulk`, no range, not static. -/
def notFoundReq : ByteArray := "GET /nope HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

-- The dense fast path STILL fires on the real `/bulk` datapath shape…
#guard newStagesOffB Datapath.ServeDenseReal.bulkDemoReq = true
-- …while a non-`/bulk` dynamic request now LEAVES the dense arm for the full
-- consolidated fold — so every outermost registry stage (errorStage included)
-- runs on it.
#guard newStagesOffB rootReq = false
#guard newStagesOffB notFoundReq = false

/-- **`errorStage` genuinely FIRES on a dynamic `404`.** On the missing-path ctx
the consolidated fold rewrites the handler's `404` body to the rendered custom
error page (status still `404`) — the outermost stage is a real byte-driver, not
inert, on the general dynamic surface. -/
theorem errorStage_fires_dynamic_404 :
    ((runPipeline [Reactor.Stage.ErrorPage.errorStage]
        (fun _ => Reactor.Stage.ErrorPage.default404)
        Reactor.Stage.ErrorPage.missingCtx).build).body
      = Reactor.Stage.ErrorPage.renderPage
          (Reactor.Stage.ErrorPage.pathOf Reactor.Stage.ErrorPage.missingCtx)
    ∧ ((runPipeline [Reactor.Stage.ErrorPage.errorStage]
        (fun _ => Reactor.Stage.ErrorPage.default404)
        Reactor.Stage.ErrorPage.missingCtx).build).status = 404 :=
  Reactor.Stage.ErrorPage.errorStage_rewrites_404

/-! ## RequestHeadLimit is deployed PRE-PARSE — the fold carries no head-limit stage

The request-head DoS gate (Z1 — an oversized request head overflows the recursive
parser's stack) is deployed OUTSIDE this fold, in the conformance wrapper
`conformantServe`, which runs `Reactor.Stage.RequestHeadLimit.headGate` on the raw
bytes BEFORE the parse — the only place a head-length gate can prevent the overflow
(a stage inside the fold runs only AFTER the parse the overflow lives in). So no
`headLimitStage` is prepended here; adding one would be redundant AND wrong — the
in-fold stage gates on the whole-message length `c.input.length`, so a legitimate
large BODY behind a small head (the body-cliff `headGate` deliberately admits) would
be falsely refused `431`. The theorems below characterize that the deployed export
answers the pre-parse gate's refusal DIRECTLY, so the head-limit deployment is
complete without touching the stage list. -/

/-- **The deployed serve answers the pre-parse head gate directly.** Whenever the
pre-parse `headGate` refuses the raw input with `r` (an oversized request-LINE →
`414`, or header BLOCK → `431`), the deployed DoS-metered default serve
`serveMeteredPipelineConnConformant` (the body of the host symbol
`drorb_serve_pipeline_conformant`) emits exactly `serialize (addDate r)` — the
fifty-two-stage fold, and every stage in it, is never run, for ANY peer / seq /
admission readings. The request-head DoS deployment lives in the conformance
wrapper, ahead of the parse. -/
theorem serveMeteredPipelineConnConformant_head_refusal
    (peer : ByteArray) (seq active span cap rateCount rateLimit burstCap burstRate : UInt64) (input : ByteArray) (r : Response)
    (hz : Reactor.Stage.RequestHeadLimit.headGate input = some r) :
    serveMeteredPipelineConnConformant peer seq active span cap rateCount rateLimit burstCap burstRate input
      = ByteArray.mk (serialize (Reactor.ServeConformant.addDate r)).toArray := by
  unfold serveMeteredPipelineConnConformant conformantServe
  rw [hz]

/-- **The deployed head refusal is exactly the RFC `414` / `431`.** By
`headGate_statuses` the pre-parse refusal is only ever the over-long request-line
`414` or the over-long header block `431`, so the deployed serve's head-DoS answer
is one of exactly those two — never a fold answer. -/
theorem serveMeteredPipelineConnConformant_head_refusal_status
    (peer : ByteArray) (seq active span cap rateCount rateLimit burstCap burstRate : UInt64) (input : ByteArray) (r : Response)
    (hz : Reactor.Stage.RequestHeadLimit.headGate input = some r) :
    serveMeteredPipelineConnConformant peer seq active span cap rateCount rateLimit burstCap burstRate input
        = ByteArray.mk (serialize (Reactor.ServeConformant.addDate r)).toArray
      ∧ (r.status = 414 ∨ r.status = 431) :=
  ⟨serveMeteredPipelineConnConformant_head_refusal peer seq active span cap
      rateCount rateLimit burstCap burstRate input r hz,
    Reactor.Stage.RequestHeadLimit.headGate_statuses input r hz⟩

/-! ### Non-vacuity — the pre-parse gate FIRES on the deployed default -/

/-- A request whose request-LINE is ~20 000 bytes — a Z1 crash shape. -/
def bigLineReq : ByteArray :=
  ("GET /" ++ String.mk (List.replicate 20000 'a')
    ++ " HTTP/1.1\r\nHost: x\r\n\r\n").toUTF8

/-- A request whose header BLOCK is ~28 KiB behind a short request-line. -/
def bigHeadReq : ByteArray :=
  ("GET / HTTP/1.1\r\nHost: x\r\n"
    ++ String.join (List.replicate 900 "x-filler: aaaaaaaaaaaaaaaaaaaa\r\n")
    ++ "\r\n").toUTF8

-- The deployed default serve refuses the oversized request-line with the `414`
-- bytes and the oversized header block with the `431` bytes — the pre-parse gate
-- FIRING on the deployed export, no in-fold stage — while a normal request passes
-- the gate into the fold.
#guard (serveMeteredPipelineConnConformant "".toUTF8 0 0 0 0 0 0 0 0 bigLineReq).toList
        == serialize (Reactor.ServeConformant.addDate
            Reactor.Stage.RequestHeadLimit.uriTooLongResp)
#guard (serveMeteredPipelineConnConformant "".toUTF8 0 0 0 0 0 0 0 0 bigHeadReq).toList
        == serialize (Reactor.ServeConformant.addDate
            Reactor.Stage.RequestHeadLimit.requestHeaderFieldsTooLargeResp)
#guard (Reactor.Stage.RequestHeadLimit.headGate
        ("GET /health HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8)).isNone


end Reactor.DeployPipeline

#print axioms Reactor.DeployPipeline.stampResp_status
#print axioms Reactor.DeployPipeline.full2_ip_gate_status
#print axioms Reactor.DeployPipeline.bulkFull2_notPage
#print axioms Reactor.DeployPipeline.newStages_collapse
#print axioms Reactor.DeployPipeline.drorbServePipelineMetered_eq_plus8_off
#print axioms Reactor.DeployPipeline.serveMeteredPipelineDenseIdx_eq
#print axioms Reactor.DeployPipeline.serveMeteredPipelineConformant_eq_stages
#print axioms Reactor.DeployPipeline.deployPipelineStages_length
#print axioms Reactor.DeployPipeline.errorStage_fires_dynamic_404
#print axioms Reactor.DeployPipeline.deployPipelineStages_peel_dos
#print axioms Reactor.DeployPipeline.connStage_ctxOfMetered_admits
#print axioms Reactor.DeployPipeline.slowStage_ctxOfMetered_ok
#print axioms Reactor.Deploy.activeOf_ctxOfMeteredConn
#print axioms Reactor.Deploy.capOf_ctxOfMeteredConn
#print axioms Reactor.DeployPipeline.connLimit_fires_deployed
#print axioms Reactor.DeployPipeline.connLimit_passes_deployed
#print axioms Reactor.DeployPipeline.browserBurst_admitted_deployed
#print axioms Reactor.DeployPipeline.rateLimit_fires_deployed
#print axioms Reactor.DeployPipeline.rateLimit_fires_deployed_status
#print axioms Reactor.DeployPipeline.rateLimit_passes_deployed
#print axioms Reactor.DeployPipeline.rateLimit_zero_off_deployed
#print axioms Reactor.DeployPipeline.slowloris_fires_deployed
#print axioms Reactor.Deploy.nowOf_ctxOfMeteredConn
#print axioms Reactor.DeployPipeline.connLimit_fires_deployed
#print axioms Reactor.DeployPipeline.slowloris_fires_deployed
#print axioms Reactor.DeployPipeline.serveMeteredPipelineConnDenseIdx_bulk_eq
#print axioms Reactor.DeployPipeline.serveMeteredPipelineConnConformant_head_refusal
#print axioms Reactor.DeployPipeline.serveMeteredPipelineConnConformant_head_refusal_status
