import Reactor.Deploy
import Reactor.Stage.Via
import Reactor.Stage.ProxyProtocol
import Reactor.Stage.StaleWhileRevalidate
import Reactor.Stage.CacheStatus
import Reactor.Stage.WarningTransform
import Reactor.Stage.LinkPreload
import Reactor.Stage.CrossOriginResource
import Reactor.Stage.PermissionsPolicy
import Reactor.Stage.AltSvc
import Proto.Kernel.Shortcuts

/-!
# Reactor.DeployPlus2 — the deployed metered serve EXTENDED with nine proven edge stages

Wires nine previously proven-but-unwired stages onto the EXACT
`Reactor.Deploy.deployStagesFull2` fold the running metered serve folds — by
PREPENDING them, so `deployStagesFull2` is referenced read-only and every existing
deployed proof stands. Wave 1 (the first three):

* `Reactor.Stage.Via.viaStage` (HEAD — outermost response): stamp `Via: 1.1 drorb`
  (RFC 9110 §7.6.3) unless an upstream `Via` is already present.
* `Reactor.Stage.ProxyProtocol.proxyProtoStage`: recover the real client address
  from a PROXY-protocol v1/v2 preamble at the head of the raw connection bytes and
  stamp it as `X-Forwarded-For`; pass through untouched when no preamble is present.
* `Reactor.Stage.StaleWhileRevalidate.swrStage` (innermost of the nine — sees the
  finalized `deployStagesFull2` response): stamp
  `Cache-Control: max-age=60, stale-while-revalidate=30` (RFC 5861) onto a `200`
  that carries no origin caching policy.

Wave 2 inserts three more between `viaStage` and
`proxyProtoStage` — response order innermost→outermost is
`deployStagesFull2` → swr → proxy → link → warning → cachestatus → via:

* `Reactor.Stage.LinkPreload.linkStage`: append
  `Link: </static/app.js>; rel=preload; as=script` (RFC 8288 + Preload) to a `200`
  carrying no `Link` — the producer the proven `103 Early Hints` emitter reads.
* `Reactor.Stage.WarningTransform.warningStage`: stamp
  `Warning: 214 drorb "Transformation Applied"` (RFC 7234 §5.5.3) onto a coded
  (`Content-Encoding`-bearing) response — the deployed gzip stage's transform marker.
* `Reactor.Stage.CacheStatus.csStage`: stamp the RFC 9211 `Cache-Status`
  (`drorb; hit` on a replayed response, `drorb; fwd=miss` otherwise) onto EVERY
  response, translating the proven cache stage's legacy `x-cache: HIT` indicator.

Wave 3 (this extension) prepends three more at the HEAD (outermost response —
innermost→outermost is now `deployStagesFull2` → swr → proxy → link → warning →
cachestatus → via → corp → permissions-policy → alt-svc), all append-only stamps,
so no gate proof moves:

* `Reactor.Stage.CrossOriginResource.corpStage`: stamp
  `Cross-Origin-Resource-Policy: same-origin` (WHATWG Fetch §3.5, the CORP
  embedding-isolation header) onto EVERY response lacking one.
* `Reactor.Stage.PermissionsPolicy.ppStage`: stamp
  `Permissions-Policy: geolocation=(), camera=(), microphone=(), payment=()`
  (W3C Permissions Policy, deny-all powerful features) onto EVERY response lacking one.
* `Reactor.Stage.AltSvc.altStage` (HEAD — outermost): stamp
  `Alt-Svc: h3=":443"; ma=86400` (RFC 7838, the h3 endpoint advertisement the
  dataplane's UDP bind needs to be discoverable) onto EVERY response lacking one.

The composition theorems here are stated over the REAL deployed fold (not a toy
chain), pure kernel unless flagged:

* `plus2_every_response_has_via` — EVERY response of the extended metered fold
  carries a `Via` field, for ALL peer/seq/input. Axioms ⊆ {propext, Classical.choice, Quot.sound}.
* `plus2_every_response_has_cache_status` — EVERY response of the extended metered
  fold carries a `Cache-Status` field, for ALL peer/seq/input.
  Axioms ⊆ {propext, Classical.choice, Quot.sound}.
* `plus3_every_response_has_corp` / `plus3_every_response_has_pp` /
  `plus3_every_response_has_alt` — EVERY response of the extended metered fold
  carries `Cross-Origin-Resource-Policy` / `Permissions-Policy` / `Alt-Svc`, for
  ALL peer/seq/input. Axioms ⊆ {propext, Classical.choice, Quot.sound}.
* `plus2_xff` / `plus2_xff_sample` — when the raw input carries a recoverable
  PROXY preamble, the extended fold's response carries `(X-Forwarded-For, ip)`;
  instantiated non-vacuously on the canonical on-the-wire v1 vector.
  Axioms ⊆ {propext, Classical.choice, Quot.sound}.
* `plus2_cacheControl` — on a non-preambled request whose deployed fold answers
  `200`, the extended fold's response carries a `Cache-Control`.
  Axioms ⊆ {propext, Classical.choice, Quot.sound}.
* `plus2_linkPreload` — when the inner fold (PROXY/swr/deployed) answers `200`
  with no `Link`, the extended fold's response carries one.
  Axioms ⊆ {propext, Classical.choice, Quot.sound}.
* `plus2_warning` — when the inner fold's response is coded
  (`Content-Encoding`-bearing — e.g. the deployed gzip stage fired), the extended
  fold's response carries a `Warning`. Axioms ⊆ {propext, Classical.choice, Quot.sound}.
* `plus2_staticGet_unconditional_headers` — for the exact concrete
  `GET /static/app.js` from the accepted loopback peer under the rate cap, FIVE of the
  eight `#guard` conjuncts (`Via`, `Cache-Status`, `Cross-Origin-Resource-Policy`,
  `Permissions-Policy`, `Alt-Svc`) are a real THEOREM, not a sample: each instantiates
  the corresponding for-ALL-inputs presence theorem above, so no fold reduction is
  needed. Axioms ⊆ {propext, Classical.choice, Quot.sound}.
* The remaining conjuncts are `#guard` SAMPLES, not theorems (see the section below).
  The same `GET /static/app.js` being answered `200` carrying `Cache-Control` and `Link`
  (and the `Accept-Encoding: gzip` GET being answered `200` carrying the `Warning: 214`
  transform marker) are conditional on the inner fold's `status = 200` / transform,
  whose pure-kernel discharge is blocked by the `String` request-parse loops AND the
  gzip coder — so they run as ONE closed computation over the 23-stage fold, a test,
  not assurance. They were `native_decide` theorems, which bought `Lean.ofReduceBool`
  (the compiler, kernel-external) in the axiom ledger for two samples nothing cites;
  `#guard` runs the identical computation and contributes no axiom. They keep their real
  job — showing that `plus2_cacheControl`'s `h200` and `plus2_warning`'s `htrans`
  hypotheses are satisfiable on the deployed route, i.e. that those theorems are not
  vacuous — a job a checked computation does as well as a Prop, since no proof cites them.

Export: `drorb_serve_metered_plus2` — the `drorb_serve_metered` ABI sibling over
the extended fold, behind the host lever `DRORB_PLUS2=1` (symbol and ABI unchanged
by this extension; the host crossing needs no edit). Residuals (named): the lever
path is the PLAIN metered fold — the RFC-conformance wrapper
(`Date`/`HEAD`-strip/validation) is not composed onto it here, because the
validation gate would refuse a PROXY-preambled input before the recovery stage
could read it; `cookieSecureStage` stays unwired (no deployed route produces a
`Set-Cookie` for it to harden — wiring it here would be provably inert); the
multipart range stage stays unwired (heavier request-phase integration).
-/

namespace Reactor.DeployPlus2

open Reactor.Pipeline
open Reactor (Response serialize)
open Reactor.Deploy (deployStagesFull2 appHandler ctxOfMetered)
open Reactor.Stage.Via (viaStage hasVia stampVia stampVia_prefix viaStage_effect
  viaStage_response_has_via)
open Reactor.Stage.ProxyProtocol (proxyProtoStage recoverClient xffName expectedIp
  clientKey proxyProtoStage_stamps proxyProtoStage_passthrough proxyProtoStage_no_invent
  recover_sampleV1)
open Reactor.Stage.StaleWhileRevalidate (swrStage applyCc hasCc ccName defaultCc
  applyCc_200_has swrStage_effect)
open Reactor.Stage.CacheStatus (csStage hasCS stampCS stampCS_prefix csStage_effect
  csStage_response_has_cs)
open Reactor.Stage.WarningTransform (warningStage hasWarning isTransformed stampWarn
  stampWarn_prefix stampWarn_marks_transform warningStage_effect)
open Reactor.Stage.LinkPreload (linkStage hasLink stampLink stampLink_prefix
  stampLink_has linkStage_effect)
open Reactor.Stage.CrossOriginResource (corpStage hasCorp stampCorp stampCorp_prefix
  corpStage_effect corpStage_response_has_corp)
open Reactor.Stage.PermissionsPolicy (ppStage hasPP stampPP stampPP_prefix
  ppStage_effect ppStage_response_has_pp)
open Reactor.Stage.AltSvc (altStage hasAlt stampAlt stampAlt_prefix
  altStage_effect altStage_response_has_alt)

/-- **The extended deployed chain.** The nine proven edge stages prepended to the
exact `deployStagesFull2` fold the running metered serve folds. Head placement ⇒
their `onResponse` runs OUTERMOST (after every inner rewrite): `altStage` last,
then `ppStage`, `corpStage`, `viaStage`, `csStage`, `warningStage`, `linkStage`,
`proxyProtoStage`, `swrStage`; none of
the nine gates, so every deployed gate proof (401/403/404/429/…) is untouched inner
behaviour. -/
def deployStagesPlus2 : List Stage :=
  [altStage, ppStage, corpStage, viaStage, csStage, warningStage, linkStage,
    proxyProtoStage, swrStage]
    ++ deployStagesFull2

/-- The built response of the extended METERED fold — the connection-aware
peer/seq context the dataplane threads in. -/
def deployRespPlus2Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Response :=
  (runPipeline deployStagesPlus2 appHandler (ctxOfMetered clientIp connSeq input)).build

/-- The extended metered serve as wire bytes — the `servePipelineFull2Metered`
sibling with the nine edges. This is what the `drorb_serve_metered_plus2` export
folds. -/
def servePipelinePlus2Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Proto.Bytes :=
  serialize (deployRespPlus2Metered clientIp connSeq input)

/-! ## The inner response and the stamp-composition spine (pure kernel) -/

/-- The finalized INNER response at the point the seven outer stamps see it: the
wave-1 `proxyProtoStage :: swrStage` pair over the deployed fold. -/
def innerResp (clientIp : Proto.Bytes) (connSeq : Nat) (input : Proto.Bytes) : Response :=
  (runPipeline (proxyProtoStage :: swrStage :: deployStagesFull2) appHandler
    (ctxOfMetered clientIp connSeq input)).build

/-- Boolean `any` survives extension to any list it is a prefix of. -/
theorem any_of_prefix {α : Type} (p : α → Bool) {l l' : List α}
    (hpre : l <+: l') (h : l.any p = true) : l'.any p = true := by
  obtain ⟨t, ht⟩ := hpre
  rw [← ht, List.any_append, h, Bool.true_or]

/-- Membership survives extension to any list it is a prefix of. -/
theorem mem_of_prefix {α : Type} {x : α} {l l' : List α}
    (hpre : l <+: l') (h : x ∈ l) : x ∈ l' := by
  obtain ⟨t, ht⟩ := hpre
  rw [← ht]
  exact List.mem_append_left t h

/-- **The composition spine.** The extended fold's finalized headers are EXACTLY the
seven outer stamps (link, warning, cache-status, via, corp, permissions-policy,
alt-svc — applied inside-out) over the
inner response's headers. Every presence theorem below rides on this equation. -/
theorem plus2_headers_eq (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) :
    (deployRespPlus2Metered clientIp connSeq input).headers
      = stampAlt (stampPP (stampCorp (stampVia (stampCS (stampWarn (stampLink
          (innerResp clientIp connSeq input).status
          (innerResp clientIp connSeq input).headers)))))) := by
  show ((runPipeline (altStage :: ppStage :: corpStage :: viaStage :: csStage
      :: warningStage :: linkStage
      :: proxyProtoStage :: swrStage :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers = _
  rw [altStage_effect, ppStage_effect, corpStage_effect, viaStage_effect,
    csStage_effect, warningStage_effect, linkStage_effect]
  rfl

/-- The inner headers are a prefix of the extended fold's headers — all seven outer
stamps are append-only, composed. -/
theorem innerResp_prefix (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) :
    (innerResp clientIp connSeq input).headers
      <+: (deployRespPlus2Metered clientIp connSeq input).headers := by
  rw [plus2_headers_eq]
  exact ((((((stampLink_prefix _ _).trans (stampWarn_prefix _)).trans
    (stampCS_prefix _)).trans (stampVia_prefix _)).trans
    (stampCorp_prefix _)).trans (stampPP_prefix _)).trans (stampAlt_prefix _)

/-! ## Via over the whole deployed fold (pure kernel) -/

/-- **Every response of the extended metered fold carries a `Via`** — for ALL
peer/seq/input, the RFC 9110 §7.6.3 intermediary obligation over the REAL deployed
fold (the three wave-3 stamps outside it only APPEND). -/
theorem plus2_every_response_has_via (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) :
    hasVia (deployRespPlus2Metered clientIp connSeq input).headers = true := by
  have hv : hasVia ((runPipeline (viaStage :: csStage :: warningStage :: linkStage
      :: proxyProtoStage :: swrStage :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers = true :=
    viaStage_response_has_via (csStage :: warningStage :: linkStage :: proxyProtoStage
      :: swrStage :: deployStagesFull2) appHandler (ctxOfMetered clientIp connSeq input)
  show hasVia ((runPipeline (altStage :: ppStage :: corpStage :: viaStage :: csStage
      :: warningStage :: linkStage :: proxyProtoStage :: swrStage
      :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers = true
  rw [altStage_effect, ppStage_effect, corpStage_effect]
  unfold Reactor.Stage.Via.hasVia at hv ⊢
  exact any_of_prefix _ (((stampCorp_prefix _).trans (stampPP_prefix _)).trans
    (stampAlt_prefix _)) hv

/-! ## Cache-Status over the whole deployed fold (pure kernel) -/

/-- **Every response of the extended metered fold carries a `Cache-Status`** — for
ALL peer/seq/input, the RFC 9211 handled-by-this-cache signal over the REAL deployed
fold (the four stamps outside it only APPEND). -/
theorem plus2_every_response_has_cache_status (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) :
    hasCS (deployRespPlus2Metered clientIp connSeq input).headers = true := by
  have hcs : hasCS ((runPipeline (csStage :: warningStage :: linkStage
      :: proxyProtoStage :: swrStage :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers = true :=
    csStage_response_has_cs _ appHandler (ctxOfMetered clientIp connSeq input)
  show hasCS ((runPipeline (altStage :: ppStage :: corpStage :: viaStage :: csStage
      :: warningStage :: linkStage :: proxyProtoStage :: swrStage
      :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers = true
  rw [altStage_effect, ppStage_effect, corpStage_effect, viaStage_effect]
  unfold Reactor.Stage.CacheStatus.hasCS at hcs ⊢
  exact any_of_prefix _ ((((stampVia_prefix _).trans (stampCorp_prefix _)).trans
    (stampPP_prefix _)).trans (stampAlt_prefix _)) hcs

/-! ## The wave-3 headers over the whole deployed fold (pure kernel) -/

/-- **Every response of the extended metered fold carries a
`Cross-Origin-Resource-Policy`** — for ALL peer/seq/input, the WHATWG Fetch CORP
embedding-isolation obligation over the REAL deployed fold (the two stamps outside
it only APPEND). -/
theorem plus3_every_response_has_corp (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) :
    hasCorp (deployRespPlus2Metered clientIp connSeq input).headers = true := by
  have hc : hasCorp ((runPipeline (corpStage :: viaStage :: csStage :: warningStage
      :: linkStage :: proxyProtoStage :: swrStage :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers = true :=
    corpStage_response_has_corp _ appHandler (ctxOfMetered clientIp connSeq input)
  show hasCorp ((runPipeline (altStage :: ppStage :: corpStage :: viaStage :: csStage
      :: warningStage :: linkStage :: proxyProtoStage :: swrStage
      :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers = true
  rw [altStage_effect, ppStage_effect]
  unfold Reactor.Stage.CrossOriginResource.hasCorp at hc ⊢
  exact any_of_prefix _ ((stampPP_prefix _).trans (stampAlt_prefix _)) hc

/-- **Every response of the extended metered fold carries a `Permissions-Policy`**
— for ALL peer/seq/input, the W3C deny-all powerful-feature posture over the REAL
deployed fold (the `altStage` outside it only APPENDS). -/
theorem plus3_every_response_has_pp (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) :
    hasPP (deployRespPlus2Metered clientIp connSeq input).headers = true := by
  have hp : hasPP ((runPipeline (ppStage :: corpStage :: viaStage :: csStage
      :: warningStage :: linkStage :: proxyProtoStage :: swrStage
      :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers = true :=
    ppStage_response_has_pp _ appHandler (ctxOfMetered clientIp connSeq input)
  show hasPP ((runPipeline (altStage :: ppStage :: corpStage :: viaStage :: csStage
      :: warningStage :: linkStage :: proxyProtoStage :: swrStage
      :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers = true
  rw [altStage_effect]
  unfold Reactor.Stage.PermissionsPolicy.hasPP at hp ⊢
  exact any_of_prefix _ (stampAlt_prefix _) hp

/-- **Every response of the extended metered fold carries an `Alt-Svc`** — for ALL
peer/seq/input, the RFC 7838 h3-endpoint advertisement over the REAL deployed fold
(`altStage` is the outermost stamp). -/
theorem plus3_every_response_has_alt (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) :
    hasAlt (deployRespPlus2Metered clientIp connSeq input).headers = true :=
  altStage_response_has_alt (ppStage :: corpStage :: viaStage :: csStage
    :: warningStage :: linkStage :: proxyProtoStage :: swrStage
    :: deployStagesFull2) appHandler (ctxOfMetered clientIp connSeq input)

/-! ## PROXY-protocol client recovery over the deployed fold (pure kernel) -/

/-- **The recovered client reaches the wire through the whole extended fold.** When
the raw connection bytes carry a PROXY preamble recovering `ip`, the extended
metered fold's response carries `(X-Forwarded-For, ip)` — through the deployed
stages and the four append-only outer stamps. -/
theorem plus2_xff (clientIp : Proto.Bytes) (connSeq : Nat) (input ip : Proto.Bytes)
    (hrec : recoverClient input = some ip) :
    (xffName, ip) ∈ (deployRespPlus2Metered clientIp connSeq input).headers := by
  have hrec' : recoverClient (ctxOfMetered clientIp connSeq input).input = some ip := hrec
  have hinner : (xffName, ip) ∈ (innerResp clientIp connSeq input).headers :=
    proxyProtoStage_stamps (swrStage :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input) ip hrec'
  exact mem_of_prefix (innerResp_prefix clientIp connSeq input) hinner

/-- Non-vacuous instantiation: the canonical on-the-wire PROXY v1 vector
(`PROXY TCP4 192.168.1.1 10.0.0.1 12345 80\r\n`) recovers `192.168.1.1` onto the
extended fold's response — for ANY peer/seq. -/
theorem plus2_xff_sample (clientIp : Proto.Bytes) (connSeq : Nat) :
    (xffName, expectedIp)
      ∈ (deployRespPlus2Metered clientIp connSeq Proxy.ProxyProtocol.sampleV1).headers :=
  plus2_xff clientIp connSeq _ _ recover_sampleV1

/-! ## Stale-while-revalidate over the deployed `200` (pure kernel) -/

/-- **The deployed `200` gains a caching policy.** On a request with no PROXY
preamble whose deployed `deployStagesFull2` fold answers `200`, the extended fold's
response carries a `Cache-Control` (the RFC 5861 stale-while-revalidate window) —
`swrStage` stamps it on the finalized inner response; `proxyProtoStage` (nothing
stashed) and the four outer stamps (append-only) preserve it outward. -/
theorem plus2_cacheControl (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes)
    (hrec : recoverClient input = none)
    (h200 : ((runPipeline deployStagesFull2 appHandler
        (ctxOfMetered clientIp connSeq input)).build).status = 200) :
    hasCc (deployRespPlus2Metered clientIp connSeq input).headers = true := by
  -- the swr layer stamps onto the finalized deployed response …
  have hcc1 : hasCc ((runPipeline (swrStage :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers = true := by
    rw [swrStage_effect]
    exact applyCc_200_has _ h200
  -- … the PROXY stage is the identity on both phases (no preamble, nothing stashed) …
  have hrec' : recoverClient (ctxOfMetered clientIp connSeq input).input = none := hrec
  have hreq : proxyProtoStage.onRequest (ctxOfMetered clientIp connSeq input)
      = .continue (ctxOfMetered clientIp connSeq input) :=
    proxyProtoStage_passthrough _ hrec'
  have hk1 : (Reactor.Stage.IpFilter.clientIpKey == clientKey) = false := by decide
  have hk2 : (Reactor.Stage.Rate.seqKey == clientKey) = false := by decide
  have hfind : (ctxOfMetered clientIp connSeq input).attrs.find?
      (fun p => p.1 == clientKey) = none :=
    Reactor.Deploy.ctxOfMetered_find_none clientIp connSeq input clientKey hk1 hk2
  have hpp : runPipeline (proxyProtoStage :: swrStage :: deployStagesFull2) appHandler
        (ctxOfMetered clientIp connSeq input)
      = runPipeline (swrStage :: deployStagesFull2) appHandler
        (ctxOfMetered clientIp connSeq input) := by
    rw [pipeline_stage_effect proxyProtoStage (swrStage :: deployStagesFull2) appHandler
        (ctxOfMetered clientIp connSeq input) (ctxOfMetered clientIp connSeq input) hreq]
    exact proxyProtoStage_no_invent _ _ hfind
  -- … so the inner response carries it, and the outer stamps only APPEND.
  have hccInner : hasCc (innerResp clientIp connSeq input).headers = true := by
    show hasCc ((runPipeline (proxyProtoStage :: swrStage :: deployStagesFull2)
        appHandler (ctxOfMetered clientIp connSeq input)).build).headers = true
    rw [hpp]
    exact hcc1
  unfold Reactor.Stage.StaleWhileRevalidate.hasCc at hccInner ⊢
  exact any_of_prefix _ (innerResp_prefix clientIp connSeq input) hccInner

/-! ## Link preload over the deployed `200` (pure kernel) -/

/-- **The deployed `200` advertises the critical asset.** When the inner fold
answers `200` carrying no `Link`, the extended fold's response carries one (the
RFC 8288 `rel=preload` producer the proven 103 emitter reads) — `linkStage` stamps
it; the six stamps above it (append-only) preserve it outward. -/
theorem plus2_linkPreload (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes)
    (h200 : (innerResp clientIp connSeq input).status = 200)
    (hnolink : hasLink (innerResp clientIp connSeq input).headers = false) :
    hasLink (deployRespPlus2Metered clientIp connSeq input).headers = true := by
  rw [plus2_headers_eq, h200]
  have h1 : hasLink (stampLink 200 (innerResp clientIp connSeq input).headers) = true :=
    stampLink_has _ hnolink
  unfold Reactor.Stage.LinkPreload.hasLink at h1 ⊢
  exact any_of_prefix _ ((((((stampWarn_prefix _).trans (stampCS_prefix _)).trans
    (stampVia_prefix _)).trans (stampCorp_prefix _)).trans
    (stampPP_prefix _)).trans (stampAlt_prefix _)) h1

/-! ## Transform warning over the deployed coded response (pure kernel) -/

/-- **The deployed coded response is marked.** When the inner fold's response
carries a `Content-Encoding` (the deployed gzip stage fired), the extended fold's
response carries a `Warning` (the RFC 7234 §5.5.3 `214 Transformation Applied`
marker) — `linkStage` below it only appends, `warningStage` stamps, and the five
stamps above it only append. -/
theorem plus2_warning (clientIp : Proto.Bytes) (connSeq : Nat) (input : Proto.Bytes)
    (htrans : isTransformed (innerResp clientIp connSeq input).headers = true) :
    hasWarning (deployRespPlus2Metered clientIp connSeq input).headers = true := by
  rw [plus2_headers_eq]
  have h1 : isTransformed (stampLink (innerResp clientIp connSeq input).status
      (innerResp clientIp connSeq input).headers) = true := by
    unfold Reactor.Stage.WarningTransform.isTransformed at htrans ⊢
    exact any_of_prefix _ (stampLink_prefix _ _) htrans
  have h2 : hasWarning (stampWarn (stampLink (innerResp clientIp connSeq input).status
      (innerResp clientIp connSeq input).headers)) = true :=
    stampWarn_marks_transform _ h1
  unfold Reactor.Stage.WarningTransform.hasWarning at h2 ⊢
  exact any_of_prefix _ (((((stampCS_prefix _).trans (stampVia_prefix _)).trans
    (stampCorp_prefix _)).trans (stampPP_prefix _)).trans (stampAlt_prefix _)) h2

/-! ## Status transparency of the edge extension (pure kernel)

The presence theorems above prove the nine edges only ADD headers; these prove they
never move the served STATUS. That upgrades the file-header claim "every deployed gate
proof (401/403/404/429/…) is untouched inner behaviour" from prose into a theorem: the
extended fold's status is provably the inner fold's status, and (with no PROXY preamble)
the exact `deployStagesFull2` status the gate proofs are stated over. -/

/-- One status-stable, request-transparent edge peels off the fold without moving the
built status. The shared step of `plus2_status_eq`. -/
theorem edge_peel_status (s : Stage) (rest : List Stage) (c : Ctx)
    (hreq : s.onRequest c = .continue c) (hst : s.statusStable) :
    ((runPipeline (s :: rest) appHandler c).build).status
      = ((runPipeline rest appHandler c).build).status := by
  rw [pipeline_stage_effect s rest appHandler c c hreq]
  exact hst c (runPipeline rest appHandler c)

/-- **The nine edges never change the served status.** For ALL peer/seq/input, the
extended metered fold's status is EXACTLY the inner response's status — the seven outer
stamps (`altStage … linkStage`) each `.continue` the request untouched and their
`onResponse` is status-stable (headers only), so no gate verdict the inner fold reached
is disturbed. -/
theorem plus2_status_eq (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) :
    (deployRespPlus2Metered clientIp connSeq input).status
      = (innerResp clientIp connSeq input).status := by
  show ((runPipeline (altStage :: ppStage :: corpStage :: viaStage :: csStage
      :: warningStage :: linkStage :: proxyProtoStage :: swrStage
      :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).status = _
  rw [edge_peel_status altStage _ _ rfl Reactor.Stage.AltSvc.altStage_statusStable,
      edge_peel_status ppStage _ _ rfl Reactor.Stage.PermissionsPolicy.ppStage_statusStable,
      edge_peel_status corpStage _ _ rfl
        Reactor.Stage.CrossOriginResource.corpStage_statusStable,
      edge_peel_status viaStage _ _ rfl Reactor.Stage.Via.viaStage_statusStable,
      edge_peel_status csStage _ _ rfl Reactor.Stage.CacheStatus.csStage_statusStable,
      edge_peel_status warningStage _ _ rfl
        Reactor.Stage.WarningTransform.warningStage_statusStable,
      edge_peel_status linkStage _ _ rfl Reactor.Stage.LinkPreload.linkStage_statusStable]
  rfl

/-- **With no PROXY preamble, the inner response's status is the deployed fold's status.**
The wave-1 `proxyProtoStage` is inert (nothing to recover, nothing stashed) and
`swrStage` is status-stable, so `innerResp` carries the exact `deployStagesFull2` status.
This is the bridge from the composition spine (stated over `innerResp`) back to the
`deployStagesFull2` fold the deployed gate proofs are stated over. -/
theorem innerResp_status_deployed (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) (hrec : recoverClient input = none) :
    (innerResp clientIp connSeq input).status
      = ((runPipeline deployStagesFull2 appHandler
          (ctxOfMetered clientIp connSeq input)).build).status := by
  have hrec' : recoverClient (ctxOfMetered clientIp connSeq input).input = none := hrec
  have hreq : proxyProtoStage.onRequest (ctxOfMetered clientIp connSeq input)
      = .continue (ctxOfMetered clientIp connSeq input) :=
    proxyProtoStage_passthrough _ hrec'
  have hk1 : (Reactor.Stage.IpFilter.clientIpKey == clientKey) = false := by decide
  have hk2 : (Reactor.Stage.Rate.seqKey == clientKey) = false := by decide
  have hfind : (ctxOfMetered clientIp connSeq input).attrs.find?
      (fun p => p.1 == clientKey) = none :=
    Reactor.Deploy.ctxOfMetered_find_none clientIp connSeq input clientKey hk1 hk2
  have hpp : runPipeline (proxyProtoStage :: swrStage :: deployStagesFull2) appHandler
        (ctxOfMetered clientIp connSeq input)
      = runPipeline (swrStage :: deployStagesFull2) appHandler
        (ctxOfMetered clientIp connSeq input) := by
    rw [pipeline_stage_effect proxyProtoStage (swrStage :: deployStagesFull2) appHandler
        (ctxOfMetered clientIp connSeq input) (ctxOfMetered clientIp connSeq input) hreq]
    exact proxyProtoStage_no_invent _ _ hfind
  show ((runPipeline (proxyProtoStage :: swrStage :: deployStagesFull2) appHandler
      (ctxOfMetered clientIp connSeq input)).build).status = _
  rw [hpp]
  exact edge_peel_status swrStage deployStagesFull2 (ctxOfMetered clientIp connSeq input)
    rfl Reactor.Stage.StaleWhileRevalidate.swrStage_statusStable

/-- **The edge extension is status-transparent on the deployed default path.** For a
request with no PROXY preamble (the deployed default — the host owns the socket, no
inner proxy prepends a v1/v2 line), the extended metered fold's status is EXACTLY the
`deployStagesFull2` fold's status. Hence every deployed gate proof (200/403/404/429/…)
stated over `deployStagesFull2` lifts verbatim to the extended fold at the status level —
not by prose, by this equation. -/
theorem plus2_status_deployed (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) (hrec : recoverClient input = none) :
    (deployRespPlus2Metered clientIp connSeq input).status
      = ((runPipeline deployStagesFull2 appHandler
          (ctxOfMetered clientIp connSeq input)).build).status := by
  rw [plus2_status_eq, innerResp_status_deployed clientIp connSeq input hrec]

/-- **The general conditional form of the whole `staticGet` `#guard`.** For ANY request
with no PROXY preamble whose `deployStagesFull2` fold answers `200` carrying no `Link`,
the extended metered fold's response provably carries ALL EIGHT of the conjuncts the
`staticGet` sample checks: status `200`, `Cache-Control`, `Link`, `Via`, `Cache-Status`,
`Cross-Origin-Resource-Policy`, `Permissions-Policy` and `Alt-Svc`. This is the ∀-theorem
the `staticGet` `#guard` only sampled; the sample now witnesses only that its three
hypotheses are inhabited (they are — by the deployed static GET route). Its `hrec`
hypothesis is discharged for the concrete `staticGet` by `staticGet_no_preamble` below; the
RESIDUAL is exactly the remaining two hypotheses (`h200`, `hnolink`) on the concrete
`staticGet` bytes, which need the request-parse + fold reduction characterized below. Non-vacuous: the hypotheses are
satisfiable on the deployed route (the `staticGet` `#guard` is their witness). -/
theorem plus2_clean_static_full_edges (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) (hrec : recoverClient input = none)
    (h200 : ((runPipeline deployStagesFull2 appHandler
        (ctxOfMetered clientIp connSeq input)).build).status = 200)
    (hnolink : hasLink (innerResp clientIp connSeq input).headers = false) :
    (deployRespPlus2Metered clientIp connSeq input).status = 200
    ∧ hasCc (deployRespPlus2Metered clientIp connSeq input).headers = true
    ∧ hasLink (deployRespPlus2Metered clientIp connSeq input).headers = true
    ∧ hasVia (deployRespPlus2Metered clientIp connSeq input).headers = true
    ∧ hasCS (deployRespPlus2Metered clientIp connSeq input).headers = true
    ∧ hasCorp (deployRespPlus2Metered clientIp connSeq input).headers = true
    ∧ hasPP (deployRespPlus2Metered clientIp connSeq input).headers = true
    ∧ hasAlt (deployRespPlus2Metered clientIp connSeq input).headers = true := by
  have hstatus : (deployRespPlus2Metered clientIp connSeq input).status = 200 := by
    rw [plus2_status_deployed clientIp connSeq input hrec]; exact h200
  have h200i : (innerResp clientIp connSeq input).status = 200 := by
    rw [innerResp_status_deployed clientIp connSeq input hrec]; exact h200
  exact ⟨hstatus,
    plus2_cacheControl clientIp connSeq input hrec h200,
    plus2_linkPreload clientIp connSeq input h200i hnolink,
    plus2_every_response_has_via clientIp connSeq input,
    plus2_every_response_has_cache_status clientIp connSeq input,
    plus3_every_response_has_corp clientIp connSeq input,
    plus3_every_response_has_pp clientIp connSeq input,
    plus3_every_response_has_alt clientIp connSeq input⟩


/-! ## Concrete deployed witnesses (`#guard` samples)

These check ONE deployed request each. A pure-kernel discharge is blocked twice over:
the well-founded `String` worker loops in the request parse (`Proto.Kernel.Shortcuts`
§3 is the step kit that would evict them), and the gzip coder in the fold, which the
kernel will not reduce at any tolerable cost. So the computation runs under the
compiler either way — `#guard` (via `evalExpr`) and `native_decide` use the SAME
evaluator. The difference is honesty, not machinery: `#guard` is a test and admits it,
where `native_decide` dressed the same sample as a theorem and charged the axiom
ledger `Lean.ofReduceBool` for it.

The REAL obligation these never discharged: a general statement, quantified over the
request, that the wired stages fire on every accepted in-cap static route. The
`plus2_*` theorems above are the general facts; these samples only witness that their
hypotheses are inhabited. -/

/-- The loopback peer `127.0.0.1`, family-tagged bit-encoded exactly as the native
host's accept path encodes it (family byte `4`, then one byte per address bit,
MSB-first per octet). -/
def loopbackPeer : Proto.Bytes :=
  4 :: ([0,1,1,1,1,1,1,1] ++ [0,0,0,0,0,0,0,0] ++ [0,0,0,0,0,0,0,0] ++ [0,0,0,0,0,0,0,1]
    : List UInt8)

/-- A concrete deployed request: `GET /static/app.js` with a `Host`. -/
def staticGet : Proto.Bytes :=
  "GET /static/app.js HTTP/1.1\r\nHost: h\r\n\r\n".toUTF8.toList

/-- The same GET advertising gzip: `Accept-Encoding: gzip`. -/
def gzipGet : Proto.Bytes :=
  "GET /static/app.js HTTP/1.1\r\nHost: h\r\nAccept-Encoding: gzip\r\n\r\n".toUTF8.toList

/-- **The concrete `staticGet` carries no PROXY preamble** — `recoverClient staticGet =
none`, in the pure kernel. This discharges the `hrec` hypothesis of
`plus2_clean_static_full_edges` for the concrete deployed static GET: the PROXY v1/v2
recogniser (`parseHeader`/`parseV1`/`parseV2`, all structural byte ops) reduces on the
concrete bytes once the `toUTF8`-derived byte list is put in structural form via
`Proto.Kernel.Shortcuts.toUTF8_toList` (the §1 `ByteArray.toList` bridge). The remaining
two hypotheses (the `deployStagesFull2` `200` and the no-inner-`Link`) still reduce only
through the HTTP request parser + fold — the parser-reduction residual. Axioms ⊆
{propext, Quot.sound}. -/
theorem staticGet_no_preamble : recoverClient staticGet = none := by
  rw [staticGet, Proto.Kernel.Shortcuts.toUTF8_toList]
  decide

/- SAMPLE: the wired stages FIRE on the deployed route. The concrete static GET from
an accepted loopback peer under the rate cap (seq 0) is answered `200` through the full
extended fold, carrying the stamped `Cache-Control`, `Via`, `Cache-Status`, `Link`,
`Cross-Origin-Resource-Policy`, `Permissions-Policy` AND `Alt-Svc`. Also witnesses that
`plus2_cacheControl`'s `h200` and `plus2_linkPreload`'s hypotheses are satisfiable on
the deployed route. -/
#guard (deployRespPlus2Metered loopbackPeer 0 staticGet).status == 200
      && hasCc (deployRespPlus2Metered loopbackPeer 0 staticGet).headers
      && hasVia (deployRespPlus2Metered loopbackPeer 0 staticGet).headers
      && hasCS (deployRespPlus2Metered loopbackPeer 0 staticGet).headers
      && hasLink (deployRespPlus2Metered loopbackPeer 0 staticGet).headers
      && hasCorp (deployRespPlus2Metered loopbackPeer 0 staticGet).headers
      && hasPP (deployRespPlus2Metered loopbackPeer 0 staticGet).headers
      && hasAlt (deployRespPlus2Metered loopbackPeer 0 staticGet).headers

/- SAMPLE: the transform marker FIRES on the deployed gzip route. The gzip-advertising
GET is answered `200` whose extended-fold response carries the `Warning` transform
marker — the deployed gzip stage coded the body and the wave-2 marker saw its
`Content-Encoding`. Also witnesses that `plus2_warning`'s `htrans` hypothesis is
satisfiable on the deployed route. -/
#guard (deployRespPlus2Metered loopbackPeer 0 gzipGet).status == 200
      && hasWarning (deployRespPlus2Metered loopbackPeer 0 gzipGet).headers

/-- **Five of the deployed static GET's wired headers are UNCONDITIONAL theorems, not
samples.** For the exact concrete `GET /static/app.js` from the accepted loopback peer
under the rate cap (`loopbackPeer`, seq `0`), the extended fold's response provably
carries `Via`, `Cache-Status`, `Cross-Origin-Resource-Policy`, `Permissions-Policy` and
`Alt-Svc` — each an instantiation of the corresponding for-ALL-inputs presence theorem
above (`plus2_every_response_has_via` / `_cache_status`, `plus3_every_response_has_corp`
/ `_pp` / `_alt`), so no fold reduction is needed. This lifts five of the eight
conjuncts of the `staticGet` `#guard` above into a real Prop; only `status = 200`,
`Cache-Control` and `Link` stay sample-bound — those are conditional on the inner fold's
`200`, whose pure-kernel discharge is blocked by the `String` request-parse loops and
the gzip coder. Axioms ⊆ {propext, Classical.choice, Quot.sound}. -/
theorem plus2_staticGet_unconditional_headers :
    hasVia (deployRespPlus2Metered loopbackPeer 0 staticGet).headers = true
    ∧ hasCS (deployRespPlus2Metered loopbackPeer 0 staticGet).headers = true
    ∧ hasCorp (deployRespPlus2Metered loopbackPeer 0 staticGet).headers = true
    ∧ hasPP (deployRespPlus2Metered loopbackPeer 0 staticGet).headers = true
    ∧ hasAlt (deployRespPlus2Metered loopbackPeer 0 staticGet).headers = true :=
  ⟨plus2_every_response_has_via loopbackPeer 0 staticGet,
   plus2_every_response_has_cache_status loopbackPeer 0 staticGet,
   plus3_every_response_has_corp loopbackPeer 0 staticGet,
   plus3_every_response_has_pp loopbackPeer 0 staticGet,
   plus3_every_response_has_alt loopbackPeer 0 staticGet⟩

/-! ## The export -/

/-- **The extended metered serve seam** (`drorb_serve_metered_plus2`). The
`drorb_serve_metered` ABI sibling over `deployStagesPlus2`: the host supplies the
accepted peer (family-tagged bit-encoded) and the per-connection request index, and
the extended fold serves. RETIRED experimental seam — the `@[export]` was removed in the consolidation, so this def is no longer a host crossing; it is retained only for the byte-identity derivation chain. The single deployed default is `drorb_serve_pipeline_conformant`. -/
def drorbServeMeteredPlus2 (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  ByteArray.mk (servePipelinePlus2Metered peer.toList seq.toNat input.toList).toArray

/-- What the export folds is definitionally the extended pipeline (totality: a
plain `def`). -/
theorem drorbServeMeteredPlus2_serves (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    drorbServeMeteredPlus2 peer seq input
      = ByteArray.mk (servePipelinePlus2Metered peer.toList seq.toNat input.toList).toArray := rfl

#print axioms plus2_headers_eq
#print axioms plus2_every_response_has_via
#print axioms plus2_every_response_has_cache_status
#print axioms plus3_every_response_has_corp
#print axioms plus3_every_response_has_pp
#print axioms plus3_every_response_has_alt
#print axioms plus2_xff
#print axioms plus2_xff_sample
#print axioms plus2_cacheControl
#print axioms plus2_linkPreload
#print axioms plus2_warning
#print axioms plus2_staticGet_unconditional_headers
#print axioms edge_peel_status
#print axioms plus2_status_eq
#print axioms innerResp_status_deployed
#print axioms plus2_status_deployed
#print axioms plus2_clean_static_full_edges
#print axioms staticGet_no_preamble
#print axioms drorbServeMeteredPlus2_serves

end Reactor.DeployPlus2
