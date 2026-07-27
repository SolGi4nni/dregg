import Datapath.DenseHead
import Datapath.ServeDenseFullReal
import Datapath.ServeFlatFull

/-!
# Datapath.ServeDenseReal — the RUNTIME-DENSE full serve on `/bulk`, assembled

This is the **culmination** of the dense-head + dense-body linchpins: a single
`ByteArray → ByteArray` serve that, on the deployed `/bulk` (1 MiB) route, produces
the deployed response bytes WITHOUT ever materialising the 1 MiB body as a
`List UInt8` cons-spine — the fix for the deployed `/bulk` body-cliff (the 1 MiB
`List` body the deployed serve conses at `respOf`/`serialize`).

## What is assembled

`serveDenseReal` forks exactly as the deployed serve (`deployedServeRef` =
`Dataplane.drorbServe`): the h2c preface to the real H2 engine, else the HTTP/1.1
path. On the H1 path it decides — by a **decidable** guard `BulkArm` evaluated on the
small request — whether this is a plain `GET /bulk` on the admitted, non-gzip,
non-CORS arm:

* **on the `/bulk` arm** it emits the DENSE head (`Datapath.DenseHead.renderHead`
  over the flat `HdrBlock` fold `denseHeadersBlock` — the proven HEAD linchpin, whose
  only `List` inputs are the ~7 app response headers and the request-derived
  `x-corr`/`x-upstream` scalars) followed by the DENSE body
  (`Datapath.ServeDenseFullReal.bulkBodyDense`, a bulk `Array.replicate`, no per-byte
  `cons`) — bulk-appended as `Array`s;
* **off the arm** it falls back to the deployed `servePipelineFull2` List serve,
  byte-identical by construction.

## What is PROVEN vs assumed (honest scope)

* PROVEN (this file, axioms ⊆ {propext, Quot.sound, Classical.choice}):
  `serveDenseReal input = deployedServeRef input` for EVERY input — byte-identical to
  the deployed serve. On the `/bulk` arm this is genuine: the head is the proven dense
  fold (`denseHeaders_eq_deployed`) and the body the proven dense linchpin
  (`bulkBodyDense`), the gate-pass hypotheses DISCHARGED from the decidable guard
  `BulkArm` (no `native_decide`, no assumed hypotheses — the guard IS the discharge,
  and correctness is proven from it by case analysis). `Dataplane.serveDenseReal_eq_drorbServe`
  transfers this to `drorbServe` (where it is in scope, past the import cycle).

* NOT a residual: the whole thing is total and equals `drorbServe`. The only
  "assumption" is that the runtime guard fires on the concrete request — but that is
  a decidable computation, not a proof obligation, and off-guard the serve is still
  byte-correct (it uses the deployed serve).
-/

namespace Datapath.ServeDenseReal

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx ResponseBuilder runPipeline)
open Reactor.Deploy
open Datapath.DenseHead
  (renderHead denseHeadersBlock denseHeaders_eq_deployed headBytes serialize_eq_head_body
   renderHead_eq_headBytes denseHeadersBlock_denote innerHeaders deployProg_eq
   deployProgPoly_eq_deployed)
open Datapath.ServeDenseFullReal (bulkBodyDense rewriteBytes_bulkBody)

/-! ## 1. The admitted `/bulk` arm as a DECIDABLE guard

Every conjunct is a decidable computation on the SMALL request (never the body): the
seven gate passes, gzip-off / CORS-none, and the `/bulk` route shape (target `["bulk"]`
under ANY non-vhost authority — neither `a.example` nor `b.example`, so the `anyHost`
block is selected) that fixes the app response to the 1 MiB body handler. -/

/-- **The `/bulk`-arm guard.** A decidable predicate on the pipeline context that
implies EXACTLY the hypotheses `denseHeaders_eq_deployed` / `full2_reduces` take,
plus the `/bulk` route shape (so the app response is the 1 MiB `bulkBody`). -/
def BulkArm (c : Ctx) : Prop :=
  isAdminPath c.req = false
  ∧ Reactor.Stage.BasicAuth.isProtectedPath c.req = false
  ∧ Reactor.Stage.Rate.admits c = true
  ∧ ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget)
  ∧ targetEscapes c.req = false
  ∧ policyReserved c.req = false
  ∧ Reactor.Stage.Gzip.acceptsGzip c.req = false
  ∧ _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none
  ∧ Reactor.App.targetSegments c.req.target = ["bulk"]
  ∧ Reactor.App.hostLabelsOf c.req ≠ ["a", "example"]
  ∧ Reactor.App.hostLabelsOf c.req ≠ ["b", "example"]

instance (c : Ctx) : Decidable (BulkArm c) := by
  unfold BulkArm; infer_instance

/-! ## 2. The `/bulk` app response and the built response scalars -/

/-- On the `/bulk` arm the app handler answers the 1 MiB body: `App.handle` selects
`bulkRoute` (target `["bulk"]` under any non-vhost authority), a `200` with `bulkBody`. -/
theorem appHandler_bulk (c : Ctx)
    (hseg : Reactor.App.targetSegments c.req.target = ["bulk"])
    (hna : Reactor.App.hostLabelsOf c.req ≠ ["a", "example"])
    (hnb : Reactor.App.hostLabelsOf c.req ≠ ["b", "example"]) :
    appHandler c = { status := 200, reason := Reactor.App.reasonFor 200,
                     headers := [], body := Reactor.App.bulkBody } := by
  unfold appHandler
  exact Reactor.App.bulk_serves_large_body_any c.req hseg hna hnb

/-- **The deployed built response scalars on the `/bulk` arm.** With every gate
admitting and the app response the 1 MiB body handler, the BUILT fold over
`deployStagesFull2` has `status 200`, `reason OK`, and `body = bulkBody` — the two
body-touching transforms (gzip off, html-rewrite the identity on the tagless body)
leave the body, the header transforms leave status/reason, the outer deploy rewrite
touches only headers. NO `respOf` used to state it; the body flows through by
`rewriteBytes_bulkBody`. -/
theorem builtScalars (c : Ctx)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hip : c.attrs.find? (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none)
    (hrate : Reactor.Stage.Rate.admits c = true)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hpol : policyReserved c.req = false)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false)
    (hcors : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none)
    (happ : appHandler c = { status := 200, reason := Reactor.App.reasonFor 200,
                             headers := [], body := Reactor.App.bulkBody }) :
    ((runPipeline deployStagesFull2 appHandler c).build).status = 200
    ∧ ((runPipeline deployStagesFull2 appHandler c).build).reason = Reactor.App.reasonFor 200
    ∧ ((runPipeline deployStagesFull2 appHandler c).build).body = Reactor.App.bulkBody := by
  -- the CORS/gzip stages are transparent on this arm (same peel `innerHeaders` uses)
  have hcorsResp : ∀ b : ResponseBuilder, deployCorsStage.onResponse c b = b := by
    intro b
    show (match _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) with
          | some v => b.addHeader (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
          | none   => b) = b
    rw [hcors]
  have hgzResp : ∀ b : ResponseBuilder, Reactor.Stage.Gzip.gzipStage.onResponse c b = b := by
    intro b
    show (match Reactor.Stage.Gzip.acceptsGzip c.req with
          | true  => (b.mapResp Reactor.Stage.Gzip.gzipBody).addHeader
                        (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal)
          | false => b) = b
    rw [hgz]
  -- both rewrites (`Lifecycle.rewriteResp` outer, `Header.rewriteResp` inner) touch ONLY
  -- headers: status/reason/body pass through. Proven over a VARIABLE response (cheap `rfl`,
  -- no concrete `appHandler` routing forced) — then applied by rewrite.
  have hlcS : ∀ (prog : List Header.Op) (r : Response),
      (Reactor.Lifecycle.rewriteResp prog r).status = r.status := fun _ _ => rfl
  have hlcR : ∀ (prog : List Header.Op) (r : Response),
      (Reactor.Lifecycle.rewriteResp prog r).reason = r.reason := fun _ _ => rfl
  have hlcB : ∀ (prog : List Header.Op) (r : Response),
      (Reactor.Lifecycle.rewriteResp prog r).body = r.body := fun _ _ => rfl
  have hhrB : ∀ r : Response, (Reactor.Stage.Header.rewriteResp r).body = r.body := fun _ => rfl
  have hhrS : ∀ r : Response, (Reactor.Stage.Header.rewriteResp r).status = r.status := fun _ => rfl
  have hhrR : ∀ r : Response, (Reactor.Stage.Header.rewriteResp r).reason = r.reason := fun _ => rfl
  -- reduce the full fold to the outer rewrite of the inner fold (unknown-arm reduction)
  rw [full2_reduces_unknown c hadmin hpriv hip hrate hredir htrav hpol, Reactor.Pipeline.build_mapResp]
  -- the outer deploy rewrite touches ONLY headers: status/reason/body pass through
  -- reduce the inner fold: peel cors/gzip (transparent), html (gated), then [sec,hdr]
  have hinner : (runPipeline full2InnerStages appHandler c).build
      = Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp
          ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                         Reactor.Stage.Header.headerStage] appHandler c).build) := by
    show (runPipeline (deployCorsStage :: Reactor.Stage.Gzip.gzipStage
        :: Reactor.Stage.HtmlRewrite.htmlrewriteStage
        :: Reactor.Stage.SecurityHeaders.securityheadersStage
        :: [Reactor.Stage.Header.headerStage]) appHandler c).build = _
    rw [Reactor.Deploy.prepend_pass deployCorsStage _ appHandler c rfl hcorsResp,
        Reactor.Deploy.prepend_pass Reactor.Stage.Gzip.gzipStage _ appHandler c rfl hgzResp,
        Reactor.Stage.HtmlRewrite.htmlrewriteStage_effect, Reactor.Pipeline.build_mapResp]
  -- the [security, header] build: status/reason/body come from appHandler (the header
  -- transforms touch ONLY headers). Projected targetedly so no expensive header field
  -- (`Header.run …`) is ever forced to whnf.
  -- reduce the [security, header] build to a clean structure-UPDATE (via
  -- `securityheadersStage_effect` + `build_addHeaders`), whose status/reason/body are the
  -- base's own — so each scalar projects cheaply, never forcing the `++ wireHeaders` /
  -- `Header.run` header field.
  have hmidReduce : (runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                            Reactor.Stage.Header.headerStage] appHandler c).build
      = { (runPipeline [Reactor.Stage.Header.headerStage] appHandler c).build with
          headers := ((runPipeline [Reactor.Stage.Header.headerStage] appHandler c).build).headers
            ++ Reactor.Stage.SecurityHeaders.wireHeaders Reactor.Stage.SecurityHeaders.policy } := by
    rw [Reactor.Stage.SecurityHeaders.securityheadersStage_effect [Reactor.Stage.Header.headerStage]
        appHandler c, Reactor.Pipeline.build_addHeaders]
  have hmidStatus : ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
      Reactor.Stage.Header.headerStage] appHandler c).build).status = (appHandler c).status := by
    rw [hmidReduce]
    show ((runPipeline [Reactor.Stage.Header.headerStage] appHandler c).build).status
      = (appHandler c).status
    rw [Reactor.Stage.Header.headerStage_effect, hhrS,
        show (runPipeline [] appHandler c).build = appHandler c from rfl]
  have hmidReason : ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
      Reactor.Stage.Header.headerStage] appHandler c).build).reason = (appHandler c).reason := by
    rw [hmidReduce]
    show ((runPipeline [Reactor.Stage.Header.headerStage] appHandler c).build).reason
      = (appHandler c).reason
    rw [Reactor.Stage.Header.headerStage_effect, hhrR,
        show (runPipeline [] appHandler c).build = appHandler c from rfl]
  have hmidBody : ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
      Reactor.Stage.Header.headerStage] appHandler c).build).body = (appHandler c).body := by
    rw [hmidReduce]
    show ((runPipeline [Reactor.Stage.Header.headerStage] appHandler c).build).body
      = (appHandler c).body
    rw [Reactor.Stage.Header.headerStage_effect, hhrB,
        show (runPipeline [] appHandler c).build = appHandler c from rfl]
  -- the outer deploy rewrite touches ONLY headers: status/reason/body pass through it
  -- (rewriteResp = `{r with headers := …}`), so each scalar is the inner fold's own.
  have hreason : ∀ r : Response,
      (Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp r).reason = r.reason := by
    intro r
    unfold Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp Reactor.Stage.HtmlRewrite.htmlTransformResp
    cases Reactor.Stage.HtmlRewrite.isHtmlCT r.headers <;> rfl
  -- assemble the three scalars (strip the outer `rewriteResp` via the variable-lemmas)
  refine ⟨?_, ?_, ?_⟩
  · -- status
    rw [hlcS, hinner, Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp_status, hmidStatus, happ]
  · -- reason
    rw [hlcR, hinner, hreason, hmidReason, happ]
  · -- body: either html branch keeps bulkBody (rewriteBytes_bulkBody)
    rw [hlcB, hinner, Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp_body, hmidBody, happ]
    split
    · exact rewriteBytes_bulkBody
    · rfl

/-- **The HEAD linchpin on the UNKNOWN, non-reserved arm.** The `Datapath.DenseHead`
ground theorem `denseHeaders_eq_deployed` is stated for a positively-admitted surface
(`deployDecisionOf = some s`); a plain `GET /bulk` is instead undeclared-but-safe
(`deployDecisionOf = none`, `policyReserved = false`), served by the app route table. This
reproves the SAME dense-head byte-identity via `full2_reduces_unknown` — every ground
piece (`innerHeaders`, `deployProg_eq`, `denseHeadersBlock_denote`,
`deployProgPoly_eq_deployed`) is reused unchanged; only the policy-gate pass differs. -/
theorem denseHeadersUnknown (c : Ctx)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hip : c.attrs.find? (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none)
    (hrate : Reactor.Stage.Rate.admits c = true)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hpol : policyReserved c.req = false)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false)
    (hcors : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none) :
    (denseHeadersBlock (appHandler c).headers
        (upstreamVal (deployPlan (deploySubs c.input))) (corrVal c.input)).denote
      = ((runPipeline deployStagesFull2 appHandler c).build).headers := by
  rw [full2_reduces_unknown c hadmin hpriv hip hrate hredir htrav hpol,
    Reactor.Pipeline.build_mapResp]
  show _ = (Reactor.Lifecycle.rewriteResp
      (deployProg (deployPlan (deploySubs c.input)) c.input)
      ((runPipeline full2InnerStages appHandler c).build)).headers
  show _ = Reactor.Lifecycle.ofHeaders (Header.run
      (deployProg (deployPlan (deploySubs c.input)) c.input)
      (Reactor.Lifecycle.toHeaders ((runPipeline full2InnerStages appHandler c).build).headers))
  rw [innerHeaders c hgz hcors, deployProg_eq,
    denseHeadersBlock_denote, deployProgPoly_eq_deployed]

/-! ## 3. The dense head bytes and the assembled serve -/

/-- The DENSE `/bulk` head bytes: the head rendered over the flat `HdrBlock` header
fold from the SMALL app headers (`[]`) and the request-derived `x-upstream`/`x-corr`
scalars — status `200`, reason `OK`, body-length `bulkSize` (never the body bytes). -/
def denseHeadBytes (input : Bytes) : Bytes :=
  renderHead 200 (Reactor.App.reasonFor 200)
    (denseHeadersBlock [] (upstreamVal (deployPlan (deploySubs input))) (corrVal input)).denote
    Reactor.App.bulkSize

/-- **The runtime-dense full serve.** Forks exactly as the deployed serve; on the
`/bulk` arm emits the dense head followed by the dense 1 MiB `Array` body
(bulk-appended, NO per-byte `cons` — the body-cliff fix), else the deployed serve. -/
@[export drorb_serve_dense_real]
def serveDenseReal (input : ByteArray) : ByteArray :=
  if Reactor.Ingress.hasH2Preface input.toList then
    ByteArray.mk (Reactor.H2Ingress.serveH2c input.toList).toArray
  else if BulkArm (ctxOf input.toList) then
    -- ByteArray `++` = `ByteArray.append` = `copySlice` (native memcpy) onto the cached
    -- unboxed 1 MiB `bulkBodyDense` — NOT `Array UInt8 ++` (which would box every byte).
    ByteArray.mk (denseHeadBytes input.toList).toArray ++ bulkBodyDense
  else
    ByteArray.mk (servePipelineFull2 input.toList).toArray

/-! ## 4. Byte-identity to the deployed serve -/

/-- Bulk-append the dense body `Array` onto the head `Array` = the flat `ByteArray`
of the head list appended with `bulkBody` — no 1 MiB `List` is ever consed. -/
theorem denseOut_eq (head : Bytes) :
    ByteArray.mk head.toArray ++ bulkBodyDense
      = ByteArray.mk (head ++ Reactor.App.bulkBody).toArray := by
  -- `ByteArray.append`'s underlying array is the packed concat (no boxing).
  -- Proven over ABSTRACT operands (as `Datapath.ByteSeq`), so nothing here evaluates the
  -- concrete 1 MiB `bulkBodyDense` size.
  have hda_gen : ∀ a b : ByteArray, (a ++ b).data = a.data ++ b.data := fun a b => by
    show (ByteArray.append a b).data = a.data ++ b.data
    apply Array.toList_inj.mp
    rw [ByteArray.toList_data_append', Array.toList_append]
  have hda : (ByteArray.mk head.toArray ++ bulkBodyDense).data
      = head.toArray ++ bulkBodyDense.data := hda_gen (ByteArray.mk head.toArray) bulkBodyDense
  -- the packed concat equals the deployed `(head ++ bulkBody).toArray` (Array level)
  have harr : head.toArray ++ bulkBodyDense.data = (head ++ Reactor.App.bulkBody).toArray := by
    apply Array.toList_inj.mp
    rw [Array.toList_append, List.toList_toArray, List.toList_toArray]
    show head.toArray.toList ++ bulkBodyDense.data.toList = head ++ Reactor.App.bulkBody
    rw [List.toList_toArray, Datapath.ServeDenseFullReal.bulkBodyDense_toList]
  -- close by structure eta on `ByteArray` (a single-field structure)
  have heta : ByteArray.mk head.toArray ++ bulkBodyDense
      = ByteArray.mk ((ByteArray.mk head.toArray ++ bulkBodyDense).data) := by
    cases (ByteArray.mk head.toArray ++ bulkBodyDense); rfl
  rw [heta, hda, harr]

/-- **The dense serve equals the deployed serve on the `/bulk` arm.** On the H1
`/bulk` arm the dense (head ++ dense-body) output is byte-identical to
`ByteArray.mk (servePipelineFull2 input.toList).toArray` — the deployed List serve —
via the HEAD linchpin (`denseHeaders_eq_deployed`), the built-scalars, and the dense
body bridge. NO `respOf`, NO 1 MiB `List` on the compute path. -/
theorem denseArm_eq (input : ByteArray) (harm : BulkArm (ctxOf input.toList)) :
    ByteArray.mk (denseHeadBytes input.toList).toArray ++ bulkBodyDense
      = ByteArray.mk (servePipelineFull2 input.toList).toArray := by
  obtain ⟨hadmin, hpriv, hrate, hredir, htrav, hpol, hgz, hcors, hseg, hna, hnb⟩ := harm
  -- the ctx has no client.ip attr (ctxOf sets attrs := [])
  have hip : (ctxOf input.toList).attrs.find?
      (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none := rfl
  -- app handler is the 1 MiB body response
  have happ : appHandler (ctxOf input.toList)
      = { status := 200, reason := Reactor.App.reasonFor 200,
          headers := [], body := Reactor.App.bulkBody } :=
    appHandler_bulk (ctxOf input.toList) hseg hna hnb
  -- built scalars (unknown, non-reserved arm)
  obtain ⟨hst, hrs, hbd⟩ :=
    builtScalars (ctxOf input.toList) hadmin hpriv hip hrate hredir htrav hpol hgz hcors happ
  -- the deployed serve is serialize of the built response
  have hserve : servePipelineFull2 input.toList
      = Reactor.serialize
          ((runPipeline deployStagesFull2 appHandler (ctxOf input.toList)).build) := rfl
  -- head linchpin (unknown arm): the built headers are the dense fold's denotation
  have hhdr := denseHeadersUnknown (ctxOf input.toList) hadmin hpriv hip hrate hredir
    htrav hpol hgz hcors
  -- rewrite the deployed side to head ++ body, over the dense head bytes
  rw [hserve, serialize_eq_head_body
        ((runPipeline deployStagesFull2 appHandler (ctxOf input.toList)).build)]
  -- headBytes built = renderHead built.status built.reason built.headers built.body.length
  rw [← renderHead_eq_headBytes
        ((runPipeline deployStagesFull2 appHandler (ctxOf input.toList)).build)]
  -- substitute the scalars and the dense header block
  rw [hst, hrs, hbd, Reactor.App.bulkBody_length]
  -- appHandler headers = [] so the dense block matches denseHeadBytes
  have hAheaders : (appHandler (ctxOf input.toList)).headers = [] := by rw [happ]
  rw [show ((runPipeline deployStagesFull2 appHandler (ctxOf input.toList)).build).headers
        = (denseHeadersBlock [] (upstreamVal (deployPlan (deploySubs (ctxOf input.toList).input)))
            (corrVal (ctxOf input.toList).input)).denote from by rw [← hhdr, hAheaders]]
  -- now both sides are (denseHeadBytes ++ bulkBody); bridge the dense body
  show ByteArray.mk (denseHeadBytes input.toList).toArray ++ bulkBodyDense
    = ByteArray.mk ((denseHeadBytes input.toList) ++ Reactor.App.bulkBody).toArray
  exact denseOut_eq (denseHeadBytes input.toList)

/-- **THE CULMINATION — `serveDenseReal` is byte-identical to the deployed serve.**
For EVERY input, `serveDenseReal input = deployedServeRef input` (=
`Dataplane.drorbServe`, closed in `Dataplane`). The h2c and off-arm branches are the
deployed serve verbatim; the `/bulk` arm is the proven dense assembly
(`denseArm_eq`). -/
theorem serveDenseReal_refines (input : ByteArray) :
    serveDenseReal input = Datapath.ServeFlatFull.deployedServeRef input := by
  unfold serveDenseReal Datapath.ServeFlatFull.deployedServeRef
  by_cases h2 : Reactor.Ingress.hasH2Preface input.toList
  · simp only [h2, if_true]
  · simp only [h2, if_false, Bool.false_eq_true]
    by_cases harm : BulkArm (ctxOf input.toList)
    · rw [if_pos harm]; exact denseArm_eq input harm
    · rw [if_neg harm]

/-! ## 5. Non-vacuity — a real `GET /bulk` request drives the dense arm -/

/-- A real `GET /bulk` request with a `localhost` authority (the arm the dense serve
fires on). -/
def bulkDemoReq : ByteArray := "GET /bulk HTTP/1.1\r\nHost: localhost\r\n\r\n".toUTF8

-- The dense serve is byte-identical to the deployed serve on the real `/bulk` request.
#guard (serveDenseReal bulkDemoReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkDemoReq).data.toList
-- The dense `/bulk` response is genuinely the 1 MiB body plus a head (> 1 MiB).
#guard (serveDenseReal bulkDemoReq).size > 1048576

/-- A real `GET /bulk` request with a NON-`localhost`, non-vhost authority
(`example.net` — neither `a.example` nor `b.example`). The generalized `BulkArm` fires
on this too: `/bulk` reaches the `anyHost` block from ANY non-vhost host, so the dense
arm is not pinned to `localhost`. -/
def bulkDemoReqAnyHost : ByteArray := "GET /bulk HTTP/1.1\r\nHost: example.net\r\n\r\n".toUTF8

-- The `BulkArm` guard genuinely FIRES on the non-`localhost` host (kernel-decided): the
-- dense path is taken, NOT the `servePipelineFull2` List fallback.
#guard decide (BulkArm (ctxOf bulkDemoReqAnyHost.toList))
-- Byte-identical to the deployed serve on the non-`localhost` `/bulk` request.
#guard (serveDenseReal bulkDemoReqAnyHost).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkDemoReqAnyHost).data.toList
-- The dense `/bulk` response on the non-`localhost` host is genuinely > 1 MiB.
#guard (serveDenseReal bulkDemoReqAnyHost).size > 1048576

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms builtScalars
#print axioms denseArm_eq
#print axioms serveDenseReal_refines

end Datapath.ServeDenseReal
