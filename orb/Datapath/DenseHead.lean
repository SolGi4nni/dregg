import Datapath.HdrSeqProto
import Reactor.Deploy

/-!
# Datapath.DenseHead — the response-phase HEADER fold of `deployStagesFull2`, DENSE

This module closes the **HEAD linchpin** named as a residual in
`Datapath.ServeDenseFullReal` (L39–50): the deployed `/bulk`-shape response HEAD
carries the two input-dependent fields `x-corr` (the request rendered as dotted
decimal) and `x-upstream` (the LB/DNS-chosen address), stamped by the OUTER deploy
header rewrite (`Reactor.Deploy.deployProg`) on top of the inner header transforms.
A runtime-dense full serve must reproduce that head WITHOUT calling `respOf`/the app
handler over the 1 MiB body it is trying to avoid — i.e. it must re-express the whole
response-phase header fold over `deployStagesFull2` DENSELY (over `HdrBlock`, the
contiguous header spine) and prove it byte-identical to the deployed fold's
`.headers`.

That is what this file does. Every header-touching response stage of
`deployStagesFull2` on the admitted, non-gzip, non-CORS `/bulk` arm is re-expressed
over `[HdrSeq H]` and instantiated at the flat `HdrBlock`:

* the INNER header stage (`Reactor.Stage.Header.headerStage`, hop-strip + `Server`)
  — `Datapath.HdrSeqProto.hrwStagePoly` (reused, proven `_eq_deployed`);
* the security-header set (`securityheadersStage`) —
  `Datapath.HdrSeqProto.securityStagePoly` (reused, proven `_eq_deployed`);
* the body-only stages (`htmlrewriteStage`, and `gzipStage` off / `deployCorsStage`
  off on this arm) — proven HEADER-transparent here;
* the OUTER deploy header rewrite (`deployProg` = strip hop + `Server` + `x-upstream`
  + `x-corr`) — `deployProgPoly`, a NEW dense re-expression proven equal to the
  deployed `Header.run deployProg` (this is the x-corr/x-upstream head, densely).

The load-bearing result `denseHeaders_eq_deployed` proves the flat `HdrBlock` fold
`denote`s **byte-identically** to
`((runPipeline deployStagesFull2 appHandler c).build).headers` — with NO `respOf`,
NO app-handler-on-the-body on the head-compute path; the only `List` inputs are the
small app response header set (`~7` pairs) and the request-derived `x-corr`/
`x-upstream` scalars (`~40 B`). `denseHead` then renders the head bytes and proves
them equal to `serialize`'s head slice of the deployed built response.

## Named residuals (honest scope)

* The admitted-arm gate hypotheses (the seven `deployStagesFull2` gate passes +
  `Policy.Served`), plus `acceptsGzip c.req = false` and `Cors.acaoValue … = none`,
  are taken as HYPOTHESES — exactly the arm `Reactor.Deploy.full2_reduces` reduces.
  Discharging them for a concrete `/bulk` input is the FULL-from-scratch
  `deploySubs` reactor evaluation (heavy `whnf`), out of this lane's scope.
* `denseHead`'s status/reason/body-length are the deployed response's own scalars
  (status `200`, reason `OK`, body-length `bulkSize` — the last supplied densely by
  the body linchpin `Datapath.ServeDenseFullReal.bulkBodyDense`). The head genuinely
  depends on the body LENGTH (a `Nat`), never the body bytes.
* The dynamic hop set of each intermediate block (`Header.dynHopSet`) is a
  denotation-derived DATA parameter — the bounded "strip-set argument" wrinkle
  `Datapath.HdrSeqProto` already names; it is computed from the small header lists,
  never the body.
-/

namespace Datapath.DenseHead

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx ResponseBuilder runPipeline)
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock)
open Reactor.Deploy
open Header (isHop nameEqb dynHopSet)
open Datapath.HdrSeqProto
  (securityStagePoly hrwStagePoly securityStageBlock_refines hrwStageBlock_refines
   hrwStagePoly_eq_deployed)

/-! ## 1. The `toHeaders`/`ofHeaders` map–filter fusion (for the OUTER rewrite) -/

/-- Filtering the field view of a pair list on a NAME predicate is the field view of
filtering the pair list on the first component. The header-map fusion the outer
rewrite's `ofHeaders`/`toHeaders` bridge needs (the `Lifecycle` sibling of
`Datapath.HdrSeqProto.strip_toFields`'s helper). -/
theorem toHeaders_filter_name (q : Bytes → Bool) (l : List (Bytes × Bytes)) :
    (Reactor.Lifecycle.toHeaders l).filter (fun f => q f.name)
      = Reactor.Lifecycle.toHeaders (l.filter (fun nv => q nv.1)) := by
  induction l with
  | nil => rfl
  | cons nv rest ih =>
    simp only [Reactor.Lifecycle.toHeaders, List.map_cons, List.filter_cons] at ih ⊢
    by_cases h : q nv.1 <;> simp [h, ih]

/-- `toHeaders` distributes over append. -/
theorem toHeaders_append (a b : List (Bytes × Bytes)) :
    Reactor.Lifecycle.toHeaders (a ++ b)
      = Reactor.Lifecycle.toHeaders a ++ Reactor.Lifecycle.toHeaders b := by
  simp [Reactor.Lifecycle.toHeaders]

/-- `ofHeaders ∘ toHeaders = id` — the field view round-trips (Prod eta). -/
theorem ofHeaders_toHeaders (hs : List (Bytes × Bytes)) :
    Reactor.Lifecycle.ofHeaders (Reactor.Lifecycle.toHeaders hs) = hs := by
  induction hs with
  | nil => rfl
  | cons nv rest ih =>
    have e : Reactor.Lifecycle.ofHeaders (Reactor.Lifecycle.toHeaders (nv :: rest))
        = nv :: Reactor.Lifecycle.ofHeaders (Reactor.Lifecycle.toHeaders rest) := rfl
    rw [e, ih]

/-- `strip` commutes with `toHeaders`: stripping a hop set on the field view is the
field view of `filter`-ing the pair list on the same name predicate. -/
theorem strip_toHeaders (hop : List Bytes) (hs : List (Bytes × Bytes)) :
    Header.strip hop (Reactor.Lifecycle.toHeaders hs)
      = Reactor.Lifecycle.toHeaders (hs.filter (fun nv => !isHop hop nv.1)) := by
  rw [Header.strip]
  exact toHeaders_filter_name (fun nm => !isHop hop nm) hs

/-- `remove` commutes with `toHeaders`. -/
theorem remove_toHeaders (n : Bytes) (hs : List (Bytes × Bytes)) :
    Header.remove n (Reactor.Lifecycle.toHeaders hs)
      = Reactor.Lifecycle.toHeaders (hs.filter (fun nv => !nameEqb nv.1 n)) := by
  rw [Header.remove]
  exact toHeaders_filter_name (fun nm => !nameEqb nm n) hs

/-- `set` commutes with `toHeaders`: setting `n := v` on the field view is the field
view of `remove`-then-append on the pair list. -/
theorem set_toHeaders (n v : Bytes) (hs : List (Bytes × Bytes)) :
    Header.set n v (Reactor.Lifecycle.toHeaders hs)
      = Reactor.Lifecycle.toHeaders (hs.filter (fun nv => !nameEqb nv.1 n) ++ [(n, v)]) := by
  rw [toHeaders_append, Header.set, remove_toHeaders]
  rfl

/-! ## 2. The OUTER deploy header rewrite, DENSE: `deployProgPoly`

`deployProg plan input = stdRewrite ++ [set x-upstream, set x-corr]` and
`stdRewrite = [hopDyn, set Server]`, so
`Header.run deployProg h = set corr (set upstream (set Server (strip (dynHopSet h) h)))`.
`deployProgPoly` writes that ONCE over `[HdrSeq H]` (strip via `filter`, each `set`
via `filter`-then-`push`), so it instantiates at the flat `HdrBlock`. -/

/-- The dense hop-strip: keep the pairs whose name is not in the hop set. -/
def stripPoly {H : Type} [HdrSeq H] (hop : List Bytes) (h : H) : H :=
  HdrSeq.filter h (fun nv => !isHop hop nv.1)

/-- The dense single-name set: drop any prior field named `n`, then push `(n, v)`. -/
def setPoly {H : Type} [HdrSeq H] (n v : Bytes) (h : H) : H :=
  HdrSeq.push (HdrSeq.filter h (fun nv => !nameEqb nv.1 n)) (n, v)

/-- **The OUTER deploy header rewrite, written ONCE over `[HdrSeq H]`.** Strip the
(dynamic) hop set, then set `Server`, `x-upstream`, `x-corr` in order — exactly
`Header.run deployProg`. `uv`/`cv` (the upstream address / correlation id, request-
derived) are parameters. -/
def deployProgPoly {H : Type} [HdrSeq H] (hop : List Bytes) (uv cv : Bytes) (h : H) : H :=
  setPoly corrName cv
    (setPoly upstreamName uv
      (setPoly Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal
        (stripPoly hop h)))

/-- The stage at the spec instance is the nested `List.filter`s + appends (the `List`
normal form). This is `deployProgPoly` at `H := List _`. -/
theorem deployProgPoly_list (hop : List Bytes) (uv cv : Bytes) (l : List (Bytes × Bytes)) :
    deployProgPoly (H := List (Bytes × Bytes)) hop uv cv l
      = ((((l.filter (fun nv => !isHop hop nv.1)).filter
              (fun nv => !nameEqb nv.1 Reactor.Lifecycle.serverName)
            ++ [(Reactor.Lifecycle.serverName, Reactor.Lifecycle.serverVal)]).filter
            (fun nv => !nameEqb nv.1 upstreamName)
          ++ [(upstreamName, uv)]).filter (fun nv => !nameEqb nv.1 corrName))
        ++ [(corrName, cv)] := rfl

/-- **The whole-rewrite refinement — FOLLOWS from the op laws.** The dense rewrite's
denotation equals the spec-instance rewrite on the denoted input; discharged by
`simp` over `push_denote` + `filter_denote`. No per-stage induction. -/
theorem deployProgPoly_refines {H : Type} [HdrSeq H] (hop : List Bytes) (uv cv : Bytes) (h : H) :
    HdrSeq.toHdrs (deployProgPoly hop uv cv h)
      = deployProgPoly (H := List (Bytes × Bytes)) hop uv cv (HdrSeq.toHdrs h) := by
  rw [deployProgPoly_list]
  simp only [deployProgPoly, setPoly, stripPoly, HdrSeq.push_denote, HdrSeq.filter_denote]

/-- The refinement at the fast `HdrBlock` instance — a DIRECT instance. -/
theorem deployProgBlock_refines (hop : List Bytes) (uv cv : Bytes) (h : HdrBlock) :
    HdrBlock.denote (deployProgPoly hop uv cv h)
      = deployProgPoly (H := List (Bytes × Bytes)) hop uv cv h.denote :=
  deployProgPoly_refines hop uv cv h

/-- The concrete deploy rewrite program `deployProg` runs, parameterised by the two
request-derived values (`stdRewrite ++ [set x-upstream, set x-corr]`). -/
def deployRewriteProg (uv cv : Bytes) : List Header.Op :=
  Reactor.Lifecycle.stdRewrite
    ++ [Header.Op.set upstreamName uv, Header.Op.set corrName cv]

/-- The deployed `deployProg` IS `deployRewriteProg` at the plan/input-derived
values — definitional (`deployProg = stdRewrite ++ [set x-upstream, set x-corr]`). -/
theorem deployProg_eq (plan : List Reactor.RingSubmission) (input : Bytes) :
    deployProg plan input = deployRewriteProg (upstreamVal plan) (corrVal input) := rfl

/-- **Grounded in the REAL deployed rewrite (non-vacuous).** With the hop set taken
to be the message's own `dynHopSet` (what `deployProg`'s `hopDyn` uses), the dense
rewrite at the spec instance computes precisely `ofHeaders (Header.run deployProg …)`
— the header block the deployed OUTER `headerRewriteStage` yields, running the real
`Header.run` under `deployProg`. Grounded on `Header.run`/`set`/`strip`, not
re-specified. -/
theorem deployProgPoly_eq_deployed (uv cv : Bytes) (hs : List (Bytes × Bytes)) :
    deployProgPoly (H := List (Bytes × Bytes))
        (dynHopSet (Reactor.Lifecycle.toHeaders hs)) uv cv hs
      = Reactor.Lifecycle.ofHeaders
          (Header.run (deployRewriteProg uv cv) (Reactor.Lifecycle.toHeaders hs)) := by
  have hrun : Header.run (deployRewriteProg uv cv) (Reactor.Lifecycle.toHeaders hs)
      = Header.set corrName cv
          (Header.set upstreamName uv
            (Header.set Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal
              (Header.strip (dynHopSet (Reactor.Lifecycle.toHeaders hs))
                (Reactor.Lifecycle.toHeaders hs)))) := by
    show Header.run (Reactor.Lifecycle.stdRewrite
        ++ [Header.Op.set upstreamName uv, Header.Op.set corrName cv])
        (Reactor.Lifecycle.toHeaders hs) = _
    rw [Header.run_append]
    have hstd : Header.run Reactor.Lifecycle.stdRewrite (Reactor.Lifecycle.toHeaders hs)
        = Header.set Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal
            (Header.strip (dynHopSet (Reactor.Lifecycle.toHeaders hs))
              (Reactor.Lifecycle.toHeaders hs)) := by
      show Header.run [Header.Op.hopDyn,
          Header.Op.set Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal]
          (Reactor.Lifecycle.toHeaders hs) = _
      rw [Header.run_hopDyn_cons, Header.run_cons, Header.run_nil]
      rfl
    rw [hstd, Header.run_cons, Header.run_cons, Header.run_nil]
    rfl
  rw [hrun, strip_toHeaders, set_toHeaders, set_toHeaders, set_toHeaders,
    ofHeaders_toHeaders, deployProgPoly_list]

/-! ## 3. The INNER header block, DENSE, and its deployed equality

On the admitted `/bulk`-shape arm the five inner response-transform stages
(`full2InnerStages`) touch the header block as: `headerStage` (hop-strip + `Server`,
`hrwStagePoly`) innermost, then `securityheadersStage` (`securityStagePoly`); the
markup rewrite is header-transparent (body only), and `gzipStage`/`deployCorsStage`
are OFF (no `Accept-Encoding: gzip`, no allowed `Origin`), so header-transparent too. -/

/-- The dense INNER header block: the app response headers `A` (small) into `HdrBlock`,
hop-stripped + `Server` (`hrwStagePoly`), then the security-header set
(`securityStagePoly`). Genuinely flat — `Array` push/filter, no `List` cons-spine on
the datapath (only the small `A` and the derived hop set are `List`s). -/
def denseInnerBlock (A : List (Bytes × Bytes)) : HdrBlock :=
  securityStagePoly (H := HdrBlock)
    (hrwStagePoly (H := HdrBlock)
      (dynHopSet (Reactor.Stage.Header.toFields A)) (HdrBlock.ofList A))

/-- The INNER block denotes to the composed spec-side header transform. -/
theorem denseInnerBlock_denote (A : List (Bytes × Bytes)) :
    (denseInnerBlock A).denote
      = hrwStagePoly (H := List (Bytes × Bytes)) (dynHopSet (Reactor.Stage.Header.toFields A)) A
        ++ Reactor.Stage.SecurityHeaders.wireHeaders Reactor.Stage.SecurityHeaders.policy := by
  show HdrBlock.denote (securityStagePoly (H := HdrBlock) _) = _
  rw [securityStageBlock_refines, hrwStageBlock_refines, HdrBlock.denote_ofList]
  show foldPush (Reactor.Stage.SecurityHeaders.wireHeaders Reactor.Stage.SecurityHeaders.policy)
      (hrwStagePoly (H := List (Bytes × Bytes)) _ A) = _
  rw [foldPush_list]

/-- The gated html transform leaves the HEADER block untouched (it rewrites only the
body; both `Content-Type`-gate branches keep `r.headers`). -/
theorem gatedHtmlTransformResp_headers (r : Response) :
    (Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp r).headers = r.headers := by
  unfold Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp Reactor.Stage.HtmlRewrite.htmlTransformResp
  cases Reactor.Stage.HtmlRewrite.isHtmlCT r.headers <;> rfl

/-- **The INNER header fold's deployed headers, on the `/bulk` arm.** With gzip OFF
and CORS OFF, the built `full2InnerStages` response's header block IS the composed
spec transform `denseInnerBlock`'s denotation — grounded on the REAL stage effects
(`headerStage_headers`, `securityStage_headers_effect`, the html header-transparency,
and the gzip/cors OFF branches), NO `respOf`. -/
theorem innerHeaders (c : Ctx)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false)
    (hcors : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none) :
    ((runPipeline full2InnerStages appHandler c).build).headers
      = (denseInnerBlock (appHandler c).headers).denote := by
  -- peel CORS (off) and gzip (off) — both header + builder transparent on this arm
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
  show ((runPipeline (deployCorsStage :: Reactor.Stage.Gzip.gzipStage
      :: Reactor.Stage.HtmlRewrite.htmlrewriteStage
      :: Reactor.Stage.SecurityHeaders.securityheadersStage
      :: [Reactor.Stage.Header.headerStage]) appHandler c).build).headers = _
  rw [Reactor.Deploy.prepend_pass deployCorsStage _ appHandler c rfl hcorsResp,
      Reactor.Deploy.prepend_pass Reactor.Stage.Gzip.gzipStage _ appHandler c rfl hgzResp,
      Reactor.Stage.HtmlRewrite.htmlrewriteStage_effect, Reactor.Pipeline.build_mapResp,
      gatedHtmlTransformResp_headers,
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.SecurityHeaders.securityheadersStage
        [Reactor.Stage.Header.headerStage] appHandler c c rfl,
      Datapath.FlatStage.securityStage_headers_effect,
      Reactor.Stage.Header.headerStage_headers]
  -- the app response headers feed the header stage
  show Reactor.Stage.Header.fromFields (Header.run Reactor.Stage.Header.rewriteProg
      (Reactor.Stage.Header.toFields ((runPipeline [] appHandler c).build).headers))
        ++ _ = _
  rw [show (runPipeline [] appHandler c).build = appHandler c from rfl]
  -- fold the header stage into hrwStagePoly, and the security append into denseInnerBlock
  have hhrw : Reactor.Stage.Header.fromFields (Header.run Reactor.Stage.Header.rewriteProg
      (Reactor.Stage.Header.toFields (appHandler c).headers))
        = hrwStagePoly (H := List (Bytes × Bytes))
            (dynHopSet (Reactor.Stage.Header.toFields (appHandler c).headers)) (appHandler c).headers := by
    have := hrwStagePoly_eq_deployed (appHandler c)
    show _ = _
    rw [this]
    rfl
  rw [hhrw, denseInnerBlock_denote]

/-! ## 4. The FULL dense head-header block, proven equal to the deployed `.headers` -/

/-- **The full dense response HEADER block.** The INNER block (`hrwStagePoly` +
`securityStagePoly`) followed by the OUTER deploy rewrite (`deployProgPoly` — strip
hop + `Server` + `x-upstream` + `x-corr`), all over the flat `HdrBlock`. `uv`/`cv`
are the request-derived upstream/correlation values (`~40 B`). -/
def denseHeadersBlock (A : List (Bytes × Bytes)) (uv cv : Bytes) : HdrBlock :=
  deployProgPoly (H := HdrBlock)
    (dynHopSet (Reactor.Lifecycle.toHeaders (denseInnerBlock A).denote)) uv cv
    (denseInnerBlock A)

/-- The full dense block denotes to the composed spec-side transform. -/
theorem denseHeadersBlock_denote (A : List (Bytes × Bytes)) (uv cv : Bytes) :
    (denseHeadersBlock A uv cv).denote
      = deployProgPoly (H := List (Bytes × Bytes))
          (dynHopSet (Reactor.Lifecycle.toHeaders (denseInnerBlock A).denote)) uv cv
          (denseInnerBlock A).denote := by
  show HdrBlock.denote (deployProgPoly (H := HdrBlock) _ uv cv _) = _
  rw [deployProgBlock_refines]

/-- **THE HEAD LINCHPIN — the dense header fold is byte-identical to the deployed
`.headers`.** On the admitted, non-gzip, non-CORS `/bulk` arm (the arm
`full2_reduces` reduces), the flat `HdrBlock` fold `denseHeadersBlock` — starting
from the SMALL app response header set and the request-derived `x-corr`/`x-upstream`
scalars, with NO `respOf` and NO body — `denote`s exactly to
`((runPipeline deployStagesFull2 appHandler c).build).headers`. Composed from the
inner-stage refinements and the OUTER `deployProgPoly` grounding; non-vacuous. -/
theorem denseHeaders_eq_deployed (c : Ctx) (s : Policy.Served)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hip : c.attrs.find? (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none)
    (hrate : Reactor.Stage.Rate.admits c = true)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hadmit : deployDecisionOf c.req = some s)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false)
    (hcors : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none) :
    (denseHeadersBlock (appHandler c).headers
        (upstreamVal (deployPlan (deploySubs c.input))) (corrVal c.input)).denote
      = ((runPipeline deployStagesFull2 appHandler c).build).headers := by
  -- deployed side: reduce to the outer rewrite of the inner built response
  rw [full2_reduces c s hadmin hpriv hip hrate hredir htrav hadmit, Reactor.Pipeline.build_mapResp]
  show _ = (Reactor.Lifecycle.rewriteResp
      (deployProg (deployPlan (deploySubs c.input)) c.input)
      ((runPipeline full2InnerStages appHandler c).build)).headers
  show _ = Reactor.Lifecycle.ofHeaders (Header.run
      (deployProg (deployPlan (deploySubs c.input)) c.input)
      (Reactor.Lifecycle.toHeaders ((runPipeline full2InnerStages appHandler c).build).headers))
  rw [innerHeaders c hgz hcors, deployProg_eq,
    denseHeadersBlock_denote, deployProgPoly_eq_deployed]

/-! ## 5. Rendering the HEAD bytes -/

/-- The rendered HEAD of a response — everything `serialize` emits before the body:
status line, CRLF, header block (incl. the derived `Content-Length`), blank line. -/
def headBytes (r : Response) : Bytes :=
  Reactor.statusLineOf r ++ Reactor.crlf ++ Reactor.headerBlockOf r ++ Reactor.crlf ++ Reactor.crlf

/-- `serialize` is the HEAD followed by the body. -/
theorem serialize_eq_head_body (r : Response) :
    Reactor.serialize r = headBytes r ++ r.body :=
  Reactor.serialize_framing r

/-- **Render the head DENSELY** from the small scalars (status, reason, body-LENGTH —
never the body bytes) and a header list. The header list is the dense block's
denotation; the `Content-Length` value is derived from the body length the body
linchpin supplies. -/
def renderHead (status : Nat) (reason : Bytes) (hdrs : List (Bytes × Bytes)) (bodyLen : Nat) : Bytes :=
  (Reactor.http11 ++ [32] ++ Reactor.natToDec status ++ [32] ++ reason) ++ Reactor.crlf
    ++ Reactor.renderHeaders (hdrs ++ [(Reactor.clName, Reactor.natToDec bodyLen)])
    ++ Reactor.crlf ++ Reactor.crlf

/-- `renderHead` on a response's own fields is exactly its `headBytes`. -/
theorem renderHead_eq_headBytes (r : Response) :
    renderHead r.status r.reason r.headers r.body.length = headBytes r := rfl

/-- **The dense HEAD render is byte-identical to the deployed head.** Given the
deployed built response's own status/reason/body-length scalars (`bodyLen` supplied
densely by the body linchpin), the head rendered over the DENSE header block equals
`serialize`'s head slice of the deployed built response — the whole head produced
without `respOf` on the body. -/
theorem denseHead_eq_deployed (c : Ctx) (s : Policy.Served)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hip : c.attrs.find? (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none)
    (hrate : Reactor.Stage.Rate.admits c = true)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hadmit : deployDecisionOf c.req = some s)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = false)
    (hcors : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none) :
    renderHead ((runPipeline deployStagesFull2 appHandler c).build).status
        ((runPipeline deployStagesFull2 appHandler c).build).reason
        (denseHeadersBlock (appHandler c).headers
          (upstreamVal (deployPlan (deploySubs c.input))) (corrVal c.input)).denote
        ((runPipeline deployStagesFull2 appHandler c).build).body.length
      = headBytes ((runPipeline deployStagesFull2 appHandler c).build) := by
  rw [denseHeaders_eq_deployed c s hadmin hpriv hip hrate hredir htrav hadmit hgz hcors,
    renderHead_eq_headBytes]

/-! ## 6. Non-vacuity — the dense rewrite genuinely stamps the head -/

-- The dense OUTER rewrite genuinely installs `Server`/`x-upstream`/`x-corr` (in order,
-- on an empty base) — it is not a constant/identity.
#guard deployProgPoly (H := List (Bytes × Bytes)) [] (natBytes 42) ("1.2.3.4".toUTF8.toList) []
        == [ (Reactor.Lifecycle.serverName, Reactor.Lifecycle.serverVal)
           , (upstreamName, natBytes 42)
           , (corrName, "1.2.3.4".toUTF8.toList) ]

-- The dense OUTER rewrite genuinely STRIPS a hop-nominated field (here `Connection`),
-- while keeping an end-to-end header — so it is not the identity map.
#guard deployProgPoly (H := List (Bytes × Bytes))
        [Reactor.Stage.Header.connField.1] (natBytes 7) ("9".toUTF8.toList)
        [Reactor.Stage.Header.connField, Reactor.Stage.Header.xtField]
      == [ Reactor.Stage.Header.xtField
         , (Reactor.Lifecycle.serverName, Reactor.Lifecycle.serverVal)
         , (upstreamName, natBytes 7)
         , (corrName, "9".toUTF8.toList) ]

-- The stripped case DIFFERS from the input (the hop header is gone).
#guard deployProgPoly (H := List (Bytes × Bytes))
        [Reactor.Stage.Header.connField.1] (natBytes 7) ("9".toUTF8.toList)
        [Reactor.Stage.Header.connField, Reactor.Stage.Header.xtField]
      != [Reactor.Stage.Header.connField, Reactor.Stage.Header.xtField]

-- The flat `HdrBlock` rewrite and the spec rewrite AGREE on a concrete input (the
-- refinement, run) — the dense path computes the same header block.
#guard (deployProgPoly (H := HdrBlock)
          [Reactor.Stage.Header.connField.1] (natBytes 7) ("9".toUTF8.toList)
          (HdrBlock.ofList [Reactor.Stage.Header.connField, Reactor.Stage.Header.xtField])).denote
      == deployProgPoly (H := List (Bytes × Bytes))
          [Reactor.Stage.Header.connField.1] (natBytes 7) ("9".toUTF8.toList)
          [Reactor.Stage.Header.connField, Reactor.Stage.Header.xtField]

-- The rendered head genuinely carries the status line and the `x-corr` header bytes.
#guard (Reactor.http11.isPrefixOf
          (renderHead 200 Reactor.reasonOK
            (deployProgPoly (H := List (Bytes × Bytes)) [] (natBytes 42) ("1.2.3.4".toUTF8.toList) []) 7))

/-! ## 7. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms deployProgPoly_refines
#print axioms deployProgPoly_eq_deployed
#print axioms denseInnerBlock_denote
#print axioms innerHeaders
#print axioms denseHeaders_eq_deployed
#print axioms denseHead_eq_deployed

end Datapath.DenseHead
