import Datapath.ServeDenseIdx

/-!
# Datapath.OffarmApp — the constant-body OFF-ARM routes, decided and reduced

The deployed serve's off-arm (everything the index-native serves still answer
through the `List` fold) contains four CONSTANT-BODY routes: the catch-all `404`,
the two exact virtual hosts, and the assets glob route. This module proves, for
each, the app-level facts the dense kit consumes:

* **the app answers** (`appHandler_notFound` / `_vhostA` / `_vhostB` / `_glob`):
  under decidable route-shape hypotheses on the request's target segments and
  authority, `appHandler` answers the route's constant body — through the REAL
  `Route.Match.bestMatch` fall-through (`bestMatch_demo_default`) and the REAL
  `RouteAdvanced.dispatch` block/route selection, not a re-specification;
* **the upstream-scalar collapse** (`uv_dispatch`): the deployed `x-upstream`
  plan value is ONE top-level constant (`uvDefault`) on EVERY dispatched request —
  the deployed proxy table routes every path to the same pool — so no arm ever
  recomputes a plan;
* **the generic constant-body arm byte-identity** (`constArm_eq`): for ANY
  admitted constant-body app answer whose body the html-rewrite fixes, the dense
  (head ++ dense-body) emission is byte-identical to the deployed
  `servePipelineFull2` — `builtScalarsGen` + `denseHeadersUnknown` +
  `denseOutGen`, the `/health`-arm kit freed from its route.
-/

namespace Datapath.OffarmApp

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx runPipeline)
open Reactor.Deploy

/-! ## 1. The four constant bodies (dense `ByteArray` constants + html-rewrite fix) -/

/-- The catch-all `404` body, `List` side — what the deployed block table answers. -/
def notFoundBody : Bytes := "not found".toUTF8.toList

/-- The catch-all `404` body as a TOP-LEVEL `ByteArray` constant. -/
def notFoundBodyDense : ByteArray := "not found".toUTF8

theorem notFoundBodyDense_toList : notFoundBodyDense.data.toList = notFoundBody :=
  (Reactor.ServeConformant.ba_toList_eq _).symm

/-- The `a.example` virtual-host body, `List` side. -/
def vhostABody : Bytes := "vhost-a".toUTF8.toList

/-- The `a.example` body as a TOP-LEVEL `ByteArray` constant. -/
def vhostABodyDense : ByteArray := "vhost-a".toUTF8

theorem vhostABodyDense_toList : vhostABodyDense.data.toList = vhostABody :=
  (Reactor.ServeConformant.ba_toList_eq _).symm

/-- The `b.example` virtual-host body, `List` side. -/
def vhostBBody : Bytes := "vhost-b".toUTF8.toList

/-- The `b.example` body as a TOP-LEVEL `ByteArray` constant. -/
def vhostBBodyDense : ByteArray := "vhost-b".toUTF8

theorem vhostBBodyDense_toList : vhostBBodyDense.data.toList = vhostBBody :=
  (Reactor.ServeConformant.ba_toList_eq _).symm

/-- The assets glob route's body, `List` side. -/
def globBody : Bytes := "glob-hit".toUTF8.toList

/-- The glob body as a TOP-LEVEL `ByteArray` constant. -/
def globBodyDense : ByteArray := "glob-hit".toUTF8

theorem globBodyDense_toList : globBodyDense.data.toList = globBody :=
  (Reactor.ServeConformant.ba_toList_eq _).symm

theorem notFoundBody_bytes :
    notFoundBody = [0x6E, 0x6F, 0x74, 0x20, 0x66, 0x6F, 0x75, 0x6E, 0x64] := by
  unfold notFoundBody
  rw [Reactor.ServeConformant.ba_toList_eq]
  decide

theorem vhostABody_bytes :
    vhostABody = [0x76, 0x68, 0x6F, 0x73, 0x74, 0x2D, 0x61] := by
  unfold vhostABody
  rw [Reactor.ServeConformant.ba_toList_eq]
  decide

theorem vhostBBody_bytes :
    vhostBBody = [0x76, 0x68, 0x6F, 0x73, 0x74, 0x2D, 0x62] := by
  unfold vhostBBody
  rw [Reactor.ServeConformant.ba_toList_eq]
  decide

theorem globBody_bytes :
    globBody = [0x67, 0x6C, 0x6F, 0x62, 0x2D, 0x68, 0x69, 0x74] := by
  unfold globBody
  rw [Reactor.ServeConformant.ba_toList_eq]
  decide

/-- The deployed html-rewrite fixes the tagless `404` body (no `<` to strip). -/
theorem rewriteBytes_notFoundBody :
    Reactor.Stage.HtmlRewrite.rewriteBytes notFoundBody = notFoundBody := by
  rw [notFoundBody_bytes, HtmlRewriteCorrect.rewriteBytes_eq_spec]
  exact Datapath.ServeDenseFullReal.strip_false_no_lt _ (by decide)

theorem rewriteBytes_vhostABody :
    Reactor.Stage.HtmlRewrite.rewriteBytes vhostABody = vhostABody := by
  rw [vhostABody_bytes, HtmlRewriteCorrect.rewriteBytes_eq_spec]
  exact Datapath.ServeDenseFullReal.strip_false_no_lt _ (by decide)

theorem rewriteBytes_vhostBBody :
    Reactor.Stage.HtmlRewrite.rewriteBytes vhostBBody = vhostBBody := by
  rw [vhostBBody_bytes, HtmlRewriteCorrect.rewriteBytes_eq_spec]
  exact Datapath.ServeDenseFullReal.strip_false_no_lt _ (by decide)

theorem rewriteBytes_globBody :
    Reactor.Stage.HtmlRewrite.rewriteBytes globBody = globBody := by
  rw [globBody_bytes, HtmlRewriteCorrect.rewriteBytes_eq_spec]
  exact Datapath.ServeDenseFullReal.strip_false_no_lt _ (by decide)

/-! ## 2. The route-shape atoms (the deployed block table's two path patterns) -/

/-- The assets glob path pattern of the deployed `anyHost` block. -/
def globPathPat : RouteAdvanced.PathPat :=
  { segs := [RouteAdvanced.SegPat.lit "health", RouteAdvanced.SegPat.lit "assets"],
    globstar := true }

/-- The `/bulk` route's path pattern. -/
def bulkPathPat : RouteAdvanced.PathPat :=
  { segs := [RouteAdvanced.SegPat.lit "bulk"], globstar := false }

/-! ## 3. `bestMatch` falls to the deployed default on an author-route miss -/

/-- **The author-table fall-through.** Segments that miss the exact `["health"]`
route and both prefix routes select the deployed DEFAULT route (the host/glob
block table) — through the real `bestMatch` class precedence. -/
theorem bestMatch_demo_default (segs : List String)
    (hnh : segs ≠ ["health"])
    (hns : List.isPrefixOf ["static"] segs = false)
    (hnc : List.isPrefixOf ["cgi-bin"] segs = false) :
    Route.Match.bestMatch Reactor.demoAppConfig.table segs
      = some ⟨Route.Match.Pat.default,
              Reactor.App.Handler.hostGlob Reactor.App.demoVhBlocks⟩ := by
  simp only [Reactor.demoAppConfig, Reactor.App.demoApp, Reactor.App.AppConfig.table,
    List.cons_append, List.nil_append, Route.Match.bestMatch, List.find?,
    Route.Match.matchesExact, Route.Match.matchesPrefix, Route.Match.matchesDefault,
    decide_eq_false hnh, hns, hnc]

/-! ## 4. The block-table dispatches (the real `RouteAdvanced.dispatch`) -/

/-- **The catch-all dispatch.** Off both exact vhosts, off the glob route, and off
the `/bulk` route, the deployed block table answers with the `404` catch-all. -/
theorem dispatch_demo_catchAll (req : Proto.Request)
    (hng : RouteAdvanced.pathMatch globPathPat (Reactor.App.targetSegments req.target) = false)
    (hnbk : RouteAdvanced.pathMatch bulkPathPat (Reactor.App.targetSegments req.target) = false)
    (hna : Reactor.App.hostLabelsOf req ≠ ["a", "example"])
    (hnb : Reactor.App.hostLabelsOf req ≠ ["b", "example"]) :
    RouteAdvanced.dispatch Reactor.App.demoVhBlocks (Reactor.App.hostReqOf req)
      = some (RouteAdvanced.catchAllRoute
          (Reactor.App.VHandler.respond 404 "not found".toUTF8.toList)) := by
  have hgm : RouteAdvanced.routeMatches (Reactor.App.hostReqOf req)
      { method := RouteAdvanced.MethodPat.anyMethod,
        path := { segs := [RouteAdvanced.SegPat.lit "health", RouteAdvanced.SegPat.lit "assets"],
                  globstar := true },
        guards := [],
        handler := Reactor.App.VHandler.respond 200 "glob-hit".toUTF8.toList } = false := by
    show (true && RouteAdvanced.pathMatch globPathPat (Reactor.App.targetSegments req.target)
        && true) = false
    rw [hng]
    rfl
  have hbm : RouteAdvanced.routeMatches (Reactor.App.hostReqOf req) Reactor.App.bulkRoute
      = false := by
    show (true && RouteAdvanced.pathMatch bulkPathPat (Reactor.App.targetSegments req.target)
        && true) = false
    rw [hnbk]
    rfl
  unfold RouteAdvanced.dispatch
  rw [Reactor.App.demoVhBlocks_selectBlock_anyHost req hna hnb]
  show List.find? (RouteAdvanced.routeMatches (Reactor.App.hostReqOf req))
      [ { method := RouteAdvanced.MethodPat.anyMethod,
          path := { segs := [RouteAdvanced.SegPat.lit "health", RouteAdvanced.SegPat.lit "assets"],
                    globstar := true },
          guards := [],
          handler := Reactor.App.VHandler.respond 200 "glob-hit".toUTF8.toList },
        Reactor.App.bulkRoute,
        RouteAdvanced.catchAllRoute (Reactor.App.VHandler.respond 404 "not found".toUTF8.toList) ]
      = some (RouteAdvanced.catchAllRoute
          (Reactor.App.VHandler.respond 404 "not found".toUTF8.toList))
  rw [List.find?_cons_of_neg _ (by rw [hgm]; exact Bool.false_ne_true),
      List.find?_cons_of_neg _ (by rw [hbm]; exact Bool.false_ne_true),
      List.find?_cons_of_pos _ (RouteAdvanced.catchAllRoute_matches _ _)]

/-- The `a.example` authority selects the FIRST exact-host block. -/
theorem selectBlock_demo_a (req : Proto.Request)
    (hva : Reactor.App.hostLabelsOf req = ["a", "example"]) :
    RouteAdvanced.selectBlock Reactor.App.demoVhBlocks (Reactor.App.hostReqOf req)
      = some { host := RouteAdvanced.HostPat.exact ["a", "example"],
               routes := [ RouteAdvanced.catchAllRoute
                   (Reactor.App.VHandler.respond 200 "vhost-a".toUTF8.toList) ] } := by
  have e0 : RouteAdvanced.hostMatch (RouteAdvanced.HostPat.exact ["a", "example"])
      (Reactor.App.hostReqOf req).host = true := by
    show RouteAdvanced.hostMatch (RouteAdvanced.HostPat.exact ["a", "example"])
        (Reactor.App.hostLabelsOf req) = true
    rw [hva]
    decide
  unfold RouteAdvanced.selectBlock
  simp only [Reactor.App.demoVhBlocks, List.find?, e0]

/-- The `b.example` authority skips the `a.example` block (exact-host isolation)
and selects the SECOND exact-host block. -/
theorem selectBlock_demo_b (req : Proto.Request)
    (hvb : Reactor.App.hostLabelsOf req = ["b", "example"]) :
    RouteAdvanced.selectBlock Reactor.App.demoVhBlocks (Reactor.App.hostReqOf req)
      = some { host := RouteAdvanced.HostPat.exact ["b", "example"],
               routes := [ RouteAdvanced.catchAllRoute
                   (Reactor.App.VHandler.respond 200 "vhost-b".toUTF8.toList) ] } := by
  have e0 : RouteAdvanced.hostMatch (RouteAdvanced.HostPat.exact ["a", "example"])
      (Reactor.App.hostReqOf req).host = false := by
    show RouteAdvanced.hostMatch (RouteAdvanced.HostPat.exact ["a", "example"])
        (Reactor.App.hostLabelsOf req) = false
    rw [hvb]
    decide
  have e1 : RouteAdvanced.hostMatch (RouteAdvanced.HostPat.exact ["b", "example"])
      (Reactor.App.hostReqOf req).host = true := by
    show RouteAdvanced.hostMatch (RouteAdvanced.HostPat.exact ["b", "example"])
        (Reactor.App.hostLabelsOf req) = true
    rw [hvb]
    decide
  unfold RouteAdvanced.selectBlock
  simp only [Reactor.App.demoVhBlocks, List.find?, e0, e1]

/-- The `a.example` block's first (and only) route is its catch-all. -/
theorem dispatch_demo_a (req : Proto.Request)
    (hva : Reactor.App.hostLabelsOf req = ["a", "example"]) :
    RouteAdvanced.dispatch Reactor.App.demoVhBlocks (Reactor.App.hostReqOf req)
      = some (RouteAdvanced.catchAllRoute
          (Reactor.App.VHandler.respond 200 "vhost-a".toUTF8.toList)) := by
  unfold RouteAdvanced.dispatch
  rw [selectBlock_demo_a req hva]
  show List.find? (RouteAdvanced.routeMatches (Reactor.App.hostReqOf req))
      [RouteAdvanced.catchAllRoute (Reactor.App.VHandler.respond 200 "vhost-a".toUTF8.toList)]
      = _
  exact List.find?_cons_of_pos _ (RouteAdvanced.catchAllRoute_matches _ _)

/-- The `b.example` block's first (and only) route is its catch-all. -/
theorem dispatch_demo_b (req : Proto.Request)
    (hvb : Reactor.App.hostLabelsOf req = ["b", "example"]) :
    RouteAdvanced.dispatch Reactor.App.demoVhBlocks (Reactor.App.hostReqOf req)
      = some (RouteAdvanced.catchAllRoute
          (Reactor.App.VHandler.respond 200 "vhost-b".toUTF8.toList)) := by
  unfold RouteAdvanced.dispatch
  rw [selectBlock_demo_b req hvb]
  show List.find? (RouteAdvanced.routeMatches (Reactor.App.hostReqOf req))
      [RouteAdvanced.catchAllRoute (Reactor.App.VHandler.respond 200 "vhost-b".toUTF8.toList)]
      = _
  exact List.find?_cons_of_pos _ (RouteAdvanced.catchAllRoute_matches _ _)

/-- A matching glob path under a non-vhost authority selects the glob route
(first in the `anyHost` block). -/
theorem dispatch_demo_glob (req : Proto.Request)
    (hg : RouteAdvanced.pathMatch globPathPat (Reactor.App.targetSegments req.target) = true)
    (hna : Reactor.App.hostLabelsOf req ≠ ["a", "example"])
    (hnb : Reactor.App.hostLabelsOf req ≠ ["b", "example"]) :
    RouteAdvanced.dispatch Reactor.App.demoVhBlocks (Reactor.App.hostReqOf req)
      = some { method := RouteAdvanced.MethodPat.anyMethod,
               path := { segs := [RouteAdvanced.SegPat.lit "health",
                                  RouteAdvanced.SegPat.lit "assets"],
                         globstar := true },
               guards := [],
               handler := Reactor.App.VHandler.respond 200 "glob-hit".toUTF8.toList } := by
  unfold RouteAdvanced.dispatch
  rw [Reactor.App.demoVhBlocks_selectBlock_anyHost req hna hnb]
  show List.find? (RouteAdvanced.routeMatches (Reactor.App.hostReqOf req))
      [ { method := RouteAdvanced.MethodPat.anyMethod,
          path := { segs := [RouteAdvanced.SegPat.lit "health", RouteAdvanced.SegPat.lit "assets"],
                    globstar := true },
          guards := [],
          handler := Reactor.App.VHandler.respond 200 "glob-hit".toUTF8.toList },
        Reactor.App.bulkRoute,
        RouteAdvanced.catchAllRoute (Reactor.App.VHandler.respond 404 "not found".toUTF8.toList) ]
      = _
  exact List.find?_cons_of_pos _ (by
    show (true && RouteAdvanced.pathMatch globPathPat (Reactor.App.targetSegments req.target)
        && true) = true
    rw [hg]
    rfl)

/-! ## 5. The four app answers -/

/-- **The catch-all `404` app answer.** A request that misses every author route,
misses the glob and `/bulk` routes, and carries a non-vhost authority is answered
`404 "not found"` — the whole deployed decision chain. -/
theorem appHandler_notFound (c : Ctx)
    (hnh : Reactor.App.targetSegments c.req.target ≠ ["health"])
    (hns : List.isPrefixOf ["static"] (Reactor.App.targetSegments c.req.target) = false)
    (hnc : List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments c.req.target) = false)
    (hng : RouteAdvanced.pathMatch globPathPat (Reactor.App.targetSegments c.req.target) = false)
    (hnbk : RouteAdvanced.pathMatch bulkPathPat (Reactor.App.targetSegments c.req.target) = false)
    (hna : Reactor.App.hostLabelsOf c.req ≠ ["a", "example"])
    (hnb : Reactor.App.hostLabelsOf c.req ≠ ["b", "example"]) :
    appHandler c = { status := 404, reason := Reactor.App.reasonFor 404,
                     headers := [], body := notFoundBody } := by
  unfold appHandler Reactor.App.handle
  rw [bestMatch_demo_default _ hnh hns hnc]
  show (match RouteAdvanced.dispatch Reactor.App.demoVhBlocks (Reactor.App.hostReqOf c.req) with
        | some rt => Reactor.App.vhandlerResponse c.req rt.handler
        | none => Reactor.App.vhandlerResponse c.req
            (Reactor.App.VHandler.respond 404 "not found".toUTF8.toList)) = _
  rw [dispatch_demo_catchAll c.req hng hnbk hna hnb]
  rfl

/-- **The `a.example` app answer**: `200 "vhost-a"`. -/
theorem appHandler_vhostA (c : Ctx)
    (hnh : Reactor.App.targetSegments c.req.target ≠ ["health"])
    (hns : List.isPrefixOf ["static"] (Reactor.App.targetSegments c.req.target) = false)
    (hnc : List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments c.req.target) = false)
    (hva : Reactor.App.hostLabelsOf c.req = ["a", "example"]) :
    appHandler c = { status := 200, reason := Reactor.App.reasonFor 200,
                     headers := [], body := vhostABody } := by
  unfold appHandler Reactor.App.handle
  rw [bestMatch_demo_default _ hnh hns hnc]
  show (match RouteAdvanced.dispatch Reactor.App.demoVhBlocks (Reactor.App.hostReqOf c.req) with
        | some rt => Reactor.App.vhandlerResponse c.req rt.handler
        | none => Reactor.App.vhandlerResponse c.req
            (Reactor.App.VHandler.respond 404 "not found".toUTF8.toList)) = _
  rw [dispatch_demo_a c.req hva]
  rfl

/-- **The `b.example` app answer**: `200 "vhost-b"`. -/
theorem appHandler_vhostB (c : Ctx)
    (hnh : Reactor.App.targetSegments c.req.target ≠ ["health"])
    (hns : List.isPrefixOf ["static"] (Reactor.App.targetSegments c.req.target) = false)
    (hnc : List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments c.req.target) = false)
    (hvb : Reactor.App.hostLabelsOf c.req = ["b", "example"]) :
    appHandler c = { status := 200, reason := Reactor.App.reasonFor 200,
                     headers := [], body := vhostBBody } := by
  unfold appHandler Reactor.App.handle
  rw [bestMatch_demo_default _ hnh hns hnc]
  show (match RouteAdvanced.dispatch Reactor.App.demoVhBlocks (Reactor.App.hostReqOf c.req) with
        | some rt => Reactor.App.vhandlerResponse c.req rt.handler
        | none => Reactor.App.vhandlerResponse c.req
            (Reactor.App.VHandler.respond 404 "not found".toUTF8.toList)) = _
  rw [dispatch_demo_b c.req hvb]
  rfl

/-- **The glob-route app answer**: `200 "glob-hit"`. -/
theorem appHandler_glob (c : Ctx)
    (hnh : Reactor.App.targetSegments c.req.target ≠ ["health"])
    (hns : List.isPrefixOf ["static"] (Reactor.App.targetSegments c.req.target) = false)
    (hnc : List.isPrefixOf ["cgi-bin"] (Reactor.App.targetSegments c.req.target) = false)
    (hg : RouteAdvanced.pathMatch globPathPat (Reactor.App.targetSegments c.req.target) = true)
    (hna : Reactor.App.hostLabelsOf c.req ≠ ["a", "example"])
    (hnb : Reactor.App.hostLabelsOf c.req ≠ ["b", "example"]) :
    appHandler c = { status := 200, reason := Reactor.App.reasonFor 200,
                     headers := [], body := globBody } := by
  unfold appHandler Reactor.App.handle
  rw [bestMatch_demo_default _ hnh hns hnc]
  show (match RouteAdvanced.dispatch Reactor.App.demoVhBlocks (Reactor.App.hostReqOf c.req) with
        | some rt => Reactor.App.vhandlerResponse c.req rt.handler
        | none => Reactor.App.vhandlerResponse c.req
            (Reactor.App.VHandler.respond 404 "not found".toUTF8.toList)) = _
  rw [dispatch_demo_glob c.req hg hna hnb]
  rfl

/-! ## 6. The `x-upstream` scalar is ONE constant on every dispatch

The deployed proxy table routes EVERY path to the same pool (a `prefix []`
catch-all reverse-proxy route), so the deployed plan value never depends on the
request at all — it is a single top-level constant, computed once at module
initialization. This subsumes the per-route collapses (`uv_arm`, `uv_health`):
no new arm ever needs its own plan constant. -/

/-- The deployed proxy route wins `bestMatch` for EVERY segment list (the table's
only author route is a `prefix []` catch-all; no exact route precedes it). -/
theorem demoProxy_bestMatch_any (segs : List String) :
    Route.Match.bestMatch Reactor.ProxyServe.demoProxyApp.table segs
      = some Reactor.ProxyServe.demoProxyRoute := by
  simp only [Reactor.ProxyServe.demoProxyApp, Reactor.App.AppConfig.table, List.cons_append,
    List.nil_append, Route.Match.bestMatch, List.find?, Route.Match.matchesExact,
    Route.Match.matchesPrefix, Reactor.ProxyServe.demoProxyRoute, List.isPrefixOf]

/-- The segment-keyed proxy routing is CONSTANT in the segments. -/
theorem routeProxySegs_demo_const (segs : List String) :
    Datapath.ServeDenseIdx.routeProxySegs Reactor.ProxyServe.demoProxyApp
        Reactor.Proxy.demoCtx segs
      = Datapath.ServeDenseIdx.routeProxySegs Reactor.ProxyServe.demoProxyApp
          Reactor.Proxy.demoCtx [] := by
  unfold Datapath.ServeDenseIdx.routeProxySegs
  rw [demoProxy_bestMatch_any segs, demoProxy_bestMatch_any []]

/-- **The deployed `x-upstream` value — a single top-level constant.** -/
def uvDefault : Header.Value :=
  upstreamVal (Reactor.DnsWire.resolveSubs Reactor.DnsWire.demoResolver
    (Datapath.ServeDenseIdx.routeProxySegs Reactor.ProxyServe.demoProxyApp
      Reactor.Proxy.demoCtx []))

/-- **`x-upstream` collapses to `uvDefault` on EVERY dispatched request** — the
proxy reads only the first dispatch, the router's answer is segment-independent
(`routeProxySegs_demo_const`), and the LB ignores the request. -/
theorem uv_dispatch (l : Bytes) (req : Proto.Request) (rest : List Reactor.RingSubmission)
    (hsub : deploySubs l = .dispatch req :: rest) :
    upstreamVal (deployPlan (deploySubs l)) = uvDefault := by
  rw [hsub]
  unfold Reactor.Deploy.deployPlan
  rw [Reactor.ProxyServe.serveProxyOn_dispatch, Datapath.ServeDenseIdx.routeProxy_eq_segs,
    routeProxySegs_demo_const]
  rfl

/-! ## 7. The generic constant-body arm byte-identity -/

open Datapath.DenseHead (renderHead denseHeadersBlock serialize_eq_head_body
  renderHead_eq_headBytes)

/-- **The constant-body dense arm equals the deployed serve** — for ANY admitted
(all eight gates passing) app answer `{st, rs, [], bd}` whose body the
html-rewrite fixes: the dense (head ++ dense-body) output is byte-identical to
`servePipelineFull2`. `builtScalarsGen` + `denseHeadersUnknown` + `denseOutGen`,
the `/health` arm's proof freed from its route so each off-arm route is ONE
instantiation. -/
theorem constArm_eq (input : Bytes) (st : Nat) (rs bd : Bytes) (bA : ByteArray)
    (hbA : bA.data.toList = bd)
    (hadmin : isAdminPath (ctxOf input).req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath (ctxOf input).req = false)
    (hrate : Reactor.Stage.Rate.admits (ctxOf input) = true)
    (hredir : ¬ ((ctxOf input).req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes (ctxOf input).req = false)
    (hpol : policyReserved (ctxOf input).req = false)
    (hgz : Reactor.Stage.Gzip.acceptsGzip (ctxOf input).req = false)
    (hcors : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf (ctxOf input))
        = none)
    (happ : appHandler (ctxOf input)
        = { status := st, reason := rs, headers := [], body := bd })
    (hfix : Reactor.Stage.HtmlRewrite.rewriteBytes bd = bd) :
    ByteArray.mk (renderHead st rs
        (denseHeadersBlock [] (upstreamVal (deployPlan (deploySubs input)))
          (corrVal input)).denote bd.length).toArray ++ bA
      = ByteArray.mk (servePipelineFull2 input).toArray := by
  have hip : (ctxOf input).attrs.find?
      (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none := rfl
  obtain ⟨hst, hrs, hbd⟩ :=
    Datapath.ServeDenseIdx.builtScalarsGen (ctxOf input) st rs bd
      hadmin hpriv hip hrate hredir htrav hpol hgz hcors happ hfix
  have hserve : servePipelineFull2 input
      = Reactor.serialize
          ((runPipeline deployStagesFull2 appHandler (ctxOf input)).build) := rfl
  have hhdr := Datapath.ServeDenseReal.denseHeadersUnknown (ctxOf input)
    hadmin hpriv hip hrate hredir htrav hpol hgz hcors
  rw [hserve, serialize_eq_head_body
        ((runPipeline deployStagesFull2 appHandler (ctxOf input)).build)]
  rw [← renderHead_eq_headBytes
        ((runPipeline deployStagesFull2 appHandler (ctxOf input)).build)]
  rw [hst, hrs, hbd]
  have hAheaders : (appHandler (ctxOf input)).headers = [] := by rw [happ]
  rw [show ((runPipeline deployStagesFull2 appHandler (ctxOf input)).build).headers
        = (denseHeadersBlock [] (upstreamVal (deployPlan (deploySubs (ctxOf input).input)))
            (corrVal (ctxOf input).input)).denote from by rw [← hhdr, hAheaders]]
  show ByteArray.mk (renderHead st rs
        (denseHeadersBlock [] (upstreamVal (deployPlan (deploySubs input)))
          (corrVal input)).denote bd.length).toArray ++ bA
    = ByteArray.mk ((renderHead st rs
        (denseHeadersBlock [] (upstreamVal (deployPlan (deploySubs input)))
          (corrVal input)).denote bd.length) ++ bd).toArray
  exact Datapath.ServeDenseIdx.denseOutGen _ bA bd hbA

/-! ## 8. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms bestMatch_demo_default
#print axioms dispatch_demo_catchAll
#print axioms appHandler_notFound
#print axioms appHandler_vhostA
#print axioms appHandler_vhostB
#print axioms appHandler_glob
#print axioms uv_dispatch
#print axioms constArm_eq

end Datapath.OffarmApp
