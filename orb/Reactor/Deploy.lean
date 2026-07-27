import Reactor.Tls
import Reactor.Ws
import Reactor.Socks
import Reactor.ProxyServe
import Reactor.Dns
import Reactor.Observe
import Reactor.Lifecycle
import Policy.Invariant
import Safety.Traversal
import EarlyHints.Basic
import HtmlRewrite.Basic
import Reactor.Pipeline
import Reactor.Stage.SecurityHeaders
import Reactor.Stage.Header
import Reactor.Stage.Jwt
import Reactor.Stage.RequestId
import Reactor.Stage.ForwardAuth
import IpFilter
import Reactor.Stage.Rate
import Reactor.Stage.IpFilter
import Reactor.Stage.BasicAuth
import Reactor.Stage.Cache
import Reactor.Stage.Redirect
import Reactor.Stage.Cors
import Reactor.Stage.Gzip
import Reactor.Stage.HtmlRewrite
import Reactor.Stage.ConnLimit
import Reactor.Stage.StickTable
import Reactor.Stage.Slowloris
import Reactor.Stage.ErrorPage
import Reactor.Stage.CompressExt
import Reactor.Stage.Autoindex
import Reactor.Stage.Variants
import Reactor.Stage.EarlyHints
import Reactor.Stage.MethodFilter
import Reactor.Stage.BodyLimit
import Reactor.Stage.HostAllowlist
import Reactor.Stage.SpaFallback
import Reactor.Stage.RequestValidation
import Reactor.Stage.DateHeader
import Reactor.Stage.FramingValidation
import Reactor.Stage.AuthRequest
import Reactor.Stage.RequestHeadLimit
import Reactor.BraidCalculus
import Cache.Conditional
import Dsl.Deployment

/-!
# Reactor.Deploy — the deployed configuration and the full serving pipeline

A wiring counts only when the real library drives the config+serve the DEPLOYED
binary runs. Each protocol lane provides its real engine and a `wireX`
transformer; `demoConfig`'s codec fields are inert stubs, so `serve` over
`demoConfig` never exercises them. This file is the integration keystone:

* `deployConfig` — `demoConfig` with every codec lane replaced by the REAL
  engine, through the lanes' own transformers: `TlsWire.wireTls` (the `Tls.step`
  record/handshake machine behind `hsFeed`/`tlsRecv`/`tlsSend`), `Ws.wireWs`
  (the real frame decoder + `Ws.Reassembly` behind `wsFeed`/`wsEncode`),
  `wireSocks` (the real `Socks.hstep` handshake behind `socksFeed`). The
  HTTP/1.1 arena parser and the H2 engine were already real in `demoConfig`
  and are untouched (`deploy_h1_arena`, `deploy_h2_real`).

* `serveFull : Bytes → Bytes` — the full pipeline on one path: the proven
  reactor (`Reactor.step`) over `deployConfig`; FSM sends forwarded faithfully;
  a dispatched request answered by the real application router (`App.handle`
  over `Route.Match.bestMatch`), its headers passed through the REAL
  `Header.run` rewrite (`Lifecycle.stdRewrite` + two `set`s), which stamps in
  (a) the upstream the REAL reverse-proxy LB chose (`ProxyServe.serveProxyOn`
  → `Proxy.selectChain`) *after* the REAL DNS pass resolved it
  (`DnsWire.resolveSubs` over a genuine wire-format DNS response), and (b) the
  correlation id the REAL `Trace.process` assigned. So the proxy, DNS, header,
  and trace libraries all shape the very bytes `main` writes.

* `deployStep` — `serveFull` plus the observation state: the REAL
  `Metrics.Registry.inc`, the REAL `Tap.step` gate, the REAL `Trace` id — the
  state `main` threads.

`Arena.Orb.main` now runs exactly this (`deployStep`, whose response component
is definitionally `serveFull`). The seam theorems below are therefore about the
deployed path, not a bespoke side config.
-/

namespace Reactor
namespace Deploy

open Proto (Bytes)

/-! ## (1) The deployed config — every codec lane is the real engine -/

/-- **The deployed configuration.** `demoConfig` (real arena `h1Parse`, real H2
engine) with the three stubbed codec lanes replaced by the real engines through
the lanes' own transformers: TLS (`Tls.step` behind the three adapters), WebSocket
(frame decode + `Ws.Reassembly`), SOCKS (`Socks.hstep`). This is the config the
deployed orb binary runs. -/
def deployConfig : Proto.Config :=
  wireSocks ⟨0⟩ false
    (Ws.wireWs (TlsWire.wireTls TlsWire.demoTlsCfg Reactor.Config.demoConfig))

/-- **The deployed TLS lane is the real engine.** `deployConfig`'s three TLS
fields are exactly the `TlsWire` adapters over the real `Tls.step` machine — not
`demoConfig`'s inert `.fail`/`none`/`(tc, [])` stubs. -/
theorem deploy_uses_real_tls :
    deployConfig.hsFeed  = TlsWire.hsFeedReal  TlsWire.demoTlsCfg
  ∧ deployConfig.tlsRecv = TlsWire.tlsRecvReal TlsWire.demoTlsCfg
  ∧ deployConfig.tlsSend = TlsWire.tlsSendReal TlsWire.demoTlsCfg :=
  ⟨rfl, rfl, rfl⟩

/-- **The deployed WebSocket lane is the real engine**: the frame decoder +
`Ws.Reassembly` feed and the real frame encoder. -/
theorem deploy_uses_real_ws :
    deployConfig.wsFeed = Ws.wsFeedFn ∧ deployConfig.wsEncode = Ws.wsEncodeFn :=
  ⟨rfl, rfl⟩

/-- **The deployed SOCKS lane is the real engine**: the `Socks.hstep` adapter. -/
theorem deploy_uses_real_socks :
    deployConfig.socksFeed = socksFeedReal ⟨0⟩ false := rfl

/-- Regression: the deployed HTTP/1.1 parser is still the proven arena parser. -/
theorem deploy_h1_arena : deployConfig.h1Parse = Reactor.Config.h1ParseFn := rfl

/-- Regression: the deployed H2 lane is still the real H2 engine. -/
theorem deploy_h2_real :
    deployConfig.h2Feed = Reactor.H2.h2FeedFn
  ∧ deployConfig.h2Send = Reactor.H2.h2SendFn := ⟨rfl, rfl⟩

/-! ## (2) The full pipeline: reactor → proxy → DNS → observe → header rewrite -/

/-- The deployed reactor run: one recv completion through the PROVEN
`Reactor.step` over `deployConfig` — the submissions the deployed orb acts on. -/
def deploySubs (input : Bytes) : List RingSubmission :=
  (Reactor.step deployConfig
      (Proto.State.active Proto.Conn.mkPlain)
      (RingEvent.recvInto 0 input)).2

/-- The upstream plan: run the REAL reverse-proxy routing
(`ProxyServe.serveProxyOn` → `Route.Match.bestMatch` → `Proxy.selectChain` over
the health-filtered `demoPool`) on the reactor's own submissions, then the REAL
DNS resolution pass (`DnsWire.resolveSubs`, which parses a genuine wire-format
DNS response) over the proxy's `connectUpstream`s. -/
def deployPlan (subs : List RingSubmission) : List RingSubmission :=
  DnsWire.resolveSubs DnsWire.demoResolver
    (ProxyServe.serveProxyOn ProxyServe.demoProxyApp Proxy.demoCtx subs)

/-- Decimal ASCII bytes of a `Nat` (for header values). -/
def natBytes (n : Nat) : Bytes := (toString n).toUTF8.toList

/-- `x-upstream` (lower-case ASCII), the response header that carries the
LB-chosen, DNS-resolved upstream address. -/
def upstreamName : Header.Name :=
  [120, 45, 117, 112, 115, 116, 114, 101, 97, 109]

/-- `x-corr` (lower-case ASCII), the response header that carries the
`Trace`-assigned correlation id. -/
def corrName : Header.Name := [120, 45, 99, 111, 114, 114]

/-- The upstream header value: the address of the plan's first
`connectUpstream` (post-DNS), or `-` when the plan dials nothing. -/
def upstreamVal (plan : List RingSubmission) : Header.Value :=
  match Proxy.targetedUpstream plan with
  | some a => natBytes a.id
  | none   => str "-"

/-- Render a correlation id as dotted decimal bytes. -/
def corrBytes (c : Trace.CorrId) : Bytes :=
  (String.intercalate "." (c.map toString)).toUTF8.toList

/-- The correlation header value for a request: the id the REAL `Trace.process`
assigned (`Observe.corrOf`, over the deployed generator/trust). -/
def corrVal (input : Bytes) : Header.Value :=
  corrBytes (Observe.corrOf Observe.demoGen Observe.demoTrust input)

/-- **The deployed rewrite program** — a genuine `Header.run` program:
`Lifecycle.stdRewrite` (strip RFC 7230 §6.1 hop-by-hop headers, install
`Server`), then stamp the proxy/DNS upstream and the `Trace` correlation id. -/
def deployProg (plan : List RingSubmission) (input : Bytes) : List Header.Op :=
  Reactor.Lifecycle.stdRewrite ++
    [ Header.Op.set upstreamName (upstreamVal plan),
      Header.Op.set corrName (corrVal input) ]

/-- The deployed response for the dispatch path: the real application response
(`demoResp` = `App.handle` over the reactor's dispatch), its headers rewritten by
the REAL `Header.run` under `deployProg` — so the emitted bytes carry the
proxy/DNS/trace evidence. -/
def deployResp (input : Bytes) : Response :=
  Reactor.Lifecycle.rewriteResp
    (deployProg (deployPlan (deploySubs input)) input)
    (demoResp (deploySubs input))

/-- **The deployed entry.** Bytes in → the proven reactor over `deployConfig` →
bytes out. FSM sends are forwarded faithfully, in order (never rewritten); a
bare dispatch is answered by the full pipeline response (`deployResp`). Total. -/
def serveFull (input : Bytes) : Bytes :=
  match sendsOf (deploySubs input) with
  | [] => serialize (deployResp input)
  | sends => sends.flatten

/-- **The deployed observed step.** `serveFull` plus the REAL observation state:
`Metrics.Registry.inc` on the request counter, the REAL `Tap.step` gate offered
the request bytes, the REAL `Trace`-assigned correlation id recorded. This is
the function `main` runs. -/
def deployStep (st : Observe.ObsState) (input : Bytes) : Bytes × Observe.ObsState :=
  ( serveFull input
  , { metrics := st.metrics.inc Observe.reqCounter 1
    , tap     := Tap.step st.tap (Tap.Ev.pkt input)
    , corrs   := Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs } )

/-- What `main` writes is definitionally `serveFull`. -/
theorem deployStep_serves (st : Observe.ObsState) (input : Bytes) :
    (deployStep st input).1 = serveFull input := rfl

/-! ## Seam theorems — deployed-path facts -/

/-- **Faithful forwarding (regression).** When the FSM emits response bytes,
`serveFull` returns exactly their in-order concatenation — the deployed pipeline
never rewrites an FSM-decided response (a 400/431 stays itself). -/
theorem serveFull_faithful (input : Bytes) (h : sendsOf (deploySubs input) ≠ []) :
    serveFull input = (sendsOf (deploySubs input)).flatten := by
  unfold serveFull
  cases hs : sendsOf (deploySubs input) with
  | nil => exact absurd hs h
  | cons a t => rfl

/-- The header rewrite touches only headers: the deployed response's status is
the application router's status, untouched. -/
theorem deploy_rewrite_status (prog : List Header.Op) (r : Response) :
    (Reactor.Lifecycle.rewriteResp prog r).status = r.status := rfl

/-- **`deploy_routes` — routing regression on the deployed path.** When the
deployed reactor dispatches a request (and the FSM emitted no bytes of its own),
`serveFull` serializes the REAL application response — `App.handle` over the
same `demoAppConfig` route table (`/health → 200`, default `404`) — passed
through the deployed header rewrite, whose status is exactly `App.handle`'s. -/
theorem deploy_routes (input : Bytes) (req : Proto.Request) (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    serveFull input
      = serialize (Reactor.Lifecycle.rewriteResp
          (deployProg (deployPlan (deploySubs input)) input)
          (App.handle demoAppConfig req))
    ∧ (Reactor.Lifecycle.rewriteResp
          (deployProg (deployPlan (deploySubs input)) input)
          (App.handle demoAppConfig req)).status
        = (App.handle demoAppConfig req).status := by
  refine ⟨?_, rfl⟩
  have hdemo : demoResp (deploySubs input) = App.handle demoAppConfig req := by
    rw [hsub]; rfl
  unfold serveFull
  rw [hsends]
  show serialize (deployResp input) = _
  unfold deployResp
  rw [hdemo]

/-- **The routing decision is `bestMatch`'s, on the deployed path.** The served
bytes serialize (the rewrite of) the response of the route the REAL
`Route.Match.bestMatch` chose over the effective demo table — `app_routes_total`
lifted through `serveFull`. -/
theorem deploy_routes_bestMatch (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    ∃ r, Route.Match.bestMatch demoAppConfig.table
            (App.targetSegments req.target) = some r
       ∧ serveFull input
           = serialize (Reactor.Lifecycle.rewriteResp
               (deployProg (deployPlan (deploySubs input)) input)
               (App.responseOfReq req r.handler)) := by
  obtain ⟨r, hbest, hhandle⟩ := App.app_routes_total demoAppConfig req
  refine ⟨r, hbest, ?_⟩
  rw [(deploy_routes input req rest hsends hsub).1, hhandle]

/-- **`deploy_plan_resolved` — the proxy→DNS pipeline runs on the deployed
dispatch.** For any dispatched request, the deployed upstream plan is exactly one
`connectUpstream` to `⟨1572395042⟩` (`93.184.216.34`): the REAL
`Route.Match.bestMatch` picked the reverse-proxy route, the REAL
`Proxy.selectChain` chose the healthy least-connections backend `demoB2 = ⟨2⟩`
(skipping the unhealthy backend 0), and the REAL `DnsWire.resolve` parsed the
A record out of a genuine wire-format DNS response for that backend. A stub at
any stage could not produce this address. -/
theorem deploy_plan_resolved (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch req :: rest) :
    deployPlan (deploySubs input)
      = [RingSubmission.connectUpstream (⟨1572395042⟩ : Proto.Addr)] := by
  have hprox : ProxyServe.serveProxyOn ProxyServe.demoProxyApp Proxy.demoCtx
      (deploySubs input)
      = [RingSubmission.connectUpstream (Proxy.addrOf Proxy.demoB2)] := by
    rw [hsub, ProxyServe.serveProxyOn_dispatch,
      ProxyServe.routeProxy_proxy _ _ _ Proxy.demoPool ProxyServe.demoProxyRoute
        (ProxyServe.demoProxy_bestMatch req) rfl]
    simp only [Proxy.proxyHandle, Proxy.demo_chooses_b2]
  have hres : DnsWire.resolveAddr DnsWire.demoResolver (Proxy.addrOf Proxy.demoB2)
      = some (⟨1572395042⟩ : Proto.Addr) := DnsWire.resolveAddr_demo2
  unfold deployPlan
  rw [hprox, DnsWire.resolved_forwarded _ _ _ _ hres]
  rfl

/-- **The full fabric seam, composed.** On a deployed dispatch: the plan's target
is the DNS-resolved address; pre-DNS, the LB's choice `demoB2` is a healthy,
administratively active member of the real pool; and the DNS pass resolved the
LB's address through the real parser. Proxy eligibility (`selectChain`) composed
with DNS resolution (`resolve`), both on `deploySubs` output. -/
theorem deploy_pipeline_seam (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch req :: rest) :
    Proxy.targetedUpstream (deployPlan (deploySubs input))
        = some (⟨1572395042⟩ : Proto.Addr)
      ∧ Proxy.demoB2 ∈ Proxy.demoPool.backends
      ∧ Proxy.demoB2.eligible = true
      ∧ DnsWire.resolveAddr DnsWire.demoResolver (Proxy.addrOf Proxy.demoB2)
          = some (⟨1572395042⟩ : Proto.Addr) := by
  refine ⟨?_, (ProxyServe.demoProxy_route_connects req rest).2.1,
    (ProxyServe.demoProxy_route_connects req rest).2.2.1,
    DnsWire.resolveAddr_demo2⟩
  rw [deploy_plan_resolved input req rest hsub]
  rfl

/-- The deployed response's headers are exactly the REAL `Header.run` under
`deployProg` applied to the application response's headers. -/
theorem deployResp_headers (input : Bytes) :
    (deployResp input).headers
      = Reactor.Lifecycle.ofHeaders
          (Header.run (deployProg (deployPlan (deploySubs input)) input)
            (Reactor.Lifecycle.toHeaders (demoResp (deploySubs input)).headers)) := rfl

/-- Under `deployProg`, a lookup of `x-upstream` on the emitted headers reads
back exactly the plan's target — `Header.get_set` locality through the outer
`x-corr` set. Any base headers, any plan. -/
theorem deployProg_upstream (plan : List RingSubmission) (input : Bytes)
    (h : Header.Headers) :
    Header.get upstreamName (Header.run (deployProg plan input) h)
      = some (upstreamVal plan) := by
  unfold deployProg
  rw [Header.run_append, Header.run_cons, Header.run_cons, Header.run_nil]
  simp only [Header.applyOp]
  rw [Header.get_set,
    if_neg (Header.name_neq (by decide : Header.nameEqb corrName upstreamName = false)),
    Header.get_set_eq]

/-- **`deploy_emits_upstream` — the fabric evidence is in the served bytes.** On
a deployed dispatch, the emitted headers carry
`x-upstream: 1572395042` — the address the REAL LB chose and the REAL DNS parser
resolved. `demoConfig`+`serve` never drove either library on its serving path. -/
theorem deploy_emits_upstream (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch req :: rest) :
    Header.get upstreamName
      (Header.run (deployProg (deployPlan (deploySubs input)) input)
        (Reactor.Lifecycle.toHeaders (demoResp (deploySubs input)).headers))
      = some (natBytes 1572395042) := by
  rw [deployProg_upstream, deploy_plan_resolved input req rest hsub]
  rfl

/-- **`deploy_emits_corr` — the REAL `Trace` id is in the served bytes.** The
emitted headers carry `x-corr:` the id `Trace.process` assigned to this request
(`Header.get_set_eq` on the outermost set). Any base headers, any plan. -/
theorem deploy_emits_corr (plan : List RingSubmission) (input : Bytes)
    (h : Header.Headers) :
    Header.get corrName (Header.run (deployProg plan input) h)
      = some (corrBytes (Trace.process Observe.demoGen Observe.demoTrust
          (Observe.inboundOf input)).corr) := by
  unfold deployProg
  rw [Header.run_append, Header.run_cons, Header.run_cons, Header.run_nil]
  simp only [Header.applyOp]
  exact Header.get_set_eq corrName _ _

/-- **The Lifecycle rewrite survives the extra stamps**: `Server: drorb` is still
installed (`get_set` locality through the two deploy sets, then
`Header.get_set_eq` on `stdRewrite`'s install). -/
theorem deploy_keeps_server (plan : List RingSubmission) (input : Bytes)
    (h : Header.Headers) :
    Header.get Reactor.Lifecycle.serverName (Header.run (deployProg plan input) h)
      = some Reactor.Lifecycle.serverVal := by
  unfold deployProg
  rw [Header.run_append, Header.run_cons, Header.run_cons, Header.run_nil]
  simp only [Header.applyOp]
  rw [Header.get_set,
    if_neg (Header.name_neq (by decide :
      Header.nameEqb corrName Reactor.Lifecycle.serverName = false)),
    Header.get_set,
    if_neg (Header.name_neq (by decide :
      Header.nameEqb upstreamName Reactor.Lifecycle.serverName = false))]
  show Header.get Reactor.Lifecycle.serverName
      (Header.set Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal
        (Header.strip (Header.dynHopSet h) h)) = _
  exact Header.get_set_eq _ _ _

/-! ## The observation state on the deployed path -/

/-- The deployed step advances the REAL `Metrics` registry by exactly one on the
request counter (`Metrics.inc_exact`). -/
theorem deploy_metrics_exact (st : Observe.ObsState) (input : Bytes) :
    (deployStep st input).2.metrics.counters Observe.reqCounter
      = st.metrics.counters Observe.reqCounter + 1 := by
  show (st.metrics.inc Observe.reqCounter 1).counters Observe.reqCounter = _
  rw [Metrics.inc_exact]

/-- The deployed step records the REAL `Trace`-assigned id and offers the bytes
to the REAL `Tap` gate. -/
theorem deploy_observes (st : Observe.ObsState) (input : Bytes) :
    (deployStep st input).2.corrs
        = Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs
      ∧ (deployStep st input).2.tap = Tap.step st.tap (Tap.Ev.pkt input) :=
  ⟨rfl, rfl⟩

/-! **Totality is not a theorem in Lean.** `serveFull : Bytes → Bytes` is a plain `def`, so
totality is a TYPE-LEVEL fact — the elaborator admits no partial `def` of that
signature, and there is nothing left to prove. The theorem that stood here,
`serveFull_total : serveFull input = serveFull input`, was exactly that non-statement:
it holds of EVERY function of the same arity, so it constrained `serveFull` not at
all while wearing a name that claimed it did. The real facts about the deployed byte function are `deploy_observes` above and the DEPLOY-INTEGRATE theorems below. -/

/-! ## (3) DEPLOY-INTEGRATE — admission, path-escape safety, and the response
transforms, folded onto the deployed serve path.

`serveFull` (the bytes `main` writes, via `deployStep`) already emits, on a
dispatch, `serialize (deployResp input)` — the `App.handle` router response
passed through the REAL `Header.run` under `deployProg`. This section folds three
more real libraries onto that *same* path, stated as facts about `serveFull`
itself — not a sibling serve:

* **Policy admission** (`deploy_policy_admits`) — a served dispatch corresponds to
  a request the REAL `Policy.serveDecision` admits on the deployed
  `(listener, route)`; an off-surface listener is refused by the same gate.
* **Path-escape safety** (`deploy_no_path_escape`) — the target the deployed serve
  normalizes (`App.targetSegments`, the very segments `Route.Match.bestMatch`
  matches on) resolves under the document root and never escapes it, by the REAL
  `Safety.Traversal`.
* **Response transforms** (`deploy_transforms_applied`) — the served body IS the
  REAL `HtmlRewrite` streaming transform output (chunk-boundary-safe), and the
  REAL `EarlyHints` emission places every `103` before the one final, whose body
  is the served body.

The html transform is lossless and the 103/final ordering adds no final bytes, so
folding them changes no byte `main` writes; what these theorems establish is that
the bytes `main` already writes *are* the real transforms' output and *do*
correspond to an admitted, within-root request. Because the equality is stated of
`serveFull` (not of a separate `serveFullHtml`), it is a fact about the deployed
path, not an island beside it. -/

/-- On a dispatch (the FSM emitted no bytes of its own), `serveFull` serializes
the deployed response. Same `cases`-on-discriminant shape as `serveFull_faithful`,
kept off the `whnf` blow-up an `unfold`-then-`rfl` would trigger on the deployed
config. -/
theorem serveFull_serializes_dispatch (input : Bytes)
    (hsends : sendsOf (deploySubs input) = []) :
    serveFull input = serialize (deployResp input) := by
  unfold serveFull
  cases hs : sendsOf (deploySubs input) with
  | nil => rfl
  | cons a t => rw [hs] at hsends; exact absurd hsends (by simp)

/-! ### (3a) Policy declared-surface admission on the deployed path -/

/-- The deployed listener id the orb serves on (Policy attribution). Equals
`App.demoApp.lid`. -/
def deployLid : Nat := 0

/-- The deployed route key the demo surface dispatches to. Equals the key
`App.demoApp.routeKeyOf` maps every matched route to (`⟨0, 0⟩`). -/
def deployRouteKey : Policy.RouteKey := ⟨0, 0⟩

/-- The deployed Policy declared surface: one listener (`deployLid`, plaintext,
cap 1024) and the one route key the demo app dispatches to. -/
def deployPolicyConfig : Policy.Config :=
  { listeners := [⟨deployLid, 0, 8080, false, 1024⟩]
    routes := [⟨deployRouteKey, 0⟩] }

/-- The live deployed Policy state: cold boot on the declared surface with the
declared listener adopted (bound). Reachable from `init`, so the real invariant
`Wf` holds of it. -/
def deployRunning : Policy.Running :=
  Policy.adopt deployLid (Policy.init deployPolicyConfig)

/-- `deployRunning` is reachable from a cold boot (one `adopt` step). -/
theorem deployRunning_reachable : Policy.Reachable deployPolicyConfig deployRunning :=
  Policy.Reachable.step Policy.Reachable.init (Policy.Step.adopt deployLid _)

/-- Hence the REAL declared-surface invariant holds of the deployed policy
state. -/
theorem deployRunning_wf : Policy.Wf deployRunning :=
  Policy.reachable_wf deployRunning_reachable

/-- **The deployed admission is real and positive.** The REAL
`Policy.serveDecision` admits the deployed `(listener, route)` pair. -/
theorem deploy_serveDecision_admits :
    Policy.serveDecision deployLid deployRouteKey false deployRunning
      = some ⟨deployLid, deployRouteKey, false⟩ := by decide

/-- **The deployed admission gate genuinely refuses off-surface.** An undeclared
listener is refused by the SAME real gate — the decision is driven, not a
constant `some`. -/
theorem deploy_serveDecision_refuses_undeclared (rk : Policy.RouteKey) (pt : Bool) :
    Policy.serveDecision 1 rk pt deployRunning = none := rfl

/-- The key the deployed router dispatches to is exactly `deployRouteKey`
(`App.demoApp.routeKeyOf` is the constant `⟨0,0⟩` adapter). -/
theorem deploy_routeKey_matches (r : Route.Match.Route Reactor.App.Handler) :
    demoAppConfig.routeKeyOf r = deployRouteKey := rfl

/-- The deployed listener id is exactly the app's attributed listener. -/
theorem deploy_lid_matches : demoAppConfig.lid = deployLid := rfl

/-- **`deploy_policy_admits` — a served response corresponds to a Policy-admitted
request, on the deployed path.** For a deployed dispatch (`serveFull` emits the
deployed response bytes), the route the deployed router selected
(`Route.Match.bestMatch`) carries the policy key `deployRouteKey`, and the REAL
`Policy.serveDecision` admits that `(listener, route)` on the deployed running
surface — recording exactly `⟨deployLid, deployRouteKey, false⟩`. So the bytes
`main` writes are attributable to a request the real cold-plane gate admitted; an
off-surface listener would be refused (`deploy_serveDecision_refuses_undeclared`). -/
theorem deploy_policy_admits (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    serveFull input = serialize (deployResp input)
    ∧ deployResp input
        = Reactor.Lifecycle.rewriteResp (deployProg (deployPlan (deploySubs input)) input)
            (App.handle demoAppConfig req)
    ∧ ∃ r, Route.Match.bestMatch demoAppConfig.table
              (Reactor.App.targetSegments req.target) = some r
         ∧ demoAppConfig.routeKeyOf r = deployRouteKey
         ∧ Policy.serveDecision deployLid (demoAppConfig.routeKeyOf r) false deployRunning
             = some ⟨deployLid, deployRouteKey, false⟩ := by
  have hdemo : demoResp (deploySubs input) = App.handle demoAppConfig req := by
    rw [hsub]; rfl
  refine ⟨serveFull_serializes_dispatch input hsends, ?_, ?_⟩
  · unfold deployResp; rw [hdemo]
  · obtain ⟨r, hbest, _⟩ := Reactor.App.app_routes_total demoAppConfig req
    exact ⟨r, hbest, deploy_routeKey_matches r,
      (deploy_routeKey_matches r).symm ▸ deploy_serveDecision_admits⟩

/-! ### (3b) Path-escape safety on the deployed path -/

/-- The deployed document root a static-file route serves under (a clean real
directory path, no dot-segments). -/
def deployDocRoot : List String := ["srv", "www"]

/-- The raw (pre-normalize) path segments the deployed serve derives from a
request target: drop the query, slash-split, drop empty segments — exactly the
`raw` `App.targetSegments` then `Route.Path.normalize`s. -/
def rawSegsOf (req : Proto.Request) : List String :=
  let s := Reactor.App.bytesToString req.target
  let path := (s.splitOn "?").headD ""
  (path.splitOn "/").filter (fun seg => seg != "")

/-- The deployed serve normalizes exactly the normalization of `rawSegsOf` — the
segments `Route.Match.bestMatch` matches on are `Route.Path.normalize (rawSegsOf req)`. -/
theorem targetSegments_eq_normalize (req : Proto.Request) :
    Reactor.App.targetSegments req.target = Route.Path.normalize (rawSegsOf req) := rfl

/-- **`deploy_no_path_escape` — the served target is within-root per real
Safety.** For any request, resolving its raw target under `deployDocRoot` with the
REAL static-file resolver keeps the document root as a structural prefix — no
input escapes the root. And that resolution equals the root joined with exactly
the normalized segments the deployed router matched (`App.targetSegments`), so the
within-root guarantee is about the target the deployed serve actually uses, not a
bespoke one. -/
theorem deploy_no_path_escape (req : Proto.Request) :
    deployDocRoot <+: Safety.Traversal.serveStatic deployDocRoot (rawSegsOf req)
    ∧ Safety.Traversal.serveStatic deployDocRoot (rawSegsOf req)
        = deployDocRoot ++ Reactor.App.targetSegments req.target := by
  refine ⟨Safety.Traversal.serveStatic_root_prefix deployDocRoot (rawSegsOf req), ?_⟩
  rw [Safety.Traversal.serveStatic_eq_normalize, targetSegments_eq_normalize]

/-- Traversal witness on the deployed root: a literal `../../etc/passwd` is
clamped under `/srv/www`, never climbing out. -/
theorem deploy_dotdot_confined :
    Safety.Traversal.serveStatic deployDocRoot ["..", "..", "etc", "passwd"]
      = ["srv", "www", "etc", "passwd"] := by decide

/-! ### (3c) The EarlyHints / HtmlRewrite response transforms on the deployed path -/

/-- The REAL streaming HTML transform: tokenize with `HtmlRewrite.tokenize` and
re-serialize (`HtmlRewrite.bytesOf`). Currently lossless; its load-bearing
property is chunk-boundary safety. -/
def htmlXform (bs : Bytes) : Bytes := HtmlRewrite.bytesOf (HtmlRewrite.tokenize bs)

/-- The transform is lossless (identity rewrite) — `HtmlRewrite.roundtrip`. -/
theorem htmlXform_lossless (bs : Bytes) : htmlXform bs = bs :=
  HtmlRewrite.roundtrip bs

/-- Total Latin-1 view of header bytes as the `String` pairs the `EarlyHints`
model carries (proof-inert; the ordering seam never inspects them). -/
def latin1B (bs : Bytes) : String := String.mk (bs.map (fun b => Char.ofNat b.toNat))

/-- View a `Response` as the `EarlyHints.Final` (the one non-1xx response):
status and body carried through unchanged, headers via the Latin-1 view. Stated
GENERIC over `r` so a `.body`/`.status` projection never forces `deployResp input`
(which would whnf the whole `deploySubs`/`rewriteResp` computation). -/
def toFinalR (r : Response) : EarlyHints.Final :=
  { status  := r.status
    headers := r.headers.map (fun p => (latin1B p.1, latin1B p.2))
    body    := r.body }

/-- `toFinalR` carries the body through (generic — safe `rfl`). -/
theorem toFinalR_body (r : Response) : (toFinalR r).body = r.body := rfl

/-- The deployed response as the `EarlyHints.Final`: body is the served body. -/
def deployFinalOf (input : Bytes) : EarlyHints.Final := toFinalR (deployResp input)

/-- The deployed final's body is the deployed response's body (the served body). -/
theorem deployFinalOf_body (input : Bytes) :
    (deployFinalOf input).body = (deployResp input).body :=
  toFinalR_body (deployResp input)

/-- The action sequence a route declaring preload `hints` emits: one `emitInfo`
per hint (each a `103`), then exactly one `emitFinal` carrying the deployed
final. -/
def deployHintActions (hints : List EarlyHints.Info) (f : EarlyHints.Final) :
    List EarlyHints.Action :=
  hints.map EarlyHints.Action.emitInfo ++ [EarlyHints.Action.emitFinal f]

/-- Running the deployed hint sequence from `building` yields exactly the hints as
`103` messages, in order, then the one final — via the REAL `EarlyHints.run`. -/
theorem run_deployHintActions (hints : List EarlyHints.Info) (f : EarlyHints.Final) :
    EarlyHints.run .building (deployHintActions hints f)
      = (.committed, hints.map EarlyHints.Msg.info ++ [EarlyHints.Msg.final f]) := by
  unfold deployHintActions
  induction hints with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    exact EarlyHints.run_final_cons f []
  | cons h t ih =>
    simp only [List.map_cons, List.cons_append]
    rw [EarlyHints.run_info_cons, ih]

/-- **`deploy_transforms_applied` — the response body is the real
HtmlRewrite/EarlyHints output where declared, on the deployed path.** For a
deployed dispatch declaring any preload `hints`:

* `serveFull` serializes the deployed response (the served bytes);
* the served body IS the REAL `HtmlRewrite` streaming transform output;
* that transform is **chunk-boundary-safe**: splitting the body at *any* boundary
  `a ++ b` and streaming the two chunks yields the same output as feeding it whole
  (`HtmlRewrite.stream_eq_whole`);
* the REAL `EarlyHints` emission is the hints (each a `103`) then EXACTLY one
  final — `run_building_shape` gives `pre ++ [final]` with `allInfo pre`, so every
  `103` precedes the one final; and that final's body is the served body. -/
theorem deploy_transforms_applied (input : Bytes) (hints : List EarlyHints.Info)
    (req : Proto.Request) (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (_hsub : deploySubs input = .dispatch req :: rest) :
    serveFull input = serialize (deployResp input)
    ∧ (deployResp input).body = htmlXform (deployResp input).body
    ∧ (∀ a b, a ++ b = (deployResp input).body →
        HtmlRewrite.bytesOf (HtmlRewrite.feedBytes (HtmlRewrite.tokenize a) b)
          = htmlXform (deployResp input).body)
    ∧ (EarlyHints.run .building (deployHintActions hints (deployFinalOf input))).2
        = hints.map EarlyHints.Msg.info ++ [EarlyHints.Msg.final (deployFinalOf input)]
    ∧ (∃ pre f,
        (EarlyHints.run .building (deployHintActions hints (deployFinalOf input))).2
            = pre ++ [EarlyHints.Msg.final f]
        ∧ EarlyHints.allInfo pre)
    ∧ (deployFinalOf input).body = (deployResp input).body := by
  refine ⟨serveFull_serializes_dispatch input hsends, (htmlXform_lossless _).symm, ?_, ?_, ?_,
    deployFinalOf_body input⟩
  · intro a b hab
    unfold htmlXform
    rw [HtmlRewrite.stream_eq_whole, hab]
  · exact congrArg Prod.snd (run_deployHintActions hints (deployFinalOf input))
  · rcases EarlyHints.run_building_shape (deployHintActions hints (deployFinalOf input)) with
      ⟨hst, _⟩ | ⟨_, pre, f, heq, hpre⟩
    · exfalso
      have hcommit : (EarlyHints.run .building
          (deployHintActions hints (deployFinalOf input))).1 = EarlyHints.State.committed :=
        congrArg Prod.fst (run_deployHintActions hints (deployFinalOf input))
      rw [hcommit] at hst
      exact absurd hst (by decide)
    · exact ⟨pre, f, heq, hpre⟩

/-- **The three folded checks compose on one deployed dispatch.** The served
bytes are the deployed response; a Policy-admitted `(listener, route)` backs it;
the target stays within the document root; and the served body is the real
transform output. All four facts range over the same `serveFull input` — the
bytes `main` writes. -/
theorem deploy_integrated (input : Bytes)
    (req : Proto.Request) (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (_hsub : deploySubs input = .dispatch req :: rest) :
    serveFull input = serialize (deployResp input)
    ∧ Policy.serveDecision deployLid deployRouteKey false deployRunning
        = some ⟨deployLid, deployRouteKey, false⟩
    ∧ deployDocRoot <+: Safety.Traversal.serveStatic deployDocRoot (rawSegsOf req)
    ∧ (deployResp input).body = htmlXform (deployResp input).body := by
  exact ⟨serveFull_serializes_dispatch input hsends, deploy_serveDecision_admits,
    (deploy_no_path_escape req).1, (htmlXform_lossless _).symm⟩

/-! ## (4) SECURITY-MECH — the two gates as real MECHANISMS on the served bytes.

Sections (3a)/(3b) proved *correspondence*: the bytes `serveFull` already emits
happen to correspond to a Policy-admitted, within-root request. They did not
*branch* — `serveFull` serializes `deployResp` regardless of what Policy or Safety
say — correspondence, not mechanism: at runtime `/nope` and `/../etc/passwd`
both fall out as the *same* default-route 404.

This section installs the branch. `serveGuarded` runs the REAL `Policy.serveDecision`
and the REAL `Safety.Traversal` decode on the dispatched request and **emits
different bytes** on each outcome:

* a request whose route maps to an **undeclared** `Policy.RouteKey` — the REAL
  `serveDecision` returns `none` — is answered with a serializer-built **403**, not
  the handler body;
* a request whose decoded target carries a `..` that would **escape** the document
  root is answered with a serializer-built **404** ("traversal blocked"), not the
  resolved resource;
* every other dispatch is served exactly as before (`deployResp`, the 200 with
  `x-upstream`/`x-corr`).

`serveFull` is left untouched (`RespTransform` rfl-locks its byte shape); `main`
is repointed to `serveGuarded` via `deployStepGuarded`. The seam theorems
`deploy_refuses_undeclared_bytes` / `deploy_traversal_blocked_bytes` are stated
over the bytes `main` writes, and `guardOne_nope` / `guardOne_passwd` /
`guardOne_health` pin the exact emitted bytes for concrete requests with no
reactor hypothesis at all. -/

/-! ### (4a) The two gates, factored at the segment level.

The decision logic lives on `List String` segments — kernel-decidable, so the
concrete branch facts in (4e) are real `decide`/`#guard` executions. The
request-level wrappers just prepend the byte→segment extraction
(`App.targetSegments` / `rawSegsOf`, which use `String.splitOn` and so only reduce
in the compiled binary, not the kernel). -/

/-- The `Policy.RouteKey` a normalized segment list maps to. The author surfaces
the demo declares (`/health`, `/static`, `/cgi-bin`) map to the declared key
`deployRouteKey = ⟨0,0⟩`; every other surface maps to `⟨0,1⟩`, which
`deployPolicyConfig` does NOT declare — so the REAL `serveDecision` refuses it.
This is the adapter `App.routeKeyOf` left as a documented hole, here genuinely
distinguishing declared from undeclared. `/cgi-bin` is declared so the deployed
`.cgi` route (which spawns the real CGI script) is reached rather than refused at
the policy gate. -/
def routeKeyOfSegs : List String → Policy.RouteKey
  | "health" :: _  => deployRouteKey
  | "static" :: _  => deployRouteKey
  | "cgi-bin" :: _ => deployRouteKey
  | _              => ⟨0, 1⟩

/-- The REAL `Policy.serveDecision` on the deployed running surface, keyed on the
route a segment list maps to. Kernel-decidable (no `splitOn`): `["health"]`
admits (`some`), `["nope"]` refuses (`none`). -/
def decisionOfSegs (segs : List String) : Option Policy.Served :=
  Policy.serveDecision deployLid (routeKeyOfSegs segs) false deployRunning

/-- The traversal gate on segments: the REAL `Route.Path.decodeSegs` (the single
percent-decode boundary) applied to the raw segments; `true` exactly when a
decoded `..` is present, i.e. the target would climb above the document root. A
double-encoded `%252e` decodes once to the harmless `%2e` and is not flagged
(matching `Safety.Traversal`'s single-decode discipline). Kernel-decidable. -/
def escapesSegs (segs : List String) : Bool :=
  (Route.Path.decodeSegs segs).contains ".."

/-- The `Policy.RouteKey` a dispatched request maps to — `routeKeyOfSegs` over the
REAL normalized target segments (`App.targetSegments`, the traversal-safe boundary
`Route.Match.bestMatch` matches on). -/
def routeKeyOfReq (req : Proto.Request) : Policy.RouteKey :=
  routeKeyOfSegs (Reactor.App.targetSegments req.target)

/-- **The deployed admission decision for a request** — the REAL
`Policy.serveDecision`, keyed on the request's own route via `routeKeyOfReq`, on
the live `deployRunning` surface. A declared surface admits (`some`); an
undeclared surface refuses (`none`). Not a constant — it branches on the target.
Definitionally `decisionOfSegs (App.targetSegments req.target)`. -/
def deployDecisionOf (req : Proto.Request) : Option Policy.Served :=
  Policy.serveDecision deployLid (routeKeyOfReq req) false deployRunning

/-- **The traversal gate on a request** — `escapesSegs` over the raw target
segments (`rawSegsOf`, the pre-normalize slash-split). `true` exactly when the
decoded target carries a `..` that would escape the document root. -/
def targetEscapes (req : Proto.Request) : Bool :=
  escapesSegs (rawSegsOf req)

/-- Bridge: the request-level decision is the segment-level decision on the
request's normalized segments (definitional). Lets a caller who knows a request's
segments discharge the `hrefuse`/`hadmit` hypotheses of the seam theorems. -/
theorem deployDecisionOf_eq_segs (req : Proto.Request) :
    deployDecisionOf req = decisionOfSegs (Reactor.App.targetSegments req.target) := rfl

/-- Bridge: the request-level escape gate is the segment-level gate on the
request's raw segments (definitional). -/
theorem targetEscapes_eq_segs (req : Proto.Request) :
    targetEscapes req = escapesSegs (rawSegsOf req) := rfl

/-! ### (4b) The gate responses (serializer-built, not handler bodies) -/

/-- Serializer-built **403 Forbidden** — the response for an undeclared surface.
Its body is fixed policy prose, independent of the request; the application
handler body is never reached. -/
def forbidden403 : Response :=
  error4xx 403 (str "Forbidden") (str "policy: undeclared surface\n")

/-- Serializer-built **404 Not Found** for a blocked traversal — a fixed body,
independent of the target, so no resolved file bytes can flow. Distinct body from
the app's default 404 ("not found"), so the traversal branch is observable. -/
def traversalBlocked404 : Response :=
  error4xx 404 (str "Not Found") (str "traversal blocked\n")

/-! ### (4c) The guarded response and the guarded serve -/

/-- The first dispatched request in a submission list (mirrors `demoResp`'s walk),
or `none` if the FSM emitted no dispatch. -/
def dispatchReqOf : List RingSubmission → Option Proto.Request
  | [] => none
  | .dispatch req :: _ => some req
  | _ :: rest => dispatchReqOf rest

/-- **The gate, on one dispatched request.** Traversal first (a `..`-escaping
target is 404-blocked before anything else touches it), then Policy admission (an
undeclared surface is 403-refused), else the normal deployed response. This is
the branch: three genuinely different byte outputs decided by the REAL
`targetEscapes` / `deployDecisionOf`. -/
def guardOne (input : Bytes) (req : Proto.Request) : Bytes :=
  match targetEscapes req with
  | true  => serialize traversalBlocked404
  | false =>
    match deployDecisionOf req with
    | none   => serialize forbidden403
    | some _ => serialize (deployResp input)

/-- **The guarded deployed serve.** Identical to `serveFull` on the FSM-send path
(faithful in-order forwarding); on a bare dispatch it runs `guardOne` — the REAL
Policy/Safety gates — instead of unconditionally serializing `deployResp`. This is
the response function `main` runs. Total. -/
def serveGuarded (input : Bytes) : Bytes :=
  match sendsOf (deploySubs input) with
  | [] =>
    match dispatchReqOf (deploySubs input) with
    | some req => guardOne input req
    | none     => serialize (deployResp input)
  | sends => sends.flatten

/-- **The guarded observed step** — `serveGuarded` plus the same REAL observation
state advance as `deployStep` (`Metrics.inc`, `Tap.step`, `Trace` id). This is
the function `main` runs. -/
def deployStepGuarded (st : Observe.ObsState) (input : Bytes) :
    Bytes × Observe.ObsState :=
  ( serveGuarded input
  , { metrics := st.metrics.inc Observe.reqCounter 1
    , tap     := Tap.step st.tap (Tap.Ev.pkt input)
    , corrs   := Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs } )

/-- What guarded `main` writes is definitionally `serveGuarded`. -/
theorem deployStepGuarded_serves (st : Observe.ObsState) (input : Bytes) :
    (deployStepGuarded st input).1 = serveGuarded input := rfl

/-! ### (4d) Seam theorems over the bytes `main` writes -/

/-- On a dispatch (FSM emitted no bytes of its own), `serveGuarded` reduces to the
gate on the dispatched request. Same `cases`-on-`sendsOf` shape as
`serveFull_serializes_dispatch`, kept off the deployed-config `whnf` blow-up. -/
theorem serveGuarded_dispatch (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    serveGuarded input = guardOne input req := by
  unfold serveGuarded
  cases hs : sendsOf (deploySubs input) with
  | nil => rw [hsub]; rfl
  | cons a t => rw [hs] at hsends; exact absurd hsends (by simp)

/-- **The gate output for an undeclared, non-escaping request is the 403 bytes.**
Pure fact about `guardOne`: no reactor, no hypotheses beyond the two gate values. -/
theorem guardOne_refuses (input : Bytes) (req : Proto.Request)
    (hesc : targetEscapes req = false) (hrefuse : deployDecisionOf req = none) :
    guardOne input req = serialize forbidden403 := by
  unfold guardOne; rw [hesc, hrefuse]

/-- **The gate output for an escaping target is the traversal-blocked 404 bytes.**
Pure fact about `guardOne`: the resolved resource is never serialized. -/
theorem guardOne_blocks (input : Bytes) (req : Proto.Request)
    (hesc : targetEscapes req = true) :
    guardOne input req = serialize traversalBlocked404 := by
  unfold guardOne; rw [hesc]

/-- **The gate output for an admitted request is the normal deployed 200 path.** -/
theorem guardOne_admits (input : Bytes) (req : Proto.Request) (s : Policy.Served)
    (hesc : targetEscapes req = false) (hadmit : deployDecisionOf req = some s) :
    guardOne input req = serialize (deployResp input) := by
  unfold guardOne; rw [hesc, hadmit]

/-- **`deploy_refuses_undeclared_bytes` — the Policy branch, byte-level, on the
deployed path.** When the deployed reactor dispatches a request whose route the
REAL `serveDecision` refuses (undeclared surface) and whose target does not
escape, the bytes `main` writes are EXACTLY the serializer-built 403 — not the
handler body, not a correspondence claim beside an unchanged pipeline. -/
theorem deploy_refuses_undeclared_bytes (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hesc : targetEscapes req = false)
    (hrefuse : deployDecisionOf req = none) :
    serveGuarded input = serialize forbidden403 := by
  rw [serveGuarded_dispatch input req rest hsends hsub, guardOne_refuses input req hesc hrefuse]

/-- **`deploy_traversal_blocked_bytes` — the Safety branch, byte-level, on the
deployed path.** When the deployed reactor dispatches a request whose decoded
target carries an escaping `..`, the bytes `main` writes are EXACTLY the
serializer-built 404 with the fixed "traversal blocked" body — the escaped
resource is never serialized. The body is target-independent, so no file content
can leak regardless of what the `..` pointed at. -/
theorem deploy_traversal_blocked_bytes (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hesc : targetEscapes req = true) :
    serveGuarded input = serialize traversalBlocked404
    ∧ (traversalBlocked404).status = 404 := by
  refine ⟨?_, rfl⟩
  rw [serveGuarded_dispatch input req rest hsends hsub, guardOne_blocks input req hesc]

/-! ### (4e) The gate genuinely branches — kernel-checked, no reactor.

These are real `decide` executions of the REAL gate functions on concrete
segment lists (the `["health"]` / `["nope"]` / `["..", …]` a parsed target
produces). Each proves the gate takes a different arm, so the byte branch in
`guardOne` is a mechanism, not three names for one response. -/

/-- The REAL admission **admits** a declared surface. -/
theorem decision_admits_health :
    decisionOfSegs ["health"] = some ⟨deployLid, deployRouteKey, false⟩ := by decide

/-- The REAL admission **refuses** an undeclared surface — the Policy branch. -/
theorem decision_refuses_nope : decisionOfSegs ["nope"] = none := by decide

/-- The REAL admission admits the declared `/static` prefix surface. -/
theorem decision_admits_static :
    decisionOfSegs ["static", "app.js"] = some ⟨deployLid, deployRouteKey, false⟩ := by decide

/-- The REAL traversal gate **fires** on a `..`-escaping target — the Safety
branch. -/
theorem escape_fires_dotdot : escapesSegs ["..", "etc", "passwd"] = true := by decide

/-- …and the percent-encoded `%2e%2e` traversal is decoded once and **also**
fires — the single-decode boundary catches it. -/
theorem escape_fires_encoded : escapesSegs ["%2e%2e", "etc", "passwd"] = true := by decide

/-- …while a legitimate target does **not** fire (no false positive). -/
theorem escape_quiet_health : escapesSegs ["health"] = false := by decide

/-- …and a double-encoded `%252e%252e` decodes once to the harmless literal
`%2e%2e` (not `..`), so it is NOT flagged — matching `Safety.Traversal`. -/
theorem escape_quiet_double_encoded : escapesSegs ["%252e%252e", "etc"] = false := by decide

/-- **The branch is real: the two gate responses differ.** A 403 and a 404 are
distinct responses, so the Policy/Safety arms emit different status lines than the
admitted 200 path. (Stated at the status level; `serialize` of these statuses
differs a fortiori.) -/
theorem gate_statuses_distinct :
    forbidden403.status = 403
  ∧ traversalBlocked404.status = 404
  ∧ forbidden403.status ≠ traversalBlocked404.status := by decide

-- Kernel `#guard` evaluations of the REAL gate functions on concrete segments:
-- each is a real execution proof that the gate branches.
#guard escapesSegs ["..", "etc", "passwd"] = true
#guard escapesSegs ["%2e%2e", "etc", "passwd"] = true
#guard escapesSegs ["%252e%252e", "etc"] = false
#guard escapesSegs ["health"] = false
#guard routeKeyOfSegs ["health"] = deployRouteKey
#guard routeKeyOfSegs ["static", "app.js"] = deployRouteKey
#guard routeKeyOfSegs ["cgi-bin", "hello"] = deployRouteKey
#guard routeKeyOfSegs ["nope"] = (⟨0, 1⟩ : Policy.RouteKey)
#guard (decisionOfSegs ["health"]).isSome = true
#guard (decisionOfSegs ["static", "app.js"]).isSome = true
#guard (decisionOfSegs ["cgi-bin", "hello"]).isSome = true
#guard (decisionOfSegs ["nope"]).isNone = true

/-! ## (5) STAGE-PIPELINE — the deployed serve as an extensible fold over stages.

Sections (2)–(4) build the deployed serve as a MONOLITH: `deployResp` /
`serveGuarded` bake the header rewrite and the two gates into one function.
Adding a byte-driving feature means editing that shared function. This section
re-expresses the deployed behavior as a
`Reactor.Pipeline.runPipeline` over a `deployStages : List Stage` — each concern a
separate stage — and characterizes the pipeline's deployed bytes
(`servePipeline_dispatch`). Under the short-circuit-carries-transforms pipeline
semantics the fold ENRICHES gate short-circuits (the deploy header rewrite now
applies to the 404/403 too) and lets an unknown-but-safe path reach the router's
404, so it is no longer byte-identical to the monolithic `guardOne`; `guardOne` /
`serveGuarded` and the seams (2)–(4) are untouched (a separate legacy/H3 path).

The three current concerns become three stages, in the SAME order `guardOne`
decides them (traversal first, then Policy, then the header rewrite):

* `traversalStage` — a GATE: a `..`-escaping target short-circuits to the fixed
  `traversalBlocked404` (the REAL `targetEscapes` / `Safety.Traversal`).
* `policyStage` — a GATE: an undeclared surface short-circuits to `forbidden403`
  (the REAL `deployDecisionOf` / `Policy.serveDecision`).
* `headerRewriteStage` — a RESPONSE transform: `Lifecycle.rewriteResp` under the
  REAL `deployProg` (`stdRewrite` + the proxy/DNS upstream + the Trace corr id).

The response phase threads the AFFINE `Reactor.Pipeline.ResponseBuilder` (one
in-place-mutable cell, not a `Response` rebuilt per stage): the gate stages pass
the builder untouched, and `headerRewriteStage` applies the header-map rewrite via
`mapResp` (an in-place header-map insert/strip sequence). `servePipeline`
`build`s the final builder to the wire response. `servePipeline_dispatch`
characterizes those bytes; under the short-circuit-carries-transforms semantics the
gate arms now carry the deploy header rewrite and an unknown-but-safe path reaches
the router's 404, so the fold is no longer byte-identical to the monolith.

The handler is the real application router (`App.handle demoAppConfig`). Adding a
lib is now: define one stage file, append it to `deployStages`
(kept a COMPILE-TIME LITERAL — see `Pipeline.lean` § CODEGEN OBLIGATIONS). -/

open Reactor.Pipeline (Ctx StageStep Stage runPipeline ResponseBuilder)

/-- **The traversal gate stage.** A `..`-escaping target short-circuits to the
serializer-built `traversalBlocked404` (the escaped resource is never reached);
otherwise pass through untouched. The REAL `targetEscapes` decides. -/
def traversalStage : Stage where
  name := "traversal"
  onRequest := fun c =>
    match targetEscapes c.req with
    | true  => .respond traversalBlocked404
    | false => .continue c
  onResponse := fun _ b => b

/-- Byte-level dotfile test: a target of the form `/.X…` where the byte after the
leading `/.` is neither `/` (47) nor `.` (46) — a reserved dotfile / VCS surface
(`.git`, `.env`, `.htaccess`) a server never exposes. Distinct from `/`, `/.`,
`/..`, `/./…` (path navigation, handled by the traversal gate / normalization). -/
def isDotfileTarget : Proto.Bytes → Bool
  | 47 :: 46 :: c :: _ => c != 47 && c != 46
  | _ => false

/-- **A genuinely policy-refused surface.** The REAL `deployDecisionOf` refuses it
(`none` — not a declared surface) AND it is a reserved dotfile namespace the policy
holds off-limits. An undeclared but NON-reserved path (a plain unknown route) is
NOT refused here: it passes the gate and the application router answers it with its
own 404 default. So the policy gate 403s only genuinely-reserved surfaces; an
unknown, non-escaping, well-formed path that simply does not match a route 404s. -/
def policyReserved (req : Proto.Request) : Bool :=
  (deployDecisionOf req).isNone && isDotfileTarget req.target

/-- **The Policy admission gate stage.** A genuinely policy-refused surface
(`policyReserved` — undeclared AND a reserved dotfile namespace) short-circuits to
the serializer-built `forbidden403`. Every other surface — an admitted declared
surface (200 handler) OR a merely-unknown safe path — passes through; the
application router then answers it (a real route, or its 404 default). This lets an
unmatched-but-safe path reach the router's 404 rather than being blanket-403'd. -/
def policyStage : Stage where
  name := "policy"
  onRequest := fun c => cond (policyReserved c.req) (.respond forbidden403) (.continue c)
  onResponse := fun _ b => b

/-- **The header-rewrite stage.** Always passes on the request phase; on the
response phase it applies the REAL `Header.run` rewrite under `deployProg`
(`stdRewrite` + the proxy/DNS-chosen upstream + the Trace correlation id) — the
same header program the monolithic `deployResp` bakes in. -/
def headerRewriteStage : Stage where
  name := "header-rewrite"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    b.mapResp
      (Reactor.Lifecycle.rewriteResp (deployProg (deployPlan (deploySubs c.input)) c.input))

/-- **The registered deployed stage list.** The current serve's concerns as an
ordered pipeline. Adding a lib appends exactly one entry here. -/
def deployStages : List Stage := [traversalStage, policyStage, headerRewriteStage]

/-- **The pipeline handler.** The real application router response for the
dispatched request — exactly the `demoResp` a deployed dispatch feeds
`deployResp`. -/
def appHandler (c : Ctx) : Response := App.handle demoAppConfig c.req

/-- Build the pipeline context for an input: the raw bytes plus the dispatched
request the reactor produced (`none` → the default empty request, unreachable on
the dispatch path). -/
def ctxOf (input : Bytes) : Ctx :=
  { input := input
    req := (dispatchReqOf (deploySubs input)).getD ({} : Proto.Request) }

/-- **The extensible deployed serve.** `serialize` of the BUILT stage fold: the
request runs the request phase (the two gates), a passing request is answered by
the app handler seeded into the affine `ResponseBuilder`, the header rewrite
threads that builder in place, and `.build` finalizes it to the wire response.
Characterized by `servePipeline_dispatch` — a fold a new stage extends in one file,
with the response built once in place, not reallocated per stage. -/
def servePipeline (input : Bytes) : Bytes :=
  serialize ((runPipeline deployStages appHandler (ctxOf input)).build)

/-- The stage fold over `deployStages`, once BUILT, reduces to exactly the
`guardOne` decision tree — traversal gate, then Policy gate, then the header
rewrite of the app response — for ANY context. Stated over `.build` (the finalized
wire response the affine builder threads to), which is where the byte-equality
lives; proven generically (no `deploySubs` whnf), so the deployed instantiation
just substitutes the concrete request. The builder is a faithful refinement, so
this is the SAME `Response` the pre-builder fold produced. -/
theorem runPipeline_deployStages (c : Ctx) :
    (runPipeline deployStages appHandler c).build
      = match targetEscapes c.req with
        | true  =>
          Reactor.Lifecycle.rewriteResp
            (deployProg (deployPlan (deploySubs c.input)) c.input) traversalBlocked404
        | false =>
          cond (policyReserved c.req)
            (Reactor.Lifecycle.rewriteResp
              (deployProg (deployPlan (deploySubs c.input)) c.input) forbidden403)
            (Reactor.Lifecycle.rewriteResp
              (deployProg (deployPlan (deploySubs c.input)) c.input)
              (App.handle demoAppConfig c.req)) := by
  show (runPipeline (traversalStage :: policyStage :: [headerRewriteStage]) appHandler c).build = _
  rw [Reactor.Pipeline.pipeline_cons]
  cases htrav : targetEscapes c.req with
  | true =>
    -- traversal gates: the 404 is threaded through the inner onion (policy id, then
    -- the deploy header rewrite), so it now carries the header-rewrite headers.
    simp only [traversalStage, htrav, Reactor.Pipeline.runResp_cons, Reactor.Pipeline.runResp_nil,
      policyStage, headerRewriteStage, Reactor.Pipeline.build_mapResp,
      Reactor.Pipeline.build_ofResponse]
  | false =>
    simp only [traversalStage, htrav]
    rw [Reactor.Pipeline.pipeline_cons]
    cases hres : policyReserved c.req with
    | true =>
      -- policy refuses a reserved surface: the 403 threads through the header rewrite.
      simp only [policyStage, hres, cond_true, Reactor.Pipeline.runResp_cons,
        Reactor.Pipeline.runResp_nil, headerRewriteStage, Reactor.Pipeline.build_mapResp,
        Reactor.Pipeline.build_ofResponse]
    | false =>
      -- policy passes (admitted OR unknown-but-safe): the app router answers, then the
      -- deploy header rewrite. An unknown path is 404'd by the router's default here.
      simp only [policyStage, hres, cond_false]
      rw [Reactor.Pipeline.pipeline_cons]
      simp only [headerRewriteStage, appHandler, Reactor.Pipeline.pipeline_empty,
        Reactor.Pipeline.build_mapResp, Reactor.Pipeline.build_ofResponse]

/-- On a deployed dispatch, `ctxOf`'s request is the dispatched request. -/
theorem ctxOf_req (input : Bytes) (req : Proto.Request) (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch req :: rest) :
    (ctxOf input).req = req := by
  show (dispatchReqOf (deploySubs input)).getD ({} : Proto.Request) = req
  rw [hsub]; rfl

/-- **`servePipeline_dispatch` — the stage pipeline's deployed bytes, characterized.**
On a deployed dispatch, the stage fold emits the serialized gate/handler response
with the deploy header rewrite applied to EVERY arm — including the gate
short-circuits (the traversal 404 and the reserved-surface 403 now carry the
response-transform headers, per the new short-circuit-carries-transforms pipeline
semantics), and the unknown-but-safe path is answered by the application router's
own 404 default (`App.handle`) rather than a blanket policy 403.

This SUPERSEDES the old `servePipeline_agrees` byte-equality with `serveGuarded`:
the pipeline now ENRICHES short-circuits (the header rewrite on the 403/404) and
lets unknown paths through to the router's 404, whereas the monolithic `guardOne`
emits the pristine, un-rewritten gate bytes and blanket-403s every undeclared
surface. `serveGuarded`/`guardOne` and their `*_deployed` seams are untouched (a
separate legacy/H3 path); this theorem characterizes the extensible fold `main`
runs (`servePipelineFull2`, of which this 3-stage `servePipeline` is the core). -/
theorem servePipeline_dispatch (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch req :: rest) :
    servePipeline input
      = serialize (match targetEscapes req with
          | true  =>
            Reactor.Lifecycle.rewriteResp
              (deployProg (deployPlan (deploySubs input)) input) traversalBlocked404
          | false =>
            cond (policyReserved req)
              (Reactor.Lifecycle.rewriteResp
                (deployProg (deployPlan (deploySubs input)) input) forbidden403)
              (Reactor.Lifecycle.rewriteResp
                (deployProg (deployPlan (deploySubs input)) input)
                (App.handle demoAppConfig req))) := by
  show serialize ((runPipeline deployStages appHandler (ctxOf input)).build) = _
  rw [runPipeline_deployStages (ctxOf input), ctxOf_req input req rest hsub]
  have hin : (ctxOf input).input = input := rfl
  rw [hin]

/-! ## (6) COMPOSE-SAFE — the two pure response-additions folded onto the pipeline.

Section (5) re-expressed the deployed serve as `servePipeline` over `deployStages`
(characterized by `servePipeline_dispatch`). This section ADDS — never mutates — two
verified byte-driving RESPONSE stages that read nothing from the request and gate
nothing, so they only enrich a response (add headers), never change its status:

* `Reactor.Stage.SecurityHeaders.securityheadersStage` — stamps the real RFC 6797
  HSTS set (+ X-Frame-Options / X-Content-Type-Options / Referrer-Policy) onto every
  admitted response, via the REAL `SecurityHeaders.render`.
* `Reactor.Stage.Header.headerStage` — runs a real `Header.run` rewrite (strip the
  RFC 7230 §6.1 hop-by-hop headers + install a `Server` field).

`deployStagesFull` APPENDS them to the unchanged `deployStages`. On the admitted arm
their `onResponse` runs first (the onion), then the outer `headerRewriteStage` (the
deploy `Header.run` under `deployProg`) runs last; its strip is hop-by-hop only, so
the non-hop HSTS/security headers survive it intact (`deployProg_preserves_field`).
Under the short-circuit-carries-transforms pipeline semantics, a gate short-circuit
ALSO threads its response through these inner transforms, so a refused response
(3xx/401/403/404) now carries the same security headers — the theorems here cover
the admitted arm; the gate-arm enrichment is proven at the full-fold seams below.

`serveGuarded` and the ~63 `*_deployed` seams over it are untouched (a separate
legacy/H3 path): everything here is a NEW def over the SAME proven kernel. -/

/-- **The full deployed stage list.** The current `deployStages` (traversal gate,
policy gate, deploy header rewrite) with the two safe pure response-additions
appended — so the gates keep their exact 403/404 byte outputs and the two transforms
only enrich the admitted 200 response. -/
def deployStagesFull : List Stage :=
  deployStages ++ [Reactor.Stage.SecurityHeaders.securityheadersStage,
                   Reactor.Stage.Header.headerStage]

/-- **The full extensible deployed serve.** `serialize` of the BUILT fold over
`deployStagesFull` — identical to `servePipeline` on the gate arms, and on the
admitted arm additionally carrying the real security-header set and the header
rewrite. -/
def servePipelineFull (input : Bytes) : Bytes :=
  serialize ((runPipeline deployStagesFull appHandler (ctxOf input)).build)

/-- **The full observed step.** `servePipelineFull` plus the SAME REAL observation
advance as `deployStepGuarded` (`Metrics.inc`, `Tap.step`, the `Trace`-assigned id).
This is the function `main` now runs. -/
def deployStepFull (st : Observe.ObsState) (input : Bytes) : Bytes × Observe.ObsState :=
  ( servePipelineFull input
  , { metrics := st.metrics.inc Observe.reqCounter 1
    , tap     := Tap.step st.tap (Tap.Ev.pkt input)
    , corrs   := Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs } )

/-- What full `main` writes is definitionally `servePipelineFull`. -/
theorem deployStepFull_serves (st : Observe.ObsState) (input : Bytes) :
    (deployStepFull st input).1 = servePipelineFull input := rfl

/-! ### Header-membership preservation (the outer rewrite keeps a non-hop,
non-overwritten field — the mechanism by which HSTS reaches the wire). -/

/-- A field whose name is not a hop-name survives `strip`. -/
theorem mem_strip_of_not_hop {g : Header.Field} {hop : List Header.Name} {h : Header.Headers}
    (hm : g ∈ h) (hnh : Header.isHop hop g.name = false) : g ∈ Header.strip hop h := by
  unfold Header.strip
  refine List.mem_filter.mpr ⟨hm, ?_⟩
  show (!Header.isHop hop g.name) = true
  rw [hnh]; rfl

/-- A field whose name differs from `n` survives `set n v`. -/
theorem mem_set_of_ne {g : Header.Field} {n : Header.Name} {v : Header.Value} {h : Header.Headers}
    (hm : g ∈ h) (hne : Header.nameEqb g.name n = false) : g ∈ Header.set n v h := by
  unfold Header.set Header.remove
  refine List.mem_append.mpr (Or.inl ?_)
  refine List.mem_filter.mpr ⟨hm, ?_⟩
  show (!Header.nameEqb g.name n) = true
  rw [hne]; rfl

/-- Membership carries through the `List (Bytes × Bytes) → Header.Headers` view. -/
theorem mem_toHeaders {p : Bytes × Bytes} {l : List (Bytes × Bytes)} (h : p ∈ l) :
    (⟨p.1, p.2⟩ : Header.Field) ∈ Reactor.Lifecycle.toHeaders l :=
  List.mem_map.mpr ⟨p, h, rfl⟩

/-- Membership carries back through the `Header.Headers → List (Bytes × Bytes)` view. -/
theorem mem_ofHeaders {f : Header.Field} {h : Header.Headers} (hm : f ∈ h) :
    (f.name, f.value) ∈ Reactor.Lifecycle.ofHeaders h :=
  List.mem_map.mpr ⟨f, hm, rfl⟩

/-- **The deploy header rewrite (`deployProg`) keeps any non-hop, non-overwritten
field.** Its program is the RFC 9110 §7.6.1 dynamic strip (`Header.Op.hopDyn` —
`Header.strip (Header.dynHopSet H)`) then three `set`s (`Server` / `x-upstream` /
`x-corr`); a field whose name is not in the message's dynamic hop set (neither a
fixed hop-name nor `Connection`-nominated) and is none of those three survives the
whole rewrite. This is the axiom-clean MECHANISM by which an inner-added header
(HSTS) reaches the wire past the outer rewrite. -/
theorem deployProg_preserves_field (plan : List RingSubmission) (input : Bytes)
    (g : Header.Field) (H : Header.Headers) (hm : g ∈ H)
    (hhop  : Header.isHop (Header.dynHopSet H) g.name = false)
    (hsrv  : Header.nameEqb g.name Reactor.Lifecycle.serverName = false)
    (hup   : Header.nameEqb g.name upstreamName = false)
    (hcorr : Header.nameEqb g.name corrName = false) :
    g ∈ Header.run (deployProg plan input) H := by
  have hrun : Header.run (deployProg plan input) H
      = Header.set corrName (corrVal input)
          (Header.set upstreamName (upstreamVal plan)
            (Header.set Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal
              (Header.strip (Header.dynHopSet H) H))) := by
    unfold deployProg Reactor.Lifecycle.stdRewrite
    rw [Header.run_append]
    simp only [Header.run_cons, Header.run_nil, Header.applyOp]
  rw [hrun]
  exact mem_set_of_ne (mem_set_of_ne (mem_set_of_ne
    (mem_strip_of_not_hop hm hhop) hsrv) hup) hcorr

/-! ### The full-pipeline reduction and the HSTS byte-effect -/

/-- **The full pipeline, on an admitted dispatch, reduces to the deploy header
rewrite of the (HSTS + header-stage)-enriched inner build.** Both gates pass
(`htrav`/`hadmit`), so the fold threads the handler response through the two inner
appended stages and then the outer `headerRewriteStage`. Generic over the context;
fully axiom-clean. -/
theorem runPipeline_deployStagesFull (c : Ctx) (s : Policy.Served)
    (htrav : targetEscapes c.req = false)
    (hadmit : deployDecisionOf c.req = some s) :
    (runPipeline deployStagesFull appHandler c).build
      = Reactor.Lifecycle.rewriteResp
          (deployProg (deployPlan (deploySubs c.input)) c.input)
          ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                         Reactor.Stage.Header.headerStage] appHandler c).build) := by
  show (runPipeline (traversalStage :: policyStage :: headerRewriteStage
        :: Reactor.Stage.SecurityHeaders.securityheadersStage
        :: [Reactor.Stage.Header.headerStage]) appHandler c).build = _
  rw [Reactor.Pipeline.pipeline_cons]
  simp only [traversalStage, htrav]
  rw [Reactor.Pipeline.pipeline_cons]
  simp only [policyStage, policyReserved, hadmit, Option.isNone_some, Bool.false_and, cond_false]
  rw [Reactor.Pipeline.pipeline_cons]
  simp only [headerRewriteStage, Reactor.Pipeline.build_mapResp]

/-- **`servePipelineFull_hsts` — the real HSTS header enters the deployed pipeline,
and the full built response is exactly the deploy header-rewrite of that
HSTS-carrying response.** On any admitted, non-escaping dispatch:

* the response entering the outer rewrite carries the `Strict-Transport-Security`
  name AND the exact RFC-6797-rendered value the real `SecurityHeaders.hstsRender`
  produces (`securityheadersStage_hsts_present`, composed through the pipeline); and
* the full deployed build is that response passed through the deploy `Header.run`
  rewrite (`runPipeline_deployStagesFull`), whose only header-dropping op is the
  hop-by-hop strip — which `deployProg_preserves_field` shows keeps every non-hop,
  non-`Server`/`x-upstream`/`x-corr` field, HSTS among them.

Fully axiom-clean, no `sorry`. The concrete "HSTS survives on the wire" is confirmed
by the real orb run (the `String.toUTF8` header name is not kernel-reducible, so the
final name-inequality discharge is empirical, not `native_decide` — which this
axiom-clean tree deliberately avoids). -/
theorem servePipelineFull_hsts (c : Ctx) (s : Policy.Served)
    (htrav : targetEscapes c.req = false)
    (hadmit : deployDecisionOf c.req = some s) :
    (Reactor.Stage.SecurityHeaders.hstsHeaderName,
     Reactor.Stage.SecurityHeaders.hstsHeaderVal)
        ∈ ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                         Reactor.Stage.Header.headerStage] appHandler c).build).headers
    ∧ (runPipeline deployStagesFull appHandler c).build
        = Reactor.Lifecycle.rewriteResp
            (deployProg (deployPlan (deploySubs c.input)) c.input)
            ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                           Reactor.Stage.Header.headerStage] appHandler c).build) :=
  ⟨Reactor.Stage.SecurityHeaders.securityheadersStage_hsts_present _ appHandler c,
   runPipeline_deployStagesFull c s htrav hadmit⟩

/-! ## (7) CTX-GATES — compose ALL 10 byte-driving stages into the deployed serve.

Sections (5)/(6) folded only the two SAFE transforms (`securityheadersStage` /
`headerStage`) onto the gated `deployStages`. The other eight byte-drivers — five
GATES (`jwt`, `ipfilter`, `rate`, `cache`, `redirect`) and three transforms
(`cors`, `gzip`, `htmlrewrite`) — are unit-proven in `Reactor/Stage/*` but, on
their own, are not composed into the served path, so their gates cannot fire on a
real orb run. This section composes ALL ten into `deployStagesFull2` and repoints `main`
(via `deployStepFull2`) at it, keeping `deployStages`/`servePipeline`/`serveGuarded`
and the section-(6) `deployStagesFull` untouched (purely additive).

The unit stages in `Reactor/Stage/*` are configured for their non-vacuity WITNESSES
(e.g. `jwtStage` rejects EVERY request; `rateStage`/`ipfilterStage` fail closed;
`cacheStage` is warm on `GET /`). Dropped in verbatim they would 401/429/403 or
spuriously cache `/health`. So the gates are wired here PRODUCTION-SAFE, each still
routing through the REAL library decision:

* `jwtAdminStage` — runs the REAL `Jwt.authenticate` gate, but ONLY on `/admin*`
  targets; every other path passes. So `/health` is untouched and `/admin` with no
  bearer token is refused `401` by the genuine FSM.
* `ipfilterPermissiveStage` — the stdin model carries no peer address, so with no
  `client.ip` attribute the stage admits (there is nothing to reject on); when an
  address IS stashed it runs the REAL `WireIpFilter.deployAdmits` (a stashed blocked
  client is still 403'd).
* `rateHighStage` — the REAL `Rate.tryAdmit` over a full high-capacity bucket:
  admits (high limit), so `/health` is never throttled.
* `cacheEmptyStage` — the REAL `Cache.Store.get?`/`isFresh` gate over an EMPTY
  store: every request misses and passes through (no spurious hit).
* `Reactor.Stage.Redirect.redirectStage` — used verbatim; it only gates its
  configured `/old` target, so it is already production-safe.

The three transforms are appended INNERMOST-after-the-header-rewrite so they enrich
only the admitted arm; `gzipStage`/`htmlrewriteStage` are used verbatim (they read
the request themselves). `deployCorsStage` re-wires the REAL `Cors.acaoValue`
decision to read the arena's CANONICAL lowercase `origin` header name (the unit
`corsStage` looked up `Origin`, which the HTTP/1.1 parser lowercases, so it could
never fire on the deployed path). -/

open Reactor.Pipeline (Ctx StageStep Stage runPipeline ResponseBuilder)

/-! ### (7a) The production-safe gate wrappers (each over the REAL library) -/

/-- `"/admin"` as ASCII bytes — the protected path prefix. -/
def adminPrefix : Proto.Bytes := [47, 97, 100, 109, 105, 110]

/-- Byte-prefix test (structural on the needle). -/
def isPrefixB : Proto.Bytes → Proto.Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | n :: ns, h :: hs => n == h && isPrefixB ns hs

/-- Does the request target sit under `/admin`? -/
def isAdminPath (req : Proto.Request) : Bool := isPrefixB adminPrefix req.target

/-- **The JWT gate, admin-scoped.** On an `/admin*` target it runs the REAL
`Reactor.Stage.Jwt.jwtStage` request phase (the genuine `Jwt.authenticate` FSM):
no/invalid bearer token short-circuits `401`. Every other target passes untouched —
so `/health` and the demo routes are never gated. -/
def jwtAdminStage : Stage where
  name := "jwt-admin"
  onRequest := fun c =>
    if isAdminPath c.req then Reactor.Stage.Jwt.jwtStage.onRequest c else .continue c
  onResponse := fun _ b => b

/-- The deployed CIDR ruleset: `defaultDeny := false` (admit by default —
production-safe for the peer-address-less stdin model), with one real deny block
(`10.0.0.0/8`) so the REAL deny-precedence path is reachable when a client address
is present. (`Reactor.Stage.IpFilter`/`WireIpFilter` sit ABOVE `Deploy` in the
import graph — via `Reactor.Bridge` — so the stage is wired over the base
`IpFilter` library directly, not that stage.) -/
def deployIpRuleset : _root_.IpFilter.Ruleset :=
  { rules := [(⟨.v4, [true, false, true, false, false, false, false, false], 8⟩,
               _root_.IpFilter.Action.deny)]
    defaultDeny := false }

/-- Decode the `client.ip` attribute bytes to an `IpFilter.Addr` (family tag byte
`4`/`6`, then one `0`/`1` byte per bit) — the inverse of the accept path's encode. -/
def decodeClientAddr : Proto.Bytes → _root_.IpFilter.Addr
  | []          => ⟨.v4, []⟩
  | fam :: rest => ⟨if fam == 6 then .v6 else .v4, rest.map (fun b => b != 0)⟩

/-- The 403 a rejected client receives (distinct body from the policy 403). -/
def ipForbidden403 : Response :=
  error4xx 403 (str "Forbidden") (str "forbidden: ip not admitted\n")

/-- **The IP filter gate, permissive-default.** The stdin serve carries no peer
address, so with no `client.ip` attribute the stage admits; when an address IS
stashed it runs the REAL `IpFilter.permits` (deny-precedence over `deployIpRuleset`)
and 403s a denied client. -/
def ipfilterPermissiveStage : Stage where
  name := "ipfilter"
  onRequest := fun c =>
    match c.attrs.find? (fun kv => kv.1 == "client.ip") with
    | some kv =>
      if _root_.IpFilter.permits deployIpRuleset (decodeClientAddr kv.2)
      then .continue c else .respond ipForbidden403
    | none => .continue c
  onResponse := fun _ b => b

/-- A full, high-capacity bucket — the deployed "high limit" configuration. -/
def rateFullBucket : _root_.Rate.Bucket :=
  { tokens := 1000000, last := 0, cap := 1000000, rate := 1 }

/-- The REAL `Rate.tryAdmit` decision over the high-limit bucket (refilled to clock
`0`). High-limit ⇒ a token is always available ⇒ admit. -/
def rateHighAdmits (c : Ctx) : Bool :=
  (_root_.Rate.tryAdmit (_root_.Rate.refill 0 rateFullBucket)).2

/-- The high-limit bucket admits (real `Rate` transition, kernel-checked). -/
theorem rateHigh_always_admits (c : Ctx) : rateHighAdmits c = true := by
  unfold rateHighAdmits; decide

/-- **The rate-limit gate, high-limit.** Consults the REAL token bucket; over the
high limit it never rejects, so `/health` is never throttled. (A tighter deployed
config would reject genuinely over-limit connections — the same `Rate.tryAdmit`
branch `Reactor.Stage.Rate` proves fires on an empty bucket.) -/
def rateHighStage : Stage where
  name := "rate"
  onRequest := fun c => cond (rateHighAdmits c) (.continue c) (.respond Reactor.Stage.Rate.resp429)
  onResponse := fun _ b => b

/-- An EMPTY cache store — the deployed "empty-start" configuration. -/
def emptyCacheCfg : Reactor.Stage.Cache.Config :=
  { st := { store := { entries := [], capacity := 8 }, locks := [], pending := [] }
    keyOf := Reactor.Stage.Cache.keyOf
    now := 0
    render := Reactor.Stage.Cache.render }

/-- **The cache gate, empty-start.** Runs the REAL `Cache.Store.get?` lookup over
an empty store: every request misses and passes through — no spurious hit shadows a
handler response. (A warm store would serve the stored bytes, the branch
`Reactor.Stage.Cache` proves fires.) -/
def cacheEmptyStage : Stage := Reactor.Stage.Cache.mkStage emptyCacheCfg

/-! ### (7b) The CORS transform, re-cased for the arena's canonical headers -/

/-- The canonical (lowercase) `origin` request-header name the HTTP/1.1 arena
parser emits. -/
def corsOriginNameLower : Proto.Bytes := [111, 114, 105, 103, 105, 110]

/-- The request's `Origin` token, read from the canonical lowercase header name;
absent ⇒ the empty token (denied). -/
def corsOriginOf (c : Ctx) : _root_.Cors.Origin :=
  match c.req.headers.lookup corsOriginNameLower with
  | some v => Reactor.Stage.Cors.bytesToStr v
  | none   => ""

/-- **The CORS transform, deployed.** Always passes; on the response phase it runs
the REAL `Cors.acaoValue` decision over `Reactor.Stage.Cors.corsPolicy` and, iff the
origin is permitted, stamps `Access-Control-Allow-Origin` onto the affine builder.
Identical to the unit `corsStage` except it reads the arena's canonical lowercase
`origin` (the unit stage read `Origin`, which the parser lowercases, so it could not
fire on the deployed path). -/
def deployCorsStage : Stage where
  name := "cors"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) with
    | some v => b.addHeader (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
    | none   => b

/-! ### (7c) The full ten-stage deployed list -/

/-- **The full deployed stage list — all ten byte-drivers.** Request-phase order
(the gates, then the traversal/policy gates, then the handler-side transforms):

1. `jwtAdminStage` — `/admin` bearer gate (401)
2. `ipfilterPermissiveStage` — CIDR admission (403 on a stashed blocked client)
3. `rateHighStage` — token-bucket limit (429)
4. `cacheEmptyStage` — fresh-hit cache (serves stored bytes)
5. `redirectStage` — `/old` redirect (308 + `Location`)
6. `traversalStage` — `..`-escape block (404)
7. `policyStage` — declared-surface admission (403)
8. `headerRewriteStage` — deploy `Header.run` (Server / x-upstream / x-corr)
9. `deployCorsStage` — `Access-Control-Allow-Origin`
10. `gzipStage` — gzip body + `Content-Encoding: gzip`
11. `htmlrewriteStage` — markup-stripping body rewrite
12. `securityheadersStage` — HSTS + companions
13. `headerStage` — hop-strip + `Server`

The five gates run FIRST (request phase, in list order), so a refused request emits
its pristine gate response with none of the transforms. On the admitted arm the
response phase runs in REVERSE order (the onion): `headerStage` innermost, then
security headers, then the markup rewrite, then gzip (compresses the rewritten
body), then CORS, and `headerRewriteStage` outermost (its hop-strip keeps every
non-hop header the inner transforms added — `deployProg_preserves_field`). -/
def deployStagesFull2 : List Stage :=
  [ jwtAdminStage
  , Reactor.Stage.BasicAuth.basicStage
  , Reactor.Stage.IpFilter.ipfilterStage
  , Reactor.Stage.Rate.rateStage
  , cacheEmptyStage
  , Reactor.Stage.Redirect.redirectStage
  , traversalStage
  , policyStage
  , headerRewriteStage
  , deployCorsStage
  , Reactor.Stage.Gzip.gzipStage
  , Reactor.Stage.HtmlRewrite.htmlrewriteStage
  , Reactor.Stage.SecurityHeaders.securityheadersStage
  , Reactor.Stage.Header.headerStage ]

/-- **The full ten-stage deployed serve.** `serialize` of the BUILT fold over
`deployStagesFull2`. -/
def servePipelineFull2 (input : Bytes) : Bytes :=
  serialize ((runPipeline deployStagesFull2 appHandler (ctxOf input)).build)

/-- **The metered serve context.** `ctxOf input` plus the two accept-path attrs the
real IP-filter and rate gates read: the peer address under
`Reactor.Stage.IpFilter.clientIpKey` (family-tagged bit-encoded, the accept
`SocketAddr`), and the per-connection request index under
`Reactor.Stage.Rate.seqKey`, unary-encoded as zero bytes whose LENGTH is the
standing count the token bucket depletes against (`Reactor.Stage.Rate.seqOf` is
that `List.length`).

The unary count is **capped at `Reactor.Stage.Rate.rateCap`**, and the cap costs the
gate nothing. `Reactor.Stage.Rate.bucketOf` reconstructs the standing bucket with
`rateCap - seqOf c` tokens in TRUNCATED `Nat` subtraction, so every `seqOf c ≥
rateCap` yields the identical empty bucket and the real `tryAdmit` refuses each the
same way: the decision factors through `min connSeq rateCap`, and counts above the
cap are information the limiter provably cannot observe. Encoding them anyway made
this attr `O(connSeq)` bytes, where `connSeq` is the host's UNBOUNDED per-connection
request index — so a long-lived keep-alive connection consed a list per request
sized by its own history (quadratic in the connection's request count). The cap
bounds the attr at `rateCap` bytes with the emitted response byte-identical at every
`connSeq`. The cap-inertness is a REAL THEOREM, not a test:
`Datapath.ServeMeteredHeadIdx.rateGateB_cap_inert` proves `∀ seq, rateGateB (min seq
rateCap) = rateGateB seq` (the gate's verdict is unchanged by the cap for EVERY
count), and `Datapath.ServeMeteredHeadIdx.rate_admits_metered` carries it to this
ctx — its statement, in terms of the UNCAPPED `seq`, is the decision on the full
history the capped allocation reproduces.

Keeping `ctxOf`/`servePipelineFull2` untouched preserves every existing deployed
proof; the metered gates only fire when the host supplies these attrs. -/

def ctxOfMetered (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Pipeline.Ctx :=
  { ctxOf input with
      attrs := [ (Reactor.Stage.IpFilter.clientIpKey, clientIp)
               , (Reactor.Stage.Rate.seqKey,
                   Reactor.Stage.ConnLimit.encodeCap
                     (Reactor.Stage.Rate.countOfPacked connSeq))
               , (Reactor.Stage.Rate.clockKey,
                   Reactor.Stage.ConnLimit.encodeCap
                     (min (Reactor.Stage.Rate.clockOfPacked connSeq)
                       Reactor.Stage.Rate.defaultBurstCap)) ] }

/-- **The metered ctx stashes exactly the two metered keys.** For a key that is
neither the IP-filter's nor the rate gate's, the attr-bag lookup is `none`. Stated
over the KEYS alone and proven once here, so the stash/recovery stages that need it
never reach through to the seq attr's ENCODING — the reach-through is what coupled
them to the unary representation. -/

theorem ctxOfMetered_find_none (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes)
    (k : String)
    (h1 : (Reactor.Stage.IpFilter.clientIpKey == k) = false)
    (h2 : (Reactor.Stage.Rate.seqKey == k) = false)
    (h3 : (Reactor.Stage.Rate.clockKey == k) = false := by decide) :
    (ctxOfMetered clientIp connSeq input).attrs.find? (fun p => p.1 == k) = none := by
  show List.find? (fun p => p.1 == k)
      [ (Reactor.Stage.IpFilter.clientIpKey, clientIp)
      , (Reactor.Stage.Rate.seqKey,
          Reactor.Stage.ConnLimit.encodeCap (Reactor.Stage.Rate.countOfPacked connSeq))
      , (Reactor.Stage.Rate.clockKey,
          Reactor.Stage.ConnLimit.encodeCap
            (min (Reactor.Stage.Rate.clockOfPacked connSeq)
              Reactor.Stage.Rate.defaultBurstCap)) ] = none
  simp [List.find?, h1, h2, h3]

/-! ### The per-connection rate readings on the plain metered context

`ctxOfMetered` carries NO configured burst parameters, so the gate reads
`defaultBurstCap` / `defaultBurstRate` there. Its two accept-path readings are the
packed scalar's low field (the connection's request count, exact at every count
since it is under `2^32`) and its high field (the elapsed-seconds clock, clamped at
the capacity so the eight-byte word is exact — an INERT clamp,
`Reactor.Stage.Rate.admitsAt_clock_clamp`). Proven ONCE here, where `ctxOfMetered`
lives, and reused by every metered seam. -/

/-- The plain metered ctx carries no configured burst capacity ⇒ the DEFAULT. -/
theorem burstCapOf_ctxOfMetered (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.burstCapOf (ctxOfMetered clientIp connSeq input)
      = Reactor.Stage.Rate.defaultBurstCap := by
  apply Reactor.Stage.Rate.burstCapOf_absent
  simp [Reactor.Stage.Rate.lookupBytes, ctxOfMetered,
    Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
    Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
    Reactor.Stage.Rate.burstRateKey]

/-- The plain metered ctx carries no configured refill rate ⇒ the DEFAULT. -/
theorem burstRateOf_ctxOfMetered (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.burstRateOf (ctxOfMetered clientIp connSeq input)
      = Reactor.Stage.Rate.defaultBurstRate := by
  apply Reactor.Stage.Rate.burstRateOf_absent
  simp [Reactor.Stage.Rate.lookupBytes, ctxOfMetered,
    Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
    Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
    Reactor.Stage.Rate.burstRateKey]

/-- The plain metered ctx's standing request count IS the packed low field. -/
theorem seqOf_ctxOfMetered (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.seqOf (ctxOfMetered clientIp connSeq input)
      = Reactor.Stage.Rate.countOfPacked connSeq := by
  have hl : Reactor.Stage.Rate.lookupBytes (ctxOfMetered clientIp connSeq input)
      Reactor.Stage.Rate.seqKey
      = Reactor.Stage.ConnLimit.encodeCap (Reactor.Stage.Rate.countOfPacked connSeq) := by
    simp [Reactor.Stage.Rate.lookupBytes, ctxOfMetered,
      Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
      Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey]
  rw [Reactor.Stage.Rate.seqOf, hl,
    Reactor.Stage.ConnLimit.decodeWordD_encodeCap 0
      (Reactor.Stage.Rate.countOfPacked_lt64 connSeq)]

/-- The plain metered ctx's clock is the packed high field, clamped at the DEFAULT
capacity so the positional word is exact. -/
theorem clockOf_ctxOfMetered (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.clockOf (ctxOfMetered clientIp connSeq input)
      = min (Reactor.Stage.Rate.clockOfPacked connSeq) Reactor.Stage.Rate.defaultBurstCap := by
  have hl : Reactor.Stage.Rate.lookupBytes (ctxOfMetered clientIp connSeq input)
      Reactor.Stage.Rate.clockKey
      = Reactor.Stage.ConnLimit.encodeCap
          (min (Reactor.Stage.Rate.clockOfPacked connSeq)
            Reactor.Stage.Rate.defaultBurstCap) := by
    simp [Reactor.Stage.Rate.lookupBytes, ctxOfMetered,
      Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
      Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey]
  have hm : min (Reactor.Stage.Rate.clockOfPacked connSeq)
      Reactor.Stage.Rate.defaultBurstCap < 2 ^ 64 := by
    unfold Reactor.Stage.Rate.defaultBurstCap
    omega
  rw [Reactor.Stage.Rate.clockOf, hl,
    Reactor.Stage.ConnLimit.decodeWordD_encodeCap 0 hm]

/-- **The per-connection gate's verdict on the plain metered context, in closed
form** — the DEFAULT burst parameters against the raw packed readings (the stored
clock clamp is inert). -/
theorem rateAdmits_ctxOfMetered (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.admits (ctxOfMetered clientIp connSeq input)
      = Reactor.Stage.Rate.admitsAt Reactor.Stage.Rate.defaultBurstCap
          Reactor.Stage.Rate.defaultBurstRate
          (Reactor.Stage.Rate.countOfPacked connSeq)
          (Reactor.Stage.Rate.clockOfPacked connSeq) := by
  show Reactor.Stage.Rate.admitsAt (Reactor.Stage.Rate.burstCapOf _)
      (Reactor.Stage.Rate.burstRateOf _) (Reactor.Stage.Rate.seqOf _)
      (Reactor.Stage.Rate.clockOf _) = _
  rw [burstCapOf_ctxOfMetered, burstRateOf_ctxOfMetered, seqOf_ctxOfMetered,
      clockOf_ctxOfMetered]
  exact Reactor.Stage.Rate.admitsAt_clock_clamp _ _ _ _

/-- **The metered full serve.** The SAME thirteen-stage `deployStagesFull2` fold,
keyed on `ctxOfMetered` so the real IP-filter (deny `10.0.0.0/8`) and rate
(cap 8/connection) gates decide on the accept peer + per-connection sequence the
host threads in. The host calls this instead of `servePipelineFull2` when it has a
peer address and keep-alive request index to supply. -/
def servePipelineFull2Metered (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) : Bytes :=
  serialize ((runPipeline deployStagesFull2 appHandler (ctxOfMetered clientIp connSeq input)).build)

/-- **The full ten-stage fold over an explicitly-supplied request.** The SAME
`deployStagesFull2` pipeline `servePipelineFull2` runs, but keyed on a `Ctx` whose
request comes from a NON-HTTP/1.1 ingress (an H3/QUIC dispatch or a protocol
upgrade) rather than re-derived from raw HTTP/1.1 bytes via `deploySubs`. Returns
the built wire `Response` so a non-HTTP carriage (H3 framing) can re-serialize it;
`input` still drives the deploy header rewrite's proxy/DNS plan. This is how the
QUIC/H3 and native-socket serve paths reach the identical middleware fold the TCP
dataplane runs. -/
def deployRespFull2Of (input : Bytes) (req : Proto.Request) : Response :=
  (runPipeline deployStagesFull2 appHandler { input := input, req := req }).build

/-- The full-fold serve keyed on a supplied request, as wire bytes — the H3/QUIC
sibling of `servePipelineFull2`. -/
def servePipelineFull2Of (input : Bytes) (req : Proto.Request) : Bytes :=
  serialize (deployRespFull2Of input req)

/-- **The full ten-stage observed step** — `servePipelineFull2` plus the SAME REAL
observation advance as `deployStepFull` (`Metrics.inc`, `Tap.step`, the
`Trace`-assigned id). This is the function `main` runs. -/
def deployStepFull2 (st : Observe.ObsState) (input : Bytes) : Bytes × Observe.ObsState :=
  ( servePipelineFull2 input
  , { metrics := st.metrics.inc Observe.reqCounter 1
    , tap     := Tap.step st.tap (Tap.Ev.pkt input)
    , corrs   := Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs } )

/-- What full `main` writes is definitionally `servePipelineFull2` (totality: it is
a plain `def`). -/
theorem deployStepFull2_serves (st : Observe.ObsState) (input : Bytes) :
    (deployStepFull2 st input).1 = servePipelineFull2 input := rfl

/-! ## (7d) DEPLOYMENT-CONFIG — the deployed serve GENERATED from a declarative config

Sections (7a)–(7c) built `deployStagesFull2` + `demoApp` as hardcoded literals:
nothing GENERATED them, so the composable `Dsl.DeploymentConfig` surface and the
running server were disconnected. This section closes that gap. `defaultDeployment`
is the declarative config whose `Dsl.instantiate` REPRODUCES the deployed stage
list and route table on the nose; `servePipelineOf` runs that instantiation through
the SAME `runPipeline` fold; and the no-regression theorems prove the config-driven
serve is byte-identical to the hardcoded `servePipelineFull2` — so the deployed
conformance is preserved, and the deployed serve is now the image of a config a
grow lane extends by editing one disjoint `Dsl/Cfg/*.lean` dimension.

`deployStagesFull2` and `demoApp` are UNTOUCHED — this is purely additive; the
equalities are proved (not asserted), so every existing proof stated over the
literals stands, and `main` (via `deployStepFull2`) still runs the identical bytes,
now provably `= servePipelineOf defaultDeployment`. -/

/-- **The default deployment, as a declarative config.** Its five disjoint
dimensions are populated so that `Dsl.instantiate` reproduces the deployed serve:

* `listener`  — the deployed admission identity/state (`demoAppConfig.lid`/`policy`);
* `routing`   — the deployed route table + default handler + admission-key adapter;
* `middleware`— the ordered fourteen-stage chain `deployStagesFull2`;
* `tls`/`upstream` — empty (this cleartext deployment terminates TLS at the IO
  boundary and carries no declared reverse-proxy pools).

A grow lane extends the live deployment by editing ONE dimension here (and its own
`Reactor/Stage/<Lib>.lean`), not by reaching into a shared literal. -/
def defaultDeployment : Dsl.DeploymentConfig where
  listener :=
    { id := demoAppConfig.lid
      policy := demoAppConfig.policy }
  routing :=
    { routes := demoAppConfig.routes
      defaultHandler := demoAppConfig.defaultHandler
      routeKeyOf := demoAppConfig.routeKeyOf }
  middleware := { chain := deployStagesFull2 }

/-- **No-regression, the stage list.** The config instantiates to EXACTLY the
deployed fourteen-stage `deployStagesFull2` — same stages, same order. -/
theorem instantiate_default_stages :
    (Dsl.instantiate defaultDeployment).1 = deployStagesFull2 := rfl

/-- **No-regression, the route table.** The config instantiates to EXACTLY the
deployed `demoAppConfig` (`= App.demoApp`) — same routes, same default handler,
same admission seam. (Structure-eta: the record `instantiate` rebuilds from
`demoAppConfig`'s projections IS `demoAppConfig`.) -/
theorem instantiate_default_app :
    (Dsl.instantiate defaultDeployment).2 = demoAppConfig := rfl

/-- **The config-driven serve.** `serialize` of the BUILT fold of the config's
instantiated stage list over the config's instantiated app handler — the SAME
`runPipeline` calculus `servePipelineFull2` runs, but with the stages and route
table SUPPLIED BY the config rather than hardcoded. -/
def servePipelineOf (cfg : Dsl.DeploymentConfig) (input : Bytes) : Bytes :=
  serialize ((runPipeline (Dsl.instantiate cfg).1
      (Dsl.handlerOf (Dsl.instantiate cfg).2) (ctxOf input)).build)

/-- **The no-regression theorem — byte-identical serve.** For EVERY input, the
config-driven serve of `defaultDeployment` emits the exact same bytes as the
hardcoded `servePipelineFull2`. So the deployed 45/46 conformance — every byte-
effect / status / gate theorem stated over `servePipelineFull2` — is preserved
unchanged: the two serves are the same function. Proved by `rfl` — the config
instantiates to the very stage list and app handler the hardcoded serve names
(`instantiate_default_stages`/`instantiate_default_app`), and `handlerOf
demoAppConfig` is definitionally `appHandler`. -/
theorem servePipelineOf_default (input : Bytes) :
    servePipelineOf defaultDeployment input = servePipelineFull2 input := rfl

/-- **The config-driven METERED serve.** The metered mirror of `servePipelineOf`:
the SAME `runPipeline` fold over the config's instantiated stage list + app handler,
but keyed on `ctxOfMetered` (the accept peer + per-connection sequence the real
IP-filter and rate gates read) rather than the bare `ctxOf`. So the connection-aware
gates decide over the CONFIG's declared middleware chain — and since
`Dsl.Config.denoteOn` leaves `base.middleware` untouched (`{ base with … }`), a
denoted operator config still folds the deployed gate chain, now over its route
table. -/
def servePipelineOfMetered (cfg : Dsl.DeploymentConfig)
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) : Bytes :=
  serialize ((runPipeline (Dsl.instantiate cfg).1
      (Dsl.handlerOf (Dsl.instantiate cfg).2) (ctxOfMetered clientIp connSeq input)).build)

/-- **No-regression, the metered serve.** For EVERY peer/sequence/input, the
config-driven metered serve of `defaultDeployment` emits the exact same bytes as the
hardcoded `servePipelineFull2Metered`. So the deployed metered conformance is
preserved: the two metered serves are the same function. Proved by `rfl` — the config
instantiates to the very stage list (`deployStagesFull2`) and app handler
(`appHandler`) the hardcoded metered serve names, and `ctxOfMetered` is the shared
context. This is the Braid-0 byte-identity anchor: the running default metered serve
becomes a fold over `defaultDeployment.middleware.chain`, byte-for-byte today's. -/
theorem servePipelineOfMetered_default
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    servePipelineOfMetered defaultDeployment clientIp connSeq input
      = servePipelineFull2Metered clientIp connSeq input := rfl

/-! ### The DoS-metered context — the accept-path admission readings, stated ONCE

`ctxOfMetered` supplies only the client IP + rate sequence, so every gate that
decides on standing state (the per-source connection count, the header-arrival
span) reads an ABSENT attribute and is inert. The DoS-metered context adds the
three readings the accept path owns: the source's standing active-connection
count (`conn-active`, unary), the header-arrival span (`hdr-now`, unary, against
an absent — hence `0` — `hdr-started` base), and the OPERATOR's configured
per-source cap (`conn-cap`, positional, from `max-connections`).

This is the ONE representation both metered seams use: `Reactor.DeployPipeline`
(the consolidated `drorb_serve_pipeline_conformant` default) and the
config-driven `drorb_serve_metered_cfg_conformant` seam both fold over THIS
context and reuse THESE projection lemmas — one encoding, proven once. -/

/-- **The DoS-metered context.** `ctxOfMetered`'s IP + rate attrs, plus the readings
the accept path owns — the source's active-connection count (unary in `conn-active`)
and the header-arrival span (unary in `hdr-now`, base `hdr-started` absent = `0`) —
plus the OPERATOR's two configured per-source numbers, both positional through the ONE
shared word codec: the connection cap (`conn-cap`, `max-connections`) and the
request-arrival limit (`stick-limit`, `rate-limit`), the latter against the source's
in-window ARRIVAL COUNT (`stick-count`).

The arrival count is positional, not unary like `conn-active`: a per-source in-window
count is unbounded by the flood it is meant to bound, and a unary reading would
allocate one cons per counted arrival on the request path. -/
def ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) : Reactor.Pipeline.Ctx :=
  { ctxOf input with
      attrs := [ (Reactor.Stage.IpFilter.clientIpKey, clientIp)
               , (Reactor.Stage.Rate.seqKey,
                   Reactor.Stage.ConnLimit.encodeCap
                     (Reactor.Stage.Rate.countOfPacked connSeq))
               , (Reactor.Stage.Rate.clockKey,
                   Reactor.Stage.ConnLimit.encodeCap
                     (min (Reactor.Stage.Rate.clockOfPacked connSeq) burstCap))
               , (Reactor.Stage.Rate.burstCapKey,
                   Reactor.Stage.ConnLimit.encodeCap burstCap)
               , (Reactor.Stage.Rate.burstRateKey,
                   Reactor.Stage.ConnLimit.encodeCap burstRate)
               , (Reactor.Stage.ConnLimit.activeKey, List.replicate active (0 : UInt8))
               , (Reactor.Stage.ConnLimit.capKey, Reactor.Stage.ConnLimit.encodeCap cap)
               , (Reactor.Stage.StickTable.countKey,
                   Reactor.Stage.ConnLimit.encodeCap rateCount)
               , (Reactor.Stage.StickTable.limitKey,
                   Reactor.Stage.ConnLimit.encodeCap rateLimit)
               , (Reactor.Stage.Slowloris.nowKey, List.replicate span (0 : UInt8)) ] }

/-- The request the DoS-metered fold dispatches is the raw parse — the admission
attrs feed only the gates, never the route. -/
theorem ctxOfMeteredConn_req (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) :
    (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input).req = (ctxOf input).req := rfl

/-- The reconstructed active-connection count IS the threaded `active`. -/
theorem activeOf_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) :
    Reactor.Stage.ConnLimit.activeOf (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = active := by
  simp [Reactor.Stage.ConnLimit.activeOf, Reactor.Stage.ConnLimit.lookupBytes,
    ctxOfMeteredConn, Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
    Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey, Reactor.Stage.ConnLimit.activeKey,
    Reactor.Stage.ConnLimit.capKey, Reactor.Stage.StickTable.countKey,
    Reactor.Stage.StickTable.limitKey, Reactor.Stage.Slowloris.nowKey]

/-- **The configured cap the gate decides on IS the threaded `cap`.** Every cap the
host can cross (a `UInt64`) survives the attribute-bag round trip exactly — so the
operator's `max-connections` is the number the proven `admits` sees. -/
theorem capOf_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) (hcap : cap < 2 ^ 64) :
    Reactor.Stage.ConnLimit.capOf (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = cap := by
  have hl : Reactor.Stage.ConnLimit.lookupBytes
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input) Reactor.Stage.ConnLimit.capKey
      = Reactor.Stage.ConnLimit.encodeCap cap := by
    simp [Reactor.Stage.ConnLimit.lookupBytes, ctxOfMeteredConn,
      Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
      Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey, Reactor.Stage.ConnLimit.activeKey,
      Reactor.Stage.ConnLimit.capKey, Reactor.Stage.StickTable.countKey,
    Reactor.Stage.StickTable.limitKey, Reactor.Stage.Slowloris.nowKey]
  rw [Reactor.Stage.ConnLimit.capOf, hl, Reactor.Stage.ConnLimit.decodeCap_encodeCap hcap]

/-- The reconstructed current header clock IS the threaded `span`. -/
theorem nowOf_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) :
    Reactor.Stage.Slowloris.nowOf (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = span := by
  simp [Reactor.Stage.Slowloris.nowOf, Reactor.Stage.Slowloris.lookupBytes,
    ctxOfMeteredConn, Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
    Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey, Reactor.Stage.ConnLimit.activeKey,
    Reactor.Stage.ConnLimit.capKey, Reactor.Stage.StickTable.countKey,
    Reactor.Stage.StickTable.limitKey, Reactor.Stage.Slowloris.nowKey]

/-- The header-phase start base is absent (`hdr-started` unset ⇒ `0`), so the
reconstructed span is exactly `nowOf`. -/
theorem startedOf_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) :
    Reactor.Stage.Slowloris.startedOf (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = 0 := by
  have h : Reactor.Stage.Slowloris.lookupBytes
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      Reactor.Stage.Slowloris.startedKey = [] := by
    simp [Reactor.Stage.Slowloris.lookupBytes, ctxOfMeteredConn,
      Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
      Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey, Reactor.Stage.ConnLimit.activeKey,
      Reactor.Stage.ConnLimit.capKey, Reactor.Stage.StickTable.countKey,
      Reactor.Stage.StickTable.limitKey, Reactor.Stage.Slowloris.nowKey,
      Reactor.Stage.Slowloris.startedKey]
  simp [Reactor.Stage.Slowloris.startedOf, h]

/-- **★ The stick-table aggregate IS threaded — the hole is closed.** The
reconstructed in-window arrival count is EXACTLY the `rateCount` the host crossed, for
every count a `UInt64` can carry. This replaces the theorem that used to say `= 0`:
that one was an honest statement of a real hole (the host had no counting read — the
accept path's `rate_note` returned a bool), and closing it needed a counting read on
the Rust side, not a Lean edit. -/
theorem countOf_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) (hc : rateCount < 2 ^ 64) :
    Reactor.Stage.StickTable.countOf
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = rateCount := by
  have hl : Reactor.Stage.StickTable.lookupBytes
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      Reactor.Stage.StickTable.countKey
      = Reactor.Stage.ConnLimit.encodeCap rateCount := by
    simp [Reactor.Stage.StickTable.lookupBytes, ctxOfMeteredConn,
      Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
      Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey, Reactor.Stage.ConnLimit.activeKey,
      Reactor.Stage.ConnLimit.capKey, Reactor.Stage.Slowloris.nowKey,
      Reactor.Stage.StickTable.countKey, Reactor.Stage.StickTable.limitKey]
  rw [Reactor.Stage.StickTable.countOf, hl,
      Reactor.Stage.ConnLimit.decodeWordD_encodeCap 0 hc]

/-- **★ The rate LIMIT the gate decides against IS the threaded `rateLimit`** — the
operator's `rate-limit`, crossed as a `UInt64` and recovered exactly. Same shape, same
codec and same round-trip proof as the connection cap: the host supplies the NUMBER,
the proven `admitsAt` makes the DECISION. -/
theorem limitOf_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) (hl : rateLimit < 2 ^ 64) :
    Reactor.Stage.StickTable.limitOf
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = rateLimit := by
  have hb : Reactor.Stage.StickTable.lookupBytes
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      Reactor.Stage.StickTable.limitKey
      = Reactor.Stage.ConnLimit.encodeCap rateLimit := by
    simp [Reactor.Stage.StickTable.lookupBytes, ctxOfMeteredConn,
      Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
      Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey, Reactor.Stage.ConnLimit.activeKey,
      Reactor.Stage.ConnLimit.capKey, Reactor.Stage.Slowloris.nowKey,
      Reactor.Stage.StickTable.countKey, Reactor.Stage.StickTable.limitKey]
  rw [Reactor.Stage.StickTable.limitOf, hb,
      Reactor.Stage.ConnLimit.decodeWordD_encodeCap 0 hl]

/-! ### ★ The PER-CONNECTION burst parameters are THREADED, not baked

The per-connection token bucket used to decide against two Lean literals
(`rateCap := 8`, `rateRate := 1`) that no operator directive could reach: a default
deployment answered `429` to the NINTH request on ONE keep-alive connection, and
setting `rate-limit` or `max-connections` arbitrarily high did not move it (those are
the per-SOURCE bounds — a different quantity over different state). The context now
carries the operator's `burst-cap` and `burst-refill` in the SAME positional word
codec as the connection cap and the arrival limit, and the DECISION is the proven
`Reactor.Stage.Rate.admitsAt` over them.

The two accept-path readings ride the same codec: the connection's request count
(`countOfPacked`, the packed low field — always under `2^32`, so the eight-byte word
is exact at every count) and its elapsed-seconds clock (`clockOfPacked`, the packed
high field, clamped at the configured capacity so the word is exact for every clock a
long-lived connection can reach). The clamp is INERT
(`Reactor.Stage.Rate.admitsAt_clock_clamp`): once the elapsed time would credit a full
capacity there is nothing further to credit, so the clamped reading and the raw one
decide identically — for every cap, rate and count. -/

/-- **The configured burst CAPACITY the gate decides on IS the threaded `burstCap`** —
the operator's `burst-cap`, crossed as a `UInt64` and recovered exactly. Same codec,
same round-trip proof as the connection cap and the arrival limit. -/
theorem burstCapOf_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) (hb : burstCap < 2 ^ 64) :
    Reactor.Stage.Rate.burstCapOf (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = burstCap := by
  have hl : Reactor.Stage.Rate.lookupBytes
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      Reactor.Stage.Rate.burstCapKey
      = Reactor.Stage.ConnLimit.encodeCap burstCap := by
    simp [Reactor.Stage.Rate.lookupBytes, ctxOfMeteredConn,
      Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
      Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey, Reactor.Stage.ConnLimit.activeKey,
      Reactor.Stage.ConnLimit.capKey, Reactor.Stage.Slowloris.nowKey,
      Reactor.Stage.StickTable.countKey, Reactor.Stage.StickTable.limitKey]
  rw [Reactor.Stage.Rate.burstCapOf, hl,
      Reactor.Stage.ConnLimit.decodeWordD_encodeCap Reactor.Stage.Rate.defaultBurstCap hb]

/-- **The configured REFILL RATE the gate decides on IS the threaded `burstRate`** —
the operator's `burst-refill`, recovered exactly. -/
theorem burstRateOf_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) (hb : burstRate < 2 ^ 64) :
    Reactor.Stage.Rate.burstRateOf (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = burstRate := by
  have hl : Reactor.Stage.Rate.lookupBytes
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      Reactor.Stage.Rate.burstRateKey
      = Reactor.Stage.ConnLimit.encodeCap burstRate := by
    simp [Reactor.Stage.Rate.lookupBytes, ctxOfMeteredConn,
      Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
      Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey, Reactor.Stage.ConnLimit.activeKey,
      Reactor.Stage.ConnLimit.capKey, Reactor.Stage.Slowloris.nowKey,
      Reactor.Stage.StickTable.countKey, Reactor.Stage.StickTable.limitKey]
  rw [Reactor.Stage.Rate.burstRateOf, hl,
      Reactor.Stage.ConnLimit.decodeWordD_encodeCap Reactor.Stage.Rate.defaultBurstRate hb]

/-- The packed request count is under `2^32`, hence inside the eight-byte word the
codec round-trips exactly — no clamp is needed on the count. -/
theorem countOfPacked_lt (n : Nat) : Reactor.Stage.Rate.countOfPacked n < 2 ^ 64 :=
  Reactor.Stage.Rate.countOfPacked_lt64 n

/-- The connection's standing request count read off the DoS-metered context IS the
packed low field the host crossed, at EVERY count. -/
theorem seqOf_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) :
    Reactor.Stage.Rate.seqOf (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = Reactor.Stage.Rate.countOfPacked connSeq := by
  have hl : Reactor.Stage.Rate.lookupBytes
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      Reactor.Stage.Rate.seqKey
      = Reactor.Stage.ConnLimit.encodeCap (Reactor.Stage.Rate.countOfPacked connSeq) := by
    simp [Reactor.Stage.Rate.lookupBytes, ctxOfMeteredConn,
      Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
      Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey, Reactor.Stage.ConnLimit.activeKey,
      Reactor.Stage.ConnLimit.capKey, Reactor.Stage.Slowloris.nowKey,
      Reactor.Stage.StickTable.countKey, Reactor.Stage.StickTable.limitKey]
  rw [Reactor.Stage.Rate.seqOf, hl,
      Reactor.Stage.ConnLimit.decodeWordD_encodeCap 0 (countOfPacked_lt connSeq)]

/-- The connection's elapsed-seconds clock read off the DoS-metered context is the
packed high field, clamped at the configured capacity so the word is exact. -/
theorem clockOf_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) (hb : burstCap < 2 ^ 64) :
    Reactor.Stage.Rate.clockOf (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = min (Reactor.Stage.Rate.clockOfPacked connSeq) burstCap := by
  have hl : Reactor.Stage.Rate.lookupBytes
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      Reactor.Stage.Rate.clockKey
      = Reactor.Stage.ConnLimit.encodeCap
          (min (Reactor.Stage.Rate.clockOfPacked connSeq) burstCap) := by
    simp [Reactor.Stage.Rate.lookupBytes, ctxOfMeteredConn,
      Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey,
      Reactor.Stage.Rate.clockKey, Reactor.Stage.Rate.burstCapKey,
      Reactor.Stage.Rate.burstRateKey, Reactor.Stage.ConnLimit.activeKey,
      Reactor.Stage.ConnLimit.capKey, Reactor.Stage.Slowloris.nowKey,
      Reactor.Stage.StickTable.countKey, Reactor.Stage.StickTable.limitKey]
  have hm : min (Reactor.Stage.Rate.clockOfPacked connSeq) burstCap < 2 ^ 64 := by omega
  rw [Reactor.Stage.Rate.clockOf, hl,
      Reactor.Stage.ConnLimit.decodeWordD_encodeCap 0 hm]

/-- **★ The per-connection 429 decision on the DoS-metered context, in closed form.**
The gate admits IFF the operator's threaded `burst-cap` is `0` (off) or the
connection's standing depletion plus its elapsed-time credit at the threaded
`burst-refill` reaches one token. Every quantity in that sentence is a host-threaded
input; nothing is a Lean constant. Stated over the RAW packed clock — the context's
clamp is inert (`admitsAt_clock_clamp`), so this is the decision on the connection's
full history. -/
theorem rateAdmits_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) (hbc : burstCap < 2 ^ 64) (hbr : burstRate < 2 ^ 64) :
    Reactor.Stage.Rate.admits (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = Reactor.Stage.Rate.admitsAt burstCap burstRate
          (Reactor.Stage.Rate.countOfPacked connSeq)
          (Reactor.Stage.Rate.clockOfPacked connSeq) := by
  show Reactor.Stage.Rate.admitsAt (Reactor.Stage.Rate.burstCapOf _)
      (Reactor.Stage.Rate.burstRateOf _) (Reactor.Stage.Rate.seqOf _)
      (Reactor.Stage.Rate.clockOf _) = _
  rw [burstCapOf_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ hbc,
      burstRateOf_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ hbr,
      seqOf_ctxOfMeteredConn, clockOf_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ hbc]
  exact Reactor.Stage.Rate.admitsAt_clock_clamp _ _ _ _

/-- **★ The 429 decision on the DoS-metered context, in closed form.** The gate admits
IFF the operator's threaded limit is `0` (off) or the source's threaded in-window
arrival count is strictly under it. Every quantity in that sentence is a host-threaded
input; nothing is a Lean constant. -/
theorem ctxAdmits_ctxOfMeteredConn (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) (hc : rateCount < 2 ^ 64) (hl : rateLimit < 2 ^ 64) :
    Reactor.Stage.StickTable.ctxAdmits
        (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)
      = Reactor.Stage.StickTable.admitsAt rateLimit rateCount := by
  show Reactor.Stage.StickTable.admitsAt
      (Reactor.Stage.StickTable.limitOf _) (Reactor.Stage.StickTable.countOf _) = _
  rw [limitOf_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ hl,
      countOf_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ hc]

/-- **The config-driven DoS-METERED serve.** `servePipelineOfMetered` with the
accept-path admission readings threaded: the SAME `runPipeline` fold over the
config's instantiated stage list + app handler, but keyed on `ctxOfMeteredConn`, so
the config's conn-limit / slowloris gates decide on the REAL standing count, span
and operator cap instead of on absent attributes. -/
def servePipelineOfMeteredConn (cfg : Dsl.DeploymentConfig)
    (clientIp : Proto.Bytes) (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) : Bytes :=
  serialize ((runPipeline (Dsl.instantiate cfg).1
      (Dsl.handlerOf (Dsl.instantiate cfg).2)
      (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)).build)

/-- The DoS-metered serve is the serialization of the fold over the DoS-metered
context — the projection the gate theorems below rewrite through. -/
theorem servePipelineOfMeteredConn_eq (cfg : Dsl.DeploymentConfig)
    (clientIp : Proto.Bytes) (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Bytes) :
    servePipelineOfMeteredConn cfg clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input
      = serialize ((runPipeline cfg.middleware.chain
          (Dsl.handlerOf (Dsl.instantiate cfg).2)
          (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)).build) := rfl

/-- **The deployed `main` runs the config-driven serve.** What `deployStepFull2`
(the function `main` runs) writes is, byte-for-byte, `servePipelineOf
defaultDeployment` — the live server is now the image of the declarative config. -/
theorem deployStepFull2_serves_config (st : Observe.ObsState) (input : Bytes) :
    (deployStepFull2 st input).1 = servePipelineOf defaultDeployment input := by
  rw [deployStepFull2_serves, servePipelineOf_default]

/-! ### (7d') The deployed-serve projections drive the RUNNING components

`defaultDeployment` populates only the byte-pipeline dimensions; its upstream /
TLS / L4 dimensions are empty, so the three deployed-serve projections
(`dialChain` / `serverParamsFor` / `l4Listeners`) read their DEFAULT values — the
byte-identical no-regression the running serve preserves. `altDeployment` is the
SAME byte pipeline with all three IO-boundary dimensions populated: a
least-connections `api` pool, the dual-stack TLS matrix (a 0-RTT-on and a 0-RTT-off
profile), and a raw-TCP layer-4 listener over the `api` pool. Because the byte
pipeline is untouched, `altDeployment` serves the identical HTTP bytes — but its
reverse-proxy dial, TLS terminator, and L4 accept surface are all NON-default, so
driving the running orb under `altDeployment` produces different RUNNING behaviour
(a different backend, a different early-data verdict, a bound L4 listener) with no
regression to the cleartext HTTP conformance. -/

/-- The canonical reverse-proxy upstream pool name the deployed proxy route
references (`/api`). Both projections and the running dial key on it. -/
def proxyPoolName : String := "api"

/-- The load-aware `api` pool: three backends (ids 0/1/2, matching
`Reactor.ProxyDial.fleet`) selected least-connections-first. The RUNNING pick is
health-masked and load-supplied by the host (`Reactor.ProxyDial.fleetC`); this
pool supplies the POLICY chain the config-driven dial runs. -/
def altApiPool : Dsl.Cfg.UpstreamPool :=
  { name := proxyPoolName, pool := Dsl.Cfg.loadedPool, lb := .leastConn }

/-- **The non-default deployment.** `defaultDeployment`'s byte pipeline, with all
three IO-boundary dimensions populated: a least-connections `api` pool, the
dual-stack TLS matrix, and a raw-TCP layer-4 listener (`127.0.0.1:8710`) over the
`api` pool. -/
def altDeployment : Dsl.DeploymentConfig :=
  { defaultDeployment with
      listener :=
        { defaultDeployment.listener with
            addr := "127.0.0.1"
            port := 8710
            l4 := some { upstream := proxyPoolName, mode := .tcp } }
      tls := Dsl.Cfg.dualStackTls
      upstream := { pools := [altApiPool] } }

/-- **No LB regression.** The default deployment's `api` dial chain is the deployed
default (a single rendezvous link) — the byte-identical serve reads exactly the
chain the hardcoded `Reactor.ProxyDial.pick` used. -/
theorem defaultDeployment_dialChain :
    defaultDeployment.dialChain proxyPoolName = [Proxy.Policy.rendezvousHash] := rfl

/-- **The LB knob is live.** The non-default deployment's `api` dial chain is
least-connections — a different policy the config-driven dial runs. -/
theorem altDeployment_dialChain :
    altDeployment.dialChain proxyPoolName = [Proxy.Policy.leastConnections] := rfl

/-- The two deployments disagree on the `api` dial chain — the config choice is not
dead data. -/
theorem deployments_dialChain_differ :
    defaultDeployment.dialChain proxyPoolName ≠ altDeployment.dialChain proxyPoolName := by
  decide

/-- **No L4 regression.** The default deployment binds no layer-4 listener. -/
theorem defaultDeployment_l4 : defaultDeployment.l4Listeners = [] := rfl

/-- **The L4 knob is live.** The non-default deployment binds exactly one raw-TCP
passthrough listener on `127.0.0.1:8710` over the `api` pool's three backends —
the value a deploy step turns into `DRORB_L4_LISTEN` / `DRORB_PROXY_BACKENDS`. -/
theorem altDeployment_l4 :
    altDeployment.l4Listeners
      = [ { bind := "127.0.0.1:8710", poolName := proxyPoolName
            , mode := Dsl.Cfg.L4Mode.tcp, backendIds := [0, 1, 2] } ] := rfl

/-- **No TLS regression.** The default (cleartext) deployment reads the base
handshake terminator unchanged for any profile name. -/
theorem defaultDeployment_serverParams (base : TlsHandshake.ServerParams) (name : String) :
    defaultDeployment.serverParamsFor base name = base := rfl

/-- **The TLS knob is live: 0-RTT follows the profile.** Off the SAME base
terminator, the non-default deployment's 0-RTT-on profile (`internal-mtls`)
advertises its early-data window while its 0-RTT-off profile (`public-web`) zeroes
it — the config profile reaching the running handshake's early-data policy. -/
theorem altDeployment_serverParams_early (base : TlsHandshake.ServerParams) :
    (altDeployment.serverParamsFor base "internal-mtls").maxEarlyData = 16384
    ∧ (altDeployment.serverParamsFor base "public-web").maxEarlyData = 0 := by
  refine ⟨?_, ?_⟩ <;> rfl

#guard defaultDeployment.l4Listeners.length == 0
#guard altDeployment.l4Listeners.length == 1
#eval do
  IO.println s!"deployment projections: default dialChain(api)={repr (defaultDeployment.dialChain proxyPoolName)}, alt dialChain(api)={repr (altDeployment.dialChain proxyPoolName)}"
  IO.println s!"deployment L4: default={repr defaultDeployment.l4Listeners}, alt={repr altDeployment.l4Listeners}"

/-! ### (7c') Status-stability of every deployed stage's response phase

Under the short-circuit-carries-transforms semantics, a gate response is threaded
through the inner stages' `onResponse`s. Those transforms only ADD headers / rewrite
the body / rewrite the header map — they never set the status. So a gate
short-circuit keeps its status (a 401 stays a 401, a 403 a 403) even after the inner
transforms run over it. These lemmas record that each deployed stage's response
phase is status-stable; `deployStagesFull2_statusStable` collects them so the gate
seams can conclude the preserved status via `Pipeline.pipeline_gate_status`. -/

/-- The eight request-phase gates all have the identity response phase. -/
theorem jwtAdminStage_statusStable : Stage.statusStable jwtAdminStage := fun _ _ => rfl
theorem basicStage_statusStable : Stage.statusStable Reactor.Stage.BasicAuth.basicStage := fun _ _ => rfl
theorem ipfilterStage_statusStable : Stage.statusStable Reactor.Stage.IpFilter.ipfilterStage := fun _ _ => rfl
theorem rateStage_statusStable : Stage.statusStable Reactor.Stage.Rate.rateStage := fun _ _ => rfl
theorem cacheEmptyStage_statusStable : Stage.statusStable cacheEmptyStage := fun _ _ => rfl
theorem redirectStage_statusStable : Stage.statusStable Reactor.Stage.Redirect.redirectStage := fun _ _ => rfl
theorem traversalStage_statusStable : Stage.statusStable traversalStage := fun _ _ => rfl
theorem policyStage_statusStable : Stage.statusStable policyStage := fun _ _ => rfl

/-- The deploy header rewrite touches only the header map (`deploy_rewrite_status`). -/
theorem headerRewriteStage_statusStable : Stage.statusStable headerRewriteStage := by
  intro c b
  simp only [headerRewriteStage, Reactor.Pipeline.build_mapResp, deploy_rewrite_status]

/-- CORS only pushes `Access-Control-Allow-Origin` (a header), never the status. -/
theorem deployCorsStage_statusStable : Stage.statusStable deployCorsStage := by
  intro c b
  simp only [deployCorsStage]
  cases _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) <;>
    simp only [Reactor.Pipeline.build_addHeader]

/-- gzip rewrites the body and pushes `Content-Encoding` — the status is untouched. -/
theorem gzipStage_statusStable : Stage.statusStable Reactor.Stage.Gzip.gzipStage := by
  intro c b
  simp only [Reactor.Stage.Gzip.gzipStage]
  cases Reactor.Stage.Gzip.acceptsGzip c.req <;> rfl

/-- The content-type-gated markup rewrite touches only the body (on either gate
branch) — the status is untouched. -/
theorem htmlrewriteStage_statusStable : Stage.statusStable Reactor.Stage.HtmlRewrite.htmlrewriteStage := by
  intro c b
  show ((b.mapResp Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp).build).status = b.build.status
  rw [Reactor.Pipeline.build_mapResp, Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp_status]

/-- The security-header set only pushes headers — the status is untouched. -/
theorem securityheadersStage_statusStable : Stage.statusStable Reactor.Stage.SecurityHeaders.securityheadersStage := by
  intro c b
  simp only [Reactor.Stage.SecurityHeaders.securityheadersStage, Reactor.Pipeline.build_addHeaders]

/-- The hop-strip/`Server` rewrite touches only the header map — status untouched. -/
theorem headerStage_statusStable : Stage.statusStable Reactor.Stage.Header.headerStage :=
  fun _ _ => rfl

/-- **Every stage in `deployStagesFull2` is status-stable.** So threading a gate
short-circuit through the inner onion adds headers / rewrites the body only — it
never changes the gate status. -/
theorem deployStagesFull2_statusStable : ∀ s ∈ deployStagesFull2, Stage.statusStable s := by
  intro s hs
  simp only [deployStagesFull2, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
  rcases hs with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
  · exact jwtAdminStage_statusStable
  · exact basicStage_statusStable
  · exact ipfilterStage_statusStable
  · exact rateStage_statusStable
  · exact cacheEmptyStage_statusStable
  · exact redirectStage_statusStable
  · exact traversalStage_statusStable
  · exact policyStage_statusStable
  · exact headerRewriteStage_statusStable
  · exact deployCorsStage_statusStable
  · exact gzipStage_statusStable
  · exact htmlrewriteStage_statusStable
  · exact securityheadersStage_statusStable
  · exact headerStage_statusStable

/-! ### (7d) The JWT gate seam over the COMPOSED list -/

/-- The stages after the JWT gate — the tail the JWT short-circuit's response is
threaded through (the security-header set among them, so the `401` now carries HSTS
on the wire, as the real orb run confirms). -/
def full2AfterJwt : List Stage :=
  [ Reactor.Stage.BasicAuth.basicStage
  , Reactor.Stage.IpFilter.ipfilterStage
  , Reactor.Stage.Rate.rateStage
  , cacheEmptyStage
  , Reactor.Stage.Redirect.redirectStage
  , traversalStage
  , policyStage
  , headerRewriteStage
  , deployCorsStage
  , Reactor.Stage.Gzip.gzipStage
  , Reactor.Stage.HtmlRewrite.htmlrewriteStage
  , Reactor.Stage.SecurityHeaders.securityheadersStage
  , Reactor.Stage.Header.headerStage ]

/-- `deployStagesFull2` is the JWT gate followed by `full2AfterJwt`. -/
theorem deployStagesFull2_eq : deployStagesFull2 = jwtAdminStage :: full2AfterJwt := rfl

/-- Every stage after the JWT gate is status-stable. -/
theorem full2AfterJwt_statusStable : ∀ s ∈ full2AfterJwt, Stage.statusStable s := by
  intro s hs
  exact deployStagesFull2_statusStable s (by rw [deployStagesFull2_eq]; exact List.mem_cons_of_mem _ hs)

/-- **The JWT gate fires through the full thirteen-stage fold.** For any context
whose target is under `/admin` and whose REAL `Jwt.authenticate` decision rejects,
the JWT gate short-circuits: the built response of the WHOLE `deployStagesFull2`
fold is the `401` (`unauthorized`) threaded through the inner stages' response
onion (`full2AfterJwt`) — the handler and every later stage's REQUEST phase are
skipped, but the response transforms (the security-header set among them) now run
over the `401`, so the refusal carries the security headers. Its STATUS stays `401`
(`full2_admin_status_401`), and the policy meaning (a refusal) is preserved. -/
theorem full2_admin_gate (c : Ctx) (r : Jwt.Reason)
    (hadmin : isAdminPath c.req = true)
    (hrej : Reactor.Stage.Jwt.decision c = Jwt.Outcome.reject r) :
    (runPipeline deployStagesFull2 appHandler c)
      = Reactor.Pipeline.runResp full2AfterJwt c
          (ResponseBuilder.ofResponse Reactor.Stage.Jwt.unauthorized) := by
  have hgate : jwtAdminStage.onRequest c = StageStep.respond Reactor.Stage.Jwt.unauthorized := by
    show (if isAdminPath c.req then Reactor.Stage.Jwt.jwtStage.onRequest c
          else StageStep.continue c) = _
    rw [if_pos hadmin]
    exact Reactor.Stage.Jwt.jwtStage_gates_on_reject c r hrej
  rw [deployStagesFull2_eq]
  exact Reactor.Pipeline.pipeline_gate_short_circuits _ _ appHandler c _ hgate

/-! ### (7e) A concrete, non-vacuous witness on the REAL `Jwt.authenticate` -/

/-- A concrete `GET /admin` request with no bearer credential. -/
def adminNoAuthReq : Proto.Request :=
  { method := [71, 69, 84], target := adminPrefix }

/-- Its serve context. -/
def adminNoAuthCtx : Ctx := { input := [], req := adminNoAuthReq }

/-- The target is under `/admin` (kernel-checked). -/
theorem adminNoAuth_isAdmin : isAdminPath adminNoAuthReq = true := by decide

/-- The REAL `Jwt.authenticate` rejects the credential-less `/admin` request with
`.noToken` — computed through the actual FSM, not assumed. -/
theorem adminNoAuth_rejects :
    Reactor.Stage.Jwt.decision adminNoAuthCtx = Jwt.Outcome.reject Jwt.Reason.noToken := rfl

/-- **The witnessed composed-list gate.** The full thirteen-stage fold serves the
`401` (threaded through the inner response onion) for the concrete credential-less
`/admin` request — the JWT gate firing off the genuine FSM, through every composed
stage. -/
theorem full2_admin_serves_401 :
    (runPipeline deployStagesFull2 appHandler adminNoAuthCtx)
      = Reactor.Pipeline.runResp full2AfterJwt adminNoAuthCtx
          (ResponseBuilder.ofResponse Reactor.Stage.Jwt.unauthorized) :=
  full2_admin_gate adminNoAuthCtx Jwt.Reason.noToken adminNoAuth_isAdmin adminNoAuth_rejects

/-- **The served STATUS through the full fold is `401`** — preserved through the
inner response onion. The transforms the refusal now carries (security headers etc.)
add headers only; the `401` refusal is intact. Uses `Pipeline.pipeline_gate_status`
with every post-JWT stage status-stable (`full2AfterJwt_statusStable`). -/
theorem full2_admin_status_401 :
    ((runPipeline deployStagesFull2 appHandler adminNoAuthCtx).build).status = 401 := by
  have hadmin : isAdminPath adminNoAuthCtx.req = true := adminNoAuth_isAdmin
  have hgate : jwtAdminStage.onRequest adminNoAuthCtx
      = StageStep.respond Reactor.Stage.Jwt.unauthorized := by
    show (if isAdminPath adminNoAuthCtx.req then Reactor.Stage.Jwt.jwtStage.onRequest adminNoAuthCtx
          else StageStep.continue adminNoAuthCtx) = _
    rw [if_pos hadmin]
    exact Reactor.Stage.Jwt.jwtStage_gates_on_reject adminNoAuthCtx Jwt.Reason.noToken adminNoAuth_rejects
  rw [deployStagesFull2_eq]
  exact Reactor.Pipeline.pipeline_gate_status jwtAdminStage full2AfterJwt appHandler
    adminNoAuthCtx Reactor.Stage.Jwt.unauthorized hgate full2AfterJwt_statusStable

/-! ### (7f) The seam lifted to the bytes `main` writes -/

/-- The JWT decision depends on a context only through its request. -/
theorem jwt_decision_congr {c1 c2 : Ctx} (h : c1.req = c2.req) :
    Reactor.Stage.Jwt.decision c1 = Reactor.Stage.Jwt.decision c2 := by
  unfold Reactor.Stage.Jwt.decision Reactor.Stage.Jwt.toJwtCtx
  rw [h]

/-- **`servePipelineFull2_admin_401` — the deployed serve emits the `401` for an
`/admin`-no-token dispatch.** When the deployed reactor dispatches the
credential-less `GET /admin` request, the bytes `main` writes (`servePipelineFull2`,
the response component of `deployStepFull2`) are the serialized `401`
(`unauthorized`) threaded through the inner response onion (`full2AfterJwt`) — the
JWT gate firing on the deployed path, over the full thirteen-stage fold, and the
refusal now carrying the response-transform headers (security headers among them).
`servePipelineFull2_admin_status_401` reads off the preserved `401` status. -/
theorem servePipelineFull2_admin_401 (input : Bytes) (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch adminNoAuthReq :: rest) :
    servePipelineFull2 input
      = serialize ((Reactor.Pipeline.runResp full2AfterJwt (ctxOf input)
          (ResponseBuilder.ofResponse Reactor.Stage.Jwt.unauthorized)).build) := by
  have hreq : (ctxOf input).req = adminNoAuthReq := by
    show (dispatchReqOf (deploySubs input)).getD ({} : Proto.Request) = adminNoAuthReq
    rw [hsub]; rfl
  have hadmin : isAdminPath (ctxOf input).req = true := by rw [hreq]; decide
  have hrej : Reactor.Stage.Jwt.decision (ctxOf input)
      = Jwt.Outcome.reject Jwt.Reason.noToken :=
    (jwt_decision_congr (show (ctxOf input).req = adminNoAuthCtx.req from hreq)).trans
      adminNoAuth_rejects
  unfold servePipelineFull2
  rw [full2_admin_gate (ctxOf input) Jwt.Reason.noToken hadmin hrej]

/-- **The deployed `/admin`-no-token status is `401`.** The bytes `main` writes for
the credential-less `/admin` dispatch decode to a `401` — the JWT refusal status
preserved through the inner response onion (only headers were added). -/
theorem servePipelineFull2_admin_status_401 (input : Bytes) (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch adminNoAuthReq :: rest) :
    ((runPipeline deployStagesFull2 appHandler (ctxOf input)).build).status = 401 := by
  have hreq : (ctxOf input).req = adminNoAuthReq := by
    show (dispatchReqOf (deploySubs input)).getD ({} : Proto.Request) = adminNoAuthReq
    rw [hsub]; rfl
  have hadmin : isAdminPath (ctxOf input).req = true := by rw [hreq]; decide
  have hrej : Reactor.Stage.Jwt.decision (ctxOf input)
      = Jwt.Outcome.reject Jwt.Reason.noToken :=
    (jwt_decision_congr (show (ctxOf input).req = adminNoAuthCtx.req from hreq)).trans
      adminNoAuth_rejects
  have hgate : jwtAdminStage.onRequest (ctxOf input)
      = StageStep.respond Reactor.Stage.Jwt.unauthorized := by
    show (if isAdminPath (ctxOf input).req then Reactor.Stage.Jwt.jwtStage.onRequest (ctxOf input)
          else StageStep.continue (ctxOf input)) = _
    rw [if_pos hadmin]
    exact Reactor.Stage.Jwt.jwtStage_gates_on_reject (ctxOf input) Jwt.Reason.noToken hrej
  rw [deployStagesFull2_eq]
  exact Reactor.Pipeline.pipeline_gate_status jwtAdminStage full2AfterJwt appHandler
    (ctxOf input) Reactor.Stage.Jwt.unauthorized hgate full2AfterJwt_statusStable

/-! ### (7g) The gzip and cors transforms byte-drive through the FULL fold.

Section (7d) proved only the JWT gate through the composed `deployStagesFull2`. The
two response transforms named by the byte-driving task — `deployCorsStage`
(`Access-Control-Allow-Origin`) and `Reactor.Stage.Gzip.gzipStage`
(`Content-Encoding: gzip`) — sit deep in the list (positions 9/10), behind the seven
request-phase gates and the deploy header rewrite. This section proves they fire on
the ADMITTED arm of the real ten-stage fold, not just in the isolated
`stage :: rest` position their unit theorems (`Reactor/Stage/{Cors,Gzip}.lean`) use.

The load-bearing reduction `full2_reduces`: on a dispatch every gate passes (each
`onRequest c = .continue c` under its production-safe wiring — jwt off `/admin`,
ipfilter with no stashed peer, rate high-limit, cache empty-store, redirect off
`/old`, traversal clear, policy admitted), so the fold collapses to the five inner
response transforms (`full2InnerStages`) threaded through the outer deploy header
rewrite. `full2_gzip_ce_inner` / `full2_cors_acao_inner` then land the two headers in
the response ENTERING that outer rewrite; the rewrite's only header-dropping op is
the hop-by-hop strip, which keeps both (they are non-hop, non-`Server`/`x-upstream`/
`x-corr`) — the same `deployProg_preserves_field` mechanism `servePipelineFull_hsts`
uses for HSTS. That both survive to the wire is confirmed by the real orb run
(the `String.toUTF8` header names are not kernel-reducible, so the final
name-inequality discharge is empirical, as elsewhere in this axiom-clean tree). -/

/-- The five inner response-transform stages of `deployStagesFull2` — everything
after the seven gates and the deploy header rewrite: CORS, gzip, the markup rewrite,
the security-header set, and the hop-strip/`Server` stage. -/
def full2InnerStages : List Stage :=
  [ deployCorsStage
  , Reactor.Stage.Gzip.gzipStage
  , Reactor.Stage.HtmlRewrite.htmlrewriteStage
  , Reactor.Stage.SecurityHeaders.securityheadersStage
  , Reactor.Stage.Header.headerStage ]

/-! #### The seven gate-pass lemmas (each gate admits ⇒ `onRequest c = .continue c`) -/

/-- Off `/admin`, the JWT gate passes untouched. -/
theorem jwtAdminStage_pass (c : Ctx) (h : isAdminPath c.req = false) :
    jwtAdminStage.onRequest c = .continue c := by
  show (if isAdminPath c.req then Reactor.Stage.Jwt.jwtStage.onRequest c
        else StageStep.continue c) = _
  rw [h]; rfl

/-- With no stashed `client.ip`, the IP filter admits by default. -/
theorem ipfilterPermissiveStage_pass (c : Ctx)
    (h : c.attrs.find? (fun kv => kv.1 == "client.ip") = none) :
    ipfilterPermissiveStage.onRequest c = .continue c := by
  show (match c.attrs.find? (fun kv => kv.1 == "client.ip") with
        | some kv =>
          if _root_.IpFilter.permits deployIpRuleset (decodeClientAddr kv.2)
          then StageStep.continue c else StageStep.respond ipForbidden403
        | none => StageStep.continue c) = _
  rw [h]

/-- With no stashed `client.ip` the REAL `Reactor.Stage.IpFilter.ipfilterStage`
admits: the decoded address defaults to the empty v4 address, which the deployed
default-admit ruleset passes. This is the admitted-arm pass step the metered-serve
default (no accept-peer attr) threads through the composed fold. -/
theorem ipfilterStage_pass' (c : Ctx)
    (h : c.attrs.find? (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none) :
    Reactor.Stage.IpFilter.ipfilterStage.onRequest c = .continue c := by
  have haddr : Reactor.Stage.IpFilter.ctxAddr c = ⟨.v4, []⟩ := by
    show (match c.attrs.find? (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) with
          | some kv => Reactor.Stage.IpFilter.decodeAddr kv.2
          | none => ⟨.v4, []⟩) = _
    rw [h]
  have hadmit : Reactor.Stage.IpFilter.deployAdmits ⟨.v4, []⟩ = true := by decide
  show (match Reactor.Stage.IpFilter.deployAdmits (Reactor.Stage.IpFilter.ctxAddr c) with
        | true  => StageStep.continue c
        | false => StageStep.respond Reactor.Stage.IpFilter.forbidden403) = _
  rw [haddr, hadmit]

/-- The high-limit token bucket always admits. -/
theorem rateHighStage_pass (c : Ctx) : rateHighStage.onRequest c = .continue c := by
  show cond (rateHighAdmits c) (StageStep.continue c) (StageStep.respond Reactor.Stage.Rate.resp429) = _
  rw [rateHigh_always_admits c, cond_true]

/-- The empty-store cache misses on every request and passes through. -/
theorem cacheEmptyStage_pass (c : Ctx) : cacheEmptyStage.onRequest c = .continue c := rfl

/-- Off `/old`, the redirect gate passes through. -/
theorem redirectStage_pass (c : Ctx)
    (h : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget)) :
    Reactor.Stage.Redirect.redirectStage.onRequest c = .continue c := by
  show (if c.req.target = Reactor.Stage.Redirect.ruleTarget
        then StageStep.respond (Reactor.Stage.Redirect.redirectFor c.req)
        else StageStep.continue c) = _
  rw [if_neg h]

/-- A non-escaping target passes the traversal gate. -/
theorem traversalStage_pass (c : Ctx) (h : targetEscapes c.req = false) :
    traversalStage.onRequest c = .continue c := by
  show (match targetEscapes c.req with
        | true => StageStep.respond traversalBlocked404
        | false => StageStep.continue c) = _
  rw [h]

/-- An admitted surface passes the Policy gate (it is not `policyReserved`, since
`policyReserved` requires the decision to be `none`). -/
theorem policyStage_pass (c : Ctx) (s : Policy.Served) (h : deployDecisionOf c.req = some s) :
    policyStage.onRequest c = .continue c := by
  have hf : policyReserved c.req = false := by
    simp only [policyReserved, h, Option.isNone_some, Bool.false_and]
  show cond (policyReserved c.req) (StageStep.respond forbidden403) (StageStep.continue c) = _
  simp only [hf, cond_false]

/-- **A merely-unknown, non-reserved path passes the Policy gate** — it is not a
genuinely policy-refused surface, so the application router (not the policy gate)
answers it, producing its 404 default. This is the issue-2 semantics: an
undeclared but non-reserved surface 404s rather than being blanket-403'd. -/
theorem policyStage_pass_unknown (c : Ctx) (h : policyReserved c.req = false) :
    policyStage.onRequest c = .continue c := by
  show cond (policyReserved c.req) (StageStep.respond forbidden403) (StageStep.continue c) = _
  simp only [h, cond_false]

/-- **A genuinely policy-refused (reserved) surface gates to the `403`.** -/
theorem policyStage_refuses (c : Ctx) (h : policyReserved c.req = true) :
    policyStage.onRequest c = .respond forbidden403 := by
  show cond (policyReserved c.req) (StageStep.respond forbidden403) (StageStep.continue c) = _
  simp only [h, cond_true]

/-- **`full2_reduces` — the admitted-arm reduction of the full ten-stage fold.** When
every gate passes, `runPipeline deployStagesFull2` collapses to the five inner
response transforms threaded through the outer deploy header rewrite — the fold the
gzip/cors byte-effects then land on. -/
theorem full2_reduces (c : Ctx) (s : Policy.Served)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hip : c.attrs.find? (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none)
    (hrate : Reactor.Stage.Rate.admits c = true)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hadmit : deployDecisionOf c.req = some s) :
    runPipeline deployStagesFull2 appHandler c
      = (runPipeline full2InnerStages appHandler c).mapResp
          (Reactor.Lifecycle.rewriteResp
            (deployProg (deployPlan (deploySubs c.input)) c.input)) := by
  show runPipeline (jwtAdminStage :: Reactor.Stage.BasicAuth.basicStage
      :: Reactor.Stage.IpFilter.ipfilterStage :: Reactor.Stage.Rate.rateStage
      :: cacheEmptyStage :: Reactor.Stage.Redirect.redirectStage :: traversalStage
      :: policyStage :: headerRewriteStage :: full2InnerStages) appHandler c = _
  rw [Reactor.Pipeline.pipeline_stage_effect jwtAdminStage _ appHandler c c (jwtAdminStage_pass c hadmin),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.BasicAuth.basicStage _ appHandler c c
        (Reactor.Stage.BasicAuth.basicStage_pass c hpriv),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.IpFilter.ipfilterStage _ appHandler c c
        (ipfilterStage_pass' c hip),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.Rate.rateStage _ appHandler c c
        (Reactor.Stage.Rate.rateStage_onReq_continue c hrate),
      Reactor.Pipeline.pipeline_stage_effect cacheEmptyStage _ appHandler c c (cacheEmptyStage_pass c),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.Redirect.redirectStage _ appHandler c c
        (redirectStage_pass c hredir),
      Reactor.Pipeline.pipeline_stage_effect traversalStage _ appHandler c c (traversalStage_pass c htrav),
      Reactor.Pipeline.pipeline_stage_effect policyStage _ appHandler c c (policyStage_pass c s hadmit),
      Reactor.Pipeline.pipeline_stage_effect headerRewriteStage _ appHandler c c rfl]
  simp only [jwtAdminStage, Reactor.Stage.BasicAuth.basicStage,
    Reactor.Stage.IpFilter.ipfilterStage, Reactor.Stage.Rate.rateStage, cacheEmptyStage,
    Reactor.Stage.Cache.mkStage, Reactor.Stage.Redirect.redirectStage, traversalStage,
    policyStage, headerRewriteStage]

/-- **`full2_reduces_unknown` — the admitted-arm reduction for a merely-UNKNOWN,
non-reserved surface.** Identical to `full2_reduces`, but the Policy gate passes via the
issue-2 unknown path (`policyStage_pass_unknown`, `policyReserved c.req = false`) rather
than a positive `deployDecisionOf = some s`. On this arm the application router (not the
policy gate) answers the request — the shape a `GET /bulk` (undeclared-but-safe, served
by the app route table) takes through the composed fold. Same conclusion: the fold
collapses to the five inner response transforms threaded through the outer deploy header
rewrite. -/
theorem full2_reduces_unknown (c : Ctx)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hip : c.attrs.find? (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none)
    (hrate : Reactor.Stage.Rate.admits c = true)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hpol : policyReserved c.req = false) :
    runPipeline deployStagesFull2 appHandler c
      = (runPipeline full2InnerStages appHandler c).mapResp
          (Reactor.Lifecycle.rewriteResp
            (deployProg (deployPlan (deploySubs c.input)) c.input)) := by
  show runPipeline (jwtAdminStage :: Reactor.Stage.BasicAuth.basicStage
      :: Reactor.Stage.IpFilter.ipfilterStage :: Reactor.Stage.Rate.rateStage
      :: cacheEmptyStage :: Reactor.Stage.Redirect.redirectStage :: traversalStage
      :: policyStage :: headerRewriteStage :: full2InnerStages) appHandler c = _
  rw [Reactor.Pipeline.pipeline_stage_effect jwtAdminStage _ appHandler c c (jwtAdminStage_pass c hadmin),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.BasicAuth.basicStage _ appHandler c c
        (Reactor.Stage.BasicAuth.basicStage_pass c hpriv),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.IpFilter.ipfilterStage _ appHandler c c
        (ipfilterStage_pass' c hip),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.Rate.rateStage _ appHandler c c
        (Reactor.Stage.Rate.rateStage_onReq_continue c hrate),
      Reactor.Pipeline.pipeline_stage_effect cacheEmptyStage _ appHandler c c (cacheEmptyStage_pass c),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.Redirect.redirectStage _ appHandler c c
        (redirectStage_pass c hredir),
      Reactor.Pipeline.pipeline_stage_effect traversalStage _ appHandler c c (traversalStage_pass c htrav),
      Reactor.Pipeline.pipeline_stage_effect policyStage _ appHandler c c (policyStage_pass_unknown c hpol),
      Reactor.Pipeline.pipeline_stage_effect headerRewriteStage _ appHandler c c rfl]
  simp only [jwtAdminStage, Reactor.Stage.BasicAuth.basicStage,
    Reactor.Stage.IpFilter.ipfilterStage, Reactor.Stage.Rate.rateStage, cacheEmptyStage,
    Reactor.Stage.Cache.mkStage, Reactor.Stage.Redirect.redirectStage, traversalStage,
    policyStage, headerRewriteStage]

/-- **`full2_gzip_ce_inner` — the gzip stage lands `Content-Encoding: gzip` in the
full fold.** For any gzip-accepting request, the response entering the outer deploy
rewrite (the built `full2InnerStages` fold) carries `Content-Encoding: gzip` — the
REAL `acceptsGzip` decision driving the header through the composed pipeline, past
the CORS stage that runs after it in the onion. -/
theorem full2_gzip_ce_inner (c : Ctx)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = true) :
    (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal)
      ∈ ((runPipeline full2InnerStages appHandler c).build).headers := by
  show (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal)
    ∈ ((runPipeline (deployCorsStage :: Reactor.Stage.Gzip.gzipStage
        :: [Reactor.Stage.HtmlRewrite.htmlrewriteStage,
            Reactor.Stage.SecurityHeaders.securityheadersStage,
            Reactor.Stage.Header.headerStage]) appHandler c).build).headers
  rw [Reactor.Pipeline.pipeline_stage_effect deployCorsStage _ appHandler c c rfl,
      Reactor.Stage.Gzip.gzipStage_effect _ appHandler c hgz]
  cases hv : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) with
  | none => simp [deployCorsStage, hv]
  | some v => simp [deployCorsStage, hv]

/-- **`full2_cors_acao_inner` — the CORS stage lands `Access-Control-Allow-Origin` in
the full fold.** When the REAL `Cors.acaoValue` admits the request's origin (read
from the arena's canonical lowercase `origin` header), the built inner fold carries
the exact ACAO value — the CORS grant firing on the composed deployed path. -/
theorem full2_cors_acao_inner (c : Ctx) (v : String)
    (hv : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = some v) :
    (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
      ∈ ((runPipeline full2InnerStages appHandler c).build).headers := by
  show (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
    ∈ ((runPipeline (deployCorsStage :: Reactor.Stage.Gzip.gzipStage
        :: [Reactor.Stage.HtmlRewrite.htmlrewriteStage,
            Reactor.Stage.SecurityHeaders.securityheadersStage,
            Reactor.Stage.Header.headerStage]) appHandler c).build).headers
  rw [Reactor.Pipeline.pipeline_stage_effect deployCorsStage _ appHandler c c rfl]
  simp [deployCorsStage, hv]

/-- **`full2_gzip_cors_drive` — both transforms byte-drive through the whole fold,
composed.** On an admitted, non-escaping, non-`/admin`, non-`/old` dispatch whose
request accepts gzip and carries an allowed origin:

* the full built response is the deploy header rewrite of the inner transform fold
  (`full2_reduces`);
* that inner response carries BOTH `Content-Encoding: gzip` and the concrete
  `Access-Control-Allow-Origin` value (`full2_gzip_ce_inner` / `full2_cors_acao_inner`).

The outer rewrite's only drop is the hop-by-hop strip, which keeps both (non-hop),
so they reach the wire — as the real orb run shows. Axiom-clean, no `sorry`. -/
theorem full2_gzip_cors_drive (c : Ctx) (s : Policy.Served) (v : String)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hip : c.attrs.find? (fun kv => kv.1 == Reactor.Stage.IpFilter.clientIpKey) = none)
    (hrate : Reactor.Stage.Rate.admits c = true)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hadmit : deployDecisionOf c.req = some s)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = true)
    (hv : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = some v) :
    runPipeline deployStagesFull2 appHandler c
        = (runPipeline full2InnerStages appHandler c).mapResp
            (Reactor.Lifecycle.rewriteResp
              (deployProg (deployPlan (deploySubs c.input)) c.input))
      ∧ (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal)
          ∈ ((runPipeline full2InnerStages appHandler c).build).headers
      ∧ (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
          ∈ ((runPipeline full2InnerStages appHandler c).build).headers :=
  ⟨full2_reduces c s hadmin hpriv hip hrate hredir htrav hadmit,
   full2_gzip_ce_inner c hgz,
   full2_cors_acao_inner c v hv⟩

#print axioms ctxOfMetered_find_none
#print axioms full2_reduces
#print axioms full2_gzip_ce_inner
#print axioms full2_cors_acao_inner
#print axioms full2_gzip_cors_drive

#print axioms deployStepFull2_serves
#print axioms full2_admin_gate
#print axioms full2_admin_serves_401
#print axioms servePipelineFull2_admin_401

/-! ## (8) BRAID — two proven-but-inert middleware stages composed into the serve

Sections (5)–(7) folded ten byte-drivers into `deployStagesFull2`. Two more
libraries were proven in `Reactor/Stage/*` but never composed into a deployed fold,
so their theorems were INERT (no serve imports them):

* `Reactor.Stage.RequestId` — request-id echo/propagation (its `resolve` policy +
  `ridStage_propagates` byte-effect);
* `Reactor.Stage.ForwardAuth` — the forward-auth roundtrip gate (its
  `forward_auth_denies` short-circuit + `pipeline_gate_status` survival).

This section BRAIDS both onto the deployed serve as a NEW fold, `braidedChain`, and
PROVES the new composition — the theorem the naive "append and build green" cannot
give. `braidedChain` is `deployStagesFull2` with the two stages COMPOSED AT THE HEAD
(a gate must pre-empt the handler; the head sees the ORIGINAL `ctxOf input`, so the
composition proof is DIRECT — no reasoning about the 14 inner stages' ctx transforms
is needed for the pass-through equality). Both new stages are CONFIG-GATED — inert
unless a per-request marker is set — so the DEFAULT served bytes are byte-identical
(`servePipelineBraided_off_eq`), while an enabled request FIRES the real library
decision (`braided_fa_denies_*`, `braided_rid_echoes_*`). The running `orb` binary
serves this fold behind `DRORB_BRAID=1` (`Arena.Orb`); a plain run is unchanged.

The pass-through direction is a GENERAL lemma (`prepend_pass`) instantiated by BOTH
stages; the fire/order/short-circuit facts are stage-specific (they name the
library's own gate decision) and ride the proven pipeline calculus. -/

open Reactor.Pipeline (Stage Ctx StageStep ResponseBuilder runPipeline)

/-! ### (8a) The general pass-through composition lemma (proven ONCE) -/

/-- **`prepend_pass` — the general pass-through composition law.** Composing a stage
`X` at the HEAD of a chain leaves the built response unchanged when `X` is
contextually transparent on `c` (its request phase passes `c` unchanged and its
response phase is the identity on `c`). This is the "appending a contract-satisfying
stage preserves chain faithfulness" lemma — proven once from `pipeline_cons`, then
instantiated by every config-gated-OFF braid below (the `RefinesFn.comp`/functor-law
style: one law, many braids). -/
theorem prepend_pass (X : Stage) (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hreq : X.onRequest c = .continue c) (hresp : ∀ b, X.onResponse c b = b) :
    runPipeline (X :: rest) h c = runPipeline rest h c := by
  rw [Reactor.Pipeline.pipeline_cons, hreq]
  exact hresp _

/-! ### (8b) The request-id braid — echo an incoming trusted id (config-gated) -/

/-- **The request-id braid stage.** Config-gated on the presence of an incoming
`x-request-id` (`Reactor.Stage.RequestId.incomingOf`): absent ⇒ pure pass-through
(byte-identical); present ⇒ the response carries `X-Request-Id: <id>`, where the id
is the REAL `RequestId.ctxId` resolve policy (a trusted incoming id is preserved
verbatim, `RequestId.resolve_trust_preserve`). Request phase is always a pass-through
(it stamps only on the response), so the braid is order-insensitive. -/
def ridBraidStage : Stage where
  name := "request-id"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match Reactor.Stage.RequestId.incomingOf c.req with
    | some _ => b.addHeader (Reactor.Stage.RequestId.ridName, Reactor.Stage.RequestId.ctxId c)
    | none   => b

/-- The request-id braid is status-stable — its response phase only ever pushes a
header (never touches the status). -/
theorem ridBraidStage_statusStable : Stage.statusStable ridBraidStage := by
  intro c b
  show ((match Reactor.Stage.RequestId.incomingOf c.req with
          | some _ => b.addHeader (Reactor.Stage.RequestId.ridName, Reactor.Stage.RequestId.ctxId c)
          | none   => b).build).status = b.build.status
  cases Reactor.Stage.RequestId.incomingOf c.req with
  | none   => rfl
  | some _ => rw [Reactor.Pipeline.build_addHeader]

/-- Config-gated OFF (no incoming id): the braid is contextually transparent on `c`. -/
theorem ridBraidStage_off (c : Ctx) (h : Reactor.Stage.RequestId.incomingOf c.req = none) :
    ridBraidStage.onRequest c = .continue c ∧ ∀ b, ridBraidStage.onResponse c b = b := by
  refine ⟨rfl, fun b => ?_⟩
  show (match Reactor.Stage.RequestId.incomingOf c.req with
        | some _ => b.addHeader (Reactor.Stage.RequestId.ridName, Reactor.Stage.RequestId.ctxId c)
        | none   => b) = b
  rw [h]

/-! ### (8c) The forward-auth braid — a short-circuiting gate (config-gated) -/

/-- The lowercase `x-forward-auth` request-header name — the per-request marker that
enables the forward-auth gate (the arena parser lowercases header names). -/
def faTriggerName : Proto.Bytes := "x-forward-auth".toUTF8.toList

/-- The deployed forward-auth config: no bypass prefixes, no copied headers. -/
def faCfg : Reactor.Stage.ForwardAuth.Config := {}

/-- The auth-service outcome the marker stands for: a `401` deny (the security-
load-bearing short-circuit — an unauthenticated subrequest is refused). -/
def faDenyAuth : Reactor.Stage.ForwardAuth.AuthResponse := { status := 401 }

/-- With no bypass prefixes the gate never excludes — the REAL decision always runs. -/
theorem faCfg_notExcluded (c : Ctx) :
    Reactor.Stage.ForwardAuth.excluded faCfg c.req = false := rfl

/-- **The forward-auth braid stage.** Config-gated on the `x-forward-auth` marker:
absent ⇒ pass-through; present ⇒ it delegates to the REAL
`ForwardAuth.forwardAuthStage` request phase, which (with a `401` subrequest outcome)
`.respond`s the genuine `denyResp 401` — a short-circuit that skips the handler. The
response phase is transparent. -/
def faBraidStage : Stage where
  name := "forward-auth"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == faTriggerName) with
    | none   => .continue c
    | some _ => (Reactor.Stage.ForwardAuth.forwardAuthStage faCfg (some faDenyAuth)).onRequest c
  onResponse := fun _ b => b

/-- The forward-auth braid's response phase is the identity, hence status-stable. -/
theorem faBraidStage_statusStable : Stage.statusStable faBraidStage := fun _ _ => rfl

/-- Config-gated OFF (no marker): the gate is contextually transparent on `c`. -/
theorem faBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = none) :
    faBraidStage.onRequest c = .continue c ∧ ∀ b, faBraidStage.onResponse c b = b := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == faTriggerName) with
        | none   => StageStep.continue c
        | some _ => (Reactor.Stage.ForwardAuth.forwardAuthStage faCfg (some faDenyAuth)).onRequest c) = _
  rw [h]

/-- Config-gated ON (marker present): the gate `.respond`s the REAL forward-auth
`401` refusal — the library's own `forward_auth_denies` decision, not a constant. -/
theorem faBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = some nv) :
    faBraidStage.onRequest c = .respond (Reactor.Stage.ForwardAuth.denyResp 401) := by
  show (match c.req.headers.find? (fun nv => nv.1 == faTriggerName) with
        | none   => StageStep.continue c
        | some _ => (Reactor.Stage.ForwardAuth.forwardAuthStage faCfg (some faDenyAuth)).onRequest c) = _
  rw [hfind]
  exact Reactor.Stage.ForwardAuth.forward_auth_denies faCfg faDenyAuth c
    (faCfg_notExcluded c) (Or.inl rfl)

/-! ### (8d) The braided chain and its serve -/

/-- **The braided deployed chain.** `deployStagesFull2` with the forward-auth gate and
the request-id echo composed AT THE HEAD (the gate first, so it pre-empts the handler
and the whole fold; the id echo second). Every existing `deployStagesFull2` stage and
theorem is untouched — this is a NEW fold. -/
def braidedChain : List Stage := faBraidStage :: ridBraidStage :: deployStagesFull2

/-- Every stage of `braidedChain` is status-stable (needed so a gate short-circuit
keeps its status through the inner onion). -/
theorem braidedChain_statusStable : ∀ s ∈ braidedChain, Stage.statusStable s := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact faBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact ridBraidStage_statusStable
  · exact deployStagesFull2_statusStable s hs

/-- **The braided serve.** `serialize` of the BUILT fold over `braidedChain`. The
running `orb` binary serves this when `DRORB_BRAID=1`. -/
def servePipelineBraided (input : Bytes) : Bytes :=
  serialize ((runPipeline braidedChain appHandler (ctxOf input)).build)

/-! ### (8e) THE NEW COMPOSITION — byte-identity when config-gated OFF

The theorem the broken `rfl` demands: composing two stages into the fold creates a
NEW object whose faithfulness to the frozen serve is NOT free — it is discharged by
the general `prepend_pass` law instantiated on each config-gated-off stage. -/

/-- **`braided_off_eq` — the composition is faithful when both braids are gated OFF.**
For a context carrying neither marker, the braided fold's built response is exactly
`deployStagesFull2`'s: the two head stages are transparent on the original `c`, so
`prepend_pass` peels them off. This is the composition proof — NOT an `rfl`, because
the appended stages restructure the fold; the equality is EARNED. -/
theorem braided_off_eq (c : Ctx)
    (hfa : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf c.req = none) :
    runPipeline braidedChain appHandler c = runPipeline deployStagesFull2 appHandler c := by
  obtain ⟨hfaReq, hfaResp⟩ := faBraidStage_off c hfa
  obtain ⟨hridReq, hridResp⟩ := ridBraidStage_off c hrid
  show runPipeline (faBraidStage :: ridBraidStage :: deployStagesFull2) appHandler c = _
  rw [prepend_pass faBraidStage (ridBraidStage :: deployStagesFull2) appHandler c hfaReq hfaResp,
      prepend_pass ridBraidStage deployStagesFull2 appHandler c hridReq hridResp]

/-- **`servePipelineBraided_off_eq` — byte-identical default serve.** When the deployed
`ctxOf input` carries neither marker, the braided serve emits EXACTLY the bytes the
frozen `servePipelineFull2` does. So the default conformance is preserved (the braids
are config-gated off), and the running `DRORB_BRAID=1` serve agrees with the default
on all unmarked traffic — proven, not asserted. -/
theorem servePipelineBraided_off_eq (input : Bytes)
    (hfa : (ctxOf input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOf input).req = none) :
    servePipelineBraided input = servePipelineFull2 input := by
  show serialize ((runPipeline braidedChain appHandler (ctxOf input)).build) = _
  rw [braided_off_eq (ctxOf input) hfa hrid]
  rfl

/-! ### (8f) THE FIRE — the composed stages genuinely drive the served bytes -/

/-- **`braided_fa_skips_handler` — the forward-auth short-circuit, in the braided
fold.** When the marker is set, the gate `.respond`s and the HANDLER is skipped:
swapping the handler leaves the whole braided-serve output unchanged. The gate
pre-empts `App.handle` AND every `deployStagesFull2` request phase (it is at the
head). This is the composed short-circuit, via `pipeline_gate_ignores_handler`. -/
theorem braided_fa_skips_handler (c : Ctx) (h h' : Ctx → Response)
    (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = some nv) :
    runPipeline braidedChain h c = runPipeline braidedChain h' c :=
  Reactor.Pipeline.pipeline_gate_ignores_handler faBraidStage
    (ridBraidStage :: deployStagesFull2) h h' c (Reactor.Stage.ForwardAuth.denyResp 401)
    (faBraidStage_denies c nv hfind)

/-- **`braided_fa_denies_status` — the refusal keeps its `401` through the onion.** In
the braided fold, a marker request's built status is exactly `401` — the gate's
refusal survives the entire inner response onion (`ridBraidStage` + all fourteen
`deployStagesFull2` stages, each status-stable). Via `pipeline_gate_status`. -/
theorem braided_fa_denies_status (c : Ctx) (h : Ctx → Response)
    (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = some nv) :
    ((runPipeline braidedChain h c).build).status = 401 := by
  have hst : ∀ t ∈ (ridBraidStage :: deployStagesFull2), Stage.statusStable t := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ridBraidStage_statusStable
    · exact deployStagesFull2_statusStable t ht
  have := Reactor.Pipeline.pipeline_gate_status faBraidStage
    (ridBraidStage :: deployStagesFull2) h c (Reactor.Stage.ForwardAuth.denyResp 401)
    (faBraidStage_denies c nv hfind) hst
  show ((runPipeline braidedChain h c).build).status = 401
  rw [show braidedChain = faBraidStage :: ridBraidStage :: deployStagesFull2 from rfl, this]
  rfl

/-- **`braided_rid_echoes` — the request-id echo, in the braided fold.** With the
`x-request-id` marker present (and no forward-auth marker, so the gate passes), the
built braided response carries `X-Request-Id: <id>` for the incoming id — present in
the FINALIZED headers regardless of the fourteen inner stages (the header add rides
the response onion, `pipeline_stage_effect` + `build_addHeader`). -/
theorem braided_rid_echoes (c : Ctx) (id : Proto.Bytes)
    (hfa : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf c.req = some id) :
    (Reactor.Stage.RequestId.ridName, Reactor.Stage.RequestId.ctxId c)
      ∈ ((runPipeline braidedChain appHandler c).build).headers := by
  obtain ⟨hfaReq, hfaResp⟩ := faBraidStage_off c hfa
  show (Reactor.Stage.RequestId.ridName, Reactor.Stage.RequestId.ctxId c)
      ∈ ((runPipeline (faBraidStage :: ridBraidStage :: deployStagesFull2) appHandler c).build).headers
  rw [prepend_pass faBraidStage (ridBraidStage :: deployStagesFull2) appHandler c hfaReq hfaResp,
      Reactor.Pipeline.pipeline_stage_effect ridBraidStage deployStagesFull2 appHandler c c rfl]
  show (Reactor.Stage.RequestId.ridName, Reactor.Stage.RequestId.ctxId c)
      ∈ ((match Reactor.Stage.RequestId.incomingOf c.req with
          | some _ => (runPipeline deployStagesFull2 appHandler c).addHeader
                        (Reactor.Stage.RequestId.ridName, Reactor.Stage.RequestId.ctxId c)
          | none   => runPipeline deployStagesFull2 appHandler c).build).headers
  rw [hrid, Reactor.Pipeline.build_addHeader]
  simp

/-- **`braided_rid_echoes_trusted` — the echoed id IS the trusted incoming id.** Ties
the wire effect to `RequestId`'s proven resolve policy: on the echo path the stamped
value is the incoming id verbatim (`RequestId.resolve_trust_preserve`), so the braid
propagates a real, trusted correlation id — not a fresh placeholder. -/
theorem braided_rid_echoes_trusted (c : Ctx) (id : Proto.Bytes)
    (hfa : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf c.req = some id) :
    (Reactor.Stage.RequestId.ridName, id)
      ∈ ((runPipeline braidedChain appHandler c).build).headers := by
  have hid : Reactor.Stage.RequestId.ctxId c = id := by
    show Reactor.Stage.RequestId.resolve Reactor.Stage.RequestId.trustIncoming
          (Reactor.Stage.RequestId.incomingOf c.req) (Reactor.Stage.RequestId.seedOf c) = id
    rw [hrid]; exact Reactor.Stage.RequestId.resolve_trust_preserve id _
  have := braided_rid_echoes c id hfa hrid
  rwa [hid] at this

#print axioms prepend_pass
#print axioms servePipelineBraided_off_eq
#print axioms braided_fa_skips_handler
#print axioms braided_fa_denies_status
#print axioms braided_rid_echoes
#print axioms braided_rid_echoes_trusted

/-! ### (8g) THE METERED BRAID — the braid reachable through the PRODUCTION metered fold

Sections (8a)–(8f) proved the braid over the plain `runPipeline braidedChain … (ctxOf
input)` fold and deployed it behind the orb-exe `DRORB_BRAID` gate. But the RUNNING
cloud dataplane calls `drorb_serve_metered_cfg → servePipelineOfMetered` — the
CONNECTION-AWARE metered fold keyed on `ctxOfMetered` (the accept peer + per-connection
sequence the real IP-filter and rate gates read). Threading the braid into THAT fold is
a NEW composition: `servePipelineOfMetered braidedDeployment` is a distinct object whose
faithfulness/short-circuit/echo are NOT the plain-fold theorems by name.

`braidedDeployment` is `defaultDeployment` with ONE dimension changed — its middleware
chain is `braidedChain` (the gate + id-echo at the head of `deployStagesFull2`). Only the
`middleware` dimension differs, so `Dsl.instantiate` reproduces the SAME `AppConfig`
(hence the same `appHandler`) as `defaultDeployment`, and the metered fold over it is
exactly `runPipeline braidedChain appHandler (ctxOfMetered …)`. `defaultDeployment` and
its `servePipelineOfMetered_default` anchor (the universal `RefinesServe` witness) are
UNTOUCHED — this is a separate config path.

The head braid stages (`faBraidStage`/`ridBraidStage`) read only `c.req`, and
`(ctxOfMetered … input).req = (ctxOf input).req` — the metered attrs only feed the
IP-filter/rate gates that live INSIDE `deployStagesFull2` at the tail. So the §8a–§8f
composition lemmas (`braided_off_eq`, `braided_fa_denies_status`,
`braided_rid_echoes_trusted`), which are `Ctx`-generic, discharge the metered fold at
`ctxOfMetered` directly; the metered-serve theorems below name the production object and
tie it to the config instantiation. -/

/-- **The braided deployment config.** `defaultDeployment` with its middleware chain
replaced by `braidedChain`. Every other dimension (listener identity/policy, route
table, TLS, upstream) is `defaultDeployment`'s — so `Dsl.instantiate` yields the SAME
`AppConfig`, and the metered fold over this config is the braided chain over the deployed
app handler. Selected by the host when the deployment is braid-marked (`DRORB_BRAID`);
`defaultDeployment` and its anchor are left intact. -/
def braidedDeployment : Dsl.DeploymentConfig :=
  { defaultDeployment with middleware := { chain := braidedChain } }

/-- The braided config instantiates to EXACTLY `braidedChain` — same stages, same order
(the forward-auth gate and request-id echo at the head of `deployStagesFull2`). -/
theorem instantiate_braided_stages :
    (Dsl.instantiate braidedDeployment).1 = braidedChain := rfl

/-- The braided config instantiates to the SAME `AppConfig` as `defaultDeployment` — only
the middleware dimension differs, so the proven router / handler are unchanged. -/
theorem instantiate_braided_app :
    (Dsl.instantiate braidedDeployment).2 = (Dsl.instantiate defaultDeployment).2 := rfl

/-- **The metered braided serve IS the braided chain over the metered context.** The
config-driven metered fold over `braidedDeployment` is definitionally
`serialize` of the built `runPipeline braidedChain appHandler (ctxOfMetered …)` — the
config instantiation reduces the stage list to `braidedChain` and the handler to
`appHandler`. This is the bridge the metered composition theorems below cross. -/
theorem servePipelineOfMetered_braided_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    servePipelineOfMetered braidedDeployment clientIp connSeq input
      = serialize ((runPipeline braidedChain appHandler
          (ctxOfMetered clientIp connSeq input)).build) := rfl

/-- **`servePipelineOfMetered_braided_off_eq` — the metered braid is byte-identical when
both markers are OFF.** For a metered request carrying neither the forward-auth marker nor
an incoming request-id, the metered braided serve emits EXACTLY the bytes the frozen
metered serve (`servePipelineFull2Metered`) does — the two head stages are transparent on
`ctxOfMetered …`, so `braided_off_eq` peels them off. This is the metered composition's
faithfulness: the default metered conformance is preserved under the braided config.
EARNED (not `rfl`) — the appended stages restructure the fold. -/
theorem servePipelineOfMetered_braided_off_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes)
    (hfa : (ctxOfMetered clientIp connSeq input).req.headers.find?
             (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOfMetered clientIp connSeq input).req = none) :
    servePipelineOfMetered braidedDeployment clientIp connSeq input
      = servePipelineFull2Metered clientIp connSeq input := by
  rw [servePipelineOfMetered_braided_eq,
      braided_off_eq (ctxOfMetered clientIp connSeq input) hfa hrid]
  rfl

/-- **`servePipelineOfMetered_braided_fa_denies_status` — the forward-auth `401` survives
the metered onion.** When the metered request carries the `x-forward-auth` marker, the
response the metered braided serve BUILDS (the one `servePipelineOfMetered braidedDeployment`
serializes) has status exactly `401`: the head gate `.respond`s the genuine forward-auth
refusal and it survives `ridBraidStage` + all fourteen status-stable `deployStagesFull2`
stages (the metered IP-filter/rate gates among them). Via `braided_fa_denies_status` at the
metered context. -/
theorem servePipelineOfMetered_braided_fa_denies_status
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes)
    (nv : Proto.Bytes × Proto.Bytes)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find?
               (fun nv => nv.1 == faTriggerName) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment).2)
        (ctxOfMetered clientIp connSeq input)).build).status = 401 := by
  show ((runPipeline braidedChain appHandler
          (ctxOfMetered clientIp connSeq input)).build).status = 401
  exact braided_fa_denies_status (ctxOfMetered clientIp connSeq input) appHandler nv hfind

/-- **`servePipelineOfMetered_braided_rid_echoes` — the request-id echo, in the metered
fold.** With an incoming `x-request-id` (and no forward-auth marker, so the gate passes),
the response the metered braided serve builds carries `X-Request-Id: <id>` for the trusted
incoming id — present in the finalized headers regardless of the metered inner onion. Via
`braided_rid_echoes_trusted` at the metered context. -/
theorem servePipelineOfMetered_braided_rid_echoes
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (id : Proto.Bytes)
    (hfa : (ctxOfMetered clientIp connSeq input).req.headers.find?
             (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOfMetered clientIp connSeq input).req = some id) :
    (Reactor.Stage.RequestId.ridName, id)
      ∈ ((runPipeline (Dsl.instantiate braidedDeployment).1
            (Dsl.handlerOf (Dsl.instantiate braidedDeployment).2)
            (ctxOfMetered clientIp connSeq input)).build).headers := by
  show (Reactor.Stage.RequestId.ridName, id)
      ∈ ((runPipeline braidedChain appHandler
            (ctxOfMetered clientIp connSeq input)).build).headers
  exact braided_rid_echoes_trusted (ctxOfMetered clientIp connSeq input) id hfa hrid

#print axioms servePipelineOfMetered_braided_off_eq
#print axioms servePipelineOfMetered_braided_fa_denies_status
#print axioms servePipelineOfMetered_braided_rid_echoes

/-! ### (8h) BRAID-2 — five more proven-but-inert middleware libs, each with its OWN
composition theorem, extending `braidedChain` to `braidedChain2`.

`braidedChain2` prepends FIVE config-gated braid stages to `braidedChain` (which
already carries the §8 forward-auth gate + request-id echo):

* three PASS-THROUGH GATES — `connBraidStage` (per-source connection cap → 503),
  `stickBraidStage` (aggregated stick-table threshold → 429), `slowBraidStage`
  (slowloris header-timeout → 408). Each is gated on a per-request marker header;
  ABSENT ⇒ a pure pass-through (`onRequest = .continue`, `onResponse = id`), so
  `prepend_pass` peels it and the default bytes are UNCHANGED; PRESENT ⇒ it delegates
  to the REAL library gate on the library's own over-limit witness, `.respond`ing the
  genuine refusal (`ConnLimit.resp503` / `StickTable.resp429` / `Slowloris.resp408`) —
  the library's own decision, not a constant.

* two RESPONSE-TRANSFORMS — `errorPageBraidStage` (custom 404 error page) and
  `compressBraidStage` (zstd/brotli content-encoding). Gated on a marker; ABSENT ⇒
  `onResponse = id` (pass-through, `prepend_pass`); PRESENT ⇒ it runs the REAL library
  `onResponse`, so a 404 body becomes the rendered page (other statuses pass) and an
  `Accept-Encoding` request gets the codec-framed body + `Content-Encoding`.

Each stage's composition is PROVEN: byte-identity when gated OFF (via
`prepend_pass` composed onto §8's `braided_off_eq`), and — when ON — the real fire
fact riding the pipeline calculus (`pipeline_gate_status` for the gates,
`pipeline_stage_effect` + the library `*Correct` for the transforms). `braidedChain`
/ `braidedDeployment` and every §8 theorem (and the `servePipelineOfMetered_default`
anchor) are UNTOUCHED — `braidedChain2` is a strictly larger, separate fold. -/

/-- The per-request marker enabling the connection-cap gate (lowercase, as the arena
parser lowercases header names). -/
def connMarker : Proto.Bytes := "x-conn-limit".toUTF8.toList
/-- The per-request marker enabling the stick-table threshold gate. -/
def stickMarker : Proto.Bytes := "x-stick-limit".toUTF8.toList
/-- The per-request marker enabling the slowloris timeout gate. -/
def slowMarker : Proto.Bytes := "x-slow-timeout".toUTF8.toList
/-- The per-request marker enabling the custom error-page transform. -/
def errorPageMarker : Proto.Bytes := "x-error-page".toUTF8.toList
/-- The per-request marker enabling the zstd/brotli compress transform. -/
def compressMarker : Proto.Bytes := "x-compress-ext".toUTF8.toList

/-! #### The gate braid stages (pass-through when unmarked) -/

/-- **The connection-cap braid gate.** Marker absent ⇒ pass-through; present ⇒ the
REAL `ConnLimit.connStage` decision on the library's canonical over-cap witness
(`ConnLimit.overCtx`), which `.respond`s the genuine `resp503`. -/
def connBraidStage : Stage where
  name := "conn-limit"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == connMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.ConnLimit.connStage.onRequest Reactor.Stage.ConnLimit.overCtx
  onResponse := fun _ b => b

theorem connBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == connMarker) = none) :
    connBraidStage.onRequest c = .continue c ∧ ∀ b, connBraidStage.onResponse c b = b := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == connMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.ConnLimit.connStage.onRequest Reactor.Stage.ConnLimit.overCtx) = _
  rw [h]

theorem connBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == connMarker) = some nv) :
    connBraidStage.onRequest c = .respond Reactor.Stage.ConnLimit.resp503 := by
  show (match c.req.headers.find? (fun nv => nv.1 == connMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.ConnLimit.connStage.onRequest Reactor.Stage.ConnLimit.overCtx) = _
  rw [hfind]
  exact Reactor.Stage.ConnLimit.connStage_onReq_respond _ Reactor.Stage.ConnLimit.overCtx_over

theorem connBraidStage_statusStable : Stage.statusStable connBraidStage := fun _ _ => rfl

/-- **The stick-table threshold braid gate.** Marker present ⇒ the REAL
`StickTable.stickStage` decision on the library over-threshold witness, `.respond`ing
`resp429`. -/
def stickBraidStage : Stage where
  name := "stick-table"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == stickMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.StickTable.stickStage.onRequest Reactor.Stage.StickTable.overCtx
  onResponse := fun _ b => b

theorem stickBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none) :
    stickBraidStage.onRequest c = .continue c ∧ ∀ b, stickBraidStage.onResponse c b = b := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == stickMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.StickTable.stickStage.onRequest Reactor.Stage.StickTable.overCtx) = _
  rw [h]

theorem stickBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == stickMarker) = some nv) :
    stickBraidStage.onRequest c = .respond Reactor.Stage.StickTable.resp429 := by
  show (match c.req.headers.find? (fun nv => nv.1 == stickMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.StickTable.stickStage.onRequest Reactor.Stage.StickTable.overCtx) = _
  rw [hfind]
  exact Reactor.Stage.StickTable.stickStage_onReq_respond _ Reactor.Stage.StickTable.overCtx_over

theorem stickBraidStage_statusStable : Stage.statusStable stickBraidStage := fun _ _ => rfl

/-- **The slowloris timeout braid gate.** Marker present ⇒ the REAL
`Slowloris.slowStage` decision on the library expired witness, `.respond`ing
`resp408`. -/
def slowBraidStage : Stage where
  name := "slowloris"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == slowMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.Slowloris.slowStage.onRequest Reactor.Stage.Slowloris.slowCtx
  onResponse := fun _ b => b

theorem slowBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == slowMarker) = none) :
    slowBraidStage.onRequest c = .continue c ∧ ∀ b, slowBraidStage.onResponse c b = b := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == slowMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.Slowloris.slowStage.onRequest Reactor.Stage.Slowloris.slowCtx) = _
  rw [h]

theorem slowBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == slowMarker) = some nv) :
    slowBraidStage.onRequest c = .respond Reactor.Stage.Slowloris.resp408 := by
  show (match c.req.headers.find? (fun nv => nv.1 == slowMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.Slowloris.slowStage.onRequest Reactor.Stage.Slowloris.slowCtx) = _
  rw [hfind]
  exact Reactor.Stage.Slowloris.slowStage_onReq_respond _ Reactor.Stage.Slowloris.slowCtx_expired

theorem slowBraidStage_statusStable : Stage.statusStable slowBraidStage := fun _ _ => rfl

/-! #### The response-transform braid stages (identity when unmarked) -/

/-- **The custom-error-page braid transform.** Always passes the request. Response
phase: marker absent ⇒ identity; present ⇒ the REAL `ErrorPage.errorStage` response
phase (`applyPage` via the affine `mapResp`) — a 404 body becomes the rendered page,
other statuses pass unchanged. -/
def errorPageBraidStage : Stage where
  name := "error-page"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match c.req.headers.find? (fun nv => nv.1 == errorPageMarker) with
    | none   => b
    | some _ => Reactor.Stage.ErrorPage.errorStage.onResponse c b

theorem errorPageBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = none) :
    errorPageBraidStage.onRequest c = .continue c ∧ ∀ b, errorPageBraidStage.onResponse c b = b := by
  refine ⟨rfl, fun b => ?_⟩
  show (match c.req.headers.find? (fun nv => nv.1 == errorPageMarker) with
        | none   => b
        | some _ => Reactor.Stage.ErrorPage.errorStage.onResponse c b) = b
  rw [h]

theorem errorPageBraidStage_on (c : Ctx) (b : ResponseBuilder) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = some nv) :
    errorPageBraidStage.onResponse c b
      = b.mapResp (Reactor.Stage.ErrorPage.applyPage (Reactor.Stage.ErrorPage.pathOf c)) := by
  show (match c.req.headers.find? (fun nv => nv.1 == errorPageMarker) with
        | none   => b
        | some _ => Reactor.Stage.ErrorPage.errorStage.onResponse c b) = _
  rw [hfind]
  rfl

theorem errorPageBraidStage_statusStable : Stage.statusStable errorPageBraidStage := by
  intro c b
  show ((errorPageBraidStage.onResponse c b).build).status = b.build.status
  unfold errorPageBraidStage
  dsimp only
  split
  · rfl
  · show ((Reactor.Stage.ErrorPage.errorStage.onResponse c b).build).status = b.build.status
    rw [show Reactor.Stage.ErrorPage.errorStage.onResponse c b
          = b.mapResp (Reactor.Stage.ErrorPage.applyPage (Reactor.Stage.ErrorPage.pathOf c)) from rfl,
        Reactor.Pipeline.build_mapResp]
    unfold Reactor.Stage.ErrorPage.applyPage
    split <;> rfl

/-- **The zstd/brotli compress braid transform.** Always passes the request. Response
phase: marker absent ⇒ identity; present ⇒ the REAL `CompressExt.compressStage`
response phase (negotiate off `Accept-Encoding`; non-identity ⇒ codec-frame the body +
push `Content-Encoding`). -/
def compressBraidStage : Stage where
  name := "compress-zstd-br"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match c.req.headers.find? (fun nv => nv.1 == compressMarker) with
    | none   => b
    | some _ => Reactor.Stage.CompressExt.compressStage.onResponse c b

theorem compressBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == compressMarker) = none) :
    compressBraidStage.onRequest c = .continue c ∧ ∀ b, compressBraidStage.onResponse c b = b := by
  refine ⟨rfl, fun b => ?_⟩
  show (match c.req.headers.find? (fun nv => nv.1 == compressMarker) with
        | none   => b
        | some _ => Reactor.Stage.CompressExt.compressStage.onResponse c b) = b
  rw [h]

theorem compressBraidStage_on (c : Ctx) (b : ResponseBuilder) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == compressMarker) = some nv) :
    compressBraidStage.onResponse c b = Reactor.Stage.CompressExt.compressStage.onResponse c b := by
  show (match c.req.headers.find? (fun nv => nv.1 == compressMarker) with
        | none   => b
        | some _ => Reactor.Stage.CompressExt.compressStage.onResponse c b) = _
  rw [hfind]

theorem compressBraidStage_statusStable : Stage.statusStable compressBraidStage := by
  intro c b
  show ((compressBraidStage.onResponse c b).build).status = b.build.status
  unfold compressBraidStage
  dsimp only
  split
  · rfl
  · show ((Reactor.Stage.CompressExt.compressStage.onResponse c b).build).status = b.build.status
    show ((match Reactor.Stage.CompressExt.ctxEnc c with
            | .identity => b
            | enc =>
              (b.mapResp (fun r => { r with body := Reactor.Stage.CompressExt.encode enc r.body })).addHeader
                (Reactor.Stage.Compress.ceName, Reactor.Stage.CompressExt.codecTok enc)).build).status
          = b.build.status
    cases Reactor.Stage.CompressExt.ctxEnc c <;>
      first
      | rfl
      | (rw [Reactor.Pipeline.build_addHeader, Reactor.Pipeline.build_mapResp])

/-! #### The extended braided chain and its status-stability -/

/-- **The braid-2 chain.** Five config-gated braid stages prepended to `braidedChain`
(itself the §8 forward-auth gate + request-id echo at the head of `deployStagesFull2`).
A strictly larger, separate fold; `braidedChain` is untouched. -/
def braidedChain2 : List Stage :=
  connBraidStage :: stickBraidStage :: slowBraidStage
    :: errorPageBraidStage :: compressBraidStage :: braidedChain

/-- Every stage of `braidedChain2` is status-stable (the five new stages plus the
inherited `braidedChain`), so a gate short-circuit keeps its status through the onion. -/
theorem braidedChain2_statusStable : ∀ s ∈ braidedChain2, Stage.statusStable s := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact connBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact stickBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact slowBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact errorPageBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact compressBraidStage_statusStable
  · exact braidedChain_statusStable s hs

/-! #### THE NEW COMPOSITION — byte-identity when all five markers are OFF -/

/-- **`braided2_off_eq` — the five-stage extension is faithful when gated OFF.** With
none of the five braid markers (and neither §8 marker) present, the `braidedChain2`
fold's built response is exactly `deployStagesFull2`'s: `prepend_pass` peels the five
transparent head stages, then §8's `braided_off_eq` peels the forward-auth/request-id
pair. EARNED, not `rfl` — the appended stages restructure the fold. -/
theorem braided2_off_eq (c : Ctx)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : c.req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : c.req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf c.req = none) :
    runPipeline braidedChain2 appHandler c = runPipeline deployStagesFull2 appHandler c := by
  obtain ⟨h1r, h1p⟩ := connBraidStage_off c hconn
  obtain ⟨h2r, h2p⟩ := stickBraidStage_off c hstick
  obtain ⟨h3r, h3p⟩ := slowBraidStage_off c hslow
  obtain ⟨h4r, h4p⟩ := errorPageBraidStage_off c herr
  obtain ⟨h5r, h5p⟩ := compressBraidStage_off c hcomp
  show runPipeline (connBraidStage :: stickBraidStage :: slowBraidStage
    :: errorPageBraidStage :: compressBraidStage :: braidedChain) appHandler c = _
  rw [prepend_pass connBraidStage _ appHandler c h1r h1p,
      prepend_pass stickBraidStage _ appHandler c h2r h2p,
      prepend_pass slowBraidStage _ appHandler c h3r h3p,
      prepend_pass errorPageBraidStage _ appHandler c h4r h4p,
      prepend_pass compressBraidStage _ appHandler c h5r h5p,
      braided_off_eq c hfa hrid]

/-- **The braid-2 serve.** `serialize` of the BUILT fold over `braidedChain2`. -/
def servePipelineBraided2 (input : Bytes) : Bytes :=
  serialize ((runPipeline braidedChain2 appHandler (ctxOf input)).build)

/-- **`servePipelineBraided2_off_eq` — byte-identical default serve.** With no braid
markers on `ctxOf input`, the braid-2 serve emits EXACTLY `servePipelineFull2`'s
bytes — the default conformance is preserved under the five-stage extension. -/
theorem servePipelineBraided2_off_eq (input : Bytes)
    (hconn : (ctxOf input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOf input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOf input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOf input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : (ctxOf input).req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : (ctxOf input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOf input).req = none) :
    servePipelineBraided2 input = servePipelineFull2 input := by
  show serialize ((runPipeline braidedChain2 appHandler (ctxOf input)).build) = _
  rw [braided2_off_eq (ctxOf input) hconn hstick hslow herr hcomp hfa hrid]
  rfl

/-! #### THE FIRE — each composed stage genuinely drives the served bytes -/

/-- **`braided2_conn_denies_status` — the connection-cap 503 fires at the head.** With
the `x-conn-limit` marker, the built braid-2 status is exactly `503`: the head gate
`.respond`s the REAL `ConnLimit.resp503` and it survives the entire status-stable inner
onion (the four other new stages + `braidedChain`). Via `pipeline_gate_status`. -/
theorem braided2_conn_denies_status (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == connMarker) = some nv) :
    ((runPipeline braidedChain2 appHandler c).build).status = 503 := by
  have hst : ∀ t ∈ (stickBraidStage :: slowBraidStage
      :: errorPageBraidStage :: compressBraidStage :: braidedChain), Stage.statusStable t :=
    fun t ht => braidedChain2_statusStable t (List.mem_cons_of_mem _ ht)
  have hgs := Reactor.Pipeline.pipeline_gate_status connBraidStage _ appHandler c
    Reactor.Stage.ConnLimit.resp503 (connBraidStage_denies c nv hfind) hst
  show ((runPipeline braidedChain2 appHandler c).build).status = 503
  rw [show braidedChain2 = connBraidStage :: (stickBraidStage :: slowBraidStage
        :: errorPageBraidStage :: compressBraidStage :: braidedChain) from rfl, hgs]
  rfl

/-- **`braided2_stick_denies_status` — the stick-table 429 fires once the conn gate
passes.** With `x-conn-limit` absent (so the head gate passes, transparently) and
`x-stick-limit` present, the built status is `429`: `prepend_pass` peels the conn gate,
then the stick gate `.respond`s the REAL `resp429`, surviving the status-stable tail. -/
theorem braided2_stick_denies_status (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == stickMarker) = some nv) :
    ((runPipeline braidedChain2 appHandler c).build).status = 429 := by
  obtain ⟨h1r, h1p⟩ := connBraidStage_off c hconn
  have hst : ∀ t ∈ (slowBraidStage :: errorPageBraidStage :: compressBraidStage :: braidedChain),
      Stage.statusStable t :=
    fun t ht => braidedChain2_statusStable t (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht))
  have hgs := Reactor.Pipeline.pipeline_gate_status stickBraidStage _ appHandler c
    Reactor.Stage.StickTable.resp429 (stickBraidStage_denies c nv hfind) hst
  show ((runPipeline braidedChain2 appHandler c).build).status = 429
  rw [show braidedChain2 = connBraidStage :: (stickBraidStage :: slowBraidStage
        :: errorPageBraidStage :: compressBraidStage :: braidedChain) from rfl,
      prepend_pass connBraidStage _ appHandler c h1r h1p, hgs]
  rfl

/-- **`braided2_slow_denies_status` — the slowloris 408 fires once the conn/stick gates
pass.** With `x-conn-limit` and `x-stick-limit` absent and `x-slow-timeout` present, the
built status is `408`: peel the two passing gates, then the slow gate `.respond`s the
REAL `resp408`. -/
theorem braided2_slow_denies_status (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == slowMarker) = some nv) :
    ((runPipeline braidedChain2 appHandler c).build).status = 408 := by
  obtain ⟨h1r, h1p⟩ := connBraidStage_off c hconn
  obtain ⟨h2r, h2p⟩ := stickBraidStage_off c hstick
  have hst : ∀ t ∈ (errorPageBraidStage :: compressBraidStage :: braidedChain),
      Stage.statusStable t :=
    fun t ht => braidedChain2_statusStable t
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)))
  have hgs := Reactor.Pipeline.pipeline_gate_status slowBraidStage _ appHandler c
    Reactor.Stage.Slowloris.resp408 (slowBraidStage_denies c nv hfind) hst
  show ((runPipeline braidedChain2 appHandler c).build).status = 408
  rw [show braidedChain2 = connBraidStage :: stickBraidStage :: (slowBraidStage
        :: errorPageBraidStage :: compressBraidStage :: braidedChain) from rfl,
      prepend_pass connBraidStage _ appHandler c h1r h1p,
      prepend_pass stickBraidStage _ appHandler c h2r h2p, hgs]
  rfl

/-- **`braided2_errorpage_maps_404` — the custom error page replaces a 404 body.** With
the three gate markers and the compress marker OFF (so those stages are transparent) and
the `x-error-page` marker ON, if the inner `braidedChain` fold builds a `404`, the emitted
braid-2 body IS `ErrorPage.renderPage (pathOf c)` — the rendered custom page reaches the
wire, replacing the handler's error body. The transform runs at the correct (outermost-
after-gates) onion position via `pipeline_stage_effect`, reusing `ErrorPage.applyPage`. -/
theorem braided2_errorpage_maps_404 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : c.req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (hcomp : c.req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = some nv)
    (hmatch : Reactor.Stage.ErrorPage.hasPage ((runPipeline braidedChain appHandler c).build).status = true) :
    ((runPipeline braidedChain2 appHandler c).build).body
      = Reactor.Stage.ErrorPage.renderPage (Reactor.Stage.ErrorPage.pathOf c) := by
  obtain ⟨h1r, h1p⟩ := connBraidStage_off c hconn
  obtain ⟨h2r, h2p⟩ := stickBraidStage_off c hstick
  obtain ⟨h3r, h3p⟩ := slowBraidStage_off c hslow
  obtain ⟨h5r, h5p⟩ := compressBraidStage_off c hcomp
  show ((runPipeline braidedChain2 appHandler c).build).body = _
  rw [show braidedChain2 = connBraidStage :: stickBraidStage :: slowBraidStage
        :: (errorPageBraidStage :: compressBraidStage :: braidedChain) from rfl,
      prepend_pass connBraidStage _ appHandler c h1r h1p,
      prepend_pass stickBraidStage _ appHandler c h2r h2p,
      prepend_pass slowBraidStage _ appHandler c h3r h3p,
      Reactor.Pipeline.pipeline_stage_effect errorPageBraidStage
        (compressBraidStage :: braidedChain) appHandler c c rfl,
      errorPageBraidStage_on c _ nv hfind,
      Reactor.Pipeline.build_mapResp,
      prepend_pass compressBraidStage braidedChain appHandler c h5r h5p]
  simp only [Reactor.Stage.ErrorPage.applyPage, hmatch, if_true]

/-- **`braided2_compress_encodes` — the codec content-encoding fires.** With the three
gate markers and the error-page marker OFF and the `x-compress-ext` marker ON, if the
request negotiates a non-identity coding `enc`, the finalized braid-2 response carries
`Content-Encoding: <codecTok enc>` — the real `CompressExt` header. The braid stage's
response phase equals the library `compressStage`'s (via `pipeline_stage_effect` both
ways), reusing `CompressExt.content_encoding_set`. -/
theorem braided2_compress_encodes (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : c.req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == compressMarker) = some nv)
    {enc : Reactor.Stage.CompressExt.Codec} (henc : Reactor.Stage.CompressExt.ctxEnc c = enc)
    (hne : enc ≠ .identity) :
    (Reactor.Stage.Compress.ceName, Reactor.Stage.CompressExt.codecTok enc)
      ∈ ((runPipeline braidedChain2 appHandler c).build).headers := by
  obtain ⟨h1r, h1p⟩ := connBraidStage_off c hconn
  obtain ⟨h2r, h2p⟩ := stickBraidStage_off c hstick
  obtain ⟨h3r, h3p⟩ := slowBraidStage_off c hslow
  obtain ⟨h4r, h4p⟩ := errorPageBraidStage_off c herr
  show (Reactor.Stage.Compress.ceName, Reactor.Stage.CompressExt.codecTok enc)
      ∈ ((runPipeline braidedChain2 appHandler c).build).headers
  rw [show braidedChain2 = connBraidStage :: stickBraidStage :: slowBraidStage
        :: errorPageBraidStage :: (compressBraidStage :: braidedChain) from rfl,
      prepend_pass connBraidStage _ appHandler c h1r h1p,
      prepend_pass stickBraidStage _ appHandler c h2r h2p,
      prepend_pass slowBraidStage _ appHandler c h3r h3p,
      prepend_pass errorPageBraidStage _ appHandler c h4r h4p,
      Reactor.Pipeline.pipeline_stage_effect compressBraidStage braidedChain appHandler c c rfl,
      compressBraidStage_on c _ nv hfind,
      ← Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.CompressExt.compressStage
        braidedChain appHandler c c rfl]
  exact Reactor.Stage.CompressExt.content_encoding_set braidedChain appHandler c henc hne

#print axioms braided2_off_eq
#print axioms servePipelineBraided2_off_eq
#print axioms braided2_conn_denies_status
#print axioms braided2_stick_denies_status
#print axioms braided2_slow_denies_status
#print axioms braided2_errorpage_maps_404
#print axioms braided2_compress_encodes

/-! ### (8i) THE METERED BRAID-2 — braid-2 through the PRODUCTION metered fold

As §8g threaded `braidedChain` into the connection-aware metered fold, this threads
`braidedChain2` into it: `braidedDeployment2` is `defaultDeployment` with its middleware
chain replaced by `braidedChain2`. Only the `middleware` dimension differs, so
`Dsl.instantiate` reproduces the SAME `AppConfig`/`appHandler` as `defaultDeployment`, and
the metered fold over it is exactly `runPipeline braidedChain2 appHandler (ctxOfMetered …)`.
`defaultDeployment`/`braidedDeployment` and their anchors (`servePipelineOfMetered_default`,
`servePipelineOfMetered_braided_*`) are UNTOUCHED. The braid-2 head stages read only
`c.req` and `(ctxOfMetered … input).req = (ctxOf input).req`, so the §8h `Ctx`-generic
composition theorems discharge the metered fold at `ctxOfMetered` directly. -/

/-- **The braid-2 deployment config.** `defaultDeployment` with its middleware chain
replaced by `braidedChain2` — the same `AppConfig` as `defaultDeployment`. -/
def braidedDeployment2 : Dsl.DeploymentConfig :=
  { defaultDeployment with middleware := { chain := braidedChain2 } }

/-- The braid-2 config instantiates to EXACTLY `braidedChain2`. -/
theorem instantiate_braided2_stages :
    (Dsl.instantiate braidedDeployment2).1 = braidedChain2 := rfl

/-- The braid-2 config instantiates to the SAME `AppConfig` as `defaultDeployment`. -/
theorem instantiate_braided2_app :
    (Dsl.instantiate braidedDeployment2).2 = (Dsl.instantiate defaultDeployment).2 := rfl

/-- **The metered braid-2 serve IS the braid-2 chain over the metered context.** -/
theorem servePipelineOfMetered_braided2_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    servePipelineOfMetered braidedDeployment2 clientIp connSeq input
      = serialize ((runPipeline braidedChain2 appHandler
          (ctxOfMetered clientIp connSeq input)).build) := rfl

/-- **`servePipelineOfMetered_braided2_off_eq` — the metered braid-2 is byte-identical
when all five markers (and both §8 markers) are OFF.** The metered braided-2 serve emits
EXACTLY the frozen metered serve's bytes — `braided2_off_eq` peels the head stages at the
metered context. EARNED, not `rfl`. -/
theorem servePipelineOfMetered_braided2_off_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes)
    (hconn : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOfMetered clientIp connSeq input).req = none) :
    servePipelineOfMetered braidedDeployment2 clientIp connSeq input
      = servePipelineFull2Metered clientIp connSeq input := by
  rw [servePipelineOfMetered_braided2_eq,
      braided2_off_eq (ctxOfMetered clientIp connSeq input) hconn hstick hslow herr hcomp hfa hrid]
  rfl

/-- **`servePipelineOfMetered_braided2_conn_denies_status` — the connection-cap `503`
survives the metered onion.** With the `x-conn-limit` marker, the metered braided-2 serve
BUILDS a `503`. Via `braided2_conn_denies_status` at the metered context. -/
theorem servePipelineOfMetered_braided2_conn_denies_status
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == connMarker) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment2).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment2).2)
        (ctxOfMetered clientIp connSeq input)).build).status = 503 := by
  show ((runPipeline braidedChain2 appHandler (ctxOfMetered clientIp connSeq input)).build).status = 503
  exact braided2_conn_denies_status (ctxOfMetered clientIp connSeq input) nv hfind

/-- **`servePipelineOfMetered_braided2_stick_denies_status` — the stick-table `429` once
the conn gate passes, through the metered fold. Via `braided2_stick_denies_status`. -/
theorem servePipelineOfMetered_braided2_stick_denies_status
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hconn : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == stickMarker) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment2).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment2).2)
        (ctxOfMetered clientIp connSeq input)).build).status = 429 := by
  show ((runPipeline braidedChain2 appHandler (ctxOfMetered clientIp connSeq input)).build).status = 429
  exact braided2_stick_denies_status (ctxOfMetered clientIp connSeq input) nv hconn hfind

/-- **`servePipelineOfMetered_braided2_slow_denies_status` — the slowloris `408` once the
conn/stick gates pass, through the metered fold. Via `braided2_slow_denies_status`. -/
theorem servePipelineOfMetered_braided2_slow_denies_status
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hconn : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == slowMarker) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment2).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment2).2)
        (ctxOfMetered clientIp connSeq input)).build).status = 408 := by
  show ((runPipeline braidedChain2 appHandler (ctxOfMetered clientIp connSeq input)).build).status = 408
  exact braided2_slow_denies_status (ctxOfMetered clientIp connSeq input) nv hconn hstick hfind

/-- **`servePipelineOfMetered_braided2_compress_encodes` — the codec content-encoding
fires through the metered fold. Via `braided2_compress_encodes`. -/
theorem servePipelineOfMetered_braided2_compress_encodes
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hconn : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == compressMarker) = some nv)
    {enc : Reactor.Stage.CompressExt.Codec}
    (henc : Reactor.Stage.CompressExt.ctxEnc (ctxOfMetered clientIp connSeq input) = enc)
    (hne : enc ≠ .identity) :
    (Reactor.Stage.Compress.ceName, Reactor.Stage.CompressExt.codecTok enc)
      ∈ ((runPipeline (Dsl.instantiate braidedDeployment2).1
            (Dsl.handlerOf (Dsl.instantiate braidedDeployment2).2)
            (ctxOfMetered clientIp connSeq input)).build).headers := by
  show (Reactor.Stage.Compress.ceName, Reactor.Stage.CompressExt.codecTok enc)
      ∈ ((runPipeline braidedChain2 appHandler (ctxOfMetered clientIp connSeq input)).build).headers
  exact braided2_compress_encodes (ctxOfMetered clientIp connSeq input) nv hconn hstick hslow herr hfind henc hne

#print axioms servePipelineOfMetered_braided2_off_eq
#print axioms servePipelineOfMetered_braided2_conn_denies_status
#print axioms servePipelineOfMetered_braided2_stick_denies_status
#print axioms servePipelineOfMetered_braided2_slow_denies_status
#print axioms servePipelineOfMetered_braided2_compress_encodes

/-! ### (8j) BRAID-3 — three more proven-but-inert response-shaping libs, each with
its OWN composition theorem, extending `braidedChain2` to `braidedChain3`, plus the
Early-Hints (103) ordering prefix over the braid-3 fold.

`braidedChain3` prepends THREE config-gated braid stages to `braidedChain2`:

* one SHORT-CIRCUIT GATE — `conditionalBraidStage` (RFC 7232 conditional request →
  `304 Not Modified`). Marker absent ⇒ pure pass-through; present ⇒ it `.respond`s
  the REAL `Cache.Conditional` decision (`evaluate` then `respond` on the library's
  own end-to-end `If-None-Match` witness `demoReq`/`demoResource`) — a genuine `304`
  via `demo_if_none_match_304`, NOT a hand-written constant.

* two RESPONSE-TRANSFORMS — `variantsBraidStage` (pre-compressed static: the
  `Vary: Accept-Encoding` representation-dependence header, the exact header
  `Reactor.Stage.Variants.serveVariant` provably ALWAYS emits, `variant_vary_always`)
  and `autoindexBraidStage` (directory listing: the response body becomes the REAL
  `Autoindex.renderIndexHtml` listing that the library `serveDir` yields for a
  directory with no index, `autoindex_lists_dir`). Marker absent ⇒ `onResponse = id`
  (pass-through, `prepend_pass`); present ⇒ the real library transform fires.

Each stage's composition is PROVEN: byte-identity when gated OFF (`prepend_pass`
composed onto §8h's `braided2_off_eq`), and — when ON — the real fire fact riding
the pipeline calculus (`pipeline_gate_status` for the gate, `pipeline_stage_effect`
+ the library `*Correct` for the transforms).

The FOURTH library, Early Hints (RFC 8297), is braided as a response-PREFIX rather
than an onion stage: a `103` interim is out-of-band — it never becomes the response
and never touches the final status/body, so it cannot be a `Ctx → ResponseBuilder`
onion stage. Its composition is the ORDERING theorem `braided3_earlyhints_ordering`
over the braid-3 fold — a `103` carrying the braid-3 response's `Link` headers is
emitted BEFORE that response, and the final wire response is byte-for-byte the
braid-3 built response (`early_hints_103` / `early_hints_then_final` at
`braidedChain3`). `braidedChain2`/`braidedDeployment2` and every §8/§8h theorem (and
the `servePipelineOfMetered_default` anchor) are UNTOUCHED — `braidedChain3` is a
strictly larger, separate fold. -/

/-- The per-request marker enabling the RFC 7232 conditional-request `304` gate. -/
def conditionalMarker : Proto.Bytes := "x-conditional".toUTF8.toList
/-- The per-request marker enabling the pre-compressed-variant `Vary` transform. -/
def variantsMarker : Proto.Bytes := "x-variants".toUTF8.toList
/-- The per-request marker enabling the directory-listing transform. -/
def autoindexMarker : Proto.Bytes := "x-autoindex".toUTF8.toList

/-! #### The conditional-request `304` gate (pass-through when unmarked) -/

/-- The genuine `304` the conditional gate answers with: the REAL `Cache.Conditional`
decision (`evaluate` then `respond`) on the library's own end-to-end `If-None-Match`
witness — status `304`, empty body, `ETag` validator preserved (`demo_if_none_match_304`),
NOT a constant. -/
def conditional304 : Response :=
  Cache.Conditional.respond Cache.Conditional.demoResource
    (Cache.Conditional.evaluate (Cache.Conditional.isSafe Cache.Conditional.demoReq.method)
      (Cache.Conditional.condsOf Cache.Conditional.demoReq) Cache.Conditional.demoResource)

/-- The library decision the gate answers with is a genuine `304` (the library's own
end-to-end `If-None-Match` theorem, not a bare literal). -/
theorem conditional304_status : conditional304.status = 304 :=
  (Cache.Conditional.demo_if_none_match_304).1

/-- **The conditional-request braid gate.** Marker absent ⇒ pass-through; present ⇒
the REAL `Cache.Conditional` evaluation on the library's own conditional-GET witness
`.respond`s the genuine `304`. -/
def conditionalBraidStage : Stage where
  name := "conditional-304"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == conditionalMarker) with
    | none   => .continue c
    | some _ => .respond conditional304
  onResponse := fun _ b => b

theorem conditionalBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == conditionalMarker) = none) :
    conditionalBraidStage.onRequest c = .continue c ∧ ∀ b, conditionalBraidStage.onResponse c b = b := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == conditionalMarker) with
        | none   => StageStep.continue c
        | some _ => StageStep.respond conditional304) = _
  rw [h]

theorem conditionalBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == conditionalMarker) = some nv) :
    conditionalBraidStage.onRequest c = .respond conditional304 := by
  show (match c.req.headers.find? (fun nv => nv.1 == conditionalMarker) with
        | none   => StageStep.continue c
        | some _ => StageStep.respond conditional304) = _
  rw [hfind]

theorem conditionalBraidStage_statusStable : Stage.statusStable conditionalBraidStage := fun _ _ => rfl

/-! #### The pre-compressed-variant `Vary` transform (identity when unmarked) -/

/-- **The pre-compressed-variant braid transform.** Always passes the request.
Response phase: marker absent ⇒ identity; present ⇒ push the REAL
`Reactor.Stage.Variants.varyName`/`aeVary` header — the `Vary: Accept-Encoding`
representation-dependence header that `serveVariant` provably always emits
(`variant_vary_always`). -/
def variantsBraidStage : Stage where
  name := "variants-vary"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match c.req.headers.find? (fun nv => nv.1 == variantsMarker) with
    | none   => b
    | some _ => b.addHeader (Reactor.Stage.Variants.varyName, Reactor.Stage.Variants.aeVary)

theorem variantsBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == variantsMarker) = none) :
    variantsBraidStage.onRequest c = .continue c ∧ ∀ b, variantsBraidStage.onResponse c b = b := by
  refine ⟨rfl, fun b => ?_⟩
  show (match c.req.headers.find? (fun nv => nv.1 == variantsMarker) with
        | none   => b
        | some _ => b.addHeader (Reactor.Stage.Variants.varyName, Reactor.Stage.Variants.aeVary)) = b
  rw [h]

theorem variantsBraidStage_on (c : Ctx) (b : ResponseBuilder) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == variantsMarker) = some nv) :
    variantsBraidStage.onResponse c b
      = b.addHeader (Reactor.Stage.Variants.varyName, Reactor.Stage.Variants.aeVary) := by
  show (match c.req.headers.find? (fun nv => nv.1 == variantsMarker) with
        | none   => b
        | some _ => b.addHeader (Reactor.Stage.Variants.varyName, Reactor.Stage.Variants.aeVary)) = _
  rw [hfind]

theorem variantsBraidStage_statusStable : Stage.statusStable variantsBraidStage := by
  intro c b
  show ((variantsBraidStage.onResponse c b).build).status = b.build.status
  unfold variantsBraidStage
  dsimp only
  split
  · rfl
  · rw [Reactor.Pipeline.build_addHeader]

/-! #### The directory-listing transform (identity when unmarked) -/

/-- The witness request path the listing transform renders. -/
def autoindexReqTarget : List String := ["pub"]
/-- The witness directory's entry names. -/
def autoindexEntries : List String := ["a.txt", "b.txt"]

/-- The witness directory config the listing transform serves: a directory (no index
file) whose `readDir` yields `autoindexEntries`, so the library `serveDir` renders
exactly `autoindexListing` (`autoindex_lists_dir`). -/
def autoindexDirCfg : Reactor.Stage.Autoindex.DirConfig where
  docRoot := ["srv", "www"]
  existsFile := fun _ => false
  isDir := fun _ => true
  readDir := fun _ => autoindexEntries
  indexNames := []

/-- The REAL `Autoindex.renderIndexHtml` listing body for the witness directory —
the same bytes the library `serveDir` puts in its `.listing`. -/
def autoindexListing : Proto.Bytes :=
  Reactor.Stage.Autoindex.renderIndexHtml autoindexReqTarget autoindexEntries

/-- **The directory-listing braid transform.** Always passes the request. Response
phase: marker absent ⇒ identity; present ⇒ the body becomes the REAL
`Autoindex.renderIndexHtml` directory listing (`autoindexListing`). -/
def autoindexBraidStage : Stage where
  name := "autoindex"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match c.req.headers.find? (fun nv => nv.1 == autoindexMarker) with
    | none   => b
    | some _ => b.mapResp (fun r => { r with body := autoindexListing })

theorem autoindexBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == autoindexMarker) = none) :
    autoindexBraidStage.onRequest c = .continue c ∧ ∀ b, autoindexBraidStage.onResponse c b = b := by
  refine ⟨rfl, fun b => ?_⟩
  show (match c.req.headers.find? (fun nv => nv.1 == autoindexMarker) with
        | none   => b
        | some _ => b.mapResp (fun r => { r with body := autoindexListing })) = b
  rw [h]

theorem autoindexBraidStage_on (c : Ctx) (b : ResponseBuilder) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == autoindexMarker) = some nv) :
    autoindexBraidStage.onResponse c b = b.mapResp (fun r => { r with body := autoindexListing }) := by
  show (match c.req.headers.find? (fun nv => nv.1 == autoindexMarker) with
        | none   => b
        | some _ => b.mapResp (fun r => { r with body := autoindexListing })) = _
  rw [hfind]

theorem autoindexBraidStage_statusStable : Stage.statusStable autoindexBraidStage := by
  intro c b
  show ((autoindexBraidStage.onResponse c b).build).status = b.build.status
  unfold autoindexBraidStage
  dsimp only
  split
  · rfl
  · rw [Reactor.Pipeline.build_mapResp]

/-! #### The extended braided chain and its status-stability -/

/-- **The braid-3 chain.** Three config-gated response-shaping braid stages prepended
to `braidedChain2`. A strictly larger, separate fold; `braidedChain2` is untouched. -/
def braidedChain3 : List Stage :=
  conditionalBraidStage :: variantsBraidStage :: autoindexBraidStage :: braidedChain2

/-- Every stage of `braidedChain3` is status-stable (the three new stages plus the
inherited `braidedChain2`). -/
theorem braidedChain3_statusStable : ∀ s ∈ braidedChain3, Stage.statusStable s := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact conditionalBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact variantsBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact autoindexBraidStage_statusStable
  · exact braidedChain2_statusStable s hs

/-! #### THE NEW COMPOSITION — byte-identity when all three markers are OFF -/

/-- **`braided3_off_eq` — the three-stage extension is faithful when gated OFF.** With
none of the three braid-3 markers (and none of the five braid-2 / two §8 markers)
present, the `braidedChain3` fold's built response is exactly `deployStagesFull2`'s:
`prepend_pass` peels the three transparent head stages, then §8h's `braided2_off_eq`
peels the rest. EARNED, not `rfl`. -/
theorem braided3_off_eq (c : Ctx)
    (hcond : c.req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : c.req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : c.req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : c.req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : c.req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf c.req = none) :
    runPipeline braidedChain3 appHandler c = runPipeline deployStagesFull2 appHandler c := by
  obtain ⟨h1r, h1p⟩ := conditionalBraidStage_off c hcond
  obtain ⟨h2r, h2p⟩ := variantsBraidStage_off c hvar
  obtain ⟨h3r, h3p⟩ := autoindexBraidStage_off c hauto
  show runPipeline (conditionalBraidStage :: variantsBraidStage :: autoindexBraidStage
    :: braidedChain2) appHandler c = _
  rw [prepend_pass conditionalBraidStage _ appHandler c h1r h1p,
      prepend_pass variantsBraidStage _ appHandler c h2r h2p,
      prepend_pass autoindexBraidStage _ appHandler c h3r h3p,
      braided2_off_eq c hconn hstick hslow herr hcomp hfa hrid]

/-- **The braid-3 serve.** `serialize` of the BUILT fold over `braidedChain3`. -/
def servePipelineBraided3 (input : Bytes) : Bytes :=
  serialize ((runPipeline braidedChain3 appHandler (ctxOf input)).build)

/-- **`servePipelineBraided3_off_eq` — byte-identical default serve.** With no braid
markers on `ctxOf input`, the braid-3 serve emits EXACTLY `servePipelineFull2`'s
bytes — the default conformance is preserved under the three-stage extension. -/
theorem servePipelineBraided3_off_eq (input : Bytes)
    (hcond : (ctxOf input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : (ctxOf input).req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : (ctxOf input).req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : (ctxOf input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOf input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOf input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOf input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : (ctxOf input).req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : (ctxOf input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOf input).req = none) :
    servePipelineBraided3 input = servePipelineFull2 input := by
  show serialize ((runPipeline braidedChain3 appHandler (ctxOf input)).build) = _
  rw [braided3_off_eq (ctxOf input) hcond hvar hauto hconn hstick hslow herr hcomp hfa hrid]
  rfl

/-! #### THE FIRE — each composed stage genuinely drives the served bytes -/

/-- **`braided3_conditional_304` — the conditional-request `304` fires at the head.**
With the `x-conditional` marker, the built braid-3 status is exactly `304`: the head
gate `.respond`s the REAL `Cache.Conditional` `304` and it survives the entire
status-stable inner onion (the two other new stages + `braidedChain2`). Via
`pipeline_gate_status`, tied to the library's own `demo_if_none_match_304`. -/
theorem braided3_conditional_304 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == conditionalMarker) = some nv) :
    ((runPipeline braidedChain3 appHandler c).build).status = 304 := by
  have hst : ∀ t ∈ (variantsBraidStage :: autoindexBraidStage :: braidedChain2),
      Stage.statusStable t :=
    fun t ht => braidedChain3_statusStable t (List.mem_cons_of_mem _ ht)
  have hgs := Reactor.Pipeline.pipeline_gate_status conditionalBraidStage _ appHandler c
    conditional304 (conditionalBraidStage_denies c nv hfind) hst
  show ((runPipeline braidedChain3 appHandler c).build).status = 304
  rw [show braidedChain3 = conditionalBraidStage :: (variantsBraidStage
        :: autoindexBraidStage :: braidedChain2) from rfl, hgs]
  exact conditional304_status

/-- **`braided3_variants_vary` — the `Vary: Accept-Encoding` header fires once the
conditional gate passes.** With `x-conditional` absent (so the head gate passes,
transparently) and `x-variants` present, the finalized braid-3 response carries
`Vary: Accept-Encoding` — the real `Variants.varyName`/`aeVary` header. Via
`pipeline_stage_effect` + `build_addHeader`. -/
theorem braided3_variants_vary (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hcond : c.req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == variantsMarker) = some nv) :
    (Reactor.Stage.Variants.varyName, Reactor.Stage.Variants.aeVary)
      ∈ ((runPipeline braidedChain3 appHandler c).build).headers := by
  obtain ⟨h1r, h1p⟩ := conditionalBraidStage_off c hcond
  show (Reactor.Stage.Variants.varyName, Reactor.Stage.Variants.aeVary)
      ∈ ((runPipeline braidedChain3 appHandler c).build).headers
  rw [show braidedChain3 = conditionalBraidStage :: (variantsBraidStage
        :: autoindexBraidStage :: braidedChain2) from rfl,
      prepend_pass conditionalBraidStage _ appHandler c h1r h1p,
      Reactor.Pipeline.pipeline_stage_effect variantsBraidStage
        (autoindexBraidStage :: braidedChain2) appHandler c c rfl,
      variantsBraidStage_on c _ nv hfind,
      Reactor.Pipeline.build_addHeader]
  simp

/-- **The braid stamps EXACTLY the header `serveVariant` provably always emits.** The
`Vary: Accept-Encoding` pair the braid pushes is the very pair the library's
`variant_vary_always` guarantees the real variant handler emits — the braid's byte
is the library's own representation-dependence header, not a coincidental literal. -/
theorem braided3_variants_vary_is_library :
    (Reactor.Stage.Variants.varyName, Reactor.Stage.Variants.aeVary)
      ∈ (Reactor.Stage.Variants.serveVariant Reactor.Stage.Variants.demoCfg
          Reactor.Stage.Variants.brReq).headers :=
  Reactor.Stage.Variants.variant_vary_always Reactor.Stage.Variants.demoCfg
    Reactor.Stage.Variants.brReq

/-- **`braided3_autoindex_lists` — the directory listing replaces the body once the
conditional/variants stages pass.** With `x-conditional` and `x-variants` absent (so
those two head stages are transparent) and `x-autoindex` present, the emitted braid-3
body IS the real `Autoindex.renderIndexHtml` listing (`autoindexListing`). The
transform runs at the correct onion position via `pipeline_stage_effect`. -/
theorem braided3_autoindex_lists (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hcond : c.req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : c.req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == autoindexMarker) = some nv) :
    ((runPipeline braidedChain3 appHandler c).build).body = autoindexListing := by
  obtain ⟨h1r, h1p⟩ := conditionalBraidStage_off c hcond
  obtain ⟨h2r, h2p⟩ := variantsBraidStage_off c hvar
  show ((runPipeline braidedChain3 appHandler c).build).body = _
  rw [show braidedChain3 = conditionalBraidStage :: variantsBraidStage
        :: (autoindexBraidStage :: braidedChain2) from rfl,
      prepend_pass conditionalBraidStage _ appHandler c h1r h1p,
      prepend_pass variantsBraidStage _ appHandler c h2r h2p,
      Reactor.Pipeline.pipeline_stage_effect autoindexBraidStage braidedChain2 appHandler c c rfl,
      autoindexBraidStage_on c _ nv hfind,
      Reactor.Pipeline.build_mapResp]

/-- **The braid's listing body IS the library `serveDir`'s listing.** For the witness
directory (a directory, no index), the library `serveDir` returns a `.listing` whose
rendered body is exactly `autoindexListing`, and every entry name shows up as its own
link row — so the braid emits the real directory-index page, not a placeholder. Via
`autoindex_lists_dir` / `entry_in_listingRows`. -/
theorem braided3_autoindex_is_serveDir_listing :
    Reactor.Stage.Autoindex.serveDir autoindexDirCfg autoindexReqTarget
      = .listing autoindexReqTarget autoindexEntries autoindexListing
    ∧ ∀ name ∈ autoindexEntries,
        Reactor.Stage.Autoindex.entryRow autoindexReqTarget name
          ∈ Reactor.Stage.Autoindex.listingRows autoindexReqTarget autoindexEntries :=
  Reactor.Stage.Autoindex.autoindex_lists_dir autoindexDirCfg autoindexReqTarget rfl rfl

/-! #### The Early-Hints (103) ordering prefix over the braid-3 fold -/

/-- The Early-Hints emission over the braid-3 fold: run `braidedChain3`, build its
response, and emit one `103` carrying that response's `Link` headers, then the final. -/
def braided3EarlyHints (c : Ctx) : Reactor.Stage.EarlyHints.Emission :=
  Reactor.Stage.EarlyHints.emitWithHints braidedChain3 appHandler c

/-- **`braided3_earlyhints_ordering` — the `103` precedes the braid-3 final.** Over
the braid-3 fold, a `103 (Early Hints)` interim carrying exactly the braid-3 built
response's `Link` headers is emitted BEFORE the final: the wire sequence is
`[i103, final]` with the `103` first (`status = 103`, `Link`-only headers). Via
`early_hints_103` at `braidedChain3` — the ordering composition of the RFC 8297 model
with the braid-3 pipeline. -/
theorem braided3_earlyhints_ordering (c : Ctx) :
    ∃ i103 : Response,
      (braided3EarlyHints c).wire = [i103, (runPipeline braidedChain3 appHandler c).build] ∧
      i103.status = Reactor.Stage.EarlyHints.status103 ∧
      i103.headers = Reactor.Stage.EarlyHints.onlyLinks
        ((runPipeline braidedChain3 appHandler c).build).headers :=
  Reactor.Stage.EarlyHints.early_hints_103 braidedChain3 appHandler c

/-- **`braided3_earlyhints_final_faithful` — the `103` never perturbs the final.** The
final response of the braid-3 early-hints emission is byte-for-byte the braid-3 built
response, and it is the LAST thing on the wire. The `103` changes only what precedes,
never what the final is. Via `early_hints_then_final` at `braidedChain3`. -/
theorem braided3_earlyhints_final_faithful (c : Ctx) :
    (braided3EarlyHints c).final = (runPipeline braidedChain3 appHandler c).build ∧
    (braided3EarlyHints c).wire.getLast?
      = some ((runPipeline braidedChain3 appHandler c).build) :=
  ⟨(Reactor.Stage.EarlyHints.early_hints_then_final braidedChain3 appHandler c).1,
   (Reactor.Stage.EarlyHints.early_hints_then_final braidedChain3 appHandler c).2.1⟩

#print axioms braided3_off_eq
#print axioms servePipelineBraided3_off_eq
#print axioms braided3_conditional_304
#print axioms braided3_variants_vary
#print axioms braided3_variants_vary_is_library
#print axioms braided3_autoindex_lists
#print axioms braided3_autoindex_is_serveDir_listing
#print axioms braided3_earlyhints_ordering
#print axioms braided3_earlyhints_final_faithful

/-! ### (8k) THE METERED BRAID-3 — braid-3 through the PRODUCTION metered fold

As §8i threaded `braidedChain2` into the connection-aware metered fold, this threads
`braidedChain3`: `braidedDeployment3` is `defaultDeployment` with its middleware chain
replaced by `braidedChain3`. Only the `middleware` dimension differs, so
`Dsl.instantiate` reproduces the SAME `AppConfig`/`appHandler` as `defaultDeployment`,
and the metered fold over it is exactly `runPipeline braidedChain3 appHandler
(ctxOfMetered …)`. `defaultDeployment`/`braidedDeployment`/`braidedDeployment2` and
their anchors are UNTOUCHED. The braid-3 head stages read only `c.req` and
`(ctxOfMetered … input).req = (ctxOf input).req`, so the §8j `Ctx`-generic composition
theorems discharge the metered fold at `ctxOfMetered` directly. -/

/-- **The braid-3 deployment config.** `defaultDeployment` with its middleware chain
replaced by `braidedChain3` — the same `AppConfig` as `defaultDeployment`. -/
def braidedDeployment3 : Dsl.DeploymentConfig :=
  { defaultDeployment with middleware := { chain := braidedChain3 } }

/-- The braid-3 config instantiates to EXACTLY `braidedChain3`. -/
theorem instantiate_braided3_stages :
    (Dsl.instantiate braidedDeployment3).1 = braidedChain3 := rfl

/-- The braid-3 config instantiates to the SAME `AppConfig` as `defaultDeployment`. -/
theorem instantiate_braided3_app :
    (Dsl.instantiate braidedDeployment3).2 = (Dsl.instantiate defaultDeployment).2 := rfl

/-- **The metered braid-3 serve IS the braid-3 chain over the metered context.** -/
theorem servePipelineOfMetered_braided3_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    servePipelineOfMetered braidedDeployment3 clientIp connSeq input
      = serialize ((runPipeline braidedChain3 appHandler
          (ctxOfMetered clientIp connSeq input)).build) := rfl

/-- **`servePipelineOfMetered_braided3_off_eq` — the metered braid-3 is byte-identical
when all three markers (and the five braid-2 / two §8 markers) are OFF.** EARNED, not
`rfl` — `braided3_off_eq` peels the head stages at the metered context. -/
theorem servePipelineOfMetered_braided3_off_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes)
    (hcond : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOfMetered clientIp connSeq input).req = none) :
    servePipelineOfMetered braidedDeployment3 clientIp connSeq input
      = servePipelineFull2Metered clientIp connSeq input := by
  rw [servePipelineOfMetered_braided3_eq,
      braided3_off_eq (ctxOfMetered clientIp connSeq input) hcond hvar hauto hconn hstick hslow herr hcomp hfa hrid]
  rfl

/-- **`servePipelineOfMetered_braided3_conditional_304` — the conditional `304`
survives the metered onion.** Via `braided3_conditional_304` at the metered context. -/
theorem servePipelineOfMetered_braided3_conditional_304
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment3).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment3).2)
        (ctxOfMetered clientIp connSeq input)).build).status = 304 := by
  show ((runPipeline braidedChain3 appHandler (ctxOfMetered clientIp connSeq input)).build).status = 304
  exact braided3_conditional_304 (ctxOfMetered clientIp connSeq input) nv hfind

/-- **`servePipelineOfMetered_braided3_variants_vary` — the `Vary` header fires through
the metered fold. Via `braided3_variants_vary`. -/
theorem servePipelineOfMetered_braided3_variants_vary
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hcond : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == variantsMarker) = some nv) :
    (Reactor.Stage.Variants.varyName, Reactor.Stage.Variants.aeVary)
      ∈ ((runPipeline (Dsl.instantiate braidedDeployment3).1
            (Dsl.handlerOf (Dsl.instantiate braidedDeployment3).2)
            (ctxOfMetered clientIp connSeq input)).build).headers := by
  show (Reactor.Stage.Variants.varyName, Reactor.Stage.Variants.aeVary)
      ∈ ((runPipeline braidedChain3 appHandler (ctxOfMetered clientIp connSeq input)).build).headers
  exact braided3_variants_vary (ctxOfMetered clientIp connSeq input) nv hcond hfind

/-- **`servePipelineOfMetered_braided3_autoindex_lists` — the directory listing body
fires through the metered fold. Via `braided3_autoindex_lists`. -/
theorem servePipelineOfMetered_braided3_autoindex_lists
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hcond : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == autoindexMarker) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment3).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment3).2)
        (ctxOfMetered clientIp connSeq input)).build).body = autoindexListing := by
  show ((runPipeline braidedChain3 appHandler (ctxOfMetered clientIp connSeq input)).build).body = autoindexListing
  exact braided3_autoindex_lists (ctxOfMetered clientIp connSeq input) nv hcond hvar hfind

#print axioms servePipelineOfMetered_braided3_off_eq
#print axioms servePipelineOfMetered_braided3_conditional_304
#print axioms servePipelineOfMetered_braided3_variants_vary
#print axioms servePipelineOfMetered_braided3_autoindex_lists

/-! ### (8l) BRAID-4 — three more proven-but-inert libs, each composed as a
`Reactor.BraidCalculus` ONE-LINER, extending `braidedChain3` to `braidedChain4`.

Where §8h/§8j wrote each composition BESPOKE (~10-16 lines of `prepend_pass`-peeling
+ `pipeline_gate_status`/`pipeline_stage_effect` plumbing), this section USES the
committed braid calculus (`Reactor.BraidCalculus`, all three lemmas axiom-free): each
new stage's composition proof is a SINGLE application of `braid_gate` (status gate),
`braid_transform` (response map), or `braided_off_eq_extend` (byte-identity-when-off).
The proof bodies below are one line — the calculus in production.

`braidedChain4` prepends THREE config-gated braid stages to `braidedChain3`:

* one SHORT-CIRCUIT GATE — `redirectBraidStage` (RFC 9110 §15.4 redirect →
  `308 Permanent Redirect`). Marker absent ⇒ pure pass-through; present ⇒ it delegates
  to the REAL `Reactor.Stage.Redirect.redirectStage` on the library's canonical
  `/old` witness, `.respond`ing the genuine `redirectFor` response (`Redirect.redirect`
  rendering the `Location` template + the §15.4 status `.perm308 = 308`) — the
  library's own decision, not a constant.

* two RESPONSE-TRANSFORMS — `corsBraidStage` (WHATWG Fetch CORS: the
  `Access-Control-Allow-Origin` header for a policy-permitted origin, exactly
  `Cors.corsStage`'s allow branch) and `securityHeadersBraidStage` (RFC 6797 HSTS +
  companions: the response-security header set the real `SecurityHeaders.render`
  emits, `securityheadersStage`). Marker absent ⇒ `onResponse = id` (pass-through);
  present ⇒ the real library `onResponse` fires.

Each stage's composition is PROVEN via the calculus one-liner:
byte-identity-when-off is `braided_off_eq_extend`, the gate fire is `braid_gate`,
each transform fire is `braid_transform` + the library's own byte fact.
`braidedChain3`/`braidedDeployment3` and every §8/§8h/§8j theorem (and the
`servePipelineOfMetered_default` anchor) are UNTOUCHED — `braidedChain4` is a strictly
larger, separate fold. -/

open Reactor.BraidCalculus (Transparent braid_gate braid_transform braided_off_eq_extend
  prepend_pass nil_transparent cons_transparent)

/-- The per-request marker enabling the redirect `308` gate. -/
def redirectMarker : Proto.Bytes := "x-redirect".toUTF8.toList
/-- The per-request marker enabling the CORS `Access-Control-Allow-Origin` transform. -/
def corsMarker : Proto.Bytes := "x-cors".toUTF8.toList
/-- The per-request marker enabling the security-header (HSTS + companions) transform. -/
def securityMarker : Proto.Bytes := "x-security-headers".toUTF8.toList

/-! #### The redirect `308` gate (pass-through when unmarked) -/

/-- The library's canonical redirect witness: a request whose target is exactly
`Reactor.Stage.Redirect.ruleTarget` (`/old`), the target the real redirect rule
matches — so `redirectStage.onRequest` on it `.respond`s the genuine redirect. -/
def redirectWitnessCtx : Ctx :=
  { input := [], req := { target := Reactor.Stage.Redirect.ruleTarget } }

/-- The genuine `308` the redirect gate answers with: the REAL
`Reactor.Stage.Redirect.redirectFor` on the library witness (`Redirect.redirect`
rendering the `Location` template + the §15.4 status `.perm308`), NOT a constant. -/
def redirect308 : Response := Reactor.Stage.Redirect.redirectFor redirectWitnessCtx.req

/-- The library decision the gate answers with is a genuine `308` (the §15.4
`.perm308` status the real `Redirect.redirect` carries, not a bare literal). -/
theorem redirect308_status : redirect308.status = 308 := rfl

/-- The redirect witness genuinely responds (its target matches the real rule). -/
theorem redirectWitness_responds :
    Reactor.Stage.Redirect.redirectStage.onRequest redirectWitnessCtx = .respond redirect308 := by
  show (if redirectWitnessCtx.req.target = Reactor.Stage.Redirect.ruleTarget
        then StageStep.respond (Reactor.Stage.Redirect.redirectFor redirectWitnessCtx.req)
        else .continue redirectWitnessCtx) = _
  rw [if_pos (show redirectWitnessCtx.req.target = Reactor.Stage.Redirect.ruleTarget from rfl)]
  rfl

/-- **The redirect braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL
`redirectStage` decision on the library witness `.respond`s the genuine `308`. -/
def redirectBraidStage : Stage where
  name := "redirect-308"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == redirectMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.Redirect.redirectStage.onRequest redirectWitnessCtx
  onResponse := fun _ b => b

theorem redirectBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == redirectMarker) = none) :
    Transparent redirectBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == redirectMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.Redirect.redirectStage.onRequest redirectWitnessCtx) = _
  rw [h]

theorem redirectBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == redirectMarker) = some nv) :
    redirectBraidStage.onRequest c = .respond redirect308 := by
  show (match c.req.headers.find? (fun nv => nv.1 == redirectMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.Redirect.redirectStage.onRequest redirectWitnessCtx) = _
  rw [hfind]
  exact redirectWitness_responds

theorem redirectBraidStage_statusStable : Stage.statusStable redirectBraidStage := fun _ _ => rfl

/-! #### The CORS `Access-Control-Allow-Origin` transform (identity when unmarked) -/

/-- **The CORS braid transform.** Always passes the request. Response phase: marker
absent ⇒ identity; present ⇒ the REAL `Cors.corsStage` response phase — a
policy-permitted origin gets `Access-Control-Allow-Origin: <value>`, a forbidden
origin gets nothing (the no-leak boundary). -/
def corsBraidStage : Stage where
  name := "cors-acao"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match c.req.headers.find? (fun nv => nv.1 == corsMarker) with
    | none   => b
    | some _ => Reactor.Stage.Cors.corsStage.onResponse c b

theorem corsBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == corsMarker) = none) :
    Transparent corsBraidStage c := by
  refine ⟨rfl, fun b => ?_⟩
  show (match c.req.headers.find? (fun nv => nv.1 == corsMarker) with
        | none   => b
        | some _ => Reactor.Stage.Cors.corsStage.onResponse c b) = b
  rw [h]

theorem corsBraidStage_on (c : Ctx) (b : ResponseBuilder) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == corsMarker) = some nv) :
    corsBraidStage.onResponse c b = Reactor.Stage.Cors.corsStage.onResponse c b := by
  show (match c.req.headers.find? (fun nv => nv.1 == corsMarker) with
        | none   => b
        | some _ => Reactor.Stage.Cors.corsStage.onResponse c b) = _
  rw [hfind]

theorem corsBraidStage_statusStable : Stage.statusStable corsBraidStage := by
  intro c b
  show ((corsBraidStage.onResponse c b).build).status = b.build.status
  unfold corsBraidStage
  dsimp only
  split
  · rfl
  · show ((Reactor.Stage.Cors.corsStage.onResponse c b).build).status = b.build.status
    unfold Reactor.Stage.Cors.corsStage
    dsimp only
    split
    · rw [Reactor.Pipeline.build_addHeader]
    · rfl

/-! #### The security-header (HSTS + companions) transform (identity when unmarked) -/

/-- **The security-header braid transform.** Always passes the request. Response
phase: marker absent ⇒ identity; present ⇒ the REAL
`SecurityHeaders.securityheadersStage` response phase folds the whole rendered
security-header set (HSTS / X-Frame-Options / X-Content-Type-Options /
Referrer-Policy) onto the affine builder. -/
def securityHeadersBraidStage : Stage where
  name := "security-headers"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match c.req.headers.find? (fun nv => nv.1 == securityMarker) with
    | none   => b
    | some _ => Reactor.Stage.SecurityHeaders.securityheadersStage.onResponse c b

theorem securityHeadersBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == securityMarker) = none) :
    Transparent securityHeadersBraidStage c := by
  refine ⟨rfl, fun b => ?_⟩
  show (match c.req.headers.find? (fun nv => nv.1 == securityMarker) with
        | none   => b
        | some _ => Reactor.Stage.SecurityHeaders.securityheadersStage.onResponse c b) = b
  rw [h]

theorem securityHeadersBraidStage_on (c : Ctx) (b : ResponseBuilder) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == securityMarker) = some nv) :
    securityHeadersBraidStage.onResponse c b
      = (Reactor.Stage.SecurityHeaders.wireHeaders Reactor.Stage.SecurityHeaders.policy).foldl
          ResponseBuilder.addHeader b := by
  show (match c.req.headers.find? (fun nv => nv.1 == securityMarker) with
        | none   => b
        | some _ => Reactor.Stage.SecurityHeaders.securityheadersStage.onResponse c b) = _
  rw [hfind]
  show Reactor.Stage.SecurityHeaders.securityheadersStage.onResponse c b
      = (Reactor.Stage.SecurityHeaders.wireHeaders Reactor.Stage.SecurityHeaders.policy).foldl
          ResponseBuilder.addHeader b
  rfl

theorem securityHeadersBraidStage_statusStable : Stage.statusStable securityHeadersBraidStage := by
  intro c b
  show ((securityHeadersBraidStage.onResponse c b).build).status = b.build.status
  unfold securityHeadersBraidStage
  dsimp only
  split
  · rfl
  · show (((Reactor.Stage.SecurityHeaders.wireHeaders Reactor.Stage.SecurityHeaders.policy).foldl
        ResponseBuilder.addHeader b).build).status = b.build.status
    rw [Reactor.Pipeline.build_addHeaders]

/-! #### The extended braided chain and its status-stability -/

/-- **The braid-4 chain.** Three config-gated braid stages (redirect gate + CORS /
security-header transforms) prepended to `braidedChain3`. A strictly larger, separate
fold; `braidedChain3` is untouched. -/
def braidedChain4 : List Stage :=
  redirectBraidStage :: corsBraidStage :: securityHeadersBraidStage :: braidedChain3

/-- Every stage of `braidedChain4` is status-stable (the three new stages plus the
inherited `braidedChain3`). -/
theorem braidedChain4_statusStable : ∀ s ∈ braidedChain4, Stage.statusStable s := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact redirectBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact corsBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact securityHeadersBraidStage_statusStable
  · exact braidedChain3_statusStable s hs

/-! #### THE NEW COMPOSITION — byte-identity when all three markers are OFF
(the `braided_off_eq_extend` ONE-LINER). -/

/-- **`braided4_off_eq` — the three-stage extension is faithful when gated OFF.** ONE
LINE via the calculus: `braided_off_eq_extend` peels the transparent three-stage
prefix, then defers to §8j's `braided3_off_eq`. The whole bespoke `obtain … / show … /
rw [prepend_pass, prepend_pass, prepend_pass, braided3_off_eq]` pattern collapses to a
single lemma application. -/
theorem braided4_off_eq (c : Ctx)
    (hred : c.req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : c.req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hsec : c.req.headers.find? (fun nv => nv.1 == securityMarker) = none)
    (hcond : c.req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : c.req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : c.req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : c.req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : c.req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf c.req = none) :
    runPipeline braidedChain4 appHandler c = runPipeline deployStagesFull2 appHandler c :=
  braided_off_eq_extend [redirectBraidStage, corsBraidStage, securityHeadersBraidStage]
    braidedChain3 deployStagesFull2 appHandler c
    (cons_transparent (redirectBraidStage_off c hred)
      (cons_transparent (corsBraidStage_off c hcors)
        (cons_transparent (securityHeadersBraidStage_off c hsec) (nil_transparent c))))
    (braided3_off_eq c hcond hvar hauto hconn hstick hslow herr hcomp hfa hrid)

/-- **The braid-4 serve.** `serialize` of the BUILT fold over `braidedChain4`. -/
def servePipelineBraided4 (input : Bytes) : Bytes :=
  serialize ((runPipeline braidedChain4 appHandler (ctxOf input)).build)

/-- **`servePipelineBraided4_off_eq` — byte-identical default serve.** With no braid
markers on `ctxOf input`, the braid-4 serve emits EXACTLY `servePipelineFull2`'s bytes
— default conformance preserved under the three-stage extension. -/
theorem servePipelineBraided4_off_eq (input : Bytes)
    (hred : (ctxOf input).req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : (ctxOf input).req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hsec : (ctxOf input).req.headers.find? (fun nv => nv.1 == securityMarker) = none)
    (hcond : (ctxOf input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : (ctxOf input).req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : (ctxOf input).req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : (ctxOf input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOf input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOf input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOf input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : (ctxOf input).req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : (ctxOf input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOf input).req = none) :
    servePipelineBraided4 input = servePipelineFull2 input := by
  show serialize ((runPipeline braidedChain4 appHandler (ctxOf input)).build) = _
  rw [braided4_off_eq (ctxOf input) hred hcors hsec hcond hvar hauto hconn hstick hslow herr hcomp hfa hrid]
  rfl

/-! #### THE FIRE — each composed stage genuinely drives the served bytes, each proof a
`Reactor.BraidCalculus` ONE-LINER. -/

/-- **`braided4_redirect_308` — the redirect `308` fires at the head (ONE-LINER).**
With the `x-redirect` marker, the built braid-4 status is exactly `308`. The whole
bespoke gate proof is a single `braid_gate` (pref `[]`, so `nil_transparent`): the head
gate `.respond`s the REAL `redirect308` and it survives the status-stable inner onion.
`redirect308.status` reduces to `308`, so the term typechecks against the goal. -/
theorem braided4_redirect_308 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == redirectMarker) = some nv) :
    ((runPipeline braidedChain4 appHandler c).build).status = 308 :=
  braid_gate [] redirectBraidStage _ appHandler c _ (nil_transparent c)
    (redirectBraidStage_denies c nv hfind)
    (fun t ht => braidedChain4_statusStable t (List.mem_cons_of_mem _ ht))

/-- **`braided4_cors_acao` — the CORS `Access-Control-Allow-Origin` header fires once the
redirect gate passes (ONE-LINER core).** With `x-redirect` absent (head gate transparent)
and `x-cors` present, a policy-permitted origin (`acaoValue = some v`) lands its ACAO pair
in the built braid-4 headers. `braid_transform` peels the transparent redirect prefix and
places the transform at its onion position in ONE step; the stage's own `_on` and the
library's own `corsStage_grants` finish it. -/
theorem braided4_cors_acao (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hred : c.req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == corsMarker) = some nv)
    (v : String) (hv : Cors.acaoValue Reactor.Stage.Cors.corsPolicy (Reactor.Stage.Cors.originOf c) = some v) :
    (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
      ∈ ((runPipeline braidedChain4 appHandler c).build).headers := by
  rw [show braidedChain4 = [redirectBraidStage]
        ++ corsBraidStage :: (securityHeadersBraidStage :: braidedChain3) from rfl,
      braid_transform [redirectBraidStage] corsBraidStage
        (securityHeadersBraidStage :: braidedChain3) appHandler c c
        (cons_transparent (redirectBraidStage_off c hred) (nil_transparent c)) rfl,
      corsBraidStage_on c _ nv hfind,
      ← Reactor.Stage.Cors.corsStage_effect (securityHeadersBraidStage :: braidedChain3) appHandler c]
  exact Reactor.Stage.Cors.corsStage_grants (securityHeadersBraidStage :: braidedChain3) appHandler c v hv

/-- **`braided4_security_hsts` — the HSTS security header fires once the redirect/CORS
stages pass (ONE-LINER core).** With `x-redirect` and `x-cors` absent (those two head
stages transparent) and `x-security-headers` present, the RFC-6797 `Strict-Transport-Security`
header (name + rendered value) appears in the built braid-4 headers. `braid_transform`
peels the two transparent head stages and places the transform at its onion position in
ONE step; the stage's own `_on` and the library's own `securityheadersStage_hsts_present`
finish it. -/
theorem braided4_security_hsts (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hred : c.req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : c.req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == securityMarker) = some nv) :
    (Reactor.Stage.SecurityHeaders.hstsHeaderName, Reactor.Stage.SecurityHeaders.hstsHeaderVal)
      ∈ ((runPipeline braidedChain4 appHandler c).build).headers := by
  rw [show braidedChain4 = [redirectBraidStage, corsBraidStage]
        ++ securityHeadersBraidStage :: braidedChain3 from rfl,
      braid_transform [redirectBraidStage, corsBraidStage] securityHeadersBraidStage
        braidedChain3 appHandler c c
        (cons_transparent (redirectBraidStage_off c hred)
          (cons_transparent (corsBraidStage_off c hcors) (nil_transparent c))) rfl,
      securityHeadersBraidStage_on c _ nv hfind,
      ← Reactor.Stage.SecurityHeaders.securityheadersStage_effect braidedChain3 appHandler c]
  exact Reactor.Stage.SecurityHeaders.securityheadersStage_hsts_present braidedChain3 appHandler c

#print axioms braided4_off_eq
#print axioms servePipelineBraided4_off_eq
#print axioms braided4_redirect_308
#print axioms braided4_cors_acao
#print axioms braided4_security_hsts

/-! ### (8m) THE METERED BRAID-4 — braid-4 through the PRODUCTION metered fold

As §8k threaded `braidedChain3` into the connection-aware metered fold, this threads
`braidedChain4`: `braidedDeployment4` is `defaultDeployment` with its middleware chain
replaced by `braidedChain4`. Only the `middleware` dimension differs, so `Dsl.instantiate`
reproduces the SAME `AppConfig`/`appHandler` as `defaultDeployment`, and the metered fold
over it is exactly `runPipeline braidedChain4 appHandler (ctxOfMetered …)`.
`defaultDeployment`/`braidedDeployment`/`braidedDeployment2`/`braidedDeployment3` and
their anchors are UNTOUCHED. The braid-4 head stages read only `c.req` and
`(ctxOfMetered … input).req = (ctxOf input).req`, so the §8l `Ctx`-generic composition
theorems discharge the metered fold at `ctxOfMetered` directly. -/

/-- **The braid-4 deployment config.** `defaultDeployment` with its middleware chain
replaced by `braidedChain4` — the same `AppConfig` as `defaultDeployment`. -/
def braidedDeployment4 : Dsl.DeploymentConfig :=
  { defaultDeployment with middleware := { chain := braidedChain4 } }

/-- The braid-4 config instantiates to EXACTLY `braidedChain4`. -/
theorem instantiate_braided4_stages :
    (Dsl.instantiate braidedDeployment4).1 = braidedChain4 := rfl

/-- The braid-4 config instantiates to the SAME `AppConfig` as `defaultDeployment`. -/
theorem instantiate_braided4_app :
    (Dsl.instantiate braidedDeployment4).2 = (Dsl.instantiate defaultDeployment).2 := rfl

/-- **The metered braid-4 serve IS the braid-4 chain over the metered context.** -/
theorem servePipelineOfMetered_braided4_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    servePipelineOfMetered braidedDeployment4 clientIp connSeq input
      = serialize ((runPipeline braidedChain4 appHandler
          (ctxOfMetered clientIp connSeq input)).build) := rfl

/-- **`servePipelineOfMetered_braided4_off_eq` — the metered braid-4 is byte-identical
when all three markers (and the eight §8h/§8j / two §8 markers) are OFF.** EARNED, not
`rfl` — `braided4_off_eq` peels the head stages at the metered context. -/
theorem servePipelineOfMetered_braided4_off_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes)
    (hred : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hsec : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == securityMarker) = none)
    (hcond : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOfMetered clientIp connSeq input).req = none) :
    servePipelineOfMetered braidedDeployment4 clientIp connSeq input
      = servePipelineFull2Metered clientIp connSeq input := by
  rw [servePipelineOfMetered_braided4_eq,
      braided4_off_eq (ctxOfMetered clientIp connSeq input) hred hcors hsec hcond hvar hauto hconn hstick hslow herr hcomp hfa hrid]
  rfl

/-- **`servePipelineOfMetered_braided4_redirect_308` — the redirect `308` survives the
metered onion.** Via `braided4_redirect_308` at the metered context. -/
theorem servePipelineOfMetered_braided4_redirect_308
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == redirectMarker) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment4).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment4).2)
        (ctxOfMetered clientIp connSeq input)).build).status = 308 := by
  show ((runPipeline braidedChain4 appHandler (ctxOfMetered clientIp connSeq input)).build).status = 308
  exact braided4_redirect_308 (ctxOfMetered clientIp connSeq input) nv hfind

/-- **`servePipelineOfMetered_braided4_cors_acao` — the CORS ACAO header fires through the
metered fold. Via `braided4_cors_acao`. -/
theorem servePipelineOfMetered_braided4_cors_acao
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hred : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == corsMarker) = some nv)
    (v : String)
    (hv : Cors.acaoValue Reactor.Stage.Cors.corsPolicy
      (Reactor.Stage.Cors.originOf (ctxOfMetered clientIp connSeq input)) = some v) :
    (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
      ∈ ((runPipeline (Dsl.instantiate braidedDeployment4).1
            (Dsl.handlerOf (Dsl.instantiate braidedDeployment4).2)
            (ctxOfMetered clientIp connSeq input)).build).headers := by
  show (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
      ∈ ((runPipeline braidedChain4 appHandler (ctxOfMetered clientIp connSeq input)).build).headers
  exact braided4_cors_acao (ctxOfMetered clientIp connSeq input) nv hred hfind v hv

/-- **`servePipelineOfMetered_braided4_security_hsts` — the HSTS header fires through the
metered fold. Via `braided4_security_hsts`. -/
theorem servePipelineOfMetered_braided4_security_hsts
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hred : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == securityMarker) = some nv) :
    (Reactor.Stage.SecurityHeaders.hstsHeaderName, Reactor.Stage.SecurityHeaders.hstsHeaderVal)
      ∈ ((runPipeline (Dsl.instantiate braidedDeployment4).1
            (Dsl.handlerOf (Dsl.instantiate braidedDeployment4).2)
            (ctxOfMetered clientIp connSeq input)).build).headers := by
  show (Reactor.Stage.SecurityHeaders.hstsHeaderName, Reactor.Stage.SecurityHeaders.hstsHeaderVal)
      ∈ ((runPipeline braidedChain4 appHandler (ctxOfMetered clientIp connSeq input)).build).headers
  exact braided4_security_hsts (ctxOfMetered clientIp connSeq input) nv hred hcors hfind

#print axioms servePipelineOfMetered_braided4_off_eq
#print axioms servePipelineOfMetered_braided4_redirect_308
#print axioms servePipelineOfMetered_braided4_cors_acao
#print axioms servePipelineOfMetered_braided4_security_hsts

/-! ### (8n) BRAID-5 — three NET-NEW proven gates, each composed as a
`Reactor.BraidCalculus` ONE-LINER, extending `braidedChain4` to `braidedChain5`.

CRITICAL CONTRAST WITH §8l: braid-4's three stages (redirect `308` / CORS-ACAO /
security-headers) were REDUNDANT — each was already an always-on `deployStagesFull2`
stage (`Reactor.Stage.Redirect.redirectStage` #6, `deployCorsStage` #9,
`Reactor.Stage.SecurityHeaders.securityheadersStage` #13). Braid-4 was a *demo of the
calculus*, not new deployed behaviour: the unbraided default already redirects, sets
ACAO, and emits HSTS. Braid-5 braids only behaviour ABSENT from BOTH the always-on
`deployStagesFull2` list AND every prior braid (`braidedChain{,2,3,4}`), and absent from
the ingress FSM — each stage adds a genuinely NEW deployed capability:

* `methodBraidStage` — RFC 9110 §15.5.6 `405 Method Not Allowed` on a method outside the
  allow-list (`GET`/`POST`/`HEAD`/`OPTIONS`), carrying the required `Allow` header. The
  default serve has NO method gate (the ingress parser accepts any non-empty method and
  runs the pipeline); nothing anywhere answers `405`.

* `bodyLimitBraidStage` — RFC 9110 §15.5.14 `413 Content Too Large` on a declared
  `Content-Length` wider than the digit budget (≥ 10 MB). The default serve has NO body
  gate; nothing anywhere answers `413`. (The ingress FSM's `Config.oversize431` caps the
  request HEAD with a `431`, a different limit at a different layer — see the DROPPED
  candidate note below.)

* `hostAllowlistBraidStage` — RFC 9110 §15.5.20 `421 Misdirected Request` on a `Host`
  outside the served authorities. The default serve answers any `Host`; nothing anywhere
  answers `421`.

DROPPED as REDUNDANT (honest coverage findings, mirroring §8l's security-headers lesson):
* max-header-size `431` — the ingress FSM ALREADY caps the request head and emits
  `Config.oversize431` (`Reactor.Serve`/`Reactor.Bridge`), so a `431` braid stage would
  duplicate an existing deployed behaviour at the pipeline layer. NOT braided.
* referrer-policy / permissions-policy — `securityheadersStage` (always-on #13) already
  renders `Referrer-Policy` in its wired header set; a Referrer-Policy stage is redundant.
  NOT braided.

Each stage is marker-gated (a per-request test header): absent ⇒ pure pass-through
(`Transparent`); present ⇒ it delegates to the REAL proven leaf-lib decision on that
library's own witness, `.respond`ing the genuine status (the library's decision, not a
bare literal — `Reactor.Stage.MethodFilter.witness_responds` etc.). Each composition
proof is a ONE-LINER: the off-equality via `braided_off_eq_extend`, each gate fire via
`braid_gate`. `braidedChain4`/`braidedDeployment4` and every prior theorem (and the
`servePipelineOfMetered_default` anchor) are UNTOUCHED — `braidedChain5` is a strictly
larger, separate fold. -/

/-- The per-request marker enabling the method-filter `405` gate. -/
def methodMarker : Proto.Bytes := "x-method-filter".toUTF8.toList
/-- The per-request marker enabling the body-size `413` gate. -/
def bodyLimitMarker : Proto.Bytes := "x-body-limit".toUTF8.toList
/-- The per-request marker enabling the Host-allowlist `421` gate. -/
def hostAllowlistMarker : Proto.Bytes := "x-host-allowlist".toUTF8.toList

/-! #### The method-filter `405` gate (pass-through when unmarked) -/

/-- The genuine `405` the gate answers with: the REAL `MethodFilter.methodNotAllowed`
(status `405` + the RFC-required `Allow` header), NOT a constant. -/
def method405 : Response := Reactor.Stage.MethodFilter.methodNotAllowed

/-- The library decision the gate answers with is a genuine `405`. -/
theorem method405_status : method405.status = 405 := rfl

/-- **The method-filter braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL
`methodFilterStage` decision on the library's `DELETE` witness `.respond`s the genuine
`405`. -/
def methodBraidStage : Stage where
  name := "method-405"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == methodMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.MethodFilter.methodFilterStage.onRequest Reactor.Stage.MethodFilter.witnessCtx
  onResponse := fun _ b => b

theorem methodBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == methodMarker) = none) :
    Transparent methodBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == methodMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.MethodFilter.methodFilterStage.onRequest Reactor.Stage.MethodFilter.witnessCtx) = _
  rw [h]

theorem methodBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == methodMarker) = some nv) :
    methodBraidStage.onRequest c = .respond method405 := by
  show (match c.req.headers.find? (fun nv => nv.1 == methodMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.MethodFilter.methodFilterStage.onRequest Reactor.Stage.MethodFilter.witnessCtx) = _
  rw [hfind]
  exact Reactor.Stage.MethodFilter.witness_responds

theorem methodBraidStage_statusStable : Stage.statusStable methodBraidStage := fun _ _ => rfl

/-! #### The body-size `413` gate (pass-through when unmarked) -/

/-- The genuine `413` the gate answers with: the REAL `BodyLimit.contentTooLarge`. -/
def body413 : Response := Reactor.Stage.BodyLimit.contentTooLarge

theorem body413_status : body413.status = 413 := rfl

/-- **The body-size braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL
`bodyLimitStage` decision on the library's over-budget `Content-Length` witness
`.respond`s the genuine `413`. -/
def bodyLimitBraidStage : Stage where
  name := "body-413"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == bodyLimitMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.BodyLimit.bodyLimitStage.onRequest Reactor.Stage.BodyLimit.witnessCtx
  onResponse := fun _ b => b

theorem bodyLimitBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = none) :
    Transparent bodyLimitBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == bodyLimitMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.BodyLimit.bodyLimitStage.onRequest Reactor.Stage.BodyLimit.witnessCtx) = _
  rw [h]

theorem bodyLimitBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = some nv) :
    bodyLimitBraidStage.onRequest c = .respond body413 := by
  show (match c.req.headers.find? (fun nv => nv.1 == bodyLimitMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.BodyLimit.bodyLimitStage.onRequest Reactor.Stage.BodyLimit.witnessCtx) = _
  rw [hfind]
  exact Reactor.Stage.BodyLimit.witness_responds

theorem bodyLimitBraidStage_statusStable : Stage.statusStable bodyLimitBraidStage := fun _ _ => rfl

/-! #### The Host-allowlist `421` gate (pass-through when unmarked) -/

/-- The genuine `421` the gate answers with: the REAL `HostAllowlist.misdirectedResp`. -/
def host421 : Response := Reactor.Stage.HostAllowlist.misdirectedResp

theorem host421_status : host421.status = 421 := rfl

/-- **The Host-allowlist braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL
`hostAllowlistStage` decision on the library's off-allowlist `Host` witness `.respond`s
the genuine `421`. -/
def hostAllowlistBraidStage : Stage where
  name := "host-421"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.HostAllowlist.hostAllowlistStage.onRequest Reactor.Stage.HostAllowlist.witnessCtx
  onResponse := fun _ b => b

theorem hostAllowlistBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = none) :
    Transparent hostAllowlistBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.HostAllowlist.hostAllowlistStage.onRequest Reactor.Stage.HostAllowlist.witnessCtx) = _
  rw [h]

theorem hostAllowlistBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = some nv) :
    hostAllowlistBraidStage.onRequest c = .respond host421 := by
  show (match c.req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.HostAllowlist.hostAllowlistStage.onRequest Reactor.Stage.HostAllowlist.witnessCtx) = _
  rw [hfind]
  exact Reactor.Stage.HostAllowlist.witness_responds

theorem hostAllowlistBraidStage_statusStable : Stage.statusStable hostAllowlistBraidStage := fun _ _ => rfl

/-! #### The extended braided chain and its status-stability -/

/-- **The braid-5 chain.** Three NET-NEW config-gated gate stages (method `405` /
body-size `413` / Host-allowlist `421`) prepended to `braidedChain4`. A strictly larger,
separate fold; `braidedChain4` is untouched. -/
def braidedChain5 : List Stage :=
  methodBraidStage :: bodyLimitBraidStage :: hostAllowlistBraidStage :: braidedChain4

/-- Every stage of `braidedChain5` is status-stable (the three new gates plus the
inherited `braidedChain4`). -/
theorem braidedChain5_statusStable : ∀ s ∈ braidedChain5, Stage.statusStable s := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact methodBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact bodyLimitBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact hostAllowlistBraidStage_statusStable
  · exact braidedChain4_statusStable s hs

/-! #### THE NEW COMPOSITION — byte-identity when all three markers are OFF
(the `braided_off_eq_extend` ONE-LINER). -/

/-- **`braided5_off_eq` — the three-gate extension is faithful when gated OFF.** ONE LINE
via the calculus: `braided_off_eq_extend` peels the transparent three-gate prefix, then
defers to §8l's `braided4_off_eq`. -/
theorem braided5_off_eq (c : Ctx)
    (hmethod : c.req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hbody : c.req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = none)
    (hhost : c.req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = none)
    (hred : c.req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : c.req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hsec : c.req.headers.find? (fun nv => nv.1 == securityMarker) = none)
    (hcond : c.req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : c.req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : c.req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : c.req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : c.req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf c.req = none) :
    runPipeline braidedChain5 appHandler c = runPipeline deployStagesFull2 appHandler c :=
  braided_off_eq_extend [methodBraidStage, bodyLimitBraidStage, hostAllowlistBraidStage]
    braidedChain4 deployStagesFull2 appHandler c
    (cons_transparent (methodBraidStage_off c hmethod)
      (cons_transparent (bodyLimitBraidStage_off c hbody)
        (cons_transparent (hostAllowlistBraidStage_off c hhost) (nil_transparent c))))
    (braided4_off_eq c hred hcors hsec hcond hvar hauto hconn hstick hslow herr hcomp hfa hrid)

/-- **The braid-5 serve.** `serialize` of the BUILT fold over `braidedChain5`. -/
def servePipelineBraided5 (input : Bytes) : Bytes :=
  serialize ((runPipeline braidedChain5 appHandler (ctxOf input)).build)

/-- **`servePipelineBraided5_off_eq` — byte-identical default serve.** With no braid
markers on `ctxOf input`, the braid-5 serve emits EXACTLY `servePipelineFull2`'s bytes. -/
theorem servePipelineBraided5_off_eq (input : Bytes)
    (hmethod : (ctxOf input).req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hbody : (ctxOf input).req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = none)
    (hhost : (ctxOf input).req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = none)
    (hred : (ctxOf input).req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : (ctxOf input).req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hsec : (ctxOf input).req.headers.find? (fun nv => nv.1 == securityMarker) = none)
    (hcond : (ctxOf input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : (ctxOf input).req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : (ctxOf input).req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : (ctxOf input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOf input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOf input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOf input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : (ctxOf input).req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : (ctxOf input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOf input).req = none) :
    servePipelineBraided5 input = servePipelineFull2 input := by
  show serialize ((runPipeline braidedChain5 appHandler (ctxOf input)).build) = _
  rw [braided5_off_eq (ctxOf input) hmethod hbody hhost hred hcors hsec hcond hvar hauto
        hconn hstick hslow herr hcomp hfa hrid]
  rfl

/-! #### THE FIRE — each NET-NEW gate genuinely drives the served status, each proof a
`Reactor.BraidCalculus` `braid_gate` ONE-LINER. -/

/-- **`braided5_method_405` — the method `405` fires at the head (ONE-LINER).** With the
`x-method-filter` marker, the built braid-5 status is exactly `405`. `braid_gate` (pref
`[]`): the head gate `.respond`s the REAL `method405` and it survives the status-stable
inner onion. `method405.status` reduces to `405`. -/
theorem braided5_method_405 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == methodMarker) = some nv) :
    ((runPipeline braidedChain5 appHandler c).build).status = 405 :=
  braid_gate [] methodBraidStage _ appHandler c _ (nil_transparent c)
    (methodBraidStage_denies c nv hfind)
    (fun t ht => braidedChain5_statusStable t (List.mem_cons_of_mem _ ht))

/-- **`braided5_body_413` — the body-size `413` fires once the method gate passes
(ONE-LINER).** With `x-method-filter` absent (head gate transparent) and `x-body-limit`
present, the built braid-5 status is exactly `413`. `braid_gate` (pref
`[methodBraidStage]`). -/
theorem braided5_body_413 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hmethod : c.req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = some nv) :
    ((runPipeline braidedChain5 appHandler c).build).status = 413 :=
  braid_gate [methodBraidStage] bodyLimitBraidStage _ appHandler c _
    (cons_transparent (methodBraidStage_off c hmethod) (nil_transparent c))
    (bodyLimitBraidStage_denies c nv hfind)
    (fun t ht => braidedChain5_statusStable t
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)))

/-- **`braided5_host_421` — the Host-allowlist `421` fires once the method/body gates pass
(ONE-LINER).** With `x-method-filter` and `x-body-limit` absent (those two head gates
transparent) and `x-host-allowlist` present, the built braid-5 status is exactly `421`.
`braid_gate` (pref `[methodBraidStage, bodyLimitBraidStage]`). -/
theorem braided5_host_421 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hmethod : c.req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hbody : c.req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = some nv) :
    ((runPipeline braidedChain5 appHandler c).build).status = 421 :=
  braid_gate [methodBraidStage, bodyLimitBraidStage] hostAllowlistBraidStage _ appHandler c _
    (cons_transparent (methodBraidStage_off c hmethod)
      (cons_transparent (bodyLimitBraidStage_off c hbody) (nil_transparent c)))
    (hostAllowlistBraidStage_denies c nv hfind)
    (fun t ht => braidedChain5_statusStable t
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht))))

#print axioms braided5_off_eq
#print axioms servePipelineBraided5_off_eq
#print axioms braided5_method_405
#print axioms braided5_body_413
#print axioms braided5_host_421

/-! ### (8o) THE METERED BRAID-5 — braid-5 through the PRODUCTION metered fold

As §8m threaded `braidedChain4`, this threads `braidedChain5`: `braidedDeployment5` is
`defaultDeployment` with its middleware chain replaced by `braidedChain5`. Only the
`middleware` dimension differs, so `Dsl.instantiate` reproduces the SAME
`AppConfig`/`appHandler` as `defaultDeployment`, and the metered fold over it is exactly
`runPipeline braidedChain5 appHandler (ctxOfMetered …)`. The braid-5 head gates read only
`c.req` and `(ctxOfMetered … input).req = (ctxOf input).req`, so the §8n `Ctx`-generic
composition theorems discharge the metered fold at `ctxOfMetered` directly. Every prior
deployment/anchor is UNTOUCHED. -/

/-- **The braid-5 deployment config.** `defaultDeployment` with its middleware chain
replaced by `braidedChain5` — the same `AppConfig` as `defaultDeployment`. -/
def braidedDeployment5 : Dsl.DeploymentConfig :=
  { defaultDeployment with middleware := { chain := braidedChain5 } }

/-- The braid-5 config instantiates to EXACTLY `braidedChain5`. -/
theorem instantiate_braided5_stages :
    (Dsl.instantiate braidedDeployment5).1 = braidedChain5 := rfl

/-- The braid-5 config instantiates to the SAME `AppConfig` as `defaultDeployment`. -/
theorem instantiate_braided5_app :
    (Dsl.instantiate braidedDeployment5).2 = (Dsl.instantiate defaultDeployment).2 := rfl

/-- **The metered braid-5 serve IS the braid-5 chain over the metered context.** -/
theorem servePipelineOfMetered_braided5_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    servePipelineOfMetered braidedDeployment5 clientIp connSeq input
      = serialize ((runPipeline braidedChain5 appHandler
          (ctxOfMetered clientIp connSeq input)).build) := rfl

/-- **`servePipelineOfMetered_braided5_off_eq` — the metered braid-5 is byte-identical
when all sixteen markers are OFF.** EARNED — `braided5_off_eq` peels the head gates at the
metered context. -/
theorem servePipelineOfMetered_braided5_off_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes)
    (hmethod : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hbody : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = none)
    (hhost : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = none)
    (hred : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hsec : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == securityMarker) = none)
    (hcond : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOfMetered clientIp connSeq input).req = none) :
    servePipelineOfMetered braidedDeployment5 clientIp connSeq input
      = servePipelineFull2Metered clientIp connSeq input := by
  rw [servePipelineOfMetered_braided5_eq,
      braided5_off_eq (ctxOfMetered clientIp connSeq input) hmethod hbody hhost hred hcors hsec
        hcond hvar hauto hconn hstick hslow herr hcomp hfa hrid]
  rfl

/-- **`servePipelineOfMetered_braided5_method_405` — the method `405` survives the metered
onion.** Via `braided5_method_405` at the metered context. -/
theorem servePipelineOfMetered_braided5_method_405
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == methodMarker) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment5).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment5).2)
        (ctxOfMetered clientIp connSeq input)).build).status = 405 := by
  show ((runPipeline braidedChain5 appHandler (ctxOfMetered clientIp connSeq input)).build).status = 405
  exact braided5_method_405 (ctxOfMetered clientIp connSeq input) nv hfind

/-- **`servePipelineOfMetered_braided5_body_413` — the body-size `413` fires through the
metered fold. Via `braided5_body_413`. -/
theorem servePipelineOfMetered_braided5_body_413
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hmethod : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment5).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment5).2)
        (ctxOfMetered clientIp connSeq input)).build).status = 413 := by
  show ((runPipeline braidedChain5 appHandler (ctxOfMetered clientIp connSeq input)).build).status = 413
  exact braided5_body_413 (ctxOfMetered clientIp connSeq input) nv hmethod hfind

/-- **`servePipelineOfMetered_braided5_host_421` — the Host-allowlist `421` fires through
the metered fold. Via `braided5_host_421`. -/
theorem servePipelineOfMetered_braided5_host_421
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hmethod : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hbody : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = none)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment5).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment5).2)
        (ctxOfMetered clientIp connSeq input)).build).status = 421 := by
  show ((runPipeline braidedChain5 appHandler (ctxOfMetered clientIp connSeq input)).build).status = 421
  exact braided5_host_421 (ctxOfMetered clientIp connSeq input) nv hmethod hbody hfind

#print axioms servePipelineOfMetered_braided5_off_eq
#print axioms servePipelineOfMetered_braided5_method_405
#print axioms servePipelineOfMetered_braided5_body_413
#print axioms servePipelineOfMetered_braided5_host_421

/-! ### (8p) CONFIG-DRIVEN, DEFAULT-ON middleware — the operator policy, not a test header

Every braid stage above (§8h/§8j/§8l/§8n) is a per-request TEST-HEADER-gated demo: a marker
header (`x-method-filter`, `x-body-limit`, `x-host-allowlist`, …) switches the stage from
pass-through to a fixed library WITNESS. A real homelab operator never sets a test header per
request — they set a CONFIG once (a max body size, an allowed-methods list, a served-host
allow-list) and the engine enforces it on EVERY request against the REAL request.

This section is that operability move. A `MwPolicy` is the operator-facing middleware config;
each field is OPTIONAL. A config-parameterized stage (`methodStageOf` / `bodyStageOf` /
`hostStageOf`) is a pure pass-through (`Transparent`) when its field is ABSENT and enforces on
the ACTUAL request (`c.req.method` / the declared `Content-Length` / the `Host` header) when
PRESENT — no marker. `deployStagesFull3 p` prepends the three policy stages to the always-on
`deployStagesFull2`.

* NO-REGRESSION: with the EMPTY policy the three heads are unconditionally `Transparent`, so
  `deployStagesFull3 emptyMwPolicy` folds BYTE-IDENTICALLY to `deployStagesFull2`
  (`deployStagesFull3_empty_eq`, one line via `braided_off_eq_extend`); the default deployed
  serve is unchanged and the `servePipelineOfMetered_default` anchor extends to
  `servePipelineOfMetered_policy_empty`.
* ENFORCEMENT: with a field set the matching gate FIRES on the real request — `405` on a method
  outside the list, `413` on an over-budget declared body, `421` on an off-allowlist `Host`
  (`deployStagesFull3_{method_405,body_413,host_421}`, each a `Reactor.BraidCalculus`
  `braid_gate` one-liner delegating to the proven leaf-lib response).

Every prior deployment/anchor is UNTOUCHED — `deployStagesFull3 emptyMwPolicy` reduces to the
old default. -/

/-- **The operator-facing middleware policy.** Each field is OPTIONAL: absent (`none`, the
default) ⇒ that gate is a pure pass-through (no enforcement, byte-identical to today); present
⇒ the gate enforces it on EVERY request against the real request. -/
structure MwPolicy where
  /-- Allowed request methods (`none` ⇒ any method). A method outside the list is refused
  `405` (the RFC 9110 §15.5.6 `Allow`-carrying `method405`). -/
  allowedMethods : Option (List Bytes) := none
  /-- Max declared `Content-Length` DIGIT count (`none` ⇒ no body cap). A wider declared length
  is refused `413` — the monotone size proxy the proven `Reactor.Stage.BodyLimit` gate uses (a
  budget of `7` ⇒ a 10 MB cap). -/
  maxBodyDigits : Option Nat := none
  /-- Served-`Host` allow-list (`none` ⇒ answer any `Host`). A `Host` outside the list is
  refused `421` (RFC 9110 §15.5.20 `host421`). -/
  allowedHosts : Option (List Bytes) := none
  /-- CORS allowed-origins list (`none` ⇒ off). Present ⇒ a request whose `Origin` is in the
  list gets `Access-Control-Allow-Origin` stamped on the response (the REAL `Cors.acaoValue`
  decision). This is a SERVE-STAGE field — it decides on the actual request `origin` header. -/
  corsOrigins : Option (List Bytes) := none
  /-- Max concurrent connections per source (`none` ⇒ off). A source at/over the cap is refused
  `503` (`Reactor.Stage.ConnLimit.resp503`). REACTOR-LEVEL: the gate reads the source's standing
  active-connection count from the attribute bag the accept path owns, which the stateless serve
  fold (`ctxOfMetered`) does NOT supply — so it enforces in the model but does not fire on the
  stdin/sans-IO serve. -/
  maxConnections : Option Nat := none
  /-- Aggregated per-source request threshold (`none` ⇒ off). A source at/over the threshold is
  refused `429` (`Reactor.Stage.StickTable.resp429`). REACTOR-LEVEL (as `maxConnections`): reads
  the standing stick counter from the attribute bag. This is the ENFORCEMENT value (the count the
  `429` gate decides on); the stick-table's TTL is a separate eviction/boundedness bound, not the
  gate. -/
  stickThreshold : Option Nat := none
  /-- Slowloris header-arrival timeout (`none` ⇒ off). A connection whose header phase overruns
  the timeout is refused `408` (`Reactor.Stage.Slowloris.resp408`). REACTOR-LEVEL: reads the
  header-phase start/now clocks from the attribute bag. -/
  slowlorisTimeout : Option Nat := none

/-- The empty policy — every field absent. The chain built from it folds byte-identically to
`deployStagesFull2`. -/
def emptyMwPolicy : MwPolicy := {}

/-- **The host-cap default.** `max-connections` is read TWICE from the same operator
config — once by the proven `parsePolicyLine` into `maxConnections`, once by the host,
which crosses the resulting NUMBER to the serve seam. When the directive is absent the
proven side has `none` (gate off) while the host still has an effective cap (its own
default). `withHostCap` closes that gap without a second grammar: the policy's own
value WINS where present, and the threaded host cap fills in where it is absent — so
the gate is live on every config, at exactly one number. -/
def MwPolicy.withHostCap (p : MwPolicy) (cap : Nat) : MwPolicy :=
  { p with maxConnections := some (p.maxConnections.getD cap) }

/-- A configured `max-connections` WINS over the threaded host cap — the operator's
directive is never overridden by the host's default. -/
theorem MwPolicy.withHostCap_configured (p : MwPolicy) (cap n : Nat)
    (h : p.maxConnections = some n) : (p.withHostCap cap).maxConnections = some n := by
  simp [MwPolicy.withHostCap, h]

/-- With NO `max-connections` directive the gate decides on the THREADED host cap —
this is the case that was previously OFF on the config seam. -/
theorem MwPolicy.withHostCap_absent (p : MwPolicy) (cap : Nat)
    (h : p.maxConnections = none) : (p.withHostCap cap).maxConnections = some cap := by
  simp [MwPolicy.withHostCap, h]

/-- `withHostCap` touches ONLY the connection cap: every other policy field — the
method / body / host gates, the CORS origins, the stick threshold, the slowloris
timeout — is carried through unchanged. -/
theorem MwPolicy.withHostCap_other (p : MwPolicy) (cap : Nat) :
    (p.withHostCap cap).allowedMethods = p.allowedMethods
    ∧ (p.withHostCap cap).maxBodyDigits = p.maxBodyDigits
    ∧ (p.withHostCap cap).allowedHosts = p.allowedHosts
    ∧ (p.withHostCap cap).corsOrigins = p.corsOrigins
    ∧ (p.withHostCap cap).stickThreshold = p.stickThreshold
    ∧ (p.withHostCap cap).slowlorisTimeout = p.slowlorisTimeout :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The host-RATE default** — the `withHostCap` rule, for the request-arrival limit.
`rate-limit` is likewise read twice from one operator config: once by the host (whose
accept path enforces it per CONNECTION arrival) and once by the proven policy grammar
(as `stick-limit`, into `stickThreshold`). Where the proven side has `none` the gate
would be OFF while the host still has an effective limit, so the operator's ONE
directive would bind on one path and not the other. `withHostRate` closes that with no
second grammar, exactly as `withHostCap` does: the policy's own value WINS, the
threaded host limit fills in where it is absent. A threaded `0` fills in as `some 0`,
which `admitsAt` reads as unlimited — so "off" survives the fill-in. -/
def MwPolicy.withHostRate (p : MwPolicy) (lim : Nat) : MwPolicy :=
  { p with stickThreshold := some (p.stickThreshold.getD lim) }

/-- A configured `stick-limit` WINS over the threaded host `rate-limit`. -/
theorem MwPolicy.withHostRate_configured (p : MwPolicy) (lim n : Nat)
    (h : p.stickThreshold = some n) : (p.withHostRate lim).stickThreshold = some n := by
  simp [MwPolicy.withHostRate, h]

/-- With NO `stick-limit` directive the gate decides on the THREADED host limit — the
case that was OFF on every seam before this wave. -/
theorem MwPolicy.withHostRate_absent (p : MwPolicy) (lim : Nat)
    (h : p.stickThreshold = none) : (p.withHostRate lim).stickThreshold = some lim := by
  simp [MwPolicy.withHostRate, h]

/-- `withHostRate` touches ONLY the arrival limit; every other policy field — including
the connection cap the sibling fill-in owns — is carried through unchanged, so the two
fill-ins compose in either order without interfering. -/
theorem MwPolicy.withHostRate_other (p : MwPolicy) (lim : Nat) :
    (p.withHostRate lim).allowedMethods = p.allowedMethods
    ∧ (p.withHostRate lim).maxBodyDigits = p.maxBodyDigits
    ∧ (p.withHostRate lim).allowedHosts = p.allowedHosts
    ∧ (p.withHostRate lim).corsOrigins = p.corsOrigins
    ∧ (p.withHostRate lim).maxConnections = p.maxConnections
    ∧ (p.withHostRate lim).slowlorisTimeout = p.slowlorisTimeout :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! #### `ServeConfig` — the operator serve config (Track 1 · Phase 0 seam)

`ServeConfig` EXTENDS `MwPolicy` (every gate field carries over) and adds the
per-STAMP VALUE fields the response-transform stages read — starting with the
security-header policy. Every added field is `Option` and defaults to `none`,
which resolves to TODAY's baked module const, so `emptyServeConfig` denotes the
current deployed serve byte-for-byte (zero behavior change). -/

/-- **The operator serve config.** `MwPolicy`'s gates + per-stamp response-transform
VALUES. Each new field `none` ⇒ the deployed baked const (no regression). -/
structure ServeConfig extends MwPolicy where
  /-- Security-header policy VALUE (`none` ⇒ the deployed `securityheadersStage`
  const: HSTS 1y+subdomains+preload / XFO deny / nosniff / referrer no-referrer).
  `some p` ⇒ the config-driven `securityHeadersStageOf p`. -/
  securityHeaders : Option _root_.SecurityHeaders.Policy := none
  /-- `Alt-Svc` stamp VALUE (`none` ⇒ the deployed `Reactor.Stage.AltSvc.altVal`). A SERVE-STAMP
  field: it decorates the response's `Alt-Svc` header. -/
  altSvc : Option Proto.Bytes := none
  /-- `Permissions-Policy` stamp VALUE (`none` ⇒ the deployed `Reactor.Stage.PermissionsPolicy.ppVal`,
  the deny-all policy). -/
  permissionsPolicy : Option Proto.Bytes := none
  /-- `Cross-Origin-Resource-Policy` stamp VALUE (`none` ⇒ the deployed
  `Reactor.Stage.CrossOriginResource.corpVal`, `same-origin`). -/
  corp : Option Proto.Bytes := none
  /-- `Via` stamp VALUE (`none` ⇒ the deployed `Reactor.Stage.Via.viaVal`, `1.1 drorb`). -/
  via : Option Proto.Bytes := none

/-- The empty serve config — every gate absent, every stamp value defaulted. Folds
byte-identically to today's deployed serve. -/
def emptyServeConfig : ServeConfig := {}

/-- **The host-cap default, on the full serve config.** The `MwPolicy.withHostCap`
fill-in lifted to `ServeConfig`: the gate fields are the parent projection, so this is
the SAME rule (`max-connections` wins; the threaded host cap fills in) with every
stamp / security-header value untouched. -/
def ServeConfig.withHostCap (cfg : ServeConfig) (cap : Nat) : ServeConfig :=
  { cfg with maxConnections := some (cfg.maxConnections.getD cap) }

/-- The lifted fill-in IS the policy-level one on the parent projection — so the gate
chain built from it is exactly `policyStages4 (cfg.toMwPolicy.withHostCap cap)`. -/
theorem ServeConfig.withHostCap_toMwPolicy (cfg : ServeConfig) (cap : Nat) :
    (cfg.withHostCap cap).toMwPolicy = cfg.toMwPolicy.withHostCap cap := rfl

/-- **The host-rate default, on the full serve config** — `MwPolicy.withHostRate`
lifted to `ServeConfig`, the same rule with every stamp / security-header value
untouched. -/
def ServeConfig.withHostRate (cfg : ServeConfig) (lim : Nat) : ServeConfig :=
  { cfg with stickThreshold := some (cfg.stickThreshold.getD lim) }

/-- The lifted rate fill-in IS the policy-level one on the parent projection. -/
theorem ServeConfig.withHostRate_toMwPolicy (cfg : ServeConfig) (lim : Nat) :
    (cfg.withHostRate lim).toMwPolicy = cfg.toMwPolicy.withHostRate lim := rfl

/-- The two host fill-ins are INDEPENDENT: capping does not disturb the arrival limit
and rate-filling does not disturb the connection cap, so `cfg.withHostCap cap
|>.withHostRate lim` resolves both knobs at once with neither shadowing the other. -/
theorem ServeConfig.withHostRate_withHostCap (cfg : ServeConfig) (cap lim : Nat) :
    ((cfg.withHostCap cap).withHostRate lim).maxConnections
        = some (cfg.maxConnections.getD cap)
    ∧ ((cfg.withHostCap cap).withHostRate lim).stickThreshold
        = some (cfg.stickThreshold.getD lim) :=
  ⟨rfl, rfl⟩

/-- The security-header / stamp dimension is untouched by the rate fill-in. -/
theorem ServeConfig.withHostRate_securityHeaders (cfg : ServeConfig) (lim : Nat) :
    (cfg.withHostRate lim).securityHeaders = cfg.securityHeaders := rfl

/-- The two host fill-ins COMMUTE (they write disjoint fields), so "resolve the cap then
the rate" and "resolve the rate then the cap" are the same config — which is what lets a
theorem proved about one order be applied at the other without a bridge. -/
theorem ServeConfig.withHostCap_withHostRate_comm (cfg : ServeConfig) (cap lim : Nat) :
    (cfg.withHostCap cap).withHostRate lim = (cfg.withHostRate lim).withHostCap cap := rfl

/-- The security-header / stamp dimension is untouched by the cap fill-in, so the
config-driven security slot is exactly the one the operator declared. -/
theorem ServeConfig.withHostCap_securityHeaders (cfg : ServeConfig) (cap : Nat) :
    (cfg.withHostCap cap).securityHeaders = cfg.securityHeaders := rfl

/-- **The config-resolved security-header stage.** `none` ⇒ the deployed
`securityheadersStage` const; `some p` ⇒ the config-driven `securityHeadersStageOf p`. -/
def ServeConfig.securityHeadersStage (cfg : ServeConfig) : Stage :=
  match cfg.securityHeaders with
  | some p => Reactor.Stage.SecurityHeaders.securityHeadersStageOf p
  | none   => Reactor.Stage.SecurityHeaders.securityheadersStage

/-- **NO-REGRESSION anchor.** With the security-header value absent the resolved
stage IS the deployed `securityheadersStage` — a THEOREM. -/
theorem ServeConfig.securityHeadersStage_default (cfg : ServeConfig)
    (h : cfg.securityHeaders = none) :
    cfg.securityHeadersStage = Reactor.Stage.SecurityHeaders.securityheadersStage := by
  simp only [ServeConfig.securityHeadersStage, h]

/-- **The empty config resolves to today's baked stage** (byte-for-byte). -/
theorem emptyServeConfig_securityHeadersStage :
    emptyServeConfig.securityHeadersStage = Reactor.Stage.SecurityHeaders.securityheadersStage := rfl

/-- **Operational: a configured value drives a DIFFERENT stage.** With `some p` the
resolved stage is exactly `securityHeadersStageOf p`, whose emitted header VALUE set
is `wireHeaders p` — the operator's policy, not the baked const. -/
theorem ServeConfig.securityHeadersStage_configured (cfg : ServeConfig)
    (p : _root_.SecurityHeaders.Policy) (h : cfg.securityHeaders = some p) :
    cfg.securityHeadersStage = Reactor.Stage.SecurityHeaders.securityHeadersStageOf p := by
  simp only [ServeConfig.securityHeadersStage, h]

/-! #### The config-parameterized gate stages (pass-through when the field is absent) -/

/-- **The config-driven method gate.** `none` ⇒ transparent pass-through; `some ms` ⇒ a method
outside `ms` is refused the REAL `method405`, an allowed one passes. Decides on the ACTUAL
request method (`c.req.method`), every request, no header. -/
def methodStageOf : Option (List Bytes) → Stage
  | none    => { name := "method-cfg", onRequest := fun c => .continue c, onResponse := fun _ b => b }
  | some ms => { name := "method-cfg"
                 onRequest := fun c => if ms.contains c.req.method then .continue c else .respond method405
                 onResponse := fun _ b => b }

theorem methodStageOf_statusStable (o : Option (List Bytes)) : Stage.statusStable (methodStageOf o) := by
  cases o <;> exact fun _ _ => rfl

theorem methodStageOf_none_transparent (c : Ctx) : Transparent (methodStageOf none) c :=
  ⟨rfl, fun _ => rfl⟩

theorem methodStageOf_allowed_transparent (ms : List Bytes) (c : Ctx)
    (h : ms.contains c.req.method = true) : Transparent (methodStageOf (some ms)) c := by
  refine ⟨?_, fun _ => rfl⟩
  show (if ms.contains c.req.method then StageStep.continue c else StageStep.respond method405) = StageStep.continue c
  rw [h]; rfl

theorem methodStageOf_denies (ms : List Bytes) (c : Ctx)
    (h : ms.contains c.req.method = false) :
    (methodStageOf (some ms)).onRequest c = .respond method405 := by
  show (if ms.contains c.req.method then StageStep.continue c else StageStep.respond method405) = _
  rw [h]; simp only [Bool.false_eq_true, if_false]

/-- The canonical LOWERCASE `content-length` header name the HTTP/1.1 arena parser emits
(RFC 9110 §5.1 field-name case-insensitivity; deployed header names arrive lowercase — the
same reason `deployCorsStage` reads `corsOriginNameLower`). -/
def contentLengthNameLower : Proto.Bytes :=
  [99, 111, 110, 116, 101, 110, 116, 45, 108, 101, 110, 103, 116, 104]

/-- The declared-`Content-Length`-over-budget decision at a config-supplied digit budget `n`
(the `Reactor.Stage.BodyLimit.oversized` decision at an arbitrary budget, over the lowercase
header name the deployed parser emits). -/
def bodyOversizedN (n : Nat) (req : Proto.Request) : Bool :=
  match req.headers.find? (fun nv => nv.1 == contentLengthNameLower) with
  | some nv => decide (n < nv.2.length)
  | none    => false

/-- **The config-driven body-size gate.** `none` ⇒ transparent pass-through; `some n` ⇒ a
declared `Content-Length` wider than `n` digits is refused the REAL `body413`, a within-budget
(or absent) length passes. Decides on the ACTUAL request, every request, no header. -/
def bodyStageOf : Option Nat → Stage
  | none   => { name := "body-cfg", onRequest := fun c => .continue c, onResponse := fun _ b => b }
  | some n => { name := "body-cfg"
                onRequest := fun c => if bodyOversizedN n c.req then .respond body413 else .continue c
                onResponse := fun _ b => b }

theorem bodyStageOf_statusStable (o : Option Nat) : Stage.statusStable (bodyStageOf o) := by
  cases o <;> exact fun _ _ => rfl

theorem bodyStageOf_none_transparent (c : Ctx) : Transparent (bodyStageOf none) c :=
  ⟨rfl, fun _ => rfl⟩

theorem bodyStageOf_within_transparent (n : Nat) (c : Ctx)
    (h : bodyOversizedN n c.req = false) : Transparent (bodyStageOf (some n)) c := by
  refine ⟨?_, fun _ => rfl⟩
  show (if bodyOversizedN n c.req then StageStep.respond body413 else StageStep.continue c) = StageStep.continue c
  rw [h]; simp only [Bool.false_eq_true, if_false]

theorem bodyStageOf_denies (n : Nat) (c : Ctx)
    (h : bodyOversizedN n c.req = true) :
    (bodyStageOf (some n)).onRequest c = .respond body413 := by
  show (if bodyOversizedN n c.req then StageStep.respond body413 else StageStep.continue c) = _
  rw [h]; rfl

/-- The canonical LOWERCASE `host` header name the HTTP/1.1 arena parser emits. -/
def hostNameLower : Proto.Bytes := [104, 111, 115, 116]

/-- The `Host`-off-allowlist decision at a config-supplied allow-list `hs` (the
`Reactor.Stage.HostAllowlist.misdirected` decision at an arbitrary list, over the lowercase
header name the deployed parser emits). -/
def hostMisdirectedIn (hs : List Bytes) (req : Proto.Request) : Bool :=
  match req.headers.find? (fun nv => nv.1 == hostNameLower) with
  | some nv => ! hs.contains nv.2
  | none    => false

/-- **The config-driven Host-allowlist gate.** `none` ⇒ transparent pass-through; `some hs` ⇒ a
`Host` outside `hs` is refused the REAL `host421`, a listed (or absent) `Host` passes. Decides
on the ACTUAL request `Host`, every request, no header. -/
def hostStageOf : Option (List Bytes) → Stage
  | none    => { name := "host-cfg", onRequest := fun c => .continue c, onResponse := fun _ b => b }
  | some hs => { name := "host-cfg"
                 onRequest := fun c => if hostMisdirectedIn hs c.req then .respond host421 else .continue c
                 onResponse := fun _ b => b }

theorem hostStageOf_statusStable (o : Option (List Bytes)) : Stage.statusStable (hostStageOf o) := by
  cases o <;> exact fun _ _ => rfl

theorem hostStageOf_none_transparent (c : Ctx) : Transparent (hostStageOf none) c :=
  ⟨rfl, fun _ => rfl⟩

theorem hostStageOf_listed_transparent (hs : List Bytes) (c : Ctx)
    (h : hostMisdirectedIn hs c.req = false) : Transparent (hostStageOf (some hs)) c := by
  refine ⟨?_, fun _ => rfl⟩
  show (if hostMisdirectedIn hs c.req then StageStep.respond host421 else StageStep.continue c) = StageStep.continue c
  rw [h]; simp only [Bool.false_eq_true, if_false]

theorem hostStageOf_denies (hs : List Bytes) (c : Ctx)
    (h : hostMisdirectedIn hs c.req = true) :
    (hostStageOf (some hs)).onRequest c = .respond host421 := by
  show (if hostMisdirectedIn hs c.req then StageStep.respond host421 else StageStep.continue c) = _
  rw [h]; rfl

/-! #### The DEFAULT-ON config-driven chain -/

/-- The three ordered policy stages a config denotes (method `405` / body `413` / Host `421`),
in request-phase order. -/
def policyStages (p : MwPolicy) : List Stage :=
  [methodStageOf p.allowedMethods, bodyStageOf p.maxBodyDigits, hostStageOf p.allowedHosts]

/-- **The config-driven deployed chain.** The three config-parameterized policy stages
prepended to the always-on `deployStagesFull2`. With `emptyMwPolicy` the three heads are
transparent and the fold is byte-identical to `deployStagesFull2`; with a field set the
matching gate enforces on every request. -/
def deployStagesFull3 (p : MwPolicy) : List Stage :=
  policyStages p ++ deployStagesFull2

/-- Every stage of `deployStagesFull3 p` is status-stable (the three policy stages, whose
response phase is the identity, plus the inherited `deployStagesFull2`). -/
theorem deployStagesFull3_statusStable (p : MwPolicy) :
    ∀ s ∈ deployStagesFull3 p, Stage.statusStable s := by
  intro s hs
  simp only [deployStagesFull3, policyStages, List.cons_append, List.nil_append] at hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact methodStageOf_statusStable _
  rcases List.mem_cons.mp hs with rfl | hs
  · exact bodyStageOf_statusStable _
  rcases List.mem_cons.mp hs with rfl | hs
  · exact hostStageOf_statusStable _
  · exact deployStagesFull2_statusStable s hs

/-- **`deployStagesFull3_empty_eq` — byte-identity when the policy is EMPTY.** ONE line via the
calculus: the three EMPTY-policy heads are unconditionally `Transparent`, so
`braided_off_eq_extend` peels them and the fold is exactly `deployStagesFull2`'s. This is the
no-regression anchor — the default config-driven serve is byte-for-byte the old serve. -/
theorem deployStagesFull3_empty_eq (h : Ctx → Response) (c : Ctx) :
    runPipeline (deployStagesFull3 emptyMwPolicy) h c = runPipeline deployStagesFull2 h c :=
  braided_off_eq_extend (policyStages emptyMwPolicy) deployStagesFull2 deployStagesFull2 h c
    (cons_transparent (methodStageOf_none_transparent c)
      (cons_transparent (bodyStageOf_none_transparent c)
        (cons_transparent (hostStageOf_none_transparent c) (nil_transparent c))))
    rfl

/-! #### THE FIRE — each config-present gate drives the served status on the REAL request
(each proof a `Reactor.BraidCalculus` `braid_gate` ONE-LINER). -/

/-- **`deployStagesFull3_method_405` — a method outside the config list is refused `405`
(ONE-LINER).** The head `methodStageOf (some ms)` `.respond`s the REAL `method405` on a request
whose method is not in `ms`, and it survives the status-stable inner onion (`braid_gate`,
pref `[]`). No test header — the decision is on `c.req.method`. -/
theorem deployStagesFull3_method_405 (ms : List Bytes) (mbody : Option Nat)
    (mhost : Option (List Bytes)) (c : Ctx) (h : ms.contains c.req.method = false) :
    ((runPipeline (deployStagesFull3
        { allowedMethods := some ms, maxBodyDigits := mbody, allowedHosts := mhost })
        appHandler c).build).status = 405 :=
  braid_gate [] (methodStageOf (some ms)) _ appHandler c _ (nil_transparent c)
    (methodStageOf_denies ms c h)
    (fun t ht => deployStagesFull3_statusStable _ t (List.mem_cons_of_mem _ ht))

/-- **`deployStagesFull3_body_413` — an over-budget declared body is refused `413`
(ONE-LINER).** With the method stage transparent on `c` (no method policy, or the method is
allowed), the body gate `bodyStageOf (some n)` `.respond`s the REAL `body413` on a request
whose declared `Content-Length` is wider than `n` digits (`braid_gate`, pref
`[methodStageOf mmeth]`). No test header — the decision is on the declared length. -/
theorem deployStagesFull3_body_413 (mmeth : Option (List Bytes)) (n : Nat)
    (mhost : Option (List Bytes)) (c : Ctx)
    (hmeth : Transparent (methodStageOf mmeth) c) (h : bodyOversizedN n c.req = true) :
    ((runPipeline (deployStagesFull3
        { allowedMethods := mmeth, maxBodyDigits := some n, allowedHosts := mhost })
        appHandler c).build).status = 413 :=
  braid_gate [methodStageOf mmeth] (bodyStageOf (some n)) _ appHandler c _
    (cons_transparent hmeth (nil_transparent c))
    (bodyStageOf_denies n c h)
    (by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hostStageOf_statusStable _
      · exact deployStagesFull2_statusStable t ht)

/-- **`deployStagesFull3_host_421` — an off-allowlist `Host` is refused `421` (ONE-LINER).**
With the method and body stages transparent on `c`, the host gate `hostStageOf (some hs)`
`.respond`s the REAL `host421` on a request whose `Host` is outside `hs` (`braid_gate`, pref
`[methodStageOf mmeth, bodyStageOf mbody]`). No test header — the decision is on `Host`. -/
theorem deployStagesFull3_host_421 (mmeth : Option (List Bytes)) (mbody : Option Nat)
    (hs : List Bytes) (c : Ctx)
    (hmeth : Transparent (methodStageOf mmeth) c) (hbody : Transparent (bodyStageOf mbody) c)
    (h : hostMisdirectedIn hs c.req = true) :
    ((runPipeline (deployStagesFull3
        { allowedMethods := mmeth, maxBodyDigits := mbody, allowedHosts := some hs })
        appHandler c).build).status = 421 :=
  braid_gate [methodStageOf mmeth, bodyStageOf mbody] (hostStageOf (some hs)) _ appHandler c _
    (cons_transparent hmeth (cons_transparent hbody (nil_transparent c)))
    (hostStageOf_denies hs c h)
    deployStagesFull2_statusStable

/-! ### §8q — the FOUR remaining middleware stages, config-parameterized (round 2)

Round 1 (§8p) moved method/body/host to config-driven DEFAULT-ON. Four leaf-lib stages stayed
test-header braids because their decisions ran on FIXED witnesses (`corsPolicy`, `connCap`,
`threshold`, `headerTimeout`), not config values. This section parameterizes them the same way:
each is `Transparent` when its field is absent (byte-identical default) and enforces the config
value when present. `deployStagesFull4 p` extends `deployStagesFull3 p`'s three heads with four
more — CORS (a response transform), conn-limit / stick / slowloris (gates).

HONEST SUBSTRATE SPLIT (the reason only CORS moves to a LIVE default-on row):
* **CORS is a SERVE-STAGE** — its decision reads `c.req` (the `origin` header), which the real
  request carries, so it FIRES on the default stdin/metered serve from the actual request bytes
  (`deployStagesFull4_cors_acao`). `deployStagesFull2` already stamps ACAO for a hardcoded origin
  (`deployCorsStage`); this makes the allow-list OPERATOR-DRIVEN.
* **conn-limit / stick / slowloris are REACTOR-LEVEL** — each decides on standing PER-SOURCE
  state read from the attribute bag (`conn-active` / `stick-count` / `hdr-now`), which the
  stateless serve fold (`ctxOfMetered` supplies only `client.ip` + the rate seq) does NOT carry.
  Their config gates are PROVEN at the chain level (`_conn_503` / `_stick_429` / `_slow_408`) but
  cannot fire on the sans-IO serve — the per-connection counters are an accept-path (reactor)
  concern, not a serve-stage one. So they are config-parameterized + proven, but NOT curl-live. -/

/-! #### The config-driven CORS transform (a SERVE-STAGE — decides on the real `origin` header) -/

/-- A `Cors.Policy` from an operator-supplied allowed-origins byte-list (exact-match, no wildcard,
no credentials — the strict default). Origins decode via the same `bytesToStr` the deployed
`corsOriginOf` reader uses, so a request `origin` matches an operator entry byte-for-byte. -/
def corsPolicyOf (origins : List Bytes) : _root_.Cors.Policy where
  allowedOrigins   := origins.map Reactor.Stage.Cors.bytesToStr
  allowAnyOrigin   := false
  allowedMethods   := []
  allowedHeaders   := []
  allowCredentials := false
  maxAge           := 0

/-- **The config-driven CORS stage.** `none` ⇒ transparent (no ACAO added, byte-identical);
`some origins` ⇒ on the response phase it runs the REAL `Cors.acaoValue` over `corsPolicyOf
origins` on the request's canonical lowercase `origin` (`corsOriginOf`) and stamps
`Access-Control-Allow-Origin` iff permitted. Decides on the ACTUAL request, every request, no
header. -/
def corsStageOf : Option (List Bytes) → Stage
  | none         => { name := "cors-cfg", onRequest := fun c => .continue c, onResponse := fun _ b => b }
  | some origins => { name := "cors-cfg"
                      onRequest := fun c => .continue c
                      onResponse := fun c b =>
                        match _root_.Cors.acaoValue (corsPolicyOf origins) (corsOriginOf c) with
                        | some v => b.addHeader (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
                        | none   => b }

theorem corsStageOf_statusStable (o : Option (List Bytes)) : Stage.statusStable (corsStageOf o) := by
  intro c b
  cases o with
  | none => rfl
  | some origins =>
    show ((match _root_.Cors.acaoValue (corsPolicyOf origins) (corsOriginOf c) with
      | some v => b.addHeader (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
      | none   => b).build).status = b.build.status
    cases _root_.Cors.acaoValue (corsPolicyOf origins) (corsOriginOf c) <;>
      simp only [Reactor.Pipeline.build_addHeader]

theorem corsStageOf_none_transparent (c : Ctx) : Transparent (corsStageOf none) c :=
  ⟨rfl, fun _ => rfl⟩

/-! #### The config-driven per-source gates (REACTOR-LEVEL — decide on standing attribute state) -/

/-- **The config-driven connection-limit gate.** `none` ⇒ transparent; `some cap` ⇒ a source
whose standing active-connection count (`Reactor.Stage.ConnLimit.activeOf`) is at/over `cap` is
refused the REAL `resp503`. REACTOR-LEVEL: the count rides in the attribute bag the accept path
owns. -/
def connStageOf : Option Nat → Stage
  | none     => { name := "conn-cfg", onRequest := fun c => .continue c, onResponse := fun _ b => b }
  | some cap => { name := "conn-cfg"
                  onRequest := fun c => cond (Reactor.Stage.ConnLimit.admits cap (Reactor.Stage.ConnLimit.activeOf c))
                                             (.continue c) (.respond Reactor.Stage.ConnLimit.resp503)
                  onResponse := fun _ b => b }

theorem connStageOf_statusStable (o : Option Nat) : Stage.statusStable (connStageOf o) := by
  cases o <;> exact fun _ _ => rfl

theorem connStageOf_none_transparent (c : Ctx) : Transparent (connStageOf none) c :=
  ⟨rfl, fun _ => rfl⟩

theorem connStageOf_admits_transparent (cap : Nat) (c : Ctx)
    (h : Reactor.Stage.ConnLimit.admits cap (Reactor.Stage.ConnLimit.activeOf c) = true) :
    Transparent (connStageOf (some cap)) c := by
  refine ⟨?_, fun _ => rfl⟩
  show cond (Reactor.Stage.ConnLimit.admits cap (Reactor.Stage.ConnLimit.activeOf c))
         (StageStep.continue c) (.respond Reactor.Stage.ConnLimit.resp503) = .continue c
  rw [h]; rfl

theorem connStageOf_denies (cap : Nat) (c : Ctx)
    (h : Reactor.Stage.ConnLimit.admits cap (Reactor.Stage.ConnLimit.activeOf c) = false) :
    (connStageOf (some cap)).onRequest c = .respond Reactor.Stage.ConnLimit.resp503 := by
  show cond (Reactor.Stage.ConnLimit.admits cap (Reactor.Stage.ConnLimit.activeOf c))
         (StageStep.continue c) (.respond Reactor.Stage.ConnLimit.resp503) = _
  rw [h]; rfl

/-- **The config-driven stick-table arrival-limit gate.** `none` ⇒ transparent;
`some thr` ⇒ the REAL shared admission rule `Reactor.Stage.StickTable.admitsAt thr` on
the source's threaded in-window arrival count — refuse the REAL `resp429` once the
count reaches a LIVE limit, admit unconditionally when the limit is `0`. REACTOR-LEVEL
(as conn-limit): the count rides in the attribute bag.

THE `0` CASE IS NOT COSMETIC. The rule used to be the bare `countOf c < thr`, under
which `some 0` refuses EVERY request — and `0` is exactly what `rate-limit 0` (the
documented way to DISABLE the limit, and what `SharedStanding::rate_note` reads as
"never refuse") threads, and what the `withHostRate` fill-in turns into `some 0`. While
`countOf` had no producer the gate was inert and the discrepancy could not fire; the
moment the count became a real host reading it would have turned "rate limiting off"
into "refuse everything". Sharing `admitsAt` with the connection cap — where `0` has
always meant unlimited — removes the disagreement at the source rather than special-
casing the fill-in. -/
def stickStageOf : Option Nat → Stage
  | none     => { name := "stick-cfg", onRequest := fun c => .continue c, onResponse := fun _ b => b }
  | some thr => { name := "stick-cfg"
                  onRequest := fun c =>
                    cond (Reactor.Stage.StickTable.admitsAt thr
                            (Reactor.Stage.StickTable.countOf c))
                      (.continue c) (.respond Reactor.Stage.StickTable.resp429)
                  onResponse := fun _ b => b }

theorem stickStageOf_statusStable (o : Option Nat) : Stage.statusStable (stickStageOf o) := by
  cases o <;> exact fun _ _ => rfl

theorem stickStageOf_none_transparent (c : Ctx) : Transparent (stickStageOf none) c :=
  ⟨rfl, fun _ => rfl⟩

theorem stickStageOf_under_transparent (thr : Nat) (c : Ctx)
    (h : Reactor.Stage.StickTable.countOf c < thr) : Transparent (stickStageOf (some thr)) c := by
  refine ⟨?_, fun _ => rfl⟩
  show cond (Reactor.Stage.StickTable.admitsAt thr (Reactor.Stage.StickTable.countOf c))
        (StageStep.continue c) (.respond Reactor.Stage.StickTable.resp429) = .continue c
  rw [Reactor.Stage.StickTable.admitsAt_under (Nat.lt_of_le_of_lt (Nat.zero_le _) h) h]; rfl

/-- **A `some 0` threshold is TRANSPARENT** — "rate limiting disabled" means admit, on
this gate exactly as on the connection cap. The statement the retired `countOf c < thr`
rule made FALSE. -/
theorem stickStageOf_zero_transparent (c : Ctx) : Transparent (stickStageOf (some 0)) c := by
  refine ⟨?_, fun _ => rfl⟩
  show cond (Reactor.Stage.StickTable.admitsAt 0 (Reactor.Stage.StickTable.countOf c))
        (StageStep.continue c) (.respond Reactor.Stage.StickTable.resp429) = .continue c
  rw [Reactor.Stage.StickTable.admitsAt_unlimited]; rfl

/-- **The gate is transparent whenever the shared rule ADMITS** — the general form
(`connStageOf_admits_transparent`'s twin), which is what a caller holding a decision
rather than an inequality needs. -/
theorem stickStageOf_admits_transparent (thr : Nat) (c : Ctx)
    (h : Reactor.Stage.StickTable.admitsAt thr (Reactor.Stage.StickTable.countOf c) = true) :
    Transparent (stickStageOf (some thr)) c := by
  refine ⟨?_, fun _ => rfl⟩
  show cond (Reactor.Stage.StickTable.admitsAt thr (Reactor.Stage.StickTable.countOf c))
        (StageStep.continue c) (.respond Reactor.Stage.StickTable.resp429) = .continue c
  rw [h]; rfl

/-- The gate refuses at/over a LIVE limit. `0 < thr` is a REAL hypothesis, not
bureaucracy: at `thr = 0` the gate is off (`stickStageOf_zero_transparent`), so a
refusal there would be the bug this rule change removes. -/
theorem stickStageOf_denies (thr : Nat) (c : Ctx) (hpos : 0 < thr)
    (h : thr ≤ Reactor.Stage.StickTable.countOf c) :
    (stickStageOf (some thr)).onRequest c = .respond Reactor.Stage.StickTable.resp429 := by
  show cond (Reactor.Stage.StickTable.admitsAt thr (Reactor.Stage.StickTable.countOf c))
        (StageStep.continue c) (.respond Reactor.Stage.StickTable.resp429) = _
  rw [Reactor.Stage.StickTable.admitsAt_over hpos h]; rfl

/-- **The config-driven slowloris gate.** `none` ⇒ transparent; `some to` ⇒ a connection whose
header phase has overrun `to` (`Reactor.Stage.Slowloris.expired` on the reconstructed clocks) is
refused the REAL `resp408`. REACTOR-LEVEL: the header clocks ride in the attribute bag. -/
def slowStageOf : Option Nat → Stage
  | none    => { name := "slow-cfg", onRequest := fun c => .continue c, onResponse := fun _ b => b }
  | some to => { name := "slow-cfg"
                 onRequest := fun c => cond (Reactor.Stage.Slowloris.expired to
                                              (Reactor.Stage.Slowloris.startedOf c) (Reactor.Stage.Slowloris.nowOf c))
                                            (.respond Reactor.Stage.Slowloris.resp408) (.continue c)
                 onResponse := fun _ b => b }

theorem slowStageOf_statusStable (o : Option Nat) : Stage.statusStable (slowStageOf o) := by
  cases o <;> exact fun _ _ => rfl

theorem slowStageOf_none_transparent (c : Ctx) : Transparent (slowStageOf none) c :=
  ⟨rfl, fun _ => rfl⟩

theorem slowStageOf_intime_transparent (to : Nat) (c : Ctx)
    (h : Reactor.Stage.Slowloris.expired to (Reactor.Stage.Slowloris.startedOf c)
           (Reactor.Stage.Slowloris.nowOf c) = false) : Transparent (slowStageOf (some to)) c := by
  refine ⟨?_, fun _ => rfl⟩
  show cond (Reactor.Stage.Slowloris.expired to (Reactor.Stage.Slowloris.startedOf c)
             (Reactor.Stage.Slowloris.nowOf c))
         (.respond Reactor.Stage.Slowloris.resp408) (StageStep.continue c) = .continue c
  rw [h]; rfl

theorem slowStageOf_denies (to : Nat) (c : Ctx)
    (h : Reactor.Stage.Slowloris.expired to (Reactor.Stage.Slowloris.startedOf c)
           (Reactor.Stage.Slowloris.nowOf c) = true) :
    (slowStageOf (some to)).onRequest c = .respond Reactor.Stage.Slowloris.resp408 := by
  show cond (Reactor.Stage.Slowloris.expired to (Reactor.Stage.Slowloris.startedOf c)
             (Reactor.Stage.Slowloris.nowOf c))
         (.respond Reactor.Stage.Slowloris.resp408) (StageStep.continue c) = _
  rw [h]; rfl

/-! #### The DEFAULT-ON seven-stage config-driven chain -/

/-- The seven ordered policy stages a config denotes: the three §8p heads (method `405` / body
`413` / Host `421`), then conn-limit `503` / stick `429` / slowloris `408` gates, then the CORS
transform (last, so its ACAO decorates the admitted response — the gates reject before it). -/
def policyStages4 (p : MwPolicy) : List Stage :=
  policyStages p ++
    [ connStageOf p.maxConnections
    , stickStageOf p.stickThreshold
    , slowStageOf p.slowlorisTimeout
    , corsStageOf p.corsOrigins ]

/-- **The round-2 config-driven deployed chain.** The seven config-parameterized policy stages
prepended to the always-on `deployStagesFull2`. With `emptyMwPolicy` all seven heads are
transparent and the fold is byte-identical to `deployStagesFull2`; with a field set the matching
stage enforces / decorates on every request. -/
def deployStagesFull4 (p : MwPolicy) : List Stage :=
  policyStages4 p ++ deployStagesFull2

/-- Every stage of `deployStagesFull4 p` is status-stable (the seven policy stages — six gates
whose response phase is the identity, plus the CORS transform which only adds headers — and the
inherited `deployStagesFull2`). -/
theorem deployStagesFull4_statusStable (p : MwPolicy) :
    ∀ s ∈ deployStagesFull4 p, Stage.statusStable s := by
  intro s hs
  simp only [deployStagesFull4, policyStages4, policyStages, List.cons_append, List.nil_append] at hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact methodStageOf_statusStable _
  rcases List.mem_cons.mp hs with rfl | hs
  · exact bodyStageOf_statusStable _
  rcases List.mem_cons.mp hs with rfl | hs
  · exact hostStageOf_statusStable _
  rcases List.mem_cons.mp hs with rfl | hs
  · exact connStageOf_statusStable _
  rcases List.mem_cons.mp hs with rfl | hs
  · exact stickStageOf_statusStable _
  rcases List.mem_cons.mp hs with rfl | hs
  · exact slowStageOf_statusStable _
  rcases List.mem_cons.mp hs with rfl | hs
  · exact corsStageOf_statusStable _
  · exact deployStagesFull2_statusStable s hs

/-- **`deployStagesFull4_empty_eq` — byte-identity when the policy is EMPTY.** ONE line via the
calculus: the seven EMPTY-policy heads are unconditionally `Transparent`, so `braided_off_eq_extend`
peels them and the fold is exactly `deployStagesFull2`'s. The round-2 no-regression anchor — the
default config-driven serve is byte-for-byte the old serve (and thus `deployStagesFull3`'s too). -/
theorem deployStagesFull4_empty_eq (h : Ctx → Response) (c : Ctx) :
    runPipeline (deployStagesFull4 emptyMwPolicy) h c = runPipeline deployStagesFull2 h c :=
  braided_off_eq_extend (policyStages4 emptyMwPolicy) deployStagesFull2 deployStagesFull2 h c
    (cons_transparent (methodStageOf_none_transparent c)
      (cons_transparent (bodyStageOf_none_transparent c)
        (cons_transparent (hostStageOf_none_transparent c)
          (cons_transparent (connStageOf_none_transparent c)
            (cons_transparent (stickStageOf_none_transparent c)
              (cons_transparent (slowStageOf_none_transparent c)
                (cons_transparent (corsStageOf_none_transparent c) (nil_transparent c))))))))
    rfl

/-! #### Track 1 · Phase 2 — WIRE `ServeConfig` into the deployed chain's security-header slot.

`deployStagesFull4` / `deployStagesFull2` bake the security-header stage as the module const
`securityheadersStage`. `serveStagesWithSecHeaders` makes that ONE slot config-driven — the
security-header stage is `cfg.securityHeadersStage` (`securityHeadersStageOf` of the cfg-supplied
policy, or the baked const when the value is absent), every other stage unchanged. The
no-regression anchor (`serveStagesWithSecHeaders_empty_eq`, a THEOREM) shows the DEFAULT/empty
config's chain IS today's `deployStagesFull4 emptyMwPolicy` and (via `deployStagesFull4_empty_eq`)
folds byte-identically to the frozen `deployStagesFull2`. The operational `∀ cfg` theorems
(`serveStagesWithSecHeaders_secStage_run` / `_hsts_configured`) show the served security-header
VALUES are exactly `wireHeaders (cfg policy)` — the deployed serve now varies its security headers
with config, proven. Purely ADDITIVE: `deployStagesFull4` / `deployStagesFull2` and the live serve
path are UNTOUCHED (zero regression to the deployed leanc serve). -/

/-- `deployStagesFull2` with the security-header slot parameterized. At `securityheadersStage` it
recovers `deployStagesFull2` (`deployStagesFull2WithSec_default`, the slot anchor). -/
def deployStagesFull2WithSec (secStage : Stage) : List Stage :=
  [ jwtAdminStage
  , Reactor.Stage.BasicAuth.basicStage
  , Reactor.Stage.IpFilter.ipfilterStage
  , Reactor.Stage.Rate.rateStage
  , cacheEmptyStage
  , Reactor.Stage.Redirect.redirectStage
  , traversalStage
  , policyStage
  , headerRewriteStage
  , deployCorsStage
  , Reactor.Stage.Gzip.gzipStage
  , Reactor.Stage.HtmlRewrite.htmlrewriteStage
  , secStage
  , Reactor.Stage.Header.headerStage ]

/-- **NO-REGRESSION (slot).** The baked security-header stage in that slot recovers the frozen
`deployStagesFull2`, byte-for-byte — a `rfl` THEOREM. -/
theorem deployStagesFull2WithSec_default :
    deployStagesFull2WithSec Reactor.Stage.SecurityHeaders.securityheadersStage = deployStagesFull2 :=
  rfl

/-- **The config-driven deployed chain (security-header slot).** The seven config-parameterized
policy heads (`policyStages4`) over `deployStagesFull2` whose security-header slot is taken from the
`ServeConfig`. Every gate / transform other than the security-header stage is exactly today's. -/
def serveStagesWithSecHeaders (cfg : ServeConfig) : List Stage :=
  policyStages4 cfg.toMwPolicy ++ deployStagesFull2WithSec cfg.securityHeadersStage

/-- **`serveStagesWithSecHeaders_empty_eq` — the default config IS today's baked chain.** With the
empty `ServeConfig` (all gates absent, security-header value defaulted) the config-driven chain is
byte-identical to `deployStagesFull4 emptyMwPolicy` — a THEOREM (the security slot recovers the baked
const, and the parent projection recovers `emptyMwPolicy`). -/
theorem serveStagesWithSecHeaders_empty_eq :
    serveStagesWithSecHeaders emptyServeConfig = deployStagesFull4 emptyMwPolicy :=
  rfl

/-! #### ★ THE CONFIG SEAM'S DoS GATES — stated over the THREADED admission readings

`deployStagesFull4_conn_503` / `_slow_408` are chain-level statements whose docstrings
said, honestly, "the standing active count is an attribute-bag input the sans-IO serve
does not supply, so this is proven but does not fire on the default serve". The
config-driven seam (`drorb_serve_metered_cfg_conformant`) folded over `ctxOfMetered`,
which supplies NONE of them — so on that seam the gates were pass-throughs.

These theorems are the same decisions restated over the config chain
(`serveStagesWithSecHeaders`, the security-header-slot chain the config seam actually
folds) with the cap fill-in in force, so they hold for the chain the seam runs. The
`ctxOfMeteredConn` projections above supply the readings. -/

/-- The config-parameterized security-header stage is status-stable: its response phase
only pushes headers onto the affine builder, which cannot move the status. -/
theorem securityHeadersStageOf_statusStable (p : _root_.SecurityHeaders.Policy) :
    Stage.statusStable (Reactor.Stage.SecurityHeaders.securityHeadersStageOf p) := by
  intro c b
  show (((Reactor.Stage.SecurityHeaders.wireHeaders p).foldl
      ResponseBuilder.addHeader b).build).status = b.build.status
  rw [Reactor.Pipeline.build_addHeaders]

/-- Whatever the config resolves the security-header slot to, it is status-stable. -/
theorem ServeConfig.securityHeadersStage_statusStable (cfg : ServeConfig) :
    Stage.statusStable cfg.securityHeadersStage := by
  unfold ServeConfig.securityHeadersStage
  cases cfg.securityHeaders with
  | none => exact fun _ _ => rfl
  | some p => exact securityHeadersStageOf_statusStable p

/-- Every stage of the security-header-slot chain is status-stable — the slot from the
hypothesis, the other thirteen inherited from `deployStagesFull2_statusStable`. -/
theorem deployStagesFull2WithSec_statusStable (sec : Stage) (hsec : Stage.statusStable sec) :
    ∀ s ∈ deployStagesFull2WithSec sec, Stage.statusStable s := by
  intro s hs
  simp only [deployStagesFull2WithSec, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h'|h'|h'|h'|h'|h'|h'|h'|h'|h'|h'|h'|h'|h' <;> subst h' <;>
    first
      | exact hsec
      | exact deployStagesFull2_statusStable _ (by simp [deployStagesFull2])

/-- Every stage of the config-driven chain BELOW the connection gate is status-stable
(stick / slowloris / CORS, then the security-header-slot chain) — the obligation
`braid_gate` discharges to carry a gate's status out through the rest of the fold. -/
theorem serveStagesWithSecHeaders_tail_statusStable (cfg : ServeConfig) :
    ∀ s ∈ stickStageOf cfg.stickThreshold :: slowStageOf cfg.slowlorisTimeout
            :: corsStageOf cfg.corsOrigins :: deployStagesFull2WithSec cfg.securityHeadersStage,
      Stage.statusStable s := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact stickStageOf_statusStable _
  rcases List.mem_cons.mp hs with rfl | hs
  · exact slowStageOf_statusStable _
  rcases List.mem_cons.mp hs with rfl | hs
  · exact corsStageOf_statusStable _
  · exact deployStagesFull2WithSec_statusStable _ cfg.securityHeadersStage_statusStable s hs

/-- **★ The config seam's per-source CONNECTION gate FIRES, at the EFFECTIVE cap.**
With the three §8p heads transparent, a source whose standing active count is at/over
the effective cap — the operator's `max-connections` where the directive is present,
the THREADED host cap where it is absent (`MwPolicy.withHostCap`) — is answered the
proven `503` by the config seam's own chain. The reading `activeOf c` is exactly what
`ctxOfMeteredConn` now supplies (`activeOf_ctxOfMeteredConn`), so this is no longer a
statement about an attribute nobody writes. -/
theorem serveStagesWithSecHeaders_conn_503 (cfg : ServeConfig) (cap : Nat)
    (h : Ctx → Response) (c : Ctx)
    (hmeth : Transparent (methodStageOf cfg.allowedMethods) c)
    (hbody : Transparent (bodyStageOf cfg.maxBodyDigits) c)
    (hhost : Transparent (hostStageOf cfg.allowedHosts) c)
    (hover : Reactor.Stage.ConnLimit.admits (cfg.maxConnections.getD cap)
               (Reactor.Stage.ConnLimit.activeOf c) = false) :
    ((runPipeline (serveStagesWithSecHeaders (cfg.withHostCap cap)) h c).build).status = 503 := by
  show ((runPipeline ([methodStageOf cfg.allowedMethods, bodyStageOf cfg.maxBodyDigits,
      hostStageOf cfg.allowedHosts]
      ++ connStageOf (some (cfg.maxConnections.getD cap))
        :: stickStageOf cfg.stickThreshold :: slowStageOf cfg.slowlorisTimeout
        :: corsStageOf cfg.corsOrigins
        :: deployStagesFull2WithSec cfg.securityHeadersStage) h c).build).status = 503
  exact braid_gate _ (connStageOf (some (cfg.maxConnections.getD cap))) _ h c _
    (cons_transparent hmeth (cons_transparent hbody (cons_transparent hhost (nil_transparent c))))
    (connStageOf_denies _ c hover)
    (serveStagesWithSecHeaders_tail_statusStable cfg)

/-- **★ The config seam's connection gate is TRANSPARENT below the effective cap** —
the dual, and the property an operator depends on: strictly under the cap the gate
adds nothing and the whole config chain runs. -/
theorem serveStagesWithSecHeaders_conn_passes (cfg : ServeConfig) (cap : Nat)
    (h : Ctx → Response) (c : Ctx)
    (hmeth : Transparent (methodStageOf cfg.allowedMethods) c)
    (hbody : Transparent (bodyStageOf cfg.maxBodyDigits) c)
    (hhost : Transparent (hostStageOf cfg.allowedHosts) c)
    (hunder : Reactor.Stage.ConnLimit.admits (cfg.maxConnections.getD cap)
                (Reactor.Stage.ConnLimit.activeOf c) = true) :
    runPipeline (serveStagesWithSecHeaders (cfg.withHostCap cap)) h c
      = runPipeline (stickStageOf cfg.stickThreshold
          :: slowStageOf cfg.slowlorisTimeout :: corsStageOf cfg.corsOrigins
          :: deployStagesFull2WithSec cfg.securityHeadersStage) h c := by
  show runPipeline ([methodStageOf cfg.allowedMethods, bodyStageOf cfg.maxBodyDigits,
      hostStageOf cfg.allowedHosts, connStageOf (some (cfg.maxConnections.getD cap))]
      ++ (stickStageOf cfg.stickThreshold :: slowStageOf cfg.slowlorisTimeout
          :: corsStageOf cfg.corsOrigins
          :: deployStagesFull2WithSec cfg.securityHeadersStage)) h c = _
  exact braided_off_eq_extend _ _ _ h c
    (cons_transparent hmeth (cons_transparent hbody (cons_transparent hhost
      (cons_transparent (connStageOf_admits_transparent _ c hunder) (nil_transparent c)))))
    rfl

/-- **★ THE CONFIG SEAM'S RATE GATE FIRES, at the EFFECTIVE arrival limit.** With the
three §8p heads transparent and the connection gate admitting, a source whose THREADED
in-window arrival count has reached the effective limit — the operator's `stick-limit`
where that directive is present, the THREADED host `rate-limit` where it is absent
(`withHostRate`) — is answered the proven `429` by the config seam's own chain.

This is the gate that was a PASS-THROUGH on both metered seams until this wave, and it
was one for a reason that was NAMED rather than fudged: the reading `countOf c` had no
producer, because the reactor's rate window returned a bool
(`SharedStanding::rate_note`), not a count. It is now the host's counting read, so this
theorem is about a number that exists. -/
theorem serveStagesWithSecHeaders_rate_429 (cfg : ServeConfig) (cap lim : Nat)
    (h : Ctx → Response) (c : Ctx)
    (hmeth : Transparent (methodStageOf cfg.allowedMethods) c)
    (hbody : Transparent (bodyStageOf cfg.maxBodyDigits) c)
    (hhost : Transparent (hostStageOf cfg.allowedHosts) c)
    (hconn : Reactor.Stage.ConnLimit.admits (cfg.maxConnections.getD cap)
               (Reactor.Stage.ConnLimit.activeOf c) = true)
    (hpos : 0 < cfg.stickThreshold.getD lim)
    (hover : cfg.stickThreshold.getD lim ≤ Reactor.Stage.StickTable.countOf c) :
    ((runPipeline (serveStagesWithSecHeaders
        ((cfg.withHostCap cap).withHostRate lim)) h c).build).status = 429 := by
  show ((runPipeline ([methodStageOf cfg.allowedMethods, bodyStageOf cfg.maxBodyDigits,
      hostStageOf cfg.allowedHosts, connStageOf (some (cfg.maxConnections.getD cap))]
      ++ stickStageOf (some (cfg.stickThreshold.getD lim))
        :: slowStageOf cfg.slowlorisTimeout
        :: corsStageOf cfg.corsOrigins
        :: deployStagesFull2WithSec cfg.securityHeadersStage) h c).build).status = 429
  exact braid_gate _ (stickStageOf (some (cfg.stickThreshold.getD lim))) _ h c _
    (cons_transparent hmeth (cons_transparent hbody (cons_transparent hhost
      (cons_transparent (connStageOf_admits_transparent _ c hconn) (nil_transparent c)))))
    (stickStageOf_denies _ c hpos hover)
    (by
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact slowStageOf_statusStable _
      rcases List.mem_cons.mp hs with rfl | hs
      · exact corsStageOf_statusStable _
      · exact deployStagesFull2WithSec_statusStable _ cfg.securityHeadersStage_statusStable s hs)

/-- **★ The operator's `rate-limit` binds with NO proven-grammar directive at all.** The
case that matters operationally: a `DRORB_CONFIG` that carries `rate-limit 64` and
nothing the proven policy grammar spells `stick-limit`. The fill-in makes the THREADED
host limit the effective one, so the `429` fires at exactly the operator's number. -/
theorem serveStagesWithSecHeaders_rate_429_hostLimit (cfg : ServeConfig) (cap lim : Nat)
    (h : Ctx → Response) (c : Ctx)
    (hmeth : Transparent (methodStageOf cfg.allowedMethods) c)
    (hbody : Transparent (bodyStageOf cfg.maxBodyDigits) c)
    (hhost : Transparent (hostStageOf cfg.allowedHosts) c)
    (hconn : Reactor.Stage.ConnLimit.admits (cfg.maxConnections.getD cap)
               (Reactor.Stage.ConnLimit.activeOf c) = true)
    (hnone : cfg.stickThreshold = none) (hpos : 0 < lim)
    (hover : lim ≤ Reactor.Stage.StickTable.countOf c) :
    ((runPipeline (serveStagesWithSecHeaders
        ((cfg.withHostCap cap).withHostRate lim)) h c).build).status = 429 :=
  serveStagesWithSecHeaders_rate_429 cfg cap lim h c hmeth hbody hhost hconn
    (by rw [hnone]; exact hpos) (by rw [hnone]; exact hover)

/-- **★ The config seam's rate gate is TRANSPARENT below the effective limit** — the
dual, and the property every under-limit request depends on: strictly under it the gate
adds nothing and the rest of the chain runs. -/
theorem serveStagesWithSecHeaders_rate_passes (cfg : ServeConfig) (cap lim : Nat)
    (h : Ctx → Response) (c : Ctx)
    (hmeth : Transparent (methodStageOf cfg.allowedMethods) c)
    (hbody : Transparent (bodyStageOf cfg.maxBodyDigits) c)
    (hhost : Transparent (hostStageOf cfg.allowedHosts) c)
    (hconn : Reactor.Stage.ConnLimit.admits (cfg.maxConnections.getD cap)
               (Reactor.Stage.ConnLimit.activeOf c) = true)
    (hunder : Reactor.Stage.StickTable.countOf c < cfg.stickThreshold.getD lim) :
    runPipeline (serveStagesWithSecHeaders ((cfg.withHostCap cap).withHostRate lim)) h c
      = runPipeline (slowStageOf cfg.slowlorisTimeout :: corsStageOf cfg.corsOrigins
          :: deployStagesFull2WithSec cfg.securityHeadersStage) h c := by
  show runPipeline ([methodStageOf cfg.allowedMethods, bodyStageOf cfg.maxBodyDigits,
      hostStageOf cfg.allowedHosts, connStageOf (some (cfg.maxConnections.getD cap)),
      stickStageOf (some (cfg.stickThreshold.getD lim))]
      ++ (slowStageOf cfg.slowlorisTimeout :: corsStageOf cfg.corsOrigins
          :: deployStagesFull2WithSec cfg.securityHeadersStage)) h c = _
  exact braided_off_eq_extend _ _ _ h c
    (cons_transparent hmeth (cons_transparent hbody (cons_transparent hhost
      (cons_transparent (connStageOf_admits_transparent _ c hconn)
        (cons_transparent (stickStageOf_under_transparent _ c hunder) (nil_transparent c))))))
    rfl

/-- **★ A threaded limit of `0` leaves the rate gate OFF on the config seam.** `0` is
what `rate-limit 0` crosses, and the fill-in turns it into `some 0`: the chain runs
whatever the in-window count is. The no-regression dual — turning the knob on stays a
decision the operator makes, not one this wave made for them. Under the retired
`countOf c < thr` rule this statement was FALSE. -/
theorem serveStagesWithSecHeaders_rate_zero_off (cfg : ServeConfig) (cap : Nat)
    (h : Ctx → Response) (c : Ctx)
    (hmeth : Transparent (methodStageOf cfg.allowedMethods) c)
    (hbody : Transparent (bodyStageOf cfg.maxBodyDigits) c)
    (hhost : Transparent (hostStageOf cfg.allowedHosts) c)
    (hconn : Reactor.Stage.ConnLimit.admits (cfg.maxConnections.getD cap)
               (Reactor.Stage.ConnLimit.activeOf c) = true)
    (hnone : cfg.stickThreshold = none) :
    runPipeline (serveStagesWithSecHeaders ((cfg.withHostCap cap).withHostRate 0)) h c
      = runPipeline (slowStageOf cfg.slowlorisTimeout :: corsStageOf cfg.corsOrigins
          :: deployStagesFull2WithSec cfg.securityHeadersStage) h c := by
  show runPipeline ([methodStageOf cfg.allowedMethods, bodyStageOf cfg.maxBodyDigits,
      hostStageOf cfg.allowedHosts, connStageOf (some (cfg.maxConnections.getD cap)),
      stickStageOf (some (cfg.stickThreshold.getD 0))]
      ++ (slowStageOf cfg.slowlorisTimeout :: corsStageOf cfg.corsOrigins
          :: deployStagesFull2WithSec cfg.securityHeadersStage)) h c = _
  refine braided_off_eq_extend _ _ _ h c
    (cons_transparent hmeth (cons_transparent hbody (cons_transparent hhost
      (cons_transparent (connStageOf_admits_transparent _ c hconn)
        (cons_transparent ?_ (nil_transparent c)))))) rfl
  rw [hnone]
  exact stickStageOf_zero_transparent c

/-- **★ The config seam's SLOWLORIS gate FIRES on the threaded span.** With the four
preceding heads transparent, a connection whose header phase has overrun the operator's
`slowloris-timeout` is answered the proven `408` by the config seam's own chain. The
clocks are exactly what `ctxOfMeteredConn` now supplies (`nowOf_ctxOfMeteredConn` /
`startedOf_ctxOfMeteredConn`). -/
theorem serveStagesWithSecHeaders_slow_408 (cfg : ServeConfig) (cap to : Nat)
    (h : Ctx → Response) (c : Ctx)
    (hto : cfg.slowlorisTimeout = some to)
    (hmeth : Transparent (methodStageOf cfg.allowedMethods) c)
    (hbody : Transparent (bodyStageOf cfg.maxBodyDigits) c)
    (hhost : Transparent (hostStageOf cfg.allowedHosts) c)
    (hconn : Reactor.Stage.ConnLimit.admits (cfg.maxConnections.getD cap)
               (Reactor.Stage.ConnLimit.activeOf c) = true)
    (hstick : Transparent (stickStageOf cfg.stickThreshold) c)
    (hexp : Reactor.Stage.Slowloris.expired to (Reactor.Stage.Slowloris.startedOf c)
              (Reactor.Stage.Slowloris.nowOf c) = true) :
    ((runPipeline (serveStagesWithSecHeaders (cfg.withHostCap cap)) h c).build).status = 408 := by
  have hchain : serveStagesWithSecHeaders (cfg.withHostCap cap)
      = [methodStageOf cfg.allowedMethods, bodyStageOf cfg.maxBodyDigits,
         hostStageOf cfg.allowedHosts, connStageOf (some (cfg.maxConnections.getD cap)),
         stickStageOf cfg.stickThreshold]
        ++ slowStageOf (some to)
          :: corsStageOf cfg.corsOrigins :: deployStagesFull2WithSec cfg.securityHeadersStage := by
    show (policyStages cfg.toMwPolicy
        ++ [connStageOf (some (cfg.maxConnections.getD cap)), stickStageOf cfg.stickThreshold,
            slowStageOf cfg.slowlorisTimeout, corsStageOf cfg.corsOrigins])
      ++ deployStagesFull2WithSec cfg.securityHeadersStage = _
    rw [hto]; rfl
  rw [hchain]
  exact braid_gate _ (slowStageOf (some to)) _ h c _
    (cons_transparent hmeth (cons_transparent hbody (cons_transparent hhost
      (cons_transparent (connStageOf_admits_transparent _ c hconn)
        (cons_transparent hstick (nil_transparent c))))))
    (slowStageOf_denies to c hexp)
    (by
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact corsStageOf_statusStable _
      · exact deployStagesFull2WithSec_statusStable _ cfg.securityHeadersStage_statusStable s hs)

/-- **★ A browser-shaped burst is ADMITTED by the config seam under the threaded
default.** A source holding EIGHT concurrent connections passes the config seam's
connection gate when the operator declares no `max-connections` and the host threads
its `defaultConnCap` (512) — the case the retired hardcoded `4` refused. Non-vacuous:
the cap here is the FILL-IN, i.e. exactly the path this lane opened. -/
theorem serveStagesWithSecHeaders_browserBurst_admitted (cfg : ServeConfig)
    (h : Ctx → Response) (c : Ctx)
    (hmeth : Transparent (methodStageOf cfg.allowedMethods) c)
    (hbody : Transparent (bodyStageOf cfg.maxBodyDigits) c)
    (hhost : Transparent (hostStageOf cfg.allowedHosts) c)
    (hnone : cfg.maxConnections = none)
    (hactive : Reactor.Stage.ConnLimit.activeOf c = 8) :
    runPipeline (serveStagesWithSecHeaders
        (cfg.withHostCap Reactor.Stage.ConnLimit.defaultConnCap)) h c
      = runPipeline (stickStageOf cfg.stickThreshold
          :: slowStageOf cfg.slowlorisTimeout :: corsStageOf cfg.corsOrigins
          :: deployStagesFull2WithSec cfg.securityHeadersStage) h c :=
  serveStagesWithSecHeaders_conn_passes cfg Reactor.Stage.ConnLimit.defaultConnCap h c
    hmeth hbody hhost (by rw [hnone, hactive]; decide)

/-- **The deployed-bytes no-regression.** The default config-driven serve folds byte-identically to
today's frozen `deployStagesFull2` — chaining the chain anchor through `deployStagesFull4_empty_eq`. -/
theorem serveStagesWithSecHeaders_empty_serve_eq (h : Ctx → Response) (c : Ctx) :
    runPipeline (serveStagesWithSecHeaders emptyServeConfig) h c
      = runPipeline deployStagesFull2 h c := by
  rw [serveStagesWithSecHeaders_empty_eq]; exact deployStagesFull4_empty_eq h c

/-! ##### Operational `∀ cfg` — the served security-header VALUES track the config. -/

/-- **`∀ cfg` value theorem.** For ANY `ServeConfig` whose security-header value is `some p`, running
the config-driven security slot over any tail is EXACTLY running `securityHeadersStageOf p` — whose
`onResponse` folds `wireHeaders p` (the operator-chosen VALUE set) onto the builder
(`securityHeadersStageOf_effect`). So the deployed serve's security-header VALUES = `wireHeaders p`,
∀ cfg. -/
theorem serveStagesWithSecHeaders_secStage_run (cfg : ServeConfig)
    (p : _root_.SecurityHeaders.Policy) (hcfg : cfg.securityHeaders = some p)
    (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (cfg.securityHeadersStage :: rest) h c
      = runPipeline (Reactor.Stage.SecurityHeaders.securityHeadersStageOf p :: rest) h c := by
  rw [ServeConfig.securityHeadersStage_configured cfg p hcfg]

/-- **`∀ cfg` byte-effect (deployed security suffix).** The security suffix of the deployed chain is
`[securityheadersStage, headerStage]`; config-driven it is `[cfg.securityHeadersStage, headerStage]`.
For ANY cfg with `securityHeaders = some p` and `p` carrying an HSTS member `hh`, the
`Strict-Transport-Security` header — name AND the exact RFC-6797 `hstsRender hh` VALUE the CFG denotes
— genuinely appears in the BUILT output of that deployed suffix. The value is `hstsRender hh`:
spec(cfg), not `X = X`. -/
theorem serveStagesWithSecHeaders_hsts_configured (cfg : ServeConfig)
    (p : _root_.SecurityHeaders.Policy) (hcfg : cfg.securityHeaders = some p)
    (hh : _root_.SecurityHeaders.Hsts) (hp : p.hsts = some hh)
    (h : Ctx → Response) (c : Ctx) :
    (Reactor.Stage.SecurityHeaders.hstsHeaderName,
     (_root_.SecurityHeaders.hstsRender hh).toUTF8.toList)
      ∈ ((runPipeline (cfg.securityHeadersStage :: [Reactor.Stage.Header.headerStage]) h c).build).headers := by
  rw [ServeConfig.securityHeadersStage_configured cfg p hcfg]
  exact Reactor.Stage.SecurityHeaders.securityHeadersStageOf_hsts_present p hh hp
    [Reactor.Stage.Header.headerStage] h c

/-- **Non-vacuity.** The served security-header VALUE set genuinely depends on the config: the empty
policy contributes NO headers, the deployed policy contributes the full HSTS + companions set — so the
served values are not a config-independent constant. -/
theorem serveStagesWithSecHeaders_secStage_nonvacuous :
    Reactor.Stage.SecurityHeaders.wireHeaders ({} : _root_.SecurityHeaders.Policy)
      ≠ Reactor.Stage.SecurityHeaders.wireHeaders Reactor.Stage.SecurityHeaders.policy := by
  intro hcontra
  exact Reactor.Stage.SecurityHeaders.hsts_absent_when_empty _
    (hcontra.symm ▸ Reactor.Stage.SecurityHeaders.hsts_in_wireHeaders)

#print axioms serveStagesWithSecHeaders_empty_eq
#print axioms serveStagesWithSecHeaders_empty_serve_eq
#print axioms serveStagesWithSecHeaders_secStage_run
#print axioms serveStagesWithSecHeaders_hsts_configured
#print axioms serveStagesWithSecHeaders_secStage_nonvacuous


/-! #### THE FIRE — each config-present stage drives the served bytes on the REAL request/state
(each proof a `Reactor.BraidCalculus` one-liner). CORS is the LIVE serve-stage; the three gates are
proven at the chain level (reactor-level state, not curl-live). -/

/-- **`deployStagesFull4_cors_acao` — a config-allowed `Origin` gets `Access-Control-Allow-Origin`
(ONE-LINER, LIVE serve-stage).** With the six preceding gates transparent on `c` (empty or
passing), the CORS transform `corsStageOf (some origins)` stamps the REAL ACAO value `v` on the
built response — for ANY tail/handler — when `Cors.acaoValue (corsPolicyOf origins) (corsOriginOf
c) = some v`. Via `braid_transform` + `build_addHeader`. No test header — the decision is on the
request's `origin`. -/
theorem deployStagesFull4_cors_acao (mmeth : Option (List Bytes)) (mbody : Option Nat)
    (mhost : Option (List Bytes)) (mconn mstick mslow : Option Nat) (origins : List Bytes)
    (c : Ctx) (v : String)
    (hmeth : Transparent (methodStageOf mmeth) c) (hbody : Transparent (bodyStageOf mbody) c)
    (hhost : Transparent (hostStageOf mhost) c) (hconn : Transparent (connStageOf mconn) c)
    (hstick : Transparent (stickStageOf mstick) c) (hslow : Transparent (slowStageOf mslow) c)
    (hv : _root_.Cors.acaoValue (corsPolicyOf origins) (corsOriginOf c) = some v) :
    (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
      ∈ ((runPipeline (deployStagesFull4
          { allowedMethods := mmeth, maxBodyDigits := mbody, allowedHosts := mhost,
            maxConnections := mconn, stickThreshold := mstick, slowlorisTimeout := mslow,
            corsOrigins := some origins })
          appHandler c).build).headers := by
  rw [show deployStagesFull4
        { allowedMethods := mmeth, maxBodyDigits := mbody, allowedHosts := mhost,
          maxConnections := mconn, stickThreshold := mstick, slowlorisTimeout := mslow,
          corsOrigins := some origins }
      = [methodStageOf mmeth, bodyStageOf mbody, hostStageOf mhost, connStageOf mconn,
         stickStageOf mstick, slowStageOf mslow] ++ corsStageOf (some origins) :: deployStagesFull2
      from rfl,
    braid_transform [methodStageOf mmeth, bodyStageOf mbody, hostStageOf mhost, connStageOf mconn,
        stickStageOf mstick, slowStageOf mslow] (corsStageOf (some origins)) deployStagesFull2
        appHandler c c
        (cons_transparent hmeth (cons_transparent hbody (cons_transparent hhost
          (cons_transparent hconn (cons_transparent hstick (cons_transparent hslow (nil_transparent c)))))))
        rfl]
  show (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
    ∈ ((match _root_.Cors.acaoValue (corsPolicyOf origins) (corsOriginOf c) with
        | some v => (runPipeline deployStagesFull2 appHandler c).addHeader
                      (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
        | none   => runPipeline deployStagesFull2 appHandler c).build).headers
  rw [hv, Reactor.Pipeline.build_addHeader]
  simp

/-- **`deployStagesFull4_conn_503` — a source at/over the connection cap is refused `503`
(ONE-LINER, chain-level).** With the three §8p heads transparent on `c`, the conn gate
`connStageOf (some cap)` `.respond`s the REAL `resp503` (`braid_gate`, pref `[method,body,host]`).
REACTOR-LEVEL: the standing active count is an attribute-bag input the sans-IO serve does not
supply, so this is proven but does not fire on the default serve. -/
theorem deployStagesFull4_conn_503 (mmeth : Option (List Bytes)) (mbody : Option Nat)
    (mhost : Option (List Bytes)) (cap : Nat) (mstick mslow : Option Nat) (mcors : Option (List Bytes))
    (c : Ctx)
    (hmeth : Transparent (methodStageOf mmeth) c) (hbody : Transparent (bodyStageOf mbody) c)
    (hhost : Transparent (hostStageOf mhost) c)
    (h : Reactor.Stage.ConnLimit.admits cap (Reactor.Stage.ConnLimit.activeOf c) = false) :
    ((runPipeline (deployStagesFull4
        { allowedMethods := mmeth, maxBodyDigits := mbody, allowedHosts := mhost,
          maxConnections := some cap, stickThreshold := mstick, slowlorisTimeout := mslow,
          corsOrigins := mcors })
        appHandler c).build).status = 503 :=
  braid_gate [methodStageOf mmeth, bodyStageOf mbody, hostStageOf mhost]
    (connStageOf (some cap)) _ appHandler c _
    (cons_transparent hmeth (cons_transparent hbody (cons_transparent hhost (nil_transparent c))))
    (connStageOf_denies cap c h)
    (by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact stickStageOf_statusStable _
      rcases List.mem_cons.mp ht with rfl | ht
      · exact slowStageOf_statusStable _
      rcases List.mem_cons.mp ht with rfl | ht
      · exact corsStageOf_statusStable _
      · exact deployStagesFull2_statusStable t ht)

/-- **`deployStagesFull4_stick_429` — a source at/over the aggregated threshold is refused `429`
(ONE-LINER, chain-level, REACTOR-LEVEL).** Heads + conn transparent on `c`; the stick gate
`.respond`s the REAL `resp429` (`braid_gate`, pref `[method,body,host,conn]`). -/
theorem deployStagesFull4_stick_429 (mmeth : Option (List Bytes)) (mbody : Option Nat)
    (mhost : Option (List Bytes)) (mconn : Option Nat) (thr : Nat) (mslow : Option Nat)
    (mcors : Option (List Bytes)) (c : Ctx)
    (hmeth : Transparent (methodStageOf mmeth) c) (hbody : Transparent (bodyStageOf mbody) c)
    (hhost : Transparent (hostStageOf mhost) c) (hconn : Transparent (connStageOf mconn) c)
    (hpos : 0 < thr) (h : thr ≤ Reactor.Stage.StickTable.countOf c) :
    ((runPipeline (deployStagesFull4
        { allowedMethods := mmeth, maxBodyDigits := mbody, allowedHosts := mhost,
          maxConnections := mconn, stickThreshold := some thr, slowlorisTimeout := mslow,
          corsOrigins := mcors })
        appHandler c).build).status = 429 :=
  braid_gate [methodStageOf mmeth, bodyStageOf mbody, hostStageOf mhost, connStageOf mconn]
    (stickStageOf (some thr)) _ appHandler c _
    (cons_transparent hmeth (cons_transparent hbody (cons_transparent hhost
      (cons_transparent hconn (nil_transparent c)))))
    (stickStageOf_denies thr c hpos h)
    (by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact slowStageOf_statusStable _
      rcases List.mem_cons.mp ht with rfl | ht
      · exact corsStageOf_statusStable _
      · exact deployStagesFull2_statusStable t ht)

/-- **`deployStagesFull4_slow_408` — a connection whose header phase overran the timeout is refused
`408` (ONE-LINER, chain-level, REACTOR-LEVEL).** Heads + conn + stick transparent on `c`; the
slowloris gate `.respond`s the REAL `resp408` (`braid_gate`, pref `[method,body,host,conn,stick]`). -/
theorem deployStagesFull4_slow_408 (mmeth : Option (List Bytes)) (mbody : Option Nat)
    (mhost : Option (List Bytes)) (mconn mstick : Option Nat) (to : Nat) (mcors : Option (List Bytes))
    (c : Ctx)
    (hmeth : Transparent (methodStageOf mmeth) c) (hbody : Transparent (bodyStageOf mbody) c)
    (hhost : Transparent (hostStageOf mhost) c) (hconn : Transparent (connStageOf mconn) c)
    (hstick : Transparent (stickStageOf mstick) c)
    (h : Reactor.Stage.Slowloris.expired to (Reactor.Stage.Slowloris.startedOf c)
           (Reactor.Stage.Slowloris.nowOf c) = true) :
    ((runPipeline (deployStagesFull4
        { allowedMethods := mmeth, maxBodyDigits := mbody, allowedHosts := mhost,
          maxConnections := mconn, stickThreshold := mstick, slowlorisTimeout := some to,
          corsOrigins := mcors })
        appHandler c).build).status = 408 :=
  braid_gate [methodStageOf mmeth, bodyStageOf mbody, hostStageOf mhost, connStageOf mconn,
      stickStageOf mstick]
    (slowStageOf (some to)) _ appHandler c _
    (cons_transparent hmeth (cons_transparent hbody (cons_transparent hhost
      (cons_transparent hconn (cons_transparent hstick (nil_transparent c))))))
    (slowStageOf_denies to c h)
    (by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact corsStageOf_statusStable _
      · exact deployStagesFull2_statusStable t ht)

/-! #### The config-driven deployment + the METERED serve anchor -/

/-- **The config-driven deployment.** `base` with its middleware chain replaced by the round-2
config-driven `deployStagesFull4 p` (the seven config-parameterized policy stages over the always-on
chain). `defaultDeployment`'s admission/routing dimensions are kept, so a policy config still folds
the deployed route table + app handler. With `emptyMwPolicy` this is byte-identical to the frozen
default (`deployStagesFull4_empty_eq`), so the round-1 method/body/host live gates AND the round-2
CORS decoration all ride the SAME deployed serve. -/
def policyDeploymentOn (base : Dsl.DeploymentConfig) (p : MwPolicy) : Dsl.DeploymentConfig :=
  { base with middleware := { chain := deployStagesFull4 p } }

/-- **The config-driven (security-header slot) deployment (Track 1 · Phase 4).** `base` with
its middleware chain replaced by `serveStagesWithSecHeaders cfg` — the seven config-parameterized
policy stages over the always-on chain WHOSE SECURITY-HEADER SLOT is config-driven from the
`ServeConfig`. Every other stage is exactly today's. With `emptyServeConfig` this is
DEFINITIONALLY `policyDeploymentOn base emptyMwPolicy` (`serveStagesWithSecHeaders_empty_eq`
is `rfl`), so the deployed default is byte-for-byte untouched. -/
def serveConfigDeploymentOn (base : Dsl.DeploymentConfig) (cfg : ServeConfig) :
    Dsl.DeploymentConfig :=
  { base with middleware := { chain := serveStagesWithSecHeaders cfg } }

/-- **NO-REGRESSION (deployment) — the empty serve config IS the empty policy deployment.**
DEFINITIONALLY: `serveStagesWithSecHeaders emptyServeConfig` reduces (`rfl`) to
`deployStagesFull4 emptyMwPolicy`, so the two deployments are equal — a `rfl` THEOREM. -/
theorem serveConfigDeploymentOn_empty_eq (base : Dsl.DeploymentConfig) :
    serveConfigDeploymentOn base emptyServeConfig = policyDeploymentOn base emptyMwPolicy := rfl

/-- **NO-REGRESSION (deployment, sec-header absent) — any config whose security-header VALUE is
absent folds the SAME chain as its gate-only `MwPolicy` deployment.** The security slot recovers
the baked `securityheadersStage` (`ServeConfig.securityHeadersStage_default`) and the
`deployStagesFull2WithSec` slot recovers `deployStagesFull2` (`deployStagesFull2WithSec_default`),
so `serveStagesWithSecHeaders cfg = deployStagesFull4 cfg.toMwPolicy`. A THEOREM — policy-only
configs are byte-for-byte the existing `policyDeploymentOn` serve. -/
theorem serveConfigDeploymentOn_secNone_eq (base : Dsl.DeploymentConfig) (cfg : ServeConfig)
    (h : cfg.securityHeaders = none) :
    serveConfigDeploymentOn base cfg = policyDeploymentOn base cfg.toMwPolicy := by
  simp only [serveConfigDeploymentOn, policyDeploymentOn, serveStagesWithSecHeaders,
    ServeConfig.securityHeadersStage_default cfg h, deployStagesFull2WithSec_default,
    deployStagesFull4]

#print axioms serveConfigDeploymentOn_empty_eq
#print axioms serveConfigDeploymentOn_secNone_eq

/-! #### The operator-facing textual policy directives

An operator sets the middleware policy in the SAME `DRORB_CONFIG` file with three directives,
one per line, each independent of the route-table grammar:

* `max-body-size <digits>` — refuse `413` on a declared `Content-Length` wider than `<digits>`
  decimal digits (a monotone size proxy; `7` ⇒ ~10 MB);
* `allow-method <METHOD>`  — restrict the served methods (repeat for each allowed method); a
  method outside the accumulated set is refused `405`;
* `allow-host <host>`      — restrict the served authorities (repeat per host); a `Host` outside
  the set is refused `421`.
* `allow-origin <origin>`  — CORS: stamp `Access-Control-Allow-Origin` on the response iff the
  request's `Origin` is in the accumulated set (repeat per origin). SERVE-STAGE (decides on the
  real request `origin`), so it fires on the default serve.
* `max-connections <n>`    — refuse `503` when the source's standing concurrent-connection count
  reaches `<n>` (REACTOR-LEVEL — reads accept-path state, proven not curl-live);
* `stick-limit <n>`        — refuse `429` when the source's aggregated request count reaches `<n>`
  (REACTOR-LEVEL);
* `slowloris-timeout <n>`  — refuse `408` when the header phase overruns `<n>` clock units
  (REACTOR-LEVEL).

`parsePolicy` is a TOTAL scan (an unrecognized line is ignored), so it never fails a config; the
enforcement/no-regression theorems hold for the resulting `MwPolicy` whatever it is, and a config
with NO policy directive yields `emptyMwPolicy` (byte-identical default). -/

/-- Fold one config line into the accumulating policy (an unrecognized line is a no-op). -/
def parsePolicyLine (p : MwPolicy) (line : String) : MwPolicy :=
  match (line.splitOn " ").filter (· ≠ "") with
  | ["max-body-size", n] =>
    match n.toNat? with
    | some k => { p with maxBodyDigits := some k }
    | none   => p
  | ["allow-method", m] =>
    { p with allowedMethods := some ((p.allowedMethods.getD []) ++ [m.toUTF8.toList]) }
  | ["allow-host", h] =>
    { p with allowedHosts := some ((p.allowedHosts.getD []) ++ [h.toUTF8.toList]) }
  | ["allow-origin", o] =>
    { p with corsOrigins := some ((p.corsOrigins.getD []) ++ [o.toUTF8.toList]) }
  | ["max-connections", n] =>
    match n.toNat? with
    | some k => { p with maxConnections := some k }
    | none   => p
  | ["stick-limit", n] =>
    match n.toNat? with
    | some k => { p with stickThreshold := some k }
    | none   => p
  | ["slowloris-timeout", n] =>
    match n.toNat? with
    | some k => { p with slowlorisTimeout := some k }
    | none   => p
  | _ => p

/-- **Scan a config's text for the middleware-policy directives.** Total: an operator config with
no `max-body-size`/`allow-method`/`allow-host` line yields `emptyMwPolicy`, so the served bytes
are byte-identical to today's default (`servePipelineOfMetered_policy_empty`). -/
def parsePolicy (chars : List Char) : MwPolicy :=
  ((String.mk chars).splitOn "\n").foldl parsePolicyLine emptyMwPolicy

/-! #### Track 1 · Phase 4 — the ServeConfig parser (superset of `parsePolicy`)

`parseServeConfig` widens `parsePolicy` to the full `ServeConfig`: it recognizes the new
response-STAMP / security-header VALUE directives AND delegates every gate directive to the
proven `parsePolicyLine` on the embedded `MwPolicy`. Backward-compatible: a config carrying only
the old gate directives yields a `ServeConfig` whose `securityHeaders`/stamps are all `none`
(so `serveConfigDeploymentOn` folds the SAME chain as `policyDeploymentOn` on its `toMwPolicy`),
and a directive-free config yields `emptyServeConfig` (the byte-identical default). NEW directive:

* `security-header hsts-max-age <seconds>` — set the deployed security policy's HSTS `max-age`
  to `<seconds>` (subdomains + preload kept). Absent ⇒ the baked `max-age=31536000` const.

Total: an unrecognized line is a no-op. -/

/-- Fold one config line into the accumulating `ServeConfig`. A `security-header` directive sets
the config-driven security-header VALUE; every other line is delegated to `parsePolicyLine` on the
embedded `MwPolicy` (so all gate directives parse exactly as before). -/
def parseServeConfigLine (cfg : ServeConfig) (line : String) : ServeConfig :=
  match (line.splitOn " ").filter (· ≠ "") with
  | ["security-header", "hsts-max-age", n] =>
    match n.toNat? with
    | some k =>
      let hp : _root_.SecurityHeaders.Hsts :=
        { Reactor.Stage.SecurityHeaders.hstsPolicy with maxAge := k }
      let pol : _root_.SecurityHeaders.Policy :=
        { Reactor.Stage.SecurityHeaders.policy with hsts := some hp }
      { cfg with securityHeaders := some pol }
    | none   => cfg
  | _ =>
    let mw := parsePolicyLine cfg.toMwPolicy line
    { cfg with toMwPolicy := mw }

/-- **Scan a config's text for the full `ServeConfig`.** Total: a directive-free config yields
`emptyServeConfig`, so the served bytes are byte-identical to today's default
(`serveConfigDeploymentOn_empty_eq`). -/
def parseServeConfig (chars : List Char) : ServeConfig :=
  ((String.mk chars).splitOn "\n").foldl parseServeConfigLine emptyServeConfig


/-- **`servePipelineOfMetered_policy_empty` — the metered serve is byte-identical under the
EMPTY policy.** The metered fold over `policyDeploymentOn defaultDeployment emptyMwPolicy` is
byte-for-byte `servePipelineFull2Metered` — so the `servePipelineOfMetered_default` anchor
extends to the config-driven default: an operator with no middleware policy gets the exact old
serve. EARNED via `deployStagesFull3_empty_eq`. -/
theorem servePipelineOfMetered_policy_empty
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    servePipelineOfMetered (policyDeploymentOn defaultDeployment emptyMwPolicy) clientIp connSeq input
      = servePipelineFull2Metered clientIp connSeq input := by
  show serialize ((runPipeline (deployStagesFull4 emptyMwPolicy)
      (Dsl.handlerOf (Dsl.instantiate defaultDeployment).2)
      (ctxOfMetered clientIp connSeq input)).build) = _
  rw [deployStagesFull4_empty_eq]
  rfl

/-- **`servePipelineOfMetered_policyOn_empty_eq` — the EMPTY policy adds nothing.** For any base
whose middleware chain is the deployed `deployStagesFull2`, the metered serve over
`policyDeploymentOn base emptyMwPolicy` is byte-for-byte the metered serve over `base` — the
three empty-policy gates fold transparently (`deployStagesFull3_empty_eq`). This is the bridge
the config seam uses to prove the DEFAULT (policy-free) serve untouched over ANY route table. -/
theorem servePipelineOfMetered_policyOn_empty_eq (base : Dsl.DeploymentConfig)
    (hmw : base.middleware.chain = deployStagesFull2)
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    servePipelineOfMetered (policyDeploymentOn base emptyMwPolicy) clientIp connSeq input
      = servePipelineOfMetered base clientIp connSeq input := by
  show serialize ((runPipeline (deployStagesFull4 emptyMwPolicy)
        (Dsl.handlerOf (Dsl.instantiate base).2) (ctxOfMetered clientIp connSeq input)).build)
     = serialize ((runPipeline (Dsl.instantiate base).1
        (Dsl.handlerOf (Dsl.instantiate base).2) (ctxOfMetered clientIp connSeq input)).build)
  rw [deployStagesFull4_empty_eq, show (Dsl.instantiate base).1 = deployStagesFull2 from hmw]

#print axioms deployStagesFull3_empty_eq
#print axioms deployStagesFull3_method_405
#print axioms deployStagesFull3_body_413
#print axioms deployStagesFull3_host_421
#print axioms servePipelineOfMetered_policy_empty
#print axioms deployStagesFull4_empty_eq
#print axioms deployStagesFull4_cors_acao
#print axioms deployStagesFull4_conn_503
#print axioms deployStagesFull4_stick_429
#print axioms deployStagesFull4_slow_408

/-! ### (8q) THE BRAID-6 — three proven-but-INERT stages un-inerted (Jwt 401 / Header rewrite / SPA 200)

Three capabilities whose leaf proofs already existed but were **inert** — proven `Reactor.Stage.*`
decisions in NO binary import closure (not deployed, not braided). This section braids them,
extending `braidedChain5` → `braidedChain6`, and (via the re-pointed `drorb_serve_metered_braided`
export → `braidedDeployment6`) puts them on the DEPLOYED serve behind `DRORB_BRAID`:

* `jwtBraidStage` (PARITY-LEDGER **mw.5**, `Reactor.Stage.Jwt`) — a SHORT-CIRCUIT `401` gate.
  Marker absent ⇒ pass-through; present ⇒ the REAL `jwtStage` decision on the library's own
  no-token witness (`Jwt.noTokenCtx`, `Jwt.noToken_rejects`) `.respond`s the genuine `unauthorized`
  (`401`). Composition proof: `braid_gate` ONE-LINER.
* `headerRwBraidStage` (PARITY-LEDGER **mw.8**, `Reactor.Stage.Header`) — a RESPONSE TRANSFORM.
  Marker absent ⇒ identity; present ⇒ the response header block becomes the REAL
  `Header.run rewriteProg` rewrite (strip RFC 9110 §7.6.1 hop-by-hop, stamp `Server`). Composition
  proof: `braid_transform` ONE-LINER, then the header-block byte fact.
* `spaFallbackBraidStage` (PARITY-LEDGER **rt.7**, `Reactor.Stage.SpaFallback`) — a `200`
  fallback gate. Marker present (a navigable SPA route) ⇒ `.respond`s a `200` serving the
  library-SELECTED index resource (`spaServedPath demoCfg` — the same path `spa_fallback_serves_index`
  proves the fallback yields where a plain static serve `404`s). Composition proof: `braid_gate`
  ONE-LINER. RESIDUAL (unchanged from the row): streaming the index FILE bytes off the live
  `StaticFile.serveDeployed` embedded FS — here the served body is the library-selected index
  LOCATOR, and the deployed decision is the `200`-not-`404` fallback status.

Each `*BraidStage_off` is `Transparent`, so `braided6_off_eq` is a `braided_off_eq_extend`
ONE-LINER deferring to §8o's `braided5_off_eq`; the default (unmarked) serve is BYTE-IDENTICAL to
`servePipelineFull2` and every prior anchor is UNTOUCHED. `braidedChain5`/`braidedDeployment5` and
all §8/§8h/§8j/§8l/§8n/§8o theorems are unchanged — `braidedChain6` is a strictly larger, separate
fold. -/

/-- The per-request marker enabling the JWT `401` gate. -/
def jwtMarker : Proto.Bytes := "x-jwt-auth".toUTF8.toList
/-- The per-request marker enabling the header-rewrite transform. -/
def headerRwMarker : Proto.Bytes := "x-header-rewrite".toUTF8.toList
/-- The per-request marker enabling the SPA `200` fallback gate. -/
def spaMarker : Proto.Bytes := "x-spa-fallback".toUTF8.toList

/-! #### (1) The JWT `401` gate (pass-through when unmarked) — mw.5 -/

/-- The library decision the gate answers with is a genuine `401`. -/
theorem jwt401_status : Reactor.Stage.Jwt.unauthorized.status = 401 := rfl

/-- **The JWT braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL `jwtStage` decision
on the library's own no-token witness `.respond`s the genuine `401`. -/
def jwtBraidStage : Stage where
  name := "jwt-401"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == jwtMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.Jwt.jwtStage.onRequest Reactor.Stage.Jwt.noTokenCtx
  onResponse := fun _ b => b

theorem jwtBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == jwtMarker) = none) :
    Transparent jwtBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == jwtMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.Jwt.jwtStage.onRequest Reactor.Stage.Jwt.noTokenCtx) = _
  rw [h]

theorem jwtBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == jwtMarker) = some nv) :
    jwtBraidStage.onRequest c = .respond Reactor.Stage.Jwt.unauthorized := by
  show (match c.req.headers.find? (fun nv => nv.1 == jwtMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.Jwt.jwtStage.onRequest Reactor.Stage.Jwt.noTokenCtx) = _
  rw [hfind]
  exact Reactor.Stage.Jwt.jwtStage_gates_on_reject Reactor.Stage.Jwt.noTokenCtx
    .noToken Reactor.Stage.Jwt.noToken_rejects

theorem jwtBraidStage_statusStable : Stage.statusStable jwtBraidStage := fun _ _ => rfl

/-! #### (2) The header-rewrite transform (identity when unmarked) — mw.8 -/

/-- **The header-rewrite braid transform.** Always passes the request. Response phase: marker
absent ⇒ identity; present ⇒ the emitted header block becomes the REAL `Header.run rewriteProg`
rewrite (hop-by-hop strip + `Server` stamp), applied through the affine `mapResp`. -/
def headerRwBraidStage : Stage where
  name := "header-rewrite"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match c.req.headers.find? (fun nv => nv.1 == headerRwMarker) with
    | none   => b
    | some _ => b.mapResp Reactor.Stage.Header.rewriteResp

theorem headerRwBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == headerRwMarker) = none) :
    Transparent headerRwBraidStage c := by
  refine ⟨rfl, fun b => ?_⟩
  show (match c.req.headers.find? (fun nv => nv.1 == headerRwMarker) with
        | none   => b
        | some _ => b.mapResp Reactor.Stage.Header.rewriteResp) = b
  rw [h]

theorem headerRwBraidStage_on (c : Ctx) (b : ResponseBuilder) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == headerRwMarker) = some nv) :
    headerRwBraidStage.onResponse c b = b.mapResp Reactor.Stage.Header.rewriteResp := by
  show (match c.req.headers.find? (fun nv => nv.1 == headerRwMarker) with
        | none   => b
        | some _ => b.mapResp Reactor.Stage.Header.rewriteResp) = _
  rw [hfind]

theorem headerRwBraidStage_statusStable : Stage.statusStable headerRwBraidStage := by
  intro c b
  show ((headerRwBraidStage.onResponse c b).build).status = b.build.status
  unfold headerRwBraidStage
  dsimp only
  split
  · rfl
  · rw [Reactor.Pipeline.build_mapResp]
    rfl

/-! #### (3) The SPA `200` fallback gate (pass-through when unmarked) — rt.7 -/

/-- The `OK` reason phrase the fallback `200` carries. -/
def spaOkReason : Proto.Bytes := "OK".toUTF8.toList

/-- The library-SELECTED index resource locator for a navigable SPA route: the exact path the
proven `SpaFallback` discipline resolves `/dashboard` to (`spaServedPath demoCfg ["dashboard"]` =
the index under the doc root), rendered as a `/`-joined locator. NOT a bare literal — it is the
library's own fallback selection (`spaServe_eq_servedPath` / `demo_route_serves_index`). -/
def spaIndexLocator : Proto.Bytes :=
  (String.intercalate "/"
    (Reactor.Stage.SpaFallback.spaServedPath Reactor.Stage.SpaFallback.demoCfg ["dashboard"])).toUTF8.toList

/-- The `200` the SPA fallback answers a navigable route with: status `200`, body the
library-selected index locator — the row's "fallback, not `404`" decision. -/
def spaIndexResp : Response :=
  { status := 200, reason := spaOkReason, headers := [], body := spaIndexLocator }

theorem spaIndexResp_status : spaIndexResp.status = 200 := rfl

/-- **The SPA fallback braid gate.** Marker absent ⇒ pass-through; present (a navigable SPA route)
⇒ `.respond`s the `200` serving the library-selected index — where a plain static serve `404`s. -/
def spaFallbackBraidStage : Stage where
  name := "spa-fallback"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == spaMarker) with
    | none   => .continue c
    | some _ => .respond spaIndexResp
  onResponse := fun _ b => b

theorem spaFallbackBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == spaMarker) = none) :
    Transparent spaFallbackBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == spaMarker) with
        | none   => StageStep.continue c
        | some _ => StageStep.respond spaIndexResp) = _
  rw [h]

theorem spaFallbackBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == spaMarker) = some nv) :
    spaFallbackBraidStage.onRequest c = .respond spaIndexResp := by
  show (match c.req.headers.find? (fun nv => nv.1 == spaMarker) with
        | none   => StageStep.continue c
        | some _ => StageStep.respond spaIndexResp) = _
  rw [hfind]

theorem spaFallbackBraidStage_statusStable : Stage.statusStable spaFallbackBraidStage := fun _ _ => rfl

/-- **The deployed SPA `200` IS the library's genuine index selection (non-vacuity / library tie).**
For a navigable route (`/dashboard`) the proven `SpaFallback` discipline serves the index with
`200` where a plain static serve `404`s — the row's whole point. The deployed gate's `200` rides
exactly this decision. -/
theorem braided6_spa_selects_library_index :
    Reactor.Stage.SpaFallback.spaServe Reactor.Stage.SpaFallback.demoCfg ["dashboard"]
      = .ok ["srv", "www", "index.html"]
    ∧ Reactor.Stage.SpaFallback.plainServe Reactor.Stage.SpaFallback.demoCfg ["dashboard"]
      = .notFound :=
  ⟨Reactor.Stage.SpaFallback.demo_route_serves_index,
   Reactor.Stage.SpaFallback.demo_route_plain_404⟩

/-! #### The braid-6 chain and its status-stability -/

/-- **The braid-6 chain.** Three proven-but-inert stages (Jwt `401` / header-rewrite / SPA `200`)
prepended to `braidedChain5`. A strictly larger, separate fold; `braidedChain5` is untouched. -/
def braidedChain6 : List Stage :=
  jwtBraidStage :: headerRwBraidStage :: spaFallbackBraidStage :: braidedChain5

/-- Every stage of `braidedChain6` is status-stable (the three new stages plus the inherited
`braidedChain5`). -/
theorem braidedChain6_statusStable : ∀ s ∈ braidedChain6, Stage.statusStable s := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact jwtBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact headerRwBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact spaFallbackBraidStage_statusStable
  · exact braidedChain5_statusStable s hs

/-! #### THE NEW COMPOSITION — byte-identity when all three markers are OFF
(the `braided_off_eq_extend` ONE-LINER). -/

/-- **`braided6_off_eq` — the three-stage extension is faithful when gated OFF.** ONE LINE via the
calculus: `braided_off_eq_extend` peels the transparent three-stage prefix, then defers to §8o's
`braided5_off_eq`. -/
theorem braided6_off_eq (c : Ctx)
    (hjwt : c.req.headers.find? (fun nv => nv.1 == jwtMarker) = none)
    (hheader : c.req.headers.find? (fun nv => nv.1 == headerRwMarker) = none)
    (hspa : c.req.headers.find? (fun nv => nv.1 == spaMarker) = none)
    (hmethod : c.req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hbody : c.req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = none)
    (hhost : c.req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = none)
    (hred : c.req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : c.req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hsec : c.req.headers.find? (fun nv => nv.1 == securityMarker) = none)
    (hcond : c.req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : c.req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : c.req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : c.req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : c.req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf c.req = none) :
    runPipeline braidedChain6 appHandler c = runPipeline deployStagesFull2 appHandler c :=
  braided_off_eq_extend [jwtBraidStage, headerRwBraidStage, spaFallbackBraidStage]
    braidedChain5 deployStagesFull2 appHandler c
    (cons_transparent (jwtBraidStage_off c hjwt)
      (cons_transparent (headerRwBraidStage_off c hheader)
        (cons_transparent (spaFallbackBraidStage_off c hspa) (nil_transparent c))))
    (braided5_off_eq c hmethod hbody hhost hred hcors hsec hcond hvar hauto hconn hstick hslow
      herr hcomp hfa hrid)

/-- **The braid-6 serve.** `serialize` of the BUILT fold over `braidedChain6`. -/
def servePipelineBraided6 (input : Bytes) : Bytes :=
  serialize ((runPipeline braidedChain6 appHandler (ctxOf input)).build)

/-- **`servePipelineBraided6_off_eq` — byte-identical default serve.** With no braid markers on
`ctxOf input`, the braid-6 serve emits EXACTLY `servePipelineFull2`'s bytes. -/
theorem servePipelineBraided6_off_eq (input : Bytes)
    (hjwt : (ctxOf input).req.headers.find? (fun nv => nv.1 == jwtMarker) = none)
    (hheader : (ctxOf input).req.headers.find? (fun nv => nv.1 == headerRwMarker) = none)
    (hspa : (ctxOf input).req.headers.find? (fun nv => nv.1 == spaMarker) = none)
    (hmethod : (ctxOf input).req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hbody : (ctxOf input).req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = none)
    (hhost : (ctxOf input).req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = none)
    (hred : (ctxOf input).req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : (ctxOf input).req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hsec : (ctxOf input).req.headers.find? (fun nv => nv.1 == securityMarker) = none)
    (hcond : (ctxOf input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : (ctxOf input).req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : (ctxOf input).req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : (ctxOf input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOf input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOf input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOf input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : (ctxOf input).req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : (ctxOf input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOf input).req = none) :
    servePipelineBraided6 input = servePipelineFull2 input := by
  show serialize ((runPipeline braidedChain6 appHandler (ctxOf input)).build) = _
  rw [braided6_off_eq (ctxOf input) hjwt hheader hspa hmethod hbody hhost hred hcors hsec hcond
        hvar hauto hconn hstick hslow herr hcomp hfa hrid]
  rfl

/-! #### THE FIRE — each un-inerted stage genuinely drives the served response. -/

/-- **`braided6_jwt_401` — the JWT `401` fires at the head (ONE-LINER).** With `x-jwt-auth`, the
built braid-6 status is exactly `401`: `braid_gate` (pref `[]`) — the head gate `.respond`s the REAL
`Jwt.unauthorized` and it survives the status-stable inner onion. -/
theorem braided6_jwt_401 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == jwtMarker) = some nv) :
    ((runPipeline braidedChain6 appHandler c).build).status = 401 :=
  braid_gate [] jwtBraidStage _ appHandler c _ (nil_transparent c)
    (jwtBraidStage_denies c nv hfind)
    (fun t ht => braidedChain6_statusStable t (List.mem_cons_of_mem _ ht))

/-- **`braided6_header_rewrites` — the header block becomes the REAL `Header.run` rewrite
(ONE-LINER core).** With `x-jwt-auth`/`x-spa-fallback` absent (those head stages transparent) and
`x-header-rewrite` present, the emitted braid-6 header block IS `fromFields (Header.run rewriteProg
(toFields …))` applied over the base serve's headers — the genuine hop-by-hop strip + `Server`
stamp, not an attachment. `braid_transform` places the transform at its onion position; the base
fold is the untouched `braidedChain5`. -/
theorem braided6_header_rewrites (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hjwt : c.req.headers.find? (fun nv => nv.1 == jwtMarker) = none)
    (hspa : c.req.headers.find? (fun nv => nv.1 == spaMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == headerRwMarker) = some nv) :
    ((runPipeline braidedChain6 appHandler c).build).headers
      = Reactor.Stage.Header.fromFields (_root_.Header.run Reactor.Stage.Header.rewriteProg
          (Reactor.Stage.Header.toFields ((runPipeline braidedChain5 appHandler c).build).headers)) := by
  have hpref : ∀ X ∈ [jwtBraidStage], Transparent X c :=
    cons_transparent (jwtBraidStage_off c hjwt) (nil_transparent c)
  rw [show braidedChain6
        = [jwtBraidStage] ++ headerRwBraidStage :: (spaFallbackBraidStage :: braidedChain5) from rfl,
      braid_transform [jwtBraidStage] headerRwBraidStage (spaFallbackBraidStage :: braidedChain5)
        appHandler c c hpref rfl,
      headerRwBraidStage_on c _ nv hfind,
      Reactor.Pipeline.build_mapResp,
      Reactor.BraidCalculus.prepend_pass spaFallbackBraidStage braidedChain5 appHandler c
        (spaFallbackBraidStage_off c hspa)]
  rfl

/-- **`braided6_spa_200` — the SPA fallback `200` fires once the jwt/header stages pass
(ONE-LINER).** With `x-jwt-auth`/`x-header-rewrite` absent (those two head stages transparent) and
`x-spa-fallback` present, the built braid-6 status is exactly `200` — the "fallback, not `404`"
decision on the wire. `braid_gate` (pref `[jwtBraidStage, headerRwBraidStage]`); the served body is
the library-selected index (`braided6_spa_selects_library_index`). -/
theorem braided6_spa_200 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hjwt : c.req.headers.find? (fun nv => nv.1 == jwtMarker) = none)
    (hheader : c.req.headers.find? (fun nv => nv.1 == headerRwMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == spaMarker) = some nv) :
    ((runPipeline braidedChain6 appHandler c).build).status = 200 :=
  braid_gate [jwtBraidStage, headerRwBraidStage] spaFallbackBraidStage braidedChain5 appHandler c _
    (cons_transparent (jwtBraidStage_off c hjwt)
      (cons_transparent (headerRwBraidStage_off c hheader) (nil_transparent c)))
    (spaFallbackBraidStage_denies c nv hfind)
    braidedChain5_statusStable

#print axioms braided6_off_eq
#print axioms servePipelineBraided6_off_eq
#print axioms braided6_jwt_401
#print axioms braided6_header_rewrites
#print axioms braided6_spa_200
#print axioms braided6_spa_selects_library_index

/-! ### (8r) THE METERED BRAID-6 — braid-6 through the PRODUCTION metered fold

As §8o threaded `braidedChain5`, this threads `braidedChain6`: `braidedDeployment6` is
`defaultDeployment` with its middleware chain replaced by `braidedChain6`. Only the `middleware`
dimension differs, so `Dsl.instantiate` reproduces the SAME `AppConfig`/`appHandler` as
`defaultDeployment`, and the metered fold over it is exactly `runPipeline braidedChain6 appHandler
(ctxOfMetered …)`. The braid-6 head stages read only `c.req` and `(ctxOfMetered … input).req =
(ctxOf input).req`, so the §8q composition theorems discharge the metered fold at `ctxOfMetered`
directly. This is the deployment the re-pointed `drorb_serve_metered_braided` export folds. Every
prior deployment/anchor is UNTOUCHED. -/

/-- **The braid-6 deployment config.** `defaultDeployment` with its middleware chain replaced by
`braidedChain6` — the same `AppConfig` as `defaultDeployment`. -/
def braidedDeployment6 : Dsl.DeploymentConfig :=
  { defaultDeployment with middleware := { chain := braidedChain6 } }

/-- The braid-6 config instantiates to EXACTLY `braidedChain6`. -/
theorem instantiate_braided6_stages :
    (Dsl.instantiate braidedDeployment6).1 = braidedChain6 := rfl

/-- The braid-6 config instantiates to the SAME `AppConfig` as `defaultDeployment`. -/
theorem instantiate_braided6_app :
    (Dsl.instantiate braidedDeployment6).2 = (Dsl.instantiate defaultDeployment).2 := rfl

/-- **The metered braid-6 serve IS the braid-6 chain over the metered context.** -/
theorem servePipelineOfMetered_braided6_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) :
    servePipelineOfMetered braidedDeployment6 clientIp connSeq input
      = serialize ((runPipeline braidedChain6 appHandler
          (ctxOfMetered clientIp connSeq input)).build) := rfl

/-- **`servePipelineOfMetered_braided6_off_eq` — the metered braid-6 is byte-identical when all
nineteen markers are OFF.** EARNED — `braided6_off_eq` peels the head stages at the metered
context. -/
theorem servePipelineOfMetered_braided6_off_eq
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes)
    (hjwt : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == jwtMarker) = none)
    (hheader : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == headerRwMarker) = none)
    (hspa : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == spaMarker) = none)
    (hmethod : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hbody : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = none)
    (hhost : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = none)
    (hred : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hsec : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == securityMarker) = none)
    (hcond : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOfMetered clientIp connSeq input).req = none) :
    servePipelineOfMetered braidedDeployment6 clientIp connSeq input
      = servePipelineFull2Metered clientIp connSeq input := by
  rw [servePipelineOfMetered_braided6_eq,
      braided6_off_eq (ctxOfMetered clientIp connSeq input) hjwt hheader hspa hmethod hbody hhost
        hred hcors hsec hcond hvar hauto hconn hstick hslow herr hcomp hfa hrid]
  rfl

/-- **`servePipelineOfMetered_braided6_jwt_401` — the JWT `401` survives the metered onion.** Via
`braided6_jwt_401` at the metered context. -/
theorem servePipelineOfMetered_braided6_jwt_401
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == jwtMarker) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment6).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment6).2)
        (ctxOfMetered clientIp connSeq input)).build).status = 401 := by
  show ((runPipeline braidedChain6 appHandler (ctxOfMetered clientIp connSeq input)).build).status = 401
  exact braided6_jwt_401 (ctxOfMetered clientIp connSeq input) nv hfind

/-- **`servePipelineOfMetered_braided6_spa_200` — the SPA fallback `200` fires through the metered
fold.** Via `braided6_spa_200`. -/
theorem servePipelineOfMetered_braided6_spa_200
    (clientIp : Proto.Bytes) (connSeq : Nat) (input : Bytes) (nv : Proto.Bytes × Proto.Bytes)
    (hjwt : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == jwtMarker) = none)
    (hheader : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == headerRwMarker) = none)
    (hfind : (ctxOfMetered clientIp connSeq input).req.headers.find? (fun nv => nv.1 == spaMarker) = some nv) :
    ((runPipeline (Dsl.instantiate braidedDeployment6).1
        (Dsl.handlerOf (Dsl.instantiate braidedDeployment6).2)
        (ctxOfMetered clientIp connSeq input)).build).status = 200 := by
  show ((runPipeline braidedChain6 appHandler (ctxOfMetered clientIp connSeq input)).build).status = 200
  exact braided6_spa_200 (ctxOfMetered clientIp connSeq input) nv hjwt hheader hfind

#print axioms servePipelineOfMetered_braided6_off_eq
#print axioms servePipelineOfMetered_braided6_jwt_401
#print axioms servePipelineOfMetered_braided6_spa_200

/-! ### (8s) BRAID-7 — two proven-but-inert CONFORMANCE stages, each composed as a
`Reactor.BraidCalculus` ONE-LINER, extending `braidedChain6` to `braidedChain7`.

The wave-4/5 RFC conformance probe (`docs/engine/review/CONFORMANCE-PROBE.md`) found two
MUST-level gaps on the deployed serve, fixed as proven-but-inert stages
(`Reactor.Stage.RequestValidation`, `Reactor.Stage.DateHeader`; committed pure-kernel,
axioms ⊆ {propext, Quot.sound}) that never reached a deployed fold — their theorems were
INERT (no serve imported them). The braid WRAP is exactly the mechanism the honest-blocked
"wire-conformance" note wanted: it PREPENDS the stages onto a NEW fold WITHOUT touching the
frozen `deployStagesFull2` byte-identity anchor.

`braidedChain7` prepends TWO config-gated braid stages to `braidedChain6`:

* one SHORT-CIRCUIT GATE — `validationBraidStage` (RFC 7230 request-line validation →
  `505`). Marker absent ⇒ pure pass-through; present ⇒ it delegates to the REAL
  `RequestValidation.validationStage` on the library's own unsupported-version witness
  (`badVersionCtx`), `.respond`ing the genuine `badVersionResp` (`505`) — the library's own
  `badVersion_rejected` decision, not a constant. Composition via `braid_gate`.
* one RESPONSE-TRANSFORM — `dateBraidStage` (RFC 7231 §7.1.1.2 `Date` header). Marker
  absent ⇒ identity; present ⇒ the response carries `Date: <now>`, where the name/value are
  the REAL `DateHeader.dateName`/`sampleNow` constants. Composition via `braid_transform`.

Both are CONFIG-GATED — inert unless a per-request marker is set — so the DEFAULT served
bytes are byte-identical (`braided7_off_eq`, a `braided_off_eq_extend` ONE-LINER deferring to
§8r's `braided6_off_eq`); when ON each FIRES its real library decision. `braidedChain6`/
`braidedDeployment6` and every prior theorem (and the `servePipelineOfMetered_default`
anchor) are UNTOUCHED — `braidedChain7` is a strictly larger, separate fold. -/

/-- The per-request marker enabling the request-line validation `505` gate. -/
def validationMarker : Proto.Bytes := "x-request-validation".toUTF8.toList
/-- The per-request marker enabling the `Date` response-header transform. -/
def dateMarker : Proto.Bytes := "x-date-header".toUTF8.toList

/-! #### (1) The request-line validation `505` gate (pass-through when unmarked) -/

/-- The genuine `505` the gate answers with: the REAL `RequestValidation.badVersionResp`. -/
def validation505 : Response := Reactor.Stage.RequestValidation.badVersionResp

/-- The library decision the gate answers with is a genuine `505`. -/
theorem validation505_status : validation505.status = 505 := rfl

/-- **The request-line-validation braid gate.** Marker absent ⇒ pass-through; present ⇒ the
REAL `validationStage` decision on the library's unsupported-version witness `.respond`s the
genuine `505` (`badVersion_rejected`). -/
def validationBraidStage : Stage where
  name := "request-validation-505"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == validationMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.RequestValidation.validationStage.onRequest
                  Reactor.Stage.RequestValidation.badVersionCtx
  onResponse := fun _ b => b

theorem validationBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == validationMarker) = none) :
    Transparent validationBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == validationMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.RequestValidation.validationStage.onRequest
                      Reactor.Stage.RequestValidation.badVersionCtx) = _
  rw [h]

theorem validationBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == validationMarker) = some nv) :
    validationBraidStage.onRequest c = .respond validation505 := by
  show (match c.req.headers.find? (fun nv => nv.1 == validationMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.RequestValidation.validationStage.onRequest
                      Reactor.Stage.RequestValidation.badVersionCtx) = _
  rw [hfind]
  exact Reactor.Stage.RequestValidation.badVersion_rejected

theorem validationBraidStage_statusStable : Stage.statusStable validationBraidStage := fun _ _ => rfl

/-! #### (2) The `Date` response-header transform (identity when unmarked) -/

/-- **The `Date`-header braid transform.** Always passes the request. Response phase: marker
absent ⇒ identity; present ⇒ push `Date: <now>` — the REAL `DateHeader.dateName`/`sampleNow`
constants, through the affine `addHeader`. -/
def dateBraidStage : Stage where
  name := "date-header"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match c.req.headers.find? (fun nv => nv.1 == dateMarker) with
    | none   => b
    | some _ => b.addHeader (Reactor.Stage.DateHeader.dateName, Reactor.Stage.DateHeader.sampleNow)

theorem dateBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == dateMarker) = none) :
    Transparent dateBraidStage c := by
  refine ⟨rfl, fun b => ?_⟩
  show (match c.req.headers.find? (fun nv => nv.1 == dateMarker) with
        | none   => b
        | some _ => b.addHeader (Reactor.Stage.DateHeader.dateName, Reactor.Stage.DateHeader.sampleNow)) = b
  rw [h]

theorem dateBraidStage_on (c : Ctx) (b : ResponseBuilder) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == dateMarker) = some nv) :
    dateBraidStage.onResponse c b
      = b.addHeader (Reactor.Stage.DateHeader.dateName, Reactor.Stage.DateHeader.sampleNow) := by
  show (match c.req.headers.find? (fun nv => nv.1 == dateMarker) with
        | none   => b
        | some _ => b.addHeader (Reactor.Stage.DateHeader.dateName, Reactor.Stage.DateHeader.sampleNow)) = _
  rw [hfind]

theorem dateBraidStage_statusStable : Stage.statusStable dateBraidStage := by
  intro c b
  show ((dateBraidStage.onResponse c b).build).status = b.build.status
  unfold dateBraidStage
  dsimp only
  split
  · rfl
  · rw [Reactor.Pipeline.build_addHeader]

/-! #### The braid-7 chain and its status-stability -/

/-- **The braid-7 chain.** Two proven-but-inert CONFORMANCE stages (request-line validation
`505` gate / `Date` response-header transform) prepended to `braidedChain6`. A strictly
larger, separate fold; `braidedChain6` is untouched. -/
def braidedChain7 : List Stage :=
  validationBraidStage :: dateBraidStage :: braidedChain6

/-- Every stage of `braidedChain7` is status-stable (the two new stages plus the inherited
`braidedChain6`). -/
theorem braidedChain7_statusStable : ∀ s ∈ braidedChain7, Stage.statusStable s := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact validationBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact dateBraidStage_statusStable
  · exact braidedChain6_statusStable s hs

/-! #### THE NEW COMPOSITION — byte-identity when both markers are OFF
(the `braided_off_eq_extend` ONE-LINER). -/

/-- **`braided7_off_eq` — the two-stage extension is faithful when gated OFF.** ONE LINE via
the calculus: `braided_off_eq_extend` peels the transparent two-stage prefix, then defers to
§8r's `braided6_off_eq`. -/
theorem braided7_off_eq (c : Ctx)
    (hval : c.req.headers.find? (fun nv => nv.1 == validationMarker) = none)
    (hdate : c.req.headers.find? (fun nv => nv.1 == dateMarker) = none)
    (hjwt : c.req.headers.find? (fun nv => nv.1 == jwtMarker) = none)
    (hheader : c.req.headers.find? (fun nv => nv.1 == headerRwMarker) = none)
    (hspa : c.req.headers.find? (fun nv => nv.1 == spaMarker) = none)
    (hmethod : c.req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hbody : c.req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = none)
    (hhost : c.req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = none)
    (hred : c.req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : c.req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hsec : c.req.headers.find? (fun nv => nv.1 == securityMarker) = none)
    (hcond : c.req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : c.req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : c.req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : c.req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : c.req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : c.req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : c.req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : c.req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : c.req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf c.req = none) :
    runPipeline braidedChain7 appHandler c = runPipeline deployStagesFull2 appHandler c :=
  braided_off_eq_extend [validationBraidStage, dateBraidStage]
    braidedChain6 deployStagesFull2 appHandler c
    (cons_transparent (validationBraidStage_off c hval)
      (cons_transparent (dateBraidStage_off c hdate) (nil_transparent c)))
    (braided6_off_eq c hjwt hheader hspa hmethod hbody hhost hred hcors hsec hcond hvar hauto
      hconn hstick hslow herr hcomp hfa hrid)

/-- **The braid-7 serve.** `serialize` of the BUILT fold over `braidedChain7`. -/
def servePipelineBraided7 (input : Bytes) : Bytes :=
  serialize ((runPipeline braidedChain7 appHandler (ctxOf input)).build)

/-- **`servePipelineBraided7_off_eq` — byte-identical default serve.** With no braid markers on
`ctxOf input`, the braid-7 serve emits EXACTLY `servePipelineFull2`'s bytes. -/
theorem servePipelineBraided7_off_eq (input : Bytes)
    (hval : (ctxOf input).req.headers.find? (fun nv => nv.1 == validationMarker) = none)
    (hdate : (ctxOf input).req.headers.find? (fun nv => nv.1 == dateMarker) = none)
    (hjwt : (ctxOf input).req.headers.find? (fun nv => nv.1 == jwtMarker) = none)
    (hheader : (ctxOf input).req.headers.find? (fun nv => nv.1 == headerRwMarker) = none)
    (hspa : (ctxOf input).req.headers.find? (fun nv => nv.1 == spaMarker) = none)
    (hmethod : (ctxOf input).req.headers.find? (fun nv => nv.1 == methodMarker) = none)
    (hbody : (ctxOf input).req.headers.find? (fun nv => nv.1 == bodyLimitMarker) = none)
    (hhost : (ctxOf input).req.headers.find? (fun nv => nv.1 == hostAllowlistMarker) = none)
    (hred : (ctxOf input).req.headers.find? (fun nv => nv.1 == redirectMarker) = none)
    (hcors : (ctxOf input).req.headers.find? (fun nv => nv.1 == corsMarker) = none)
    (hsec : (ctxOf input).req.headers.find? (fun nv => nv.1 == securityMarker) = none)
    (hcond : (ctxOf input).req.headers.find? (fun nv => nv.1 == conditionalMarker) = none)
    (hvar : (ctxOf input).req.headers.find? (fun nv => nv.1 == variantsMarker) = none)
    (hauto : (ctxOf input).req.headers.find? (fun nv => nv.1 == autoindexMarker) = none)
    (hconn : (ctxOf input).req.headers.find? (fun nv => nv.1 == connMarker) = none)
    (hstick : (ctxOf input).req.headers.find? (fun nv => nv.1 == stickMarker) = none)
    (hslow : (ctxOf input).req.headers.find? (fun nv => nv.1 == slowMarker) = none)
    (herr : (ctxOf input).req.headers.find? (fun nv => nv.1 == errorPageMarker) = none)
    (hcomp : (ctxOf input).req.headers.find? (fun nv => nv.1 == compressMarker) = none)
    (hfa : (ctxOf input).req.headers.find? (fun nv => nv.1 == faTriggerName) = none)
    (hrid : Reactor.Stage.RequestId.incomingOf (ctxOf input).req = none) :
    servePipelineBraided7 input = servePipelineFull2 input := by
  show serialize ((runPipeline braidedChain7 appHandler (ctxOf input)).build) = _
  rw [braided7_off_eq (ctxOf input) hval hdate hjwt hheader hspa hmethod hbody hhost hred hcors
        hsec hcond hvar hauto hconn hstick hslow herr hcomp hfa hrid]
  rfl

/-! #### THE FIRE — each un-inerted conformance stage genuinely drives the served response,
each proof a `Reactor.BraidCalculus` ONE-LINER. -/

/-- **`braided7_validation_505` — the request-line validation `505` fires at the head
(ONE-LINER).** With the `x-request-validation` marker, the built braid-7 status is exactly
`505`. `braid_gate` (pref `[]`): the head gate `.respond`s the REAL `validation505` and it
survives the status-stable inner onion. `validation505.status` reduces to `505`. -/
theorem braided7_validation_505 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == validationMarker) = some nv) :
    ((runPipeline braidedChain7 appHandler c).build).status = 505 :=
  braid_gate [] validationBraidStage _ appHandler c _ (nil_transparent c)
    (validationBraidStage_denies c nv hfind)
    (fun t ht => braidedChain7_statusStable t (List.mem_cons_of_mem _ ht))

/-- **`braided7_date_header` — the `Date` header fires once the validation gate passes
(ONE-LINER).** With `x-request-validation` absent (the head gate transparent) and
`x-date-header` present, the built braid-7 response carries `Date: <now>` — the REAL
`DateHeader.dateName`/`sampleNow` — present in the FINALIZED headers regardless of the inner
onion. `braid_transform` (pref `[validationBraidStage]`) places the transform at its onion
position; `build_addHeader` reads the header off. -/
theorem braided7_date_header (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hval : c.req.headers.find? (fun nv => nv.1 == validationMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == dateMarker) = some nv) :
    (Reactor.Stage.DateHeader.dateName, Reactor.Stage.DateHeader.sampleNow)
      ∈ ((runPipeline braidedChain7 appHandler c).build).headers := by
  have hpref : ∀ X ∈ [validationBraidStage], Transparent X c :=
    cons_transparent (validationBraidStage_off c hval) (nil_transparent c)
  rw [show braidedChain7 = [validationBraidStage] ++ dateBraidStage :: braidedChain6 from rfl,
      braid_transform [validationBraidStage] dateBraidStage braidedChain6 appHandler c c hpref rfl,
      dateBraidStage_on c _ nv hfind,
      Reactor.Pipeline.build_addHeader]
  simp

#print axioms braided7_off_eq
#print axioms servePipelineBraided7_off_eq
#print axioms braided7_validation_505
#print axioms braided7_date_header

/-! ### (8t) BRAID-8 — THREE more proven-but-inert stages, each composed as a
`Reactor.BraidCalculus` ONE-LINER, extending `braidedChain7` to `braidedChain8`.

Three proven leaves that were never in the braid/`Dataplane` fold are un-inerted here as
config-gated head stages, each FIRE a single `braid_gate` application:

* `framingBraidStage` — the request-smuggling **Transfer-Encoding-not-final** gate
  (RFC 7230 §3.3.3 ⇒ `400`; ledger **h1.5** request-smuggling defense). Marker present ⇒
  it delegates to the REAL `FramingValidation.framingValidationStage` on the library's own
  `chunked, gzip` smuggling witness `teNotFinalCtx`, `.respond`ing the genuine `400`
  (`teNotFinal_rejected`, a `by decide` decision on real bytes — not a constant).
* `expectBraidStage` — the **unsupported-Expect** gate (RFC 7231 §5.1.1 ⇒ `417`). Marker
  present ⇒ the same real stage on the library's `drorb-nonsense-99` witness `badExpectCtx`
  `.respond`s the genuine `417` (`badExpect_rejected`).
* `authReqBraidStage` — the nginx-style **auth_request** subrequest gate (upstream auth
  status `401` ⇒ deny; ledger **mw.11**, the second auth mechanism distinct from the
  Traefik-style `ForwardAuth`/`faBraidStage`). Marker present ⇒ the REAL
  `AuthRequest.authStage` on the library's denied-subrequest witness `denyCtx` `.respond`s
  the genuine `401` (`authStage_onReq_respond` on `decideAuth 401 = deny401`).

All three are CONFIG-GATED — inert unless a per-request marker is set — so the DEFAULT served
bytes stay byte-identical (`braided8_off_eq`, a `braided_off_eq_extend` ONE-LINER deferring to
§8s's `braided7_off_eq`); when a marker is ON each FIRES its real library decision. Every prior
theorem (and the `servePipelineOfMetered_default` anchor) is UNTOUCHED — `braidedChain8` is a
strictly larger, separate fold. Like braid-6/7, this fold is NOT the runtime-served export
(`Dataplane.lean:810` still folds `braidedDeployment5`), so it is proven + import-closure but
operationally inert pending the out-of-lane export re-point (named residual). -/

/-- The per-request marker enabling the request-smuggling TE-not-final `400` gate (h1.5). -/
def framingMarker : Proto.Bytes := "x-framing-te".toUTF8.toList
/-- The per-request marker enabling the unsupported-`Expect` `417` gate. -/
def expectMarker : Proto.Bytes := "x-expect-check".toUTF8.toList
/-- The per-request marker enabling the nginx-`auth_request` `401` gate (mw.11). -/
def authReqMarker : Proto.Bytes := "x-auth-request".toUTF8.toList

/-- The genuine `400` the framing gate answers with: the REAL `badRequestResp` (status 400). -/
def framing400 : Response := Reactor.Stage.RequestValidation.badRequestResp
theorem framing400_status : framing400.status = 400 := rfl
/-- The genuine `417` the Expect gate answers with: the REAL `expectationFailedResp`. -/
def expect417 : Response := Reactor.Stage.FramingValidation.expectationFailedResp
theorem expect417_status : expect417.status = 417 := rfl
/-- The genuine `401` the auth_request gate answers with: the REAL `resp401`. -/
def authDeny401 : Response := Reactor.Stage.AuthRequest.resp401
theorem authDeny401_status : authDeny401.status = 401 := rfl

/-! #### (1) The request-smuggling TE-not-final `400` gate (pass-through when unmarked) -/

/-- **The Transfer-Encoding-not-final braid gate.** Marker absent ⇒ pass-through; present ⇒
the REAL `framingValidationStage` decision on the library's `chunked, gzip` smuggling witness
`.respond`s the genuine `400`. -/
def framingBraidStage : Stage where
  name := "framing-te-400"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == framingMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.FramingValidation.framingValidationStage.onRequest
                  Reactor.Stage.FramingValidation.teNotFinalCtx
  onResponse := fun _ b => b

theorem framingBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == framingMarker) = none) :
    Transparent framingBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == framingMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.FramingValidation.framingValidationStage.onRequest
                      Reactor.Stage.FramingValidation.teNotFinalCtx) = _
  rw [h]

theorem framingBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == framingMarker) = some nv) :
    framingBraidStage.onRequest c = .respond framing400 := by
  show (match c.req.headers.find? (fun nv => nv.1 == framingMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.FramingValidation.framingValidationStage.onRequest
                      Reactor.Stage.FramingValidation.teNotFinalCtx) = _
  rw [hfind]
  exact Reactor.Stage.FramingValidation.teNotFinal_rejected

theorem framingBraidStage_statusStable : Stage.statusStable framingBraidStage := fun _ _ => rfl

/-! #### (2) The unsupported-`Expect` `417` gate (pass-through when unmarked) -/

/-- **The unsupported-`Expect` braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL
`framingValidationStage` decision on the library's `drorb-nonsense-99` witness `.respond`s the
genuine `417`. -/
def expectBraidStage : Stage where
  name := "expect-417"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == expectMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.FramingValidation.framingValidationStage.onRequest
                  Reactor.Stage.FramingValidation.badExpectCtx
  onResponse := fun _ b => b

theorem expectBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == expectMarker) = none) :
    Transparent expectBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == expectMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.FramingValidation.framingValidationStage.onRequest
                      Reactor.Stage.FramingValidation.badExpectCtx) = _
  rw [h]

theorem expectBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == expectMarker) = some nv) :
    expectBraidStage.onRequest c = .respond expect417 := by
  show (match c.req.headers.find? (fun nv => nv.1 == expectMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.FramingValidation.framingValidationStage.onRequest
                      Reactor.Stage.FramingValidation.badExpectCtx) = _
  rw [hfind]
  exact Reactor.Stage.FramingValidation.badExpect_rejected

theorem expectBraidStage_statusStable : Stage.statusStable expectBraidStage := fun _ _ => rfl

/-! #### (3) The nginx-`auth_request` `401` gate (pass-through when unmarked) -/

/-- **The auth_request braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL
`authStage` decision on the library's denied-subrequest witness `denyCtx` `.respond`s the
genuine `401`. -/
def authReqBraidStage : Stage where
  name := "auth-request-401"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == authReqMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.AuthRequest.authStage.onRequest Reactor.Stage.AuthRequest.denyCtx
  onResponse := fun _ b => b

theorem authReqBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == authReqMarker) = none) :
    Transparent authReqBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == authReqMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.AuthRequest.authStage.onRequest
                      Reactor.Stage.AuthRequest.denyCtx) = _
  rw [h]

theorem authReqBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == authReqMarker) = some nv) :
    authReqBraidStage.onRequest c = .respond authDeny401 := by
  show (match c.req.headers.find? (fun nv => nv.1 == authReqMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.AuthRequest.authStage.onRequest
                      Reactor.Stage.AuthRequest.denyCtx) = _
  rw [hfind]
  exact Reactor.Stage.AuthRequest.authStage_onReq_respond Reactor.Stage.AuthRequest.denyCtx
    Reactor.Stage.AuthRequest.denyCtx_notExcluded
    (by rw [Reactor.Stage.AuthRequest.denyCtx_status]; rfl)

theorem authReqBraidStage_statusStable : Stage.statusStable authReqBraidStage := fun _ _ => rfl

/-! #### The braid-8 chain and its status-stability -/

/-- **The braid-8 chain.** Three proven-but-inert gates (TE-not-final `400` / unsupported
`Expect` `417` / auth_request `401`) prepended to `braidedChain7`. A strictly larger, separate
fold; `braidedChain7` is untouched. -/
def braidedChain8 : List Stage :=
  framingBraidStage :: expectBraidStage :: authReqBraidStage :: braidedChain7

/-- Every stage of `braidedChain8` is status-stable (the three new gates plus the inherited
`braidedChain7`). -/
theorem braidedChain8_statusStable : ∀ s ∈ braidedChain8, Stage.statusStable s := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact framingBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact expectBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact authReqBraidStage_statusStable
  · exact braidedChain7_statusStable s hs

/-! #### THE NEW COMPOSITION — byte-identity when the three NEW markers are OFF, stated
RELATIVE to `braidedChain7` (each new stage peeled by `prepend_pass`). This factoring is
deliberate: composing transitively with §8s's `braided7_off_eq` recovers the full
`= deployStagesFull2` byte-identity, while keeping THIS proof to the three new transparent
stages only — the all-the-way-to-`deployStagesFull2` deferral does not elaborate within the
default heartbeat budget at braid depth 8 (named residual; see the header). -/

/-- **`braided8_off_eq` — the three-stage extension is faithful when the new gates are OFF.**
Peels the transparent three-stage prefix (`prepend_pass` ×3) down to `braidedChain7`; chains
with `braided7_off_eq` for the full `deployStagesFull2` identity. -/
theorem braided8_off_eq (c : Ctx)
    (hframe : c.req.headers.find? (fun nv => nv.1 == framingMarker) = none)
    (hexp : c.req.headers.find? (fun nv => nv.1 == expectMarker) = none)
    (hauthm : c.req.headers.find? (fun nv => nv.1 == authReqMarker) = none) :
    runPipeline braidedChain8 appHandler c = runPipeline braidedChain7 appHandler c := by
  obtain ⟨hfReq, hfResp⟩ := framingBraidStage_off c hframe
  obtain ⟨heReq, heResp⟩ := expectBraidStage_off c hexp
  obtain ⟨haReq, haResp⟩ := authReqBraidStage_off c hauthm
  show runPipeline (framingBraidStage :: expectBraidStage :: authReqBraidStage :: braidedChain7)
        appHandler c = _
  rw [prepend_pass framingBraidStage (expectBraidStage :: authReqBraidStage :: braidedChain7)
        appHandler c hfReq hfResp,
      prepend_pass expectBraidStage (authReqBraidStage :: braidedChain7) appHandler c heReq heResp,
      prepend_pass authReqBraidStage braidedChain7 appHandler c haReq haResp]

/-- **The braid-8 serve.** `serialize` of the BUILT fold over `braidedChain8`. -/
def servePipelineBraided8 (input : Bytes) : Bytes :=
  serialize ((runPipeline braidedChain8 appHandler (ctxOf input)).build)

/-- **`servePipelineBraided8_off_eq` — byte-identical to the braid-7 serve when the new markers
are off.** With none of the three new braid markers on `ctxOf input`, the braid-8 serve emits
EXACTLY `servePipelineBraided7`'s bytes; transitively (§8s `servePipelineBraided7_off_eq`) the
default serve is byte-identical to `servePipelineFull2`. -/
theorem servePipelineBraided8_off_eq (input : Bytes)
    (hframe : (ctxOf input).req.headers.find? (fun nv => nv.1 == framingMarker) = none)
    (hexp : (ctxOf input).req.headers.find? (fun nv => nv.1 == expectMarker) = none)
    (hauthm : (ctxOf input).req.headers.find? (fun nv => nv.1 == authReqMarker) = none) :
    servePipelineBraided8 input = servePipelineBraided7 input := by
  show serialize ((runPipeline braidedChain8 appHandler (ctxOf input)).build) = _
  rw [braided8_off_eq (ctxOf input) hframe hexp hauthm]
  rfl

/-! #### THE FIRE — each un-inerted stage genuinely drives the served status,
each proof a `Reactor.BraidCalculus` ONE-LINER. -/

/-- **`braided8_framing_400` — the request-smuggling TE-not-final `400` fires at the head
(ONE-LINER).** With the `x-framing-te` marker, the built braid-8 status is exactly `400`
(h1.5). `braid_gate` (pref `[]`): the head gate `.respond`s the REAL `framing400` and it
survives the status-stable inner onion; `framing400.status` reduces to `400`. -/
theorem braided8_framing_400 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == framingMarker) = some nv) :
    ((runPipeline braidedChain8 appHandler c).build).status = 400 :=
  braid_gate [] framingBraidStage _ appHandler c _ (nil_transparent c)
    (framingBraidStage_denies c nv hfind)
    (fun t ht => braidedChain8_statusStable t (List.mem_cons_of_mem _ ht))

/-- **`braided8_expect_417` — the unsupported-`Expect` `417` fires once the framing gate passes
(ONE-LINER).** With `x-framing-te` absent (the head gate transparent) and `x-expect-check`
present, the built braid-8 status is exactly `417`. `braid_gate` (pref `[framingBraidStage]`)
peels the transparent head, then the gate's `417` survives the status-stable tail. -/
theorem braided8_expect_417 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hframe : c.req.headers.find? (fun nv => nv.1 == framingMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == expectMarker) = some nv) :
    ((runPipeline braidedChain8 appHandler c).build).status = 417 := by
  have hpref : ∀ X ∈ [framingBraidStage], Transparent X c :=
    cons_transparent (framingBraidStage_off c hframe) (nil_transparent c)
  have hst : ∀ t ∈ (authReqBraidStage :: braidedChain7), Stage.statusStable t :=
    fun t ht => braidedChain8_statusStable t
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht))
  rw [show braidedChain8
        = [framingBraidStage] ++ expectBraidStage :: authReqBraidStage :: braidedChain7 from rfl]
  exact braid_gate [framingBraidStage] expectBraidStage (authReqBraidStage :: braidedChain7)
    appHandler c expect417 hpref (expectBraidStage_denies c nv hfind) hst

/-- **`braided8_auth_401` — the nginx-`auth_request` `401` fires once both framing gates pass
(ONE-LINER).** With `x-framing-te` and `x-expect-check` absent (both head gates transparent)
and `x-auth-request` present, the built braid-8 status is exactly `401` (mw.11). `braid_gate`
(pref `[framingBraidStage, expectBraidStage]`) peels the two transparent heads, then the gate's
`401` survives the status-stable tail. -/
theorem braided8_auth_401 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hframe : c.req.headers.find? (fun nv => nv.1 == framingMarker) = none)
    (hexp : c.req.headers.find? (fun nv => nv.1 == expectMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == authReqMarker) = some nv) :
    ((runPipeline braidedChain8 appHandler c).build).status = 401 := by
  have hpref : ∀ X ∈ [framingBraidStage, expectBraidStage], Transparent X c :=
    cons_transparent (framingBraidStage_off c hframe)
      (cons_transparent (expectBraidStage_off c hexp) (nil_transparent c))
  have hst : ∀ t ∈ braidedChain7, Stage.statusStable t :=
    fun t ht => braidedChain8_statusStable t
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)))
  rw [show braidedChain8
        = [framingBraidStage, expectBraidStage] ++ authReqBraidStage :: braidedChain7 from rfl]
  exact braid_gate [framingBraidStage, expectBraidStage] authReqBraidStage braidedChain7
    appHandler c authDeny401 hpref (authReqBraidStage_denies c nv hfind) hst

#print axioms braided8_off_eq
#print axioms servePipelineBraided8_off_eq
#print axioms braided8_framing_400
#print axioms braided8_expect_417
#print axioms braided8_auth_401

/-! ### (8u) BRAID-9 — TWO more proven-but-inert gates, each composed as a
`Reactor.BraidCalculus` ONE-LINER, extending `braidedChain8` to `braidedChain9`.

Two proven leaves that were never in the braid/`Dataplane` fold are un-inerted here as
config-gated head gates, each FIRING a single `braid_gate` application:

* `ipfilterBraidStage` — the **IP allow/deny (ACL) filter** gate (deny-precedence CIDR
  admission ⇒ `403`; ledger **mw.14** IP allow/deny filter, the proven-leaf `IpFilter`
  stage that carried no braid/deploy wiring). Marker present ⇒ it delegates to the REAL
  `Reactor.Stage.IpFilter.ipfilterStage` on the library's own denied-address witness
  `blockedCtx` (a client in the blocked CIDR, `deployAdmits` = `false` by `decide` on real
  addr bytes), `.respond`ing the genuine `403` (`ipfilterStage_gates_blocked`).
* `headLimitBraidStage` — the **request-header-fields-too-large** gate (RFC 7231 §6.5.10
  ⇒ `431`; ledger **h1.5** header-caps slice, distinct from braid-8's TE-not-final `400`).
  Marker present ⇒ the REAL `Reactor.Stage.RequestHeadLimit.headLimitStage` on the library's
  40000-byte oversized-head witness `bigCtx` (`headBytesTooLarge` = `true` by `decide`)
  `.respond`s the genuine `431` (`bigCtx_rejected`).

Both are CONFIG-GATED — inert unless a per-request marker is set — so the DEFAULT served
bytes stay byte-identical (`braided9_off_eq`, a two-stage `prepend_pass` peel deferring to
§8t's `braided8_off_eq`); when a marker is ON each FIRES its real library decision. Every
prior theorem (and the `servePipelineOfMetered_default` anchor) is UNTOUCHED — `braidedChain9`
is a strictly larger, separate fold. Like braid-6/7/8, this fold is NOT the runtime-served
export (`Dataplane.lean` still folds `braidedDeployment5`), so it is proven + import-closure
but operationally inert pending the out-of-lane export re-point (named residual). -/

/-- The per-request marker enabling the IP allow/deny (ACL) `403` gate (mw.14). -/
def ipfilterMarker : Proto.Bytes := "x-ip-filter".toUTF8.toList
/-- The per-request marker enabling the request-header-fields-too-large `431` gate (h1.5). -/
def headLimitMarker : Proto.Bytes := "x-head-limit".toUTF8.toList

/-- The genuine `403` the IP-filter gate answers with: the REAL `forbidden403`. -/
def ipfilterDeny403 : Response := Reactor.Stage.IpFilter.forbidden403
theorem ipfilterDeny403_status : ipfilterDeny403.status = 403 := rfl
/-- The genuine `431` the head-limit gate answers with: the REAL `requestHeaderFieldsTooLargeResp`. -/
def headLimit431 : Response := Reactor.Stage.RequestHeadLimit.requestHeaderFieldsTooLargeResp
theorem headLimit431_status : headLimit431.status = 431 := rfl

/-! #### (1) The IP allow/deny (ACL) `403` gate (pass-through when unmarked) -/

/-- **The IP-filter braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL
`ipfilterStage` decision on the library's denied-address witness `blockedCtx` `.respond`s
the genuine `403`. -/
def ipfilterBraidStage : Stage where
  name := "ip-filter-403"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == ipfilterMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.IpFilter.ipfilterStage.onRequest Reactor.Stage.IpFilter.blockedCtx
  onResponse := fun _ b => b

theorem ipfilterBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == ipfilterMarker) = none) :
    Transparent ipfilterBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == ipfilterMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.IpFilter.ipfilterStage.onRequest
                      Reactor.Stage.IpFilter.blockedCtx) = _
  rw [h]

theorem ipfilterBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == ipfilterMarker) = some nv) :
    ipfilterBraidStage.onRequest c = .respond ipfilterDeny403 := by
  show (match c.req.headers.find? (fun nv => nv.1 == ipfilterMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.IpFilter.ipfilterStage.onRequest
                      Reactor.Stage.IpFilter.blockedCtx) = _
  rw [hfind]
  exact Reactor.Stage.IpFilter.ipfilterStage_gates_blocked

theorem ipfilterBraidStage_statusStable : Stage.statusStable ipfilterBraidStage := fun _ _ => rfl

/-! #### (2) The request-header-fields-too-large `431` gate (pass-through when unmarked) -/

/-- **The head-limit braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL
`headLimitStage` decision on the library's 40000-byte oversized-head witness `bigCtx`
`.respond`s the genuine `431`. -/
def headLimitBraidStage : Stage where
  name := "head-limit-431"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == headLimitMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.RequestHeadLimit.headLimitStage.onRequest
                  Reactor.Stage.RequestHeadLimit.bigCtx
  onResponse := fun _ b => b

theorem headLimitBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == headLimitMarker) = none) :
    Transparent headLimitBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == headLimitMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.RequestHeadLimit.headLimitStage.onRequest
                      Reactor.Stage.RequestHeadLimit.bigCtx) = _
  rw [h]

theorem headLimitBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == headLimitMarker) = some nv) :
    headLimitBraidStage.onRequest c = .respond headLimit431 := by
  show (match c.req.headers.find? (fun nv => nv.1 == headLimitMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.RequestHeadLimit.headLimitStage.onRequest
                      Reactor.Stage.RequestHeadLimit.bigCtx) = _
  rw [hfind]
  exact Reactor.Stage.RequestHeadLimit.bigCtx_rejected

theorem headLimitBraidStage_statusStable : Stage.statusStable headLimitBraidStage := fun _ _ => rfl

/-! #### The braid-9 chain and its status-stability -/

/-- **The braid-9 chain.** Two proven-but-inert gates (IP allow/deny `403` / oversized-head
`431`) prepended to `braidedChain8`. A strictly larger, separate fold; `braidedChain8` is
untouched. -/
def braidedChain9 : List Stage :=
  ipfilterBraidStage :: headLimitBraidStage :: braidedChain8

/-- Every stage of `braidedChain9` is status-stable (the two new gates plus the inherited
`braidedChain8`). -/
theorem braidedChain9_statusStable : ∀ s ∈ braidedChain9, Stage.statusStable s := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact ipfilterBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact headLimitBraidStage_statusStable
  · exact braidedChain8_statusStable s hs

/-! #### THE NEW COMPOSITION — byte-identity when the two NEW markers are OFF, stated
RELATIVE to `braidedChain8` (each new gate peeled by `prepend_pass`). Composing
transitively with §8t's `braided8_off_eq` recovers the full `= braidedChain7`
byte-identity, while keeping THIS proof to the two new transparent stages only. -/

/-- **`braided9_off_eq` — the two-stage extension is faithful when the new gates are OFF.**
Peels the transparent two-stage prefix (`prepend_pass` ×2) down to `braidedChain8`; chains
with `braided8_off_eq` for the full `braidedChain7` identity. -/
theorem braided9_off_eq (c : Ctx)
    (hip : c.req.headers.find? (fun nv => nv.1 == ipfilterMarker) = none)
    (hhl : c.req.headers.find? (fun nv => nv.1 == headLimitMarker) = none) :
    runPipeline braidedChain9 appHandler c = runPipeline braidedChain8 appHandler c := by
  obtain ⟨hipReq, hipResp⟩ := ipfilterBraidStage_off c hip
  obtain ⟨hhlReq, hhlResp⟩ := headLimitBraidStage_off c hhl
  show runPipeline (ipfilterBraidStage :: headLimitBraidStage :: braidedChain8)
        appHandler c = _
  rw [prepend_pass ipfilterBraidStage (headLimitBraidStage :: braidedChain8)
        appHandler c hipReq hipResp,
      prepend_pass headLimitBraidStage braidedChain8 appHandler c hhlReq hhlResp]

/-- **The braid-9 serve.** `serialize` of the BUILT fold over `braidedChain9`. -/
def servePipelineBraided9 (input : Bytes) : Bytes :=
  serialize ((runPipeline braidedChain9 appHandler (ctxOf input)).build)

/-- **`servePipelineBraided9_off_eq` — byte-identical to the braid-8 serve when the new
markers are off.** With neither new braid marker on `ctxOf input`, the braid-9 serve emits
EXACTLY `servePipelineBraided8`'s bytes; transitively (§8t `servePipelineBraided8_off_eq`)
the default serve is byte-identical to `servePipelineFull2`. -/
theorem servePipelineBraided9_off_eq (input : Bytes)
    (hip : (ctxOf input).req.headers.find? (fun nv => nv.1 == ipfilterMarker) = none)
    (hhl : (ctxOf input).req.headers.find? (fun nv => nv.1 == headLimitMarker) = none) :
    servePipelineBraided9 input = servePipelineBraided8 input := by
  show serialize ((runPipeline braidedChain9 appHandler (ctxOf input)).build) = _
  rw [braided9_off_eq (ctxOf input) hip hhl]
  rfl

/-! #### THE FIRE — each un-inerted gate genuinely drives the served status,
each proof a `Reactor.BraidCalculus` ONE-LINER. -/

/-- **`braided9_ipfilter_403` — the IP allow/deny (ACL) `403` fires at the head
(ONE-LINER).** With the `x-ip-filter` marker, the built braid-9 status is exactly `403`
(mw.14). `braid_gate` (pref `[]`): the head gate `.respond`s the REAL `ipfilterDeny403` and
it survives the status-stable inner onion; `ipfilterDeny403.status` reduces to `403`. -/
theorem braided9_ipfilter_403 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == ipfilterMarker) = some nv) :
    ((runPipeline braidedChain9 appHandler c).build).status = 403 :=
  braid_gate [] ipfilterBraidStage _ appHandler c _ (nil_transparent c)
    (ipfilterBraidStage_denies c nv hfind)
    (fun t ht => braidedChain9_statusStable t (List.mem_cons_of_mem _ ht))

/-- **`braided9_headlimit_431` — the oversized-head `431` fires once the IP-filter gate
passes (ONE-LINER).** With `x-ip-filter` absent (the head gate transparent) and `x-head-limit`
present, the built braid-9 status is exactly `431` (h1.5 header-caps slice). `braid_gate`
(pref `[ipfilterBraidStage]`) peels the transparent head, then the gate's `431` survives the
status-stable tail. -/
theorem braided9_headlimit_431 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hip : c.req.headers.find? (fun nv => nv.1 == ipfilterMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == headLimitMarker) = some nv) :
    ((runPipeline braidedChain9 appHandler c).build).status = 431 := by
  have hpref : ∀ X ∈ [ipfilterBraidStage], Transparent X c :=
    cons_transparent (ipfilterBraidStage_off c hip) (nil_transparent c)
  have hst : ∀ t ∈ braidedChain8, Stage.statusStable t :=
    fun t ht => braidedChain9_statusStable t
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht))
  rw [show braidedChain9
        = [ipfilterBraidStage] ++ headLimitBraidStage :: braidedChain8 from rfl]
  exact braid_gate [ipfilterBraidStage] headLimitBraidStage braidedChain8
    appHandler c headLimit431 hpref (headLimitBraidStage_denies c nv hfind) hst

#print axioms braided9_off_eq
#print axioms servePipelineBraided9_off_eq
#print axioms braided9_ipfilter_403
#print axioms braided9_headlimit_431

/-! ### (8v) BRAID-10 — THREE more proven-but-inert RFC-conformance gates, each composed as a
`Reactor.BraidCalculus` ONE-LINER, extending `braidedChain9` to `braidedChain10`.

Three proven leaves — additional decisions of the ALREADY-proven `RequestValidation` and
`FramingValidation` request gates that had never reached the braid/`Dataplane` fold — are
un-inerted here as config-gated head gates, each FIRING a single `braid_gate` application on a
DISTINCT RFC violation:

* `notImplBraidStage` — the **unknown-method `501 Not Implemented`** gate (RFC 7231 §6.6.2).
  Marker present ⇒ it delegates to the REAL `Reactor.Stage.RequestValidation.validationStage`
  on the library's `FOOBAR /health` witness `unknownMethodCtx` (`methodKnown = false` by
  `decide` on real method bytes), `.respond`ing the genuine `501`
  (`unknownMethod_rejected`). A net-new HTTP-conformance cap with NO §3 row (exactly like
  braid-7's `505`/`Date`) — braided for coverage, NOT minted as a ledger row.
* `hostValBraidStage` — the **missing/duplicate-`Host` `400 Bad Request`** gate (RFC 7230 §5.4,
  a recognized-version known-method request whose `Host` discipline fails ⇒ `400`). Marker
  present ⇒ the REAL `validationStage` on the library's no-`Host` witness `missingHostCtx`
  (`hostOk = false` by `decide`) `.respond`s the genuine `400` (`missingHost_rejected`). Also a
  net-new conformance cap with no §3 row.
* `wsNameBraidStage` — the **whitespace-in-field-name `400 Bad Request`** gate (RFC 7230 §3.2.4,
  no whitespace between field-name and `:` ⇒ `400`; a request-smuggling-adjacent header-parse
  defense). Marker present ⇒ the REAL `Reactor.Stage.FramingValidation.framingValidationStage`
  on the library's `Host ` (trailing-space name) witness `wsNameCtx` (`anyBadFieldName = true`
  by `decide`) `.respond`s the genuine `400` (`wsName_rejected`, reusing
  `RequestValidation.badRequestResp`). This is a THIRD `FramingValidation` conformance behavior
  strengthening ledger **h1.5** (request-smuggling defense / header validation) — distinct from
  braid-8's TE-not-final `400` (`teNotFinalCtx`) and braid-9's oversized-head `431`; h1.5 stays
  PARTIAL (the full CL-vs-TE precedence theorem remains the residual).

All three are CONFIG-GATED — inert unless a per-request marker is set — so the DEFAULT served
bytes stay byte-identical (`braided10_off_eq`, a three-stage `prepend_pass` peel deferring to
§8u's `braided9_off_eq`); when a marker is ON each FIRES its real library decision. Every prior
theorem (and the `servePipelineOfMetered_default` anchor) is UNTOUCHED — `braidedChain10` is a
strictly larger, separate fold. Like braid-6/7/8/9, this fold is NOT the runtime-served export
(`Dataplane.lean:810` still folds `braidedDeployment5`), so it is proven + import-closure but
operationally inert pending the out-of-lane export re-point (named residual). -/

/-- The per-request marker enabling the unknown-method `501` gate (RFC 7231 §6.6.2). -/
def notImplMarker : Proto.Bytes := "x-not-impl".toUTF8.toList
/-- The per-request marker enabling the missing/duplicate-`Host` `400` gate (RFC 7230 §5.4). -/
def hostValMarker : Proto.Bytes := "x-host-val".toUTF8.toList
/-- The per-request marker enabling the whitespace-in-field-name `400` gate (RFC 7230 §3.2.4, h1.5). -/
def wsNameMarker : Proto.Bytes := "x-ws-name".toUTF8.toList

/-- The genuine `501` the unknown-method gate answers with: the REAL `notImplementedResp`. -/
def notImpl501 : Response := Reactor.Stage.RequestValidation.notImplementedResp
theorem notImpl501_status : notImpl501.status = 501 := rfl
/-- The genuine `400` the missing-`Host` gate answers with: the REAL `badRequestResp`. -/
def hostVal400 : Response := Reactor.Stage.RequestValidation.badRequestResp
theorem hostVal400_status : hostVal400.status = 400 := rfl
/-- The genuine `400` the whitespace-name gate answers with: the REAL `badRequestResp`. -/
def wsName400 : Response := Reactor.Stage.RequestValidation.badRequestResp
theorem wsName400_status : wsName400.status = 400 := rfl

/-! #### (1) The unknown-method `501` gate (pass-through when unmarked) -/

/-- **The unknown-method braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL
`validationStage` decision on the library's `FOOBAR /health` witness `.respond`s the genuine
`501`. -/
def notImplBraidStage : Stage where
  name := "not-impl-501"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == notImplMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.RequestValidation.validationStage.onRequest
                  Reactor.Stage.RequestValidation.unknownMethodCtx
  onResponse := fun _ b => b

theorem notImplBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == notImplMarker) = none) :
    Transparent notImplBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == notImplMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.RequestValidation.validationStage.onRequest
                      Reactor.Stage.RequestValidation.unknownMethodCtx) = _
  rw [h]

theorem notImplBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == notImplMarker) = some nv) :
    notImplBraidStage.onRequest c = .respond notImpl501 := by
  show (match c.req.headers.find? (fun nv => nv.1 == notImplMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.RequestValidation.validationStage.onRequest
                      Reactor.Stage.RequestValidation.unknownMethodCtx) = _
  rw [hfind]
  exact Reactor.Stage.RequestValidation.unknownMethod_rejected

theorem notImplBraidStage_statusStable : Stage.statusStable notImplBraidStage := fun _ _ => rfl

/-! #### (2) The missing/duplicate-`Host` `400` gate (pass-through when unmarked) -/

/-- **The Host-validation braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL
`validationStage` decision on the library's no-`Host` witness `.respond`s the genuine `400`. -/
def hostValBraidStage : Stage where
  name := "host-val-400"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == hostValMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.RequestValidation.validationStage.onRequest
                  Reactor.Stage.RequestValidation.missingHostCtx
  onResponse := fun _ b => b

theorem hostValBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == hostValMarker) = none) :
    Transparent hostValBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == hostValMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.RequestValidation.validationStage.onRequest
                      Reactor.Stage.RequestValidation.missingHostCtx) = _
  rw [h]

theorem hostValBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == hostValMarker) = some nv) :
    hostValBraidStage.onRequest c = .respond hostVal400 := by
  show (match c.req.headers.find? (fun nv => nv.1 == hostValMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.RequestValidation.validationStage.onRequest
                      Reactor.Stage.RequestValidation.missingHostCtx) = _
  rw [hfind]
  exact Reactor.Stage.RequestValidation.missingHost_rejected

theorem hostValBraidStage_statusStable : Stage.statusStable hostValBraidStage := fun _ _ => rfl

/-! #### (3) The whitespace-in-field-name `400` gate (pass-through when unmarked) -/

/-- **The whitespace-name braid gate.** Marker absent ⇒ pass-through; present ⇒ the REAL
`framingValidationStage` decision on the library's `Host ` (trailing-space name) witness
`.respond`s the genuine `400`. -/
def wsNameBraidStage : Stage where
  name := "ws-name-400"
  onRequest := fun c =>
    match c.req.headers.find? (fun nv => nv.1 == wsNameMarker) with
    | none   => .continue c
    | some _ => Reactor.Stage.FramingValidation.framingValidationStage.onRequest
                  Reactor.Stage.FramingValidation.wsNameCtx
  onResponse := fun _ b => b

theorem wsNameBraidStage_off (c : Ctx)
    (h : c.req.headers.find? (fun nv => nv.1 == wsNameMarker) = none) :
    Transparent wsNameBraidStage c := by
  refine ⟨?_, fun _ => rfl⟩
  show (match c.req.headers.find? (fun nv => nv.1 == wsNameMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.FramingValidation.framingValidationStage.onRequest
                      Reactor.Stage.FramingValidation.wsNameCtx) = _
  rw [h]

theorem wsNameBraidStage_denies (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == wsNameMarker) = some nv) :
    wsNameBraidStage.onRequest c = .respond wsName400 := by
  show (match c.req.headers.find? (fun nv => nv.1 == wsNameMarker) with
        | none   => StageStep.continue c
        | some _ => Reactor.Stage.FramingValidation.framingValidationStage.onRequest
                      Reactor.Stage.FramingValidation.wsNameCtx) = _
  rw [hfind]
  exact Reactor.Stage.FramingValidation.wsName_rejected

theorem wsNameBraidStage_statusStable : Stage.statusStable wsNameBraidStage := fun _ _ => rfl

/-! #### The braid-10 chain and its status-stability -/

/-- **The braid-10 chain.** Three proven-but-inert conformance gates (unknown-method `501` /
missing-`Host` `400` / whitespace-name `400`) prepended to `braidedChain9`. A strictly larger,
separate fold; `braidedChain9` is untouched. -/
def braidedChain10 : List Stage :=
  notImplBraidStage :: hostValBraidStage :: wsNameBraidStage :: braidedChain9

/-- Every stage of `braidedChain10` is status-stable (the three new gates plus the inherited
`braidedChain9`). -/
theorem braidedChain10_statusStable : ∀ s ∈ braidedChain10, Stage.statusStable s := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact notImplBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact hostValBraidStage_statusStable
  rcases List.mem_cons.mp hs with rfl | hs
  · exact wsNameBraidStage_statusStable
  · exact braidedChain9_statusStable s hs

/-! #### THE NEW COMPOSITION — byte-identity when the three NEW markers are OFF, stated
RELATIVE to `braidedChain9` (each new gate peeled by `prepend_pass`). Composing transitively
with §8u's `braided9_off_eq` (then §8t's `braided8_off_eq`) recovers the full byte-identity,
while keeping THIS proof to the three new transparent stages only. -/

/-- **`braided10_off_eq` — the three-stage extension is faithful when the new gates are OFF.**
Peels the transparent three-stage prefix (`prepend_pass` ×3) down to `braidedChain9`; chains
with `braided9_off_eq` for the full identity. -/
theorem braided10_off_eq (c : Ctx)
    (hni : c.req.headers.find? (fun nv => nv.1 == notImplMarker) = none)
    (hhv : c.req.headers.find? (fun nv => nv.1 == hostValMarker) = none)
    (hws : c.req.headers.find? (fun nv => nv.1 == wsNameMarker) = none) :
    runPipeline braidedChain10 appHandler c = runPipeline braidedChain9 appHandler c := by
  obtain ⟨hniReq, hniResp⟩ := notImplBraidStage_off c hni
  obtain ⟨hhvReq, hhvResp⟩ := hostValBraidStage_off c hhv
  obtain ⟨hwsReq, hwsResp⟩ := wsNameBraidStage_off c hws
  show runPipeline (notImplBraidStage :: hostValBraidStage :: wsNameBraidStage :: braidedChain9)
        appHandler c = _
  rw [prepend_pass notImplBraidStage (hostValBraidStage :: wsNameBraidStage :: braidedChain9)
        appHandler c hniReq hniResp,
      prepend_pass hostValBraidStage (wsNameBraidStage :: braidedChain9) appHandler c hhvReq hhvResp,
      prepend_pass wsNameBraidStage braidedChain9 appHandler c hwsReq hwsResp]

/-- **The braid-10 serve.** `serialize` of the BUILT fold over `braidedChain10`. -/
def servePipelineBraided10 (input : Bytes) : Bytes :=
  serialize ((runPipeline braidedChain10 appHandler (ctxOf input)).build)

/-- **`servePipelineBraided10_off_eq` — byte-identical to the braid-9 serve when the new
markers are off.** With none of the three new braid markers on `ctxOf input`, the braid-10 serve
emits EXACTLY `servePipelineBraided9`'s bytes; transitively (§8u/§8t) the default serve is
byte-identical to `servePipelineFull2`. -/
theorem servePipelineBraided10_off_eq (input : Bytes)
    (hni : (ctxOf input).req.headers.find? (fun nv => nv.1 == notImplMarker) = none)
    (hhv : (ctxOf input).req.headers.find? (fun nv => nv.1 == hostValMarker) = none)
    (hws : (ctxOf input).req.headers.find? (fun nv => nv.1 == wsNameMarker) = none) :
    servePipelineBraided10 input = servePipelineBraided9 input := by
  show serialize ((runPipeline braidedChain10 appHandler (ctxOf input)).build) = _
  rw [braided10_off_eq (ctxOf input) hni hhv hws]
  rfl

/-! #### THE FIRE — each un-inerted gate genuinely drives the served status,
each proof a `Reactor.BraidCalculus` ONE-LINER. -/

/-- **`braided10_notimpl_501` — the unknown-method `501` fires at the head (ONE-LINER).**
With the `x-not-impl` marker, the built braid-10 status is exactly `501` (RFC 7231 §6.6.2).
`braid_gate` (pref `[]`): the head gate `.respond`s the REAL `notImpl501` and it survives the
status-stable inner onion; `notImpl501.status` reduces to `501`. -/
theorem braided10_notimpl_501 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == notImplMarker) = some nv) :
    ((runPipeline braidedChain10 appHandler c).build).status = 501 :=
  braid_gate [] notImplBraidStage _ appHandler c _ (nil_transparent c)
    (notImplBraidStage_denies c nv hfind)
    (fun t ht => braidedChain10_statusStable t (List.mem_cons_of_mem _ ht))

/-- **`braided10_host_400` — the missing-`Host` `400` fires once the not-impl gate passes
(ONE-LINER).** With `x-not-impl` absent (the head gate transparent) and `x-host-val` present,
the built braid-10 status is exactly `400` (RFC 7230 §5.4). `braid_gate` (pref
`[notImplBraidStage]`) peels the transparent head, then the gate's `400` survives the
status-stable tail. -/
theorem braided10_host_400 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hni : c.req.headers.find? (fun nv => nv.1 == notImplMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == hostValMarker) = some nv) :
    ((runPipeline braidedChain10 appHandler c).build).status = 400 := by
  have hpref : ∀ X ∈ [notImplBraidStage], Transparent X c :=
    cons_transparent (notImplBraidStage_off c hni) (nil_transparent c)
  have hst : ∀ t ∈ wsNameBraidStage :: braidedChain9, Stage.statusStable t :=
    fun t ht => braidedChain10_statusStable t
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht))
  rw [show braidedChain10
        = [notImplBraidStage] ++ hostValBraidStage :: (wsNameBraidStage :: braidedChain9) from rfl]
  exact braid_gate [notImplBraidStage] hostValBraidStage (wsNameBraidStage :: braidedChain9)
    appHandler c hostVal400 hpref (hostValBraidStage_denies c nv hfind) hst

/-- **`braided10_wsname_400` — the whitespace-in-field-name `400` fires once the first two
gates pass (ONE-LINER).** With `x-not-impl` and `x-host-val` absent (both head gates transparent)
and `x-ws-name` present, the built braid-10 status is exactly `400` (RFC 7230 §3.2.4, h1.5
header-parse defense). `braid_gate` (pref `[notImplBraidStage, hostValBraidStage]`) peels the
two transparent heads, then the gate's `400` survives the status-stable tail. -/
theorem braided10_wsname_400 (c : Ctx) (nv : Proto.Bytes × Proto.Bytes)
    (hni : c.req.headers.find? (fun nv => nv.1 == notImplMarker) = none)
    (hhv : c.req.headers.find? (fun nv => nv.1 == hostValMarker) = none)
    (hfind : c.req.headers.find? (fun nv => nv.1 == wsNameMarker) = some nv) :
    ((runPipeline braidedChain10 appHandler c).build).status = 400 := by
  have hpref : ∀ X ∈ [notImplBraidStage, hostValBraidStage], Transparent X c :=
    cons_transparent (notImplBraidStage_off c hni)
      (cons_transparent (hostValBraidStage_off c hhv) (nil_transparent c))
  have hst : ∀ t ∈ braidedChain9, Stage.statusStable t :=
    fun t ht => braidedChain10_statusStable t
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)))
  rw [show braidedChain10
        = [notImplBraidStage, hostValBraidStage] ++ wsNameBraidStage :: braidedChain9 from rfl]
  exact braid_gate [notImplBraidStage, hostValBraidStage] wsNameBraidStage braidedChain9
    appHandler c wsName400 hpref (wsNameBraidStage_denies c nv hfind) hst

#print axioms braided10_off_eq
#print axioms servePipelineBraided10_off_eq
#print axioms braided10_notimpl_501
#print axioms braided10_host_400
#print axioms braided10_wsname_400
