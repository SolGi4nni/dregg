import Dsl.Deployment
import Reactor.App
import Reactor.RouteMiddleware
import RouteAdvanced
import Dsl.Cfg.Upstream

/-!
# `Dsl.Config.Gateway` — the umbrella config-as-data for the full gateway

The flat `Dsl.Config.ParsedConfig` (`Dsl/Config/Parse.lean`) already carries a
single-listener route table and a `host`/`route` virtual-host dimension. THIS file
is the *umbrella* schema that ties a WHOLE multi-vhost gateway together as one data
value: a global block (`on_demand` ask endpoint + `default_sni`) and a list of
virtual hosts, each keyed by a host/SNI pattern, each carrying a per-vhost TLS mode
(`on_demand` vs fixed cert files) and an ordered list of `(matcher → action)` routes.

The action vocabulary is the config-representable gateway surface: a reverse proxy
(with a flush window — `flushIntervalMs = -1` is the SSE streaming mode), a static
site (SPA `root` + `try_files` + `file_server`), a fixed local `respond` (the
custodial 403), and a `redirect`. A route may additionally be gated by HTTP
`basic_auth`.

**Config-as-data law.** This schema is DATA the compiled serve reads; a new route,
host, backend, or body is a new *value*, never a recompile. Only a new middleware
KIND (a new `Action` constructor) touches code.

**Dispatch.** `denote` lowers a `ServeConfig` onto the deployed
`RouteAdvanced.ServerBlock Reactor.App.VHandler` block table — so per-vhost per-route
selection is the PROVEN `RouteAdvanced.dispatch` (host/SNI selection
`route_host_isolation`, method match, `*`/`**` path globs, guards). `Handler.hostGlob
(denote cfg)` is exactly the deployed default handler `denoteVHosts` targets, so this
umbrella plugs into the served path with no new matcher.

**No-regression anchor.** An empty `ServeConfig` (`vhosts = []`) denotes onto a base
deployment verbatim (`denoteOn_empty`) — today's behavior byte-for-byte.
-/

namespace Dsl.Config.Gateway

open Reactor.App (VHandler)

/-! ## The schema (pure data) -/

/-- Per-vhost TLS provisioning mode. `onDemand` is Caddy `on_demand_tls`: the leaf is
minted lazily on first SNI, gated by the global ask endpoint. `certFiles` pins a fixed
leaf certificate + key already on disk. -/
inductive TlsMode where
  | onDemand
  | certFiles (cert key : String)
deriving DecidableEq, Repr, BEq

/-- The global (federation-wide) block: the `on_demand_tls { ask <url> }` endpoint the
minting path consults before issuing a lazy leaf, and the `default_sni` used for a
handshake that arrives with no SNI. Surfaced to the on-demand-TLS / ACME listener
(`askEndpoint` / `defaultSni`); the route dispatch does not read it. -/
structure GlobalCfg where
  onDemandAsk : Option String := none
  defaultSni  : Option String := none
deriving DecidableEq, Repr, BEq

/-- A gateway action — the terminal handler a matched route runs.

* `reverseProxy backend flushIntervalMs` — forward to `backend`; `flushIntervalMs = -1`
  is flush-immediately (the SSE streaming mode), `0` the buffered default.
* `staticSite root tryFiles fileServer` — serve a static site rooted at `root`, with an
  ordered `tryFiles` fallback chain (the SPA `try_files {path} /index.html` rewrite) and
  a `file_server` toggle.
* `respond status body` — answer locally with a fixed status + body (the custodial 403).
* `redirect status location` — a `3xx` + `Location`. -/
inductive Action where
  | reverseProxy (backend : String) (flushIntervalMs : Int)
  | staticSite (root : String) (tryFiles : List String) (fileServer : Bool)
  | respond (status : Nat) (body : String)
  | redirect (status : Nat) (location : String)
deriving DecidableEq, Repr, BEq

/-- A path matcher (the Caddy `path`/prefix subset): an exact single path, a prefix
(trailing `*`), or the SPA catch-all. -/
inductive PathMatch where
  | exact (path : String)
  | prefix (path : String)
  | anyPath
deriving DecidableEq, Repr, BEq

/-- An HTTP `basic_auth` gate: a realm and a `(username, pbkdf2-hash)` credential list.
Each credential's stored value is its AWS-LC PBKDF2-HMAC-SHA256 hash
(`pbkdf2_sha256$<iterations>$<salt_hex>$<dk_hex>`, minted by the `pbkdf2-hash` helper) —
the AUDITED adaptive KDF — verified by `Reactor.RouteMw.basicVerify` via `Crypto.pbkdf2Verify`
(stored iteration count + per-hash CSPRNG salt, constant-time derived-key compare). -/
structure BasicAuth where
  realm : String
  users : List (String × String)
deriving DecidableEq, Repr, BEq

/-- One vhost route: an optional method guard, a path matcher, an optional `basic_auth`
gate, an `encode gzip` toggle, and the terminal action it runs. -/
structure GwRoute where
  method     : Option String := none
  path       : PathMatch
  basicAuth  : Option BasicAuth := none
  encodeGzip : Bool := false
  action     : Action
deriving DecidableEq, Repr, BEq

/-- One virtual host: the host/SNI pattern (`*.rest` ⇒ leading-label wildcard, `*` ⇒
fallback, else exact), its TLS mode, and its ordered routes. -/
structure Vhost where
  host   : String
  tls    : TlsMode
  routes : List GwRoute
deriving DecidableEq, Repr, BEq

/-- The umbrella config: a global block + the vhost list. `vhosts = []` ⇒ the empty
config (no-regression anchor). -/
structure ServeConfig where
  global : GlobalCfg := {}
  vhosts : List Vhost := []
deriving DecidableEq, Repr, BEq

/-- The empty config — denotes to today's behavior (`denoteOn_empty`). -/
def empty : ServeConfig := {}

/-! ## Lowering onto the deployed proven matcher -/

/-- Split a host string into labels, mapping a leading `*` label to the deployed
`HostPat.wild` (RFC 6066 §3 leading-label wildcard), a bare `*` to `anyHost`, else an
exact label list. -/
def hostPatOf (h : String) : RouteAdvanced.HostPat :=
  if h = "*" then .anyHost
  else match h.splitOn "." with
       | "*" :: rest => .wild rest
       | labels      => .exact labels

/-- The non-empty `/`-split path segments. -/
def segsOf (p : String) : List String := (p.splitOn "/").filter (· ≠ "")

/-- Compile a path matcher to a deployed `RouteAdvanced.PathPat`. -/
def pathPatOf : PathMatch → RouteAdvanced.PathPat
  | .exact p  => { segs := (segsOf p).map .lit, globstar := false }
  | .prefix p => { segs := (segsOf p).map .lit, globstar := true }
  | .anyPath  => { segs := [], globstar := true }

/-- Compile the optional method guard to a `RouteAdvanced.MethodPat`. -/
def methodPatOf : Option String → RouteAdvanced.MethodPat
  | none   => .anyMethod
  | some m => .exact m

/-- The deployed `VHandler` an action denotes onto. A reverse proxy (any flush window,
including the SSE `-1`) denotes to the PROVEN `VHandler.proxy` over the health-filtered
`loadedPool`; the backend name + flush window are read host-side (the deployment
surfaces the proxy-vhost hostnames, exactly as `Dsl.Config.vhandlerOfSpec` does). A
static site denotes to the embedded request-aware static handler (`VHandler.static`);
the SPA `root`/`try_files` are read by the static feature lane. `respond`/`redirect`
denote directly to their data-parameterized deployed answers. -/
def actionVHandler : Action → VHandler
  | .reverseProxy _ _  => .proxy Dsl.Cfg.loadedPool
  | .staticSite _ _ _  => .static
  | .respond st body   => .respond st body.toUTF8.toList
  | .redirect st loc   => .redirect st loc.toUTF8.toList

/-- The deployed answer a route runs. A `basic_auth`-gated route wraps its action in the
proven middleware chain (`VHandler.guarded`) at the proven `Reactor.RouteMw.RouteMw.basicAuth`
gate — the REAL `BasicAuth.authenticate` decision (RFC 7617) over the route's realm +
credential store: a valid credential PASSES to the inner action, a bad/missing one is the
realm `401` (`runChain_basic_notoken_401`, `check_basic_challenges` / `check_basic_admits`).
An un-gated route denotes byte-identically to its bare action. -/
def routeVHandler (r : GwRoute) : VHandler :=
  match r.basicAuth with
  | none    => actionVHandler r.action
  | some ba => .guarded [Reactor.RouteMw.RouteMw.basicAuth ba.realm ba.users]
                        (actionVHandler r.action)

/-- Compile one route to the deployed `RouteAdvanced.Route VHandler`. -/
def routeOf (r : GwRoute) : RouteAdvanced.Route VHandler :=
  { method  := methodPatOf r.method
    path    := pathPatOf r.path
    guards  := []
    handler := routeVHandler r }

/-- Compile one vhost to a deployed `RouteAdvanced.ServerBlock VHandler`. -/
def blockOf (v : Vhost) : RouteAdvanced.ServerBlock VHandler :=
  { host := hostPatOf v.host, routes := v.routes.map routeOf }

/-- **Denote the umbrella config onto the deployed virtual-host block table.**
`RouteAdvanced.dispatch (denote cfg)` is the proven host/SNI + method + glob matcher
the deployed `Handler.hostGlob` served path drives. -/
def denote (cfg : ServeConfig) : List (RouteAdvanced.ServerBlock VHandler) :=
  cfg.vhosts.map blockOf

/-- **Wire the config into a base deployment.** A non-empty config REPLACES the base
default handler with the proven host/glob `Handler.hostGlob` over the denoted blocks;
an empty config keeps `base` verbatim. -/
def denoteOn (base : Dsl.DeploymentConfig) (cfg : ServeConfig) : Dsl.DeploymentConfig :=
  match cfg.vhosts with
  | []     => base
  | _ :: _ => { base with
      routing := { base.routing with
        defaultHandler := Reactor.App.Handler.hostGlob (denote cfg) } }

/-! ## Schema-level dispatch (returns the selected `Action`) -/

/-- A schema-level request: pre-split host labels, method, and pre-split path segments —
the same shape `RouteAdvanced.Req` carries for the matcher. -/
structure GwReq where
  host   : List String
  method : String
  segs   : List String
deriving Repr

/-- Does a route match a request? Method + path only (the umbrella carries no header/
query guards at this layer — those stay in the flat `VRouteSpec` dimension). Mirrors
`RouteAdvanced.routeMatches` with `guards = []`. -/
def routeMatches (req : GwReq) (r : GwRoute) : Bool :=
  RouteAdvanced.methodMatch (methodPatOf r.method) req.method
    && RouteAdvanced.pathMatch (pathPatOf r.path) req.segs

/-- Select the first vhost whose host pattern matches the request authority. -/
def selectVhost (cfg : ServeConfig) (req : GwReq) : Option Vhost :=
  cfg.vhosts.find? (fun v => RouteAdvanced.hostMatch (hostPatOf v.host) req.host)

/-- Select the first matching route (host, then first-match path/method). -/
def selectRoute (cfg : ServeConfig) (req : GwReq) : Option GwRoute :=
  match selectVhost cfg req with
  | none   => none
  | some v => v.routes.find? (routeMatches req)

/-- **Schema-level dispatch:** the `Action` a request runs (host → vhost → first route). -/
def dispatchAction (cfg : ServeConfig) (req : GwReq) : Option Action :=
  (selectRoute cfg req).map (·.action)

/-! ## The deployed dispatch equals the schema dispatch

`RouteAdvanced.dispatch` over the denoted blocks selects EXACTLY the route
`selectRoute` picks — the proven matcher fires the schema-declared route. -/

/-- `find?` commutes with `map` (first-match is preserved by a pointwise transform). -/
theorem find?_map_local {α β} (f : α → β) (p : β → Bool) :
    ∀ l : List α, (l.map f).find? p = (l.find? (fun a => p (f a))).map f
  | []     => rfl
  | a :: t => by
    simp only [List.map_cons, List.find?_cons]
    by_cases h : p (f a)
    · simp [h]
    · simp only [h]; exact find?_map_local f p t

/-- The deployed `routeMatches` on a compiled route equals the schema `routeMatches`
(the compiled `guards` list is empty, so it contributes `true`). -/
theorem routeMatches_routeOf (req : GwReq) (r : GwRoute) :
    RouteAdvanced.routeMatches
      { host := req.host, method := req.method, segs := req.segs, headers := [], query := [] }
      (routeOf r)
      = routeMatches req r := by
  simp [RouteAdvanced.routeMatches, routeOf, routeMatches]

/-- The deployed host predicate on a compiled block equals the schema host predicate. -/
theorem hostMatch_blockOf (host : List String) (v : Vhost) :
    RouteAdvanced.hostMatch (blockOf v).host host
      = RouteAdvanced.hostMatch (hostPatOf v.host) host := by
  simp [blockOf]

/-- **The proven dispatch fires the schema-selected route.** For any request,
`RouteAdvanced.dispatch` over the denoted blocks returns exactly `selectRoute`'s route,
compiled — so the deployed served path (`Handler.hostGlob`) runs precisely the vhost/
route the umbrella config declares. -/
theorem dispatch_denote_eq (cfg : ServeConfig) (req : GwReq) :
    RouteAdvanced.dispatch (denote cfg)
        { host := req.host, method := req.method, segs := req.segs, headers := [], query := [] }
      = (selectRoute cfg req).map routeOf := by
  let R : RouteAdvanced.Req :=
    { host := req.host, method := req.method, segs := req.segs, headers := [], query := [] }
  show RouteAdvanced.dispatch (denote cfg) R = _
  unfold RouteAdvanced.dispatch RouteAdvanced.selectBlock denote selectRoute selectVhost
  rw [find?_map_local blockOf (fun b => RouteAdvanced.hostMatch b.host R.host)]
  simp only [hostMatch_blockOf]
  cases hv : cfg.vhosts.find?
      (fun v => RouteAdvanced.hostMatch (hostPatOf v.host) req.host) with
  | none   => simp
  | some v =>
    simp only [Option.map_some]
    show (blockOf v).routes.find? (RouteAdvanced.routeMatches R) = _
    unfold blockOf
    simp only []
    rw [find?_map_local routeOf (RouteAdvanced.routeMatches R)]
    have : (fun a => RouteAdvanced.routeMatches R (routeOf a))
         = (fun a => routeMatches req a) := by
      funext a; exact routeMatches_routeOf req a
    rw [this]

/-- **Corollary — the deployed handler is the schema action's handler.** The `VHandler`
the proven dispatch runs is exactly `routeVHandler` of the schema-selected route. -/
theorem dispatch_handler_eq (cfg : ServeConfig) (req : GwReq) :
    (RouteAdvanced.dispatch (denote cfg)
        { host := req.host, method := req.method, segs := req.segs, headers := [], query := [] }).map
        (·.handler)
      = (selectRoute cfg req).map (fun r => routeVHandler r) := by
  rw [dispatch_denote_eq]
  cases selectRoute cfg req with
  | none   => rfl
  | some r => rfl

/-! ## No-regression anchor -/

/-- **An empty config is a no-op.** `vhosts = []` ⇒ the base deployment is returned
verbatim — today's behavior, byte-for-byte. -/
theorem denoteOn_empty (base : Dsl.DeploymentConfig) (cfg : ServeConfig)
    (h : cfg.vhosts = []) : denoteOn base cfg = base := by
  unfold denoteOn; rw [h]

/-- The empty config denotes to no vhost blocks. -/
theorem denote_empty : denote empty = [] := rfl

/-- The empty config dispatches nothing (falls through to the base default). -/
theorem dispatchAction_empty (req : GwReq) : dispatchAction empty req = none := rfl

/-! ## Projections surfaced to the on-demand-TLS / ACME listener -/

/-- The hosts whose vhost requests on-demand TLS (surfaced to the minting path). -/
def onDemandHosts (cfg : ServeConfig) : List String :=
  (cfg.vhosts.filter (fun v => v.tls == TlsMode.onDemand)).map (·.host)

/-- The global on-demand ask endpoint. -/
def askEndpoint (cfg : ServeConfig) : Option String := cfg.global.onDemandAsk

/-- The global default SNI. -/
def defaultSni (cfg : ServeConfig) : Option String := cfg.global.defaultSni

/-! ## The replicated dregg.net config value

The full `dregg.net` gateway as ONE data value — three virtual hosts:

* `*.apps.example.test` — on-demand TLS, everything reverse-proxied to the gateway;
* `portal.example.test` — on-demand TLS, a static SPA with `/api` proxied,
  `/observability` streamed (SSE = proxy flush `-1`), and `/api/op` custodially `403`;
* `admin.example.test` — on-demand TLS, `basic_auth`-gated `/admin` proxied to
  the discord-bot backend.

Backends are the docker services `gateway:8080` and `backend-admin:8080`.
More-specific routes precede prefixes (`/api/op` before `/api`) — first-match order. -/
def dreggNet : ServeConfig :=
  { global :=
      { onDemandAsk := some "http://localhost:9100/ask"
        defaultSni  := some "portal.example.test" }
    vhosts :=
      [ -- *.apps.example.test : on-demand TLS, proxy everything to the gateway fleet.
        { host := "*.apps.example.test"
          tls  := .onDemand
          routes :=
            [ { path := .anyPath, action := .reverseProxy "gateway:8080" 0 } ] }
        -- portal.example.test : static SPA + /api proxy + /observability SSE + /api/op 403.
      , { host := "portal.example.test"
          tls  := .onDemand
          routes :=
            [ { path := .exact "/api/op",  action := .respond 403 "forbidden" }
            , { path := .prefix "/api",    action := .reverseProxy "gateway:8080" 0 }
            , { path := .prefix "/observability",
                action := .reverseProxy "gateway:8080" (-1) }  -- SSE: flush immediately
            , { path := .anyPath,
                action := .staticSite "/srv/site" ["/index.html"] true } ] }
        -- admin.example.test : basic_auth gate + /admin proxy to the bot.
      , { host := "admin.example.test"
          tls  := .onDemand
          routes :=
            [ { path      := .prefix "/admin"
                basicAuth := some { realm := "dreggnet"
                                    users := [("simbi",
                                      "pbkdf2_sha256$600000$22150c3e3b96b36832bc71daa59a0d04$67e05eb3ebcf2c1398eac84267f366d644bf2d58fe6385cccad6fb2d1ea967db")] }
                action    := .reverseProxy "backend-admin:8080" 0 } ] } ] }

/-! ## The routing demonstration (build-gated `#guard` runs)

Each `#guard` RUNS the compiled schema dispatch on a concrete request and FAILS THE
BUILD if the wrong action fires — the "curl the route → the right handler" gate,
checked at compile time (no axioms). -/

-- `foo.apps.example.test /anything` → proxy the gateway (wildcard host).
#guard dispatchAction dreggNet ⟨["foo","dregg","works"], "GET", ["anything"]⟩ == some (Action.reverseProxy "gateway:8080" 0)
-- `portal.example.test /api/op` → custodial 403 (exact, wins over the `/api` prefix).
#guard dispatchAction dreggNet ⟨["portal","dregg","studio"], "POST", ["api","op"]⟩ == some (Action.respond 403 "forbidden")
-- `portal.example.test /api/lease` → proxy the gateway.
#guard dispatchAction dreggNet ⟨["portal","dregg","studio"], "GET", ["api","lease"]⟩ == some (Action.reverseProxy "gateway:8080" 0)
-- `portal.example.test /observability/events` → SSE stream (proxy, flush `-1`).
#guard dispatchAction dreggNet ⟨["portal","dregg","studio"], "GET", ["observability","events"]⟩ == some (Action.reverseProxy "gateway:8080" (-1))
-- `portal.example.test /` → the static SPA.
#guard dispatchAction dreggNet ⟨["portal","dregg","studio"], "GET", []⟩ == some (Action.staticSite "/srv/site" ["/index.html"] true)
-- `portal.example.test /app/dashboard` (deep SPA path) → the static SPA (catch-all).
#guard dispatchAction dreggNet ⟨["portal","dregg","studio"], "GET", ["app","dashboard"]⟩ == some (Action.staticSite "/srv/site" ["/index.html"] true)
-- `admin.example.test /admin/panel` → proxy the bot (behind the basic_auth gate).
#guard dispatchAction dreggNet ⟨["dreggnet","fg-goose","online"], "GET", ["admin","panel"]⟩ == some (Action.reverseProxy "backend-admin:8080" 0)
-- The `/admin` route carries the `basic_auth` gate (the proven `RouteMw.basicAuth` — valid cred passes, else realm 401).
#guard (selectRoute dreggNet ⟨["dreggnet","fg-goose","online"], "GET", ["admin"]⟩).map (fun r => r.basicAuth.isSome) == some true
-- A host that matches NO vhost falls through (→ the base default, not a vhost route).
#guard dispatchAction dreggNet ⟨["evil","example","com"], "GET", []⟩ == none
-- The bare apex `apps.example.test` (no leading label) does NOT match `*.apps.example.test`.
#guard dispatchAction dreggNet ⟨["dregg","works"], "GET", []⟩ == none
-- On-demand-TLS projection: all three vhosts request on-demand TLS.
#guard onDemandHosts dreggNet == ["*.apps.example.test", "portal.example.test", "admin.example.test"]
-- The global ask endpoint + default SNI are surfaced.
#guard askEndpoint dreggNet == some "http://localhost:9100/ask"
#guard defaultSni dreggNet == some "portal.example.test"

/-! Printable views (a real run of the compiled dispatch). -/

/-- A readable tag for the selected deployed handler. -/
def handlerTag : VHandler → String
  | .respond _ _  => "respond"
  | .proxy _      => "proxy"
  | .redirect _ _ => "redirect"
  | .static       => "static"
  | .guarded _ _  => "guarded"

#eval (dispatchAction dreggNet { host := ["a","dregg","works"], method := "GET", segs := ["x"] })
#eval (selectRoute dreggNet { host := ["portal","dregg","studio"], method := "GET", segs := [] }).map
        (fun r => handlerTag (routeVHandler r))

end Dsl.Config.Gateway
