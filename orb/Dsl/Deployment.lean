import Dsl.Cfg.Listener
import Dsl.Cfg.Route
import Dsl.Cfg.Middleware
import Dsl.Cfg.Tls
import Dsl.Cfg.TlsServe
import Dsl.Cfg.Upstream

/-!
# Dsl.Deployment — the declarative deployment surface, wired to the deployed serve

The package already proves two composition calculi:

* the **component calculus** (`Dsl.Component`): four primitive shapes, invariant
  preservation composes (`reachable_inv`), and the parallel product preserves the
  conjoined invariant (`prod_preserves`); and
* the **stage/pipeline calculus** (`Reactor.Pipeline`): a request threaded through
  an ordered `List Stage` via `runPipeline`, with the onion-recursion, gate
  short-circuit, gate-status-stability, per-stage byte-effect, and onion-order
  theorems — the deployed reflection of the component calculus (the affine
  `ResponseBuilder` mirrors the linear primitive's acquire→use→release-once).

But the DEPLOYED serve (`Reactor.Deploy.servePipelineFull2` /
`deployStagesFull2` + `Reactor.App.demoApp`) was a pair of hardcoded literals —
nothing *generated* it, so the composable surface and the running server were
disconnected. This file closes that gap declaratively.

## The surface

A `DeploymentConfig` is a product of five DISJOINT dimensions, each its own
structure in its own file (`Dsl/Cfg/*.lean`) so parallel grow lanes extend
disjoint files:

* `listener`   — the accept surface + admission identity/state (`Cfg.ListenerCfg`);
* `routing`    — the route table + default handler + admission-key adapter (`Cfg.RouteCfg`);
* `middleware` — the ORDERED stage chain, the `List Stage` `runPipeline` folds (`Cfg.MiddlewareCfg`);
* `tls`        — the named TLS termination profiles (`Cfg.TlsCfg`);
* `upstream`   — the named upstream pools + LB policy (`Cfg.UpstreamCfg`).

## The generator

`instantiate : DeploymentConfig → (List Stage × AppConfig)` folds the dimensions
into the two values the deployed serve consumes: the middleware chain becomes the
stage-list `runPipeline` folds over, and the listener+routing dimensions fold into
the single `AppConfig` the proven `Reactor.App.handle` router runs. The TLS and
upstream dimensions are the declarative accept/backend surface (terminated at the
IO boundary / driven by `Reactor.ProxyServe`); they do not add stages to a
cleartext deployment's fold.

`Reactor.Deploy` then defines `defaultDeployment : DeploymentConfig` whose
`instantiate` REPRODUCES `deployStagesFull2` + `demoApp` on the nose, and repoints
the serve through `servePipelineOf` — with the byte-identical no-regression
theorem proving the deployed conformance is preserved.
-/

namespace Dsl

open Reactor.Pipeline (Stage Ctx)
open Reactor.App (AppConfig Handler)
open Reactor (Response)

/-- **The declarative deployment surface.** A product of five disjoint dimensions,
each authored in its own `Dsl/Cfg/*.lean` file. This is the single value a
deployment is; `instantiate` turns it into the deployed serve's inputs. -/
structure DeploymentConfig where
  /-- The accept surface + admission identity/state. -/
  listener : Cfg.ListenerCfg
  /-- The route table + default handler + admission-key adapter. -/
  routing : Cfg.RouteCfg
  /-- The ordered middleware chain (the `List Stage` the pipeline folds). -/
  middleware : Cfg.MiddlewareCfg
  /-- The named TLS termination profiles (empty for a cleartext deployment). -/
  tls : Cfg.TlsCfg := {}
  /-- The named upstream pools + LB policy (empty for a no-proxy deployment). -/
  upstream : Cfg.UpstreamCfg := {}

/-- **The generator.** Fold a `DeploymentConfig` into the two values the deployed
serve consumes: the middleware chain (the stage-list `runPipeline` folds) and the
`AppConfig` the proven router runs — its `lid`/`policy` from the listener
dimension, its `routes`/`defaultHandler`/`routeKeyOf` from the routing dimension.
The TLS/upstream dimensions are the IO-boundary accept/backend surface and add no
stages to the pure byte fold. -/
def instantiate (cfg : DeploymentConfig) : List Stage × AppConfig :=
  ( cfg.middleware.chain
  , { routes := cfg.routing.routes
      defaultHandler := cfg.routing.defaultHandler
      lid := cfg.listener.id
      policy := cfg.listener.policy
      routeKeyOf := cfg.routing.routeKeyOf } )

/-- The deployed stage-list the config instantiates to (projection of
`instantiate`). This is exactly the `List Stage` the pipeline calculus consumes. -/
def DeploymentConfig.stages (cfg : DeploymentConfig) : List Stage := (instantiate cfg).1

/-- The `AppConfig` the config instantiates to (projection of `instantiate`). -/
def DeploymentConfig.app (cfg : DeploymentConfig) : AppConfig := (instantiate cfg).2

/-- The pipeline handler derived from an instantiated `AppConfig`: dispatch the
context's request through the proven `Reactor.App.handle` router. This is the
`Ctx → Response` `runPipeline` seeds its builder from — the config-derived twin of
`Reactor.Deploy.appHandler`. -/
def handlerOf (app : AppConfig) : Ctx → Response := fun c => Reactor.App.handle app c.req

/-- `instantiate`'s stage-list projection is definitionally the config's middleware
chain — the ordering the author declared is the fold, unchanged. -/
@[simp] theorem instantiate_stages (cfg : DeploymentConfig) :
    (instantiate cfg).1 = cfg.middleware.chain := rfl

/-- `instantiate`'s app projection reads its `lid`/`policy` from the listener
dimension and its route surface from the routing dimension. -/
@[simp] theorem instantiate_app_routes (cfg : DeploymentConfig) :
    (instantiate cfg).2.routes = cfg.routing.routes := rfl

/-- The instantiated app's admission listener id is the listener dimension's id. -/
@[simp] theorem instantiate_app_lid (cfg : DeploymentConfig) :
    (instantiate cfg).2.lid = cfg.listener.id := rfl

/-! ## The deployed-serve projections — the seams the RUNNING serve reads

`instantiate` folds the byte-pipeline dimensions (middleware + listener + routing)
into the two values the pure `Bytes → Bytes` fold consumes. The remaining three
dimensions — upstream (LB), TLS termination, and the layer-4 accept surface — are
NOT pure-fold data: they are the accept/backend surface the IO-boundary components
read. These three projections are the READ each running component performs, so a
non-default `DeploymentConfig` drives a non-default RUNNING decision:

* `dialChain name` — the LB policy chain the reverse-proxy dial runs
  (`Reactor.ProxyDial.pickWith` / `Reactor.ServeStep.serveStepWith`);
* `serverParamsFor base name` — the `TlsHandshake.ServerParams` the deployed
  handshake terminator (`TlsHandshake.serverStep`) reads, resolved through the
  named TLS profile;
* `l4Listeners` — the layer-4 passthrough bindings the running dataplane binds
  (`crates/dataplane/src/l4.rs`), each carrying its resolved backend pool + mode.
-/

open Proxy (Policy)
open TlsHandshake (ServerParams)

/-- **The LB projection.** The load-balancing policy chain the deployed
reverse-proxy dial runs for a named upstream pool — exactly the value
`Reactor.ProxyDial.pickWith` / `Reactor.ServeStep.serveStepWith` consumes, so the
backend a proxied request reaches is selected by the config-declared `LbPolicy`.
Delegates to the upstream dimension's `dialChain`, so an empty upstream dimension
(a no-proxy deployment) degrades to the default hash policy. -/
def DeploymentConfig.dialChain (cfg : DeploymentConfig) (name : String) : List Policy :=
  cfg.upstream.dialChain name

/-- **The TLS projection.** The `ServerParams` the deployed handshake terminator
reads for a listener terminating with the named profile: resolve the profile
(well-formed only) out of the TLS dimension and override the base terminator's
handshake policy (0-RTT / OCSP / cert pool) through `applyServerParams`. An
unknown / ill-formed name leaves the base terminator unchanged — so a cleartext
deployment (empty TLS dimension) reads the base params verbatim. -/
def DeploymentConfig.serverParamsFor (cfg : DeploymentConfig) (base : ServerParams)
    (name : String) : ServerParams :=
  match cfg.tls.resolveWF name with
  | some p => p.applyServerParams base
  | none   => base

/-- One resolved layer-4 passthrough binding the running dataplane binds: the
bind address the listener accepts on, the named upstream pool the balancer selects
over, the transport spliced, and the resolved backend ids the pool carries. -/
structure L4Binding where
  /-- The `host:port` the L4 listener binds (the `DRORB_L4_LISTEN` value). -/
  bind : String
  /-- The upstream pool the balancer selects over (`Dsl.Cfg.UpstreamPool.name`). -/
  poolName : String
  /-- Raw TCP stream or UDP datagram passthrough. -/
  mode : Cfg.L4Mode
  /-- The backend ids the named pool declares (the fleet the pick chooses among). -/
  backendIds : List Nat
deriving Repr

/-- **The L4 projection.** The layer-4 passthrough bindings a deployment declares:
for the (single) listener carrying an `l4` binding, its bind address, the named
pool, the transport mode, and the pool's resolved backend ids — the value a deploy
step turns into the `DRORB_L4_LISTEN` / `DRORB_PROXY_BACKENDS` the running host
binds. A deployment whose listener carries no `l4` binding projects to `[]`, so a
config-declared L4 listener is bound at deploy time (not just env-gated) and a
config with no L4 listener binds none. -/
def DeploymentConfig.l4Listeners (cfg : DeploymentConfig) : List L4Binding :=
  match cfg.listener.l4 with
  | none   => []
  | some p =>
    let ids := match cfg.upstream.byName p.upstream with
      | some u => u.pool.backends.map (·.id)
      | none   => []
    [ { bind := s!"{cfg.listener.addr}:{cfg.listener.port}"
        poolName := p.upstream
        mode := p.mode
        backendIds := ids } ]

/-- The LB projection is definitionally the upstream dimension's `dialChain`. -/
@[simp] theorem dialChain_eq_upstream (cfg : DeploymentConfig) (name : String) :
    cfg.dialChain name = cfg.upstream.dialChain name := rfl

/-- A deployment whose listener carries no L4 binding projects to no L4 listeners
— the existing (HTTP-only) deployment surface binds no passthrough listener. -/
@[simp] theorem l4Listeners_none (cfg : DeploymentConfig) (h : cfg.listener.l4 = none) :
    cfg.l4Listeners = [] := by simp [DeploymentConfig.l4Listeners, h]

/-- The TLS projection over an empty (or name-missing) TLS dimension is the base
terminator unchanged — a cleartext deployment reads the base handshake params. -/
@[simp] theorem serverParamsFor_none (cfg : DeploymentConfig) (base : ServerParams)
    (name : String) (h : cfg.tls.resolveWF name = none) :
    cfg.serverParamsFor base name = base := by
  simp [DeploymentConfig.serverParamsFor, h]

end Dsl
