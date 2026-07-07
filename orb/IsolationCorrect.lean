import Reactor.Isolation

/-!
# Per-tenant isolation, verified as information-flow non-interference

`Reactor.Isolation` builds the per-tenant capability partition
(`Reactor.Tenant.demoSystem`) over the deployed route table and proves the
resource-level invariants (`Isolation.touched_in_scope`,
`Isolation.no_cross_tenant`). This file states per-tenant isolation as an
**independent specification** and proves the deployed request dispatcher
`Reactor.App.handle` — the exact function `Reactor.serve` invokes to answer a
dispatched request — satisfies it.

## The standard

The property is *tenant confinement* as an information-flow (non-interference)
guarantee. In a multi-tenant serving surface — the tenant-isolation requirement
of NIST SP 800-125 (Full Virtualization Technologies, the multi-tenancy
isolation requirement) formalized through the non-interference model of
Goguen and Meseguer, *Security Policies and Security Models*, IEEE S&P 1982:

  * A request is served from exactly one tenant's resources — here, the handler
    of the route the router selects.
  * The response to a request served under tenant A must be a function of the
    serving tenant's state alone. It must not depend on state outside the
    serving handler: changing configuration that belongs to other tenants /
    other listeners must leave the response unchanged.
  * A resource scoped to tenant A is never also scoped to a distinct tenant B —
    resources are partitioned, so one acquired under A cannot be handed to B.

The two specifications below (`TenantConfined`, `ResourcePartitioned`) are stated
without reference to how a response is computed. Each is discharged against the
deployed object and each is shown to have teeth by an explicit counterexample: a
dispatcher whose response varies with state outside the serving handler fails
`TenantConfined`, and a system that scopes one resource to two tenants fails
`ResourcePartitioned`.
-/

namespace Reactor.IsolationCorrect

open Reactor Reactor.App
open Proto (Bytes Request)

/-! ## Which tenant serves — the observation classification

`servedHandler` names the handler a request is served from: the handler of the
route the real router (`Route.Match.bestMatch`) selects over the effective table.
It fixes the serving tenant's state (the "low" input of the non-interference
statement); it says nothing about how a response is computed. -/

/-- The handler a request is served from under a configuration: the handler of
the route the router selects, or `none` if nothing matches (unreachable for the
deployed table, which always carries a default). -/
def servedHandler (ac : AppConfig) (req : Request) : Option Handler :=
  (Route.Match.bestMatch ac.table (targetSegments req.target)).map (·.handler)

/-! ## Specification 1 — tenant confinement (information flow)

Stated independently of any dispatcher: the response is a function of the serving
handler alone. -/

/-- **Isolation spec (information flow).** A response function `D` is
*tenant-confined* when the response is determined by the serving handler alone:
any two configurations that serve a request from the same handler produce the
same response — regardless of how their other configuration (state outside the
serving tenant) differs. This is non-interference: the response may not depend on
state outside the serving tenant. -/
def TenantConfined (D : AppConfig → Request → Response) : Prop :=
  ∀ (ac₁ ac₂ : AppConfig) (req : Request) (h : Handler),
    servedHandler ac₁ req = some h →
    servedHandler ac₂ req = some h →
    D ac₁ req = D ac₂ req

/-- When a request is served from handler `h`, the deployed dispatcher's response
is exactly `responseOfHandler h`. This ties `handle`'s output to the serving
handler and nothing else. -/
theorem handle_eq_of_served (ac : AppConfig) (req : Request) (h : Handler)
    (hs : servedHandler ac req = some h) :
    App.handle ac req = responseOfReq req h := by
  unfold servedHandler at hs
  cases hb : Route.Match.bestMatch ac.table (targetSegments req.target) with
  | none => rw [hb] at hs; simp at hs
  | some r =>
    rw [hb] at hs
    simp only [Option.map_some'] at hs
    unfold App.handle
    rw [hb]
    exact congrArg (responseOfReq req) (Option.some.inj hs)

/-- **Refinement theorem (information flow).** The deployed request dispatcher
`Reactor.App.handle` — the function `Reactor.serve` invokes to answer a dispatched
request (`Reactor.serve_routes`) — is tenant-confined: its response depends only
on the serving tenant's handler, never on state outside it. -/
theorem handle_tenantConfined : TenantConfined App.handle := by
  intro ac₁ ac₂ req h h1 h2
  rw [handle_eq_of_served ac₁ req h h1, handle_eq_of_served ac₂ req h h2]

/-- The same content lifted to the deployed wire path: on a dispatched request,
`Reactor.serve` emits exactly `serialize (responseOfHandler h)` for the serving
handler `h`. Binds the deployed serving function end to end. -/
theorem serve_eq_of_served (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission) (h : Handler)
    (hsends : sendsOf (reactorSubs input) = [])
    (hsub : reactorSubs input = .dispatch req :: rest)
    (hs : servedHandler demoAppConfig req = some h) :
    serve input = serialize (responseOfReq req h) := by
  rw [serve_routes input req rest hsends hsub, handle_eq_of_served demoAppConfig req h hs]

/-! ### Non-vacuity for Specification 1

A dispatcher whose response varies with configuration outside the serving handler
(here the listener id `lid` — shared infrastructure that can host other tenants)
is *not* tenant-confined. The spec rejects a leaking implementation. -/

/-- A deliberately leaking dispatcher: it serves the routed response but folds the
listener id into its status — a dependence on state outside the serving handler. -/
def leakyDispatch (ac : AppConfig) (req : Request) : Response :=
  let base := App.handle ac req
  { base with status := base.status + ac.lid }

/-- Two configurations agreeing on every route (hence the same effective table,
the same served handler, and the same routed response) but differing in state
outside any served handler: the listener id. -/
def cfgA : AppConfig := { demoApp with lid := 7 }
def cfgB : AppConfig := { demoApp with lid := 9 }

/-- A concrete request. Its serving handler is identical under `cfgA` and `cfgB`
because the two share an effective route table. -/
def reqHealth : Request := { method := "GET".toUTF8.toList, target := "/health".toUTF8.toList }

/-- **Non-vacuity (information flow).** The leaking dispatcher violates the spec:
though `cfgA` and `cfgB` serve the request from the same handler, `leakyDispatch`
returns different responses because it read state outside the serving handler. -/
theorem leakyDispatch_not_tenantConfined : ¬ TenantConfined leakyDispatch := by
  intro hconf
  obtain ⟨r, hbest, _⟩ := App.app_routes_total cfgA reqHealth
  have hservedA : servedHandler cfgA reqHealth = some r.handler := by
    unfold servedHandler; rw [hbest]; rfl
  have hservedB : servedHandler cfgB reqHealth = some r.handler := hservedA
  have heq := hconf cfgA cfgB reqHealth r.handler hservedA hservedB
  have hst : (App.handle cfgA reqHealth).status + cfgA.lid
      = (App.handle cfgB reqHealth).status + cfgB.lid :=
    congrArg Response.status heq
  rw [show cfgA.lid = 7 from rfl, show cfgB.lid = 9 from rfl,
      show App.handle cfgB reqHealth = App.handle cfgA reqHealth from rfl] at hst
  omega

/-! ## Specification 2 — resource partition (no cross-tenant sharing)

The deployed tenant system is `Reactor.Tenant.demoSystem`, an `Isolation.System`
built over the deployed route table `demoAppConfig.table`. -/

/-- **Isolation spec (resource partition).** A tenant system keeps resources
partitioned when no resource lies in two distinct tenants' scopes: a resource
scoped to tenant A is never scoped to a different tenant B. A resource acquired
under A therefore cannot be handed to B. -/
def ResourcePartitioned (s : Isolation.System) : Prop :=
  ∀ (t₁ t₂ : Isolation.TenantId) (res : Isolation.ResourceId),
    t₁ ≠ t₂ → s.scope t₁ res = true → s.scope t₂ res = false

/-- **Refinement theorem (resource partition).** The deployed tenant system
`Reactor.Tenant.demoSystem` (built over `demoAppConfig.table`) is resource
partitioned: its generated per-tenant scopes share no resource. -/
theorem demoSystem_resourcePartitioned :
    ResourcePartitioned Reactor.Tenant.demoSystem :=
  Reactor.Tenant.demoBinding_disjoint

/-- A system that scopes one resource to every tenant — the resource-sharing
violation. -/
def sharedSystem : Isolation.System where
  scope := fun _ _ => true
  owner := fun _ => 0
  touches := fun _ => []
  wf := fun _ _ _ => rfl

/-- **Non-vacuity (resource partition).** A system that hands the same resource to
two tenants fails the spec. -/
theorem sharedSystem_not_partitioned : ¬ ResourcePartitioned sharedSystem := by
  intro h
  have hcontra : sharedSystem.scope 1 0 = false := h 0 1 0 (by decide) rfl
  simp [sharedSystem] at hcontra

end Reactor.IsolationCorrect
