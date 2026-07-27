import Reactor.ProxyServe
import Proxy.MaxConn
import Proxy.Health
import Proxy.Breaker
import Proxy.Timeout
import Dsl.Component

/-!
# Dsl.Cfg.Upstreams — the upstream / load-balancing dimension of a deployment

A reverse-proxy deployment declares **named upstream pools**: a set of backend
members, the load-balancing policy that spreads requests across the healthy
members, and the operational config (active health checking, circuit breaking,
per-request timeout budgets, per-member connection caps) that decides which
members are eligible at selection time. A route then binds to a pool *by name*.

This file owns that whole dimension as a declarative surface, and — crucially —
compiles it into the values the PROVEN load balancer already consumes, so the
config never re-implements selection:

  * a pool's members compile to `Proxy.Backend`s (weight, backup→tier, live
    health/in-flight inputs) — the snapshot the selection algebra reads;
  * a pool's policy compiles to the real `Proxy.Policy` chain (`A else B`);
  * a pool compiles to a `Reactor.Proxy.ProxyPool`, the exact value a
    `Reactor.App.Handler.proxy` route carries and `Reactor.ProxyServe` dials;
  * per-member caps compile to a `Proxy.CapTable`, honoured by the proven
    capped selector (`Proxy.selectChainCapped`).

Because the compiled artefacts are the real ones, every selection guarantee is
*inherited*, not re-proved: `compile_selects_eligible` transports
`Proxy.selectChain_eligible`, `compile_backup_only_when_primaries_out` transports
the best-tier fallback theorem, and `bound_route_connects` transports the running
`Reactor.ProxyServe.proxy_route_connects` seam — a route bound to a named pool
routes, through the reactor, to exactly the backend the proven algebra chose.

The active-health (`Proxy.Health`) and circuit-breaker (`Proxy.Breaker`) machines
are the two labelled transition systems that produce a member's live eligibility.
Modelled as `Dsl.Component`s and composed with `Dsl.Component.prod`, they exhibit
the per-upstream verdict machine whose conjoined well-formedness invariant is
preserved on every reachable state (`verdictMachine_wf`) — the component calculus
applied to this dimension, not restated.

`instantiate` (`Dsl.Deployment`) can now RESOLVE a route's named-upstream binding:
`Config.resolveHandler` maps a pool name to the compiled `Handler.proxy`, so the
routing table need not embed a `ProxyPool` literal — the pool is defined once, in
this dimension, and referenced by name.
-/

namespace Dsl.Cfg.Upstreams

open Proxy (Backend Status Policy Ctx)
open Reactor (RingSubmission)
open Reactor.Proxy (ProxyPool chooseUpstream targetedUpstream addrOf)
open Reactor.App (AppConfig Handler targetSegments)

/-! ## Load-balancing policy selection -/

/-- The load-balancing policy a pool selects with. Each maps to a PROVEN
`Proxy.Policy`; the hash policies (`ipHash`/`sticky`/`rendezvous`) are the same
rendezvous-hash selector differing only in what feeds the affinity `Ctx.key`
(client address, session cookie, or a caller-chosen key) — a host input, honoured
by the selector unchanged. -/
inductive LbPolicy where
  /-- Weighted round-robin over the tier pool (`Proxy.Wrr`). -/
  | roundRobin
  /-- Fewest in-flight connections. -/
  | leastConn
  /-- Fewest in-flight connections per unit weight. -/
  | weightedLeastConn
  /-- Rendezvous hashing keyed on the client address hash. -/
  | ipHash
  /-- Rendezvous hashing keyed on a session cookie / sticky key. -/
  | sticky
  /-- Rendezvous hashing on a caller-supplied key. -/
  | rendezvous
deriving DecidableEq, Repr

/-- The proven selector a policy chooses. -/
def LbPolicy.toProxy : LbPolicy → Policy
  | .roundRobin        => .weightedRoundRobin
  | .leastConn         => .leastConnections
  | .weightedLeastConn => .weightedLeastConnections
  | .ipHash            => .rendezvousHash
  | .sticky            => .rendezvousHash
  | .rendezvous        => .rendezvousHash

/-! ## Operational config: active health, breaker, timeouts -/

/-- Active health-check config. `rise`/`fall` are the exact consecutive-streak
thresholds of the `Proxy.Health` hysteresis machine; `intervalMs`/`path` describe
HOW the host probes (timer + probe target) and are consumed at the IO boundary,
not by pure selection. -/
structure HealthCfg where
  /-- Consecutive passes to bring a down member up (`Proxy.HealthGate.rise`). -/
  rise : Nat := 2
  /-- Consecutive failures to take an up member down (`Proxy.HealthGate.fall`). -/
  fall : Nat := 3
  /-- Probe interval in milliseconds (host timer input). -/
  intervalMs : Nat := 2000
  /-- Probe request target. -/
  path : String := "/healthz"
deriving Repr

/-- The proven hysteresis gate this config drives. -/
def HealthCfg.toGate (h : HealthCfg) : Proxy.HealthGate := ⟨h.rise, h.fall⟩

/-- Circuit-breaker config. `threshold`/`cooldownMs` are the exact parameters of
the `Proxy.Breaker` FSM. -/
structure BreakerCfg where
  /-- Consecutive failures that trip a closed breaker open. -/
  threshold : Nat := 5
  /-- Milliseconds an open breaker waits before admitting a half-open probe. -/
  cooldownMs : Nat := 30000
deriving Repr

/-- The proven breaker config this drives. -/
def BreakerCfg.toBreaker (b : BreakerCfg) : Proxy.Breaker.BreakerCfg :=
  ⟨b.threshold, b.cooldownMs⟩

/-- Per-request timeout config: one budget per outbound phase. Mirrors
`Proxy.Timeout.Budgets`; the request deadline is their sum. -/
structure TimeoutCfg where
  resolveMs : Nat := 200
  connectMs : Nat := 1000
  tlsMs : Nat := 1000
  requestWriteMs : Nat := 1000
  responseFirstByteMs : Nat := 5000
  bodyMs : Nat := 30000
deriving Repr

/-- The proven per-phase budgets this config drives. -/
def TimeoutCfg.toBudgets (t : TimeoutCfg) : Proxy.Timeout.Budgets :=
  { resolve := t.resolveMs, connect := t.connectMs, tls := t.tlsMs,
    requestWrite := t.requestWriteMs, responseFirstByte := t.responseFirstByteMs,
    body := t.bodyMs }

/-! ## Members and pools -/

/-- One upstream member. `weight` feeds the weighted policies; `maxConn` is the
per-member connection cap (`Proxy.CapTable`, `none` = unlimited); `backup` places
the member in the first backup tier (tier 1) instead of the primary tier (tier 0);
`addr` is the dial address the host maps the member's stable `id` to. -/
structure Member where
  /-- Stable member identity (selection-ring identity). -/
  id : Nat
  /-- Relative weight (weighted policies); normalized to ≥ 1 at compile. -/
  weight : Nat := 1
  /-- Per-member concurrent-connection cap (`none` = unlimited). -/
  maxConn : Option Nat := none
  /-- Place in the backup tier (used only when no primary is eligible). -/
  backup : Bool := false
  /-- Dial address (host maps `id` → socket; identity travels as `id`). -/
  addr : String := ""
deriving Repr

/-- One named upstream pool: its members, the LB policy (with an optional
fallback policy forming the `A else B` chain), and the operational config. -/
structure Pool where
  /-- The pool name a route binds to. -/
  name : String
  /-- The backend members. -/
  members : List Member
  /-- The primary LB policy. -/
  policy : LbPolicy := .roundRobin
  /-- Optional fallback policy tried when the primary selects nothing. -/
  fallback : Option LbPolicy := none
  /-- Active health-check config. -/
  health : HealthCfg := {}
  /-- Circuit-breaker config. -/
  breaker : BreakerCfg := {}
  /-- Per-request timeout budgets. -/
  timeout : TimeoutCfg := {}
deriving Repr

/-- The upstream dimension: the named pools a deployment offers. Empty for a
deployment with no reverse-proxy routes. -/
structure Config where
  /-- The named upstream pools. -/
  pools : List Pool := []
deriving Repr

/-! ## Compilation to the proven load balancer

The declarative surface compiles to the exact artefacts `Proxy.Balance` /
`Reactor.Proxy` already reason about. `up`/`load` are the LIVE inputs a member's
health machine and connection accounting supply per request; the pure config
snapshot is everything else. -/

/-- Compile one member to a `Proxy.Backend` under live health `up` and in-flight
`load`. Weight is normalized to ≥ 1 (the loader invariant the WRR/weighted-least
totality theorems assume); `backup` becomes tier 1, primaries tier 0. -/
def Member.toBackend (up : Nat → Bool) (load : Nat → Nat) (m : Member) : Backend :=
  { id := m.id, weight := max 1 m.weight, conns := load m.id,
    tier := if m.backup then 1 else 0, healthy := up m.id, status := .active }

/-- The proven policy chain a pool selects with: the primary policy, then the
optional fallback (an `A else B` chain the proven `Proxy.selectChain` folds). -/
def Pool.policies (p : Pool) : List Policy :=
  match p.fallback with
  | none   => [p.policy.toProxy]
  | some q => [p.policy.toProxy, q.toProxy]

/-- Compile a pool to a `Reactor.Proxy.ProxyPool` under live `up`/`load` — the
exact value a `Handler.proxy` route carries and `Reactor.ProxyServe` dials. -/
def Pool.compileLive (up : Nat → Bool) (load : Nat → Nat) (p : Pool) : ProxyPool :=
  { policies := p.policies, backends := p.members.map (Member.toBackend up load) }

/-- The config-snapshot pool: every member optimistically up with no in-flight
load (the fresh, pre-traffic snapshot). Live verdicts refine it per request. -/
def Pool.compile (p : Pool) : ProxyPool :=
  p.compileLive (fun _ => true) (fun _ => 0)

/-- The per-member connection-cap table a pool declares. -/
def Pool.capTable (p : Pool) : Proxy.CapTable :=
  fun id => (p.members.find? (fun m => m.id == id)).bind (·.maxConn)

/-- The cap-honouring selection over a pool: the proven capped selector
(`Proxy.selectChainCapped`) over the compiled backends and the declared caps. -/
def Pool.pickCapped (up : Nat → Bool) (load : Nat → Nat) (ctx : Ctx) (p : Pool) :
    Option Backend :=
  Proxy.selectChainCapped p.policies ctx p.capTable (p.compileLive up load).backends

/-! ## Inherited selection guarantees (not re-proved) -/

/-- **A compiled pool's LB is the proven one.** Any backend the compiled pool
selects is an eligible member of the compiled pool sitting in the best nonempty
tier — `Proxy.selectChain_eligible` transported through the compile, never a
config-side selection. -/
theorem compile_selects_eligible (up : Nat → Bool) (load : Nat → Nat) (p : Pool)
    (ctx : Ctx) {b : Backend}
    (h : chooseUpstream (p.compileLive up load) ctx = some b) :
    b ∈ (p.compileLive up load).backends ∧ b.eligible = true
      ∧ Proxy.bestTier (p.compileLive up load).backends = some b.tier := by
  unfold chooseUpstream at h
  exact Proxy.selectChain_eligible h

/-- **Backup members are used only under failover.** A selected backend's tier is
no greater than any eligible member's — so a backup-tier member (tier 1) is chosen
only when no primary (tier 0) is eligible. The best-tier fallback theorem
transported through the compile. -/
theorem compile_backup_only_when_primaries_out (up : Nat → Bool) (load : Nat → Nat)
    (p : Pool) (ctx : Ctx) {b : Backend}
    (h : chooseUpstream (p.compileLive up load) ctx = some b) :
    ∀ c ∈ (p.compileLive up load).backends, c.eligible = true → b.tier ≤ c.tier := by
  have hbt := (compile_selects_eligible up load p ctx h).2.2
  intro c hc hce
  exact Proxy.minTier_le hbt c (Proxy.mem_eligibleOf.mpr ⟨hc, hce⟩)

/-- **The declared cap binds.** A backend the cap-honouring selection picks is
strictly below its configured `maxConn` — `Proxy.selectChainCapped_under_cap`
transported through the compile. -/
theorem pickCapped_under_cap (up : Nat → Bool) (load : Nat → Nat) (ctx : Ctx)
    (p : Pool) {b : Backend} (h : p.pickCapped up load ctx = some b) :
    ∀ m, p.capTable b.id = some m → b.conns < m := by
  unfold Pool.pickCapped at h
  exact Proxy.selectChainCapped_under_cap h

/-- The cap-honouring selection still only picks eligible members that are under
their cap — the cap refines the eligible set, never widens it. -/
theorem pickCapped_eligible (up : Nat → Bool) (load : Nat → Nat) (ctx : Ctx)
    (p : Pool) {b : Backend} (h : p.pickCapped up load ctx = some b) :
    b ∈ (p.compileLive up load).backends ∧ b.eligible = true
      ∧ Proxy.underCap p.capTable b = true := by
  unfold Pool.pickCapped Proxy.selectChainCapped at h
  have hs := Proxy.selectChain_eligible h
  have hm := Proxy.mem_capPool.mp hs.1
  exact ⟨hm.1, hs.2.1, hm.2⟩

/-! ## Per-route upstream binding (the proxy-dial wiring) -/

/-- A route's declarative binding: a match pattern plus the NAME of the upstream
pool it forwards to. This is the surface a routing table references instead of
embedding a `ProxyPool` literal. -/
structure RouteBinding where
  /-- The route match pattern. -/
  pat : Route.Match.Pat
  /-- The name of the upstream pool this route forwards to. -/
  upstream : String
deriving Repr

/-- Look up a pool by name. -/
def Config.find? (cfg : Config) (name : String) : Option Pool :=
  cfg.pools.find? (fun p => p.name == name)

/-- Resolve a named upstream to the handler a routing table serves: the compiled
`Handler.proxy` when the pool exists, else a `502` (an unresolved binding is
surfaced, never silently dropped). This is the seam `instantiate` calls to turn a
named binding into a real proxy handler. -/
def Config.resolveHandler (cfg : Config) (name : String) : Handler :=
  match cfg.find? name with
  | some pool => Handler.proxy pool.compile
  | none      => Handler.static 502 "no such upstream".toUTF8.toList

/-- Resolve a whole route binding to a real `Route.Match.Route Handler`. -/
def Config.resolveRoute (cfg : Config) (rb : RouteBinding) :
    Route.Match.Route Handler :=
  ⟨rb.pat, cfg.resolveHandler rb.upstream⟩

/-- A resolved binding to an existing pool is exactly the compiled proxy handler. -/
theorem resolveHandler_proxy (cfg : Config) (name : String) {pool : Pool}
    (h : cfg.find? name = some pool) :
    cfg.resolveHandler name = Handler.proxy pool.compile := by
  simp only [Config.resolveHandler, h]

/-- **The proxy-dial wiring.** For a request whose matched route is bound to a
named pool (`r.handler = cfg.resolveHandler name`, `cfg.find? name = some pool`)
and whose compiled pool the PROVEN `Proxy.selectChain` picks backend `b` from, the
running reactor path emits a `connectUpstream` targeting exactly `addrOf b`, and
`b` is a healthy, active member of the compiled pool in the best nonempty tier.

This is `Reactor.ProxyServe.proxy_route_connects` — App routing composed with
`Proxy.selectChain_eligible` — transported through the name resolution. The named
binding adds a lookup in front of the proven seam and weakens nothing: a router
that ignored `bestMatch`, or a selector that returned an ineligible backend, would
each still break a conjunct. -/
theorem bound_route_connects (cfg : Config) (ac : AppConfig) (ctx : Ctx)
    (req : Proto.Request) (rest : List RingSubmission) (name : String) {pool : Pool}
    (r : Route.Match.Route Handler) {b : Backend}
    (hfind : cfg.find? name = some pool)
    (hbest : Route.Match.bestMatch ac.table (targetSegments req.target) = some r)
    (hpx : r.handler = cfg.resolveHandler name)
    (hsel : chooseUpstream pool.compile ctx = some b) :
    targetedUpstream
        (Reactor.ProxyServe.serveProxyOn ac ctx (RingSubmission.dispatch req :: rest))
        = some (addrOf b)
      ∧ b ∈ pool.compile.backends
      ∧ b.eligible = true
      ∧ Proxy.bestTier pool.compile.backends = some b.tier :=
  Reactor.ProxyServe.proxy_route_connects ac ctx req rest pool.compile r hbest
    (hpx.trans (resolveHandler_proxy cfg name hfind)) hsel

/-! ## The per-upstream verdict machine, via the component calculus

A member's live eligibility is produced by two labelled transition systems: the
active-health hysteresis machine and the circuit breaker. Each is a `Component`;
their parallel product is the per-upstream verdict machine, whose conjoined
invariant is preserved on every reachable state — the composition calculus applied
to this dimension. -/

/-- The active-health machine as a component: state is the hysteresis machine,
inputs are probe outcomes, the output is the up/down verdict, and the invariant is
that at most one consecutive streak is nonzero (each probe resets the opposite
streak). -/
def healthComponent (g : Proxy.HealthGate) : Dsl.Component where
  State := Proxy.HealthState
  Input := Proxy.Probe
  Output := Bool
  inv := fun s => s.passStreak = 0 ∨ s.failStreak = 0
  init := Proxy.HealthState.initUp
  step := fun s p => (Proxy.hstep g s p, [(Proxy.hstep g s p).up])
  init_wf := Or.inl rfl
  step_wf := by
    intro s p _
    cases p with
    | pass =>
      simp only [Proxy.hstep]
      by_cases hup : s.up = true
      · simp [hup]
      · by_cases hr : g.rise ≤ s.passStreak + 1 <;> simp [hup, hr]
    | fail =>
      simp only [Proxy.hstep]
      by_cases hup : s.up = true
      · by_cases hf : g.fall ≤ s.failStreak + 1 <;> simp [hup, hf]
      · simp [hup]

/-- The circuit breaker as a component: state is the breaker FSM, inputs are
breaker events, outputs are attempt/reject, and the invariant is that a probe is
in flight only in the half-open phase (the breaker admits at most one trial probe,
and only while half-open). -/
def breakerComponent (cfg : Proxy.Breaker.BreakerCfg) : Dsl.Component where
  State := Proxy.Breaker.BState
  Input := Proxy.Breaker.BEvent
  Output := Proxy.Breaker.BOutput
  inv := fun s => s.probeInFlight = true → s.phase = .halfOpen
  init := Proxy.Breaker.BState.init
  step := Proxy.Breaker.step cfg
  init_wf := by intro h; simp [Proxy.Breaker.BState.init] at h
  step_wf := by
    intro s e hinv
    cases e with
    | tick now =>
      simp only [Proxy.Breaker.step]
      cases hph : s.phase <;> simp_all <;>
        (by_cases hc : cfg.cooldown ≤ now - s.openedAt <;> simp [hc, hph])
    | probe =>
      simp only [Proxy.Breaker.step]
      cases hph : s.phase <;> simp_all
      by_cases hpf : s.probeInFlight = true <;> simp_all
    | success =>
      simp only [Proxy.Breaker.step]
      cases hph : s.phase <;> simp_all
    | failure =>
      simp only [Proxy.Breaker.step]
      cases hph : s.phase <;> simp_all
      by_cases hc : cfg.threshold ≤ s.failures + 1 <;> simp [hc]

/-- **The per-upstream verdict machine.** The parallel product of the health and
breaker components: a member's eligibility is decided by both machines at once. -/
def verdictMachine (g : Proxy.HealthGate) (cfg : Proxy.Breaker.BreakerCfg) :
    Dsl.Component :=
  (healthComponent g).prod (breakerComponent cfg)

/-- **The verdict machine is well-formed by construction.** Every reachable state
of the composed health×breaker machine satisfies the conjoined invariant — at most
one health streak is nonzero AND a breaker probe is in flight only when half-open —
with no bespoke induction: `Dsl.Component.reachable_inv` over `prod`. The component
calculus discharges the whole-dimension well-formedness. -/
theorem verdictMachine_wf (g : Proxy.HealthGate) (cfg : Proxy.Breaker.BreakerCfg)
    {s : (verdictMachine g cfg).State}
    (h : (verdictMachine g cfg).Reachable s) :
    (s.1.passStreak = 0 ∨ s.1.failStreak = 0)
      ∧ (s.2.probeInFlight = true → s.2.phase = .halfOpen) :=
  (verdictMachine g cfg).reachable_inv h

/-- The product step preserves the conjoined invariant — `prod_preserves`
instantiated at this dimension's two machines. -/
theorem verdictMachine_step_preserves (g : Proxy.HealthGate)
    (cfg : Proxy.Breaker.BreakerCfg) (s : (verdictMachine g cfg).State)
    (i : (verdictMachine g cfg).Input) (h : (verdictMachine g cfg).inv s) :
    (verdictMachine g cfg).inv ((verdictMachine g cfg).step s i).1 :=
  Dsl.prod_preserves (healthComponent g) (breakerComponent cfg) s i h

/-! ## A concrete deployment the hardcoded serve could not express

`api`: a two-tier pool. The primary tier carries a weighted member (id 0, weight 3,
capped at 100 connections) and a plain member (id 1); a backup member (id 2) sits in
tier 1. Least-connections is the policy, weighted round-robin the fallback. Active
health, a circuit breaker, and timeout budgets are declared. A route binds to it by
name. None of this is expressible as the static cleartext serve's fixed stage list +
literal static routes — there is no upstream, no LB, no health/breaker, no failover
tier in that shape. -/

/-- The primary/backup weighted pool. -/
def apiPool : Pool :=
  { name := "api"
  , members :=
      [ { id := 0, weight := 3, maxConn := some 100 }
      , { id := 1, weight := 1 }
      , { id := 2, backup := true } ]
  , policy := .leastConn
  , fallback := some .roundRobin
  , health := { rise := 2, fall := 3, intervalMs := 1000 }
  , breaker := { threshold := 5, cooldownMs := 30000 } }

/-- The single-pool deployment upstream dimension. -/
def apiCfg : Config := { pools := [apiPool] }

/-- A trivial selection context (least-connections consults neither round nor key). -/
def ctx0 : Ctx := ⟨0, 0, fun _ _ => 0⟩

/-- The pool is found by name. -/
theorem apiCfg_find : apiCfg.find? "api" = some apiPool := by rfl

/-- **Steady state: the primary is chosen.** With every member up and idle,
least-connections over the primary tier picks the first primary (id 0). -/
theorem api_steady_picks_primary :
    (chooseUpstream apiPool.compile ctx0).map Backend.id = some 0 := by decide

/-- **Failover: the backup engages only when both primaries are down.** Under a
live health verdict that fails ids 0 and 1, the eligible set is the backup tier
alone, so the proven selector dials the backup member (id 2) — a tier failover the
static serve has no shape for. -/
theorem api_failover_picks_backup :
    (chooseUpstream (apiPool.compileLive (fun id => id == 2) (fun _ => 0)) ctx0).map
      Backend.id = some 2 := by decide

/-- **The declared cap binds.** When member 0 is at its 100-connection cap
(`load 0 = 100`), the cap-honouring selection excludes it and moves to the
under-cap member (id 1) — the reference "capped-out backends receive no new work"
rule, enforced by the proven capped selector on the declared cap. -/
theorem api_cap_excludes_full :
    (apiPool.pickCapped (fun _ => true) (fun id => if id == 0 then 100 else 0) ctx0).map
      Backend.id = some 1 := by decide

/-- **A route bound by name resolves to the compiled proxy handler**, ready for
`bestMatch` to select and `Reactor.ProxyServe` to dial. This is the value
`instantiate` welds into the routing table for a `RouteBinding ⟨pat, "api"⟩`. -/
theorem api_binding_resolves :
    apiCfg.resolveRoute ⟨Route.Match.Pat.«prefix» [], "api"⟩
      = ⟨Route.Match.Pat.«prefix» [], Handler.proxy apiPool.compile⟩ := by
  simp only [Config.resolveRoute, resolveHandler_proxy apiCfg "api" apiCfg_find]

end Dsl.Cfg.Upstreams
