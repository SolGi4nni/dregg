import Reactor.Proxy
import Proxy.MaxConn
import Proxy.SlowStart
import Proxy.StickyPin
import Proxy.Outlier

/-!
# Dsl.Cfg.Upstream — the upstream-pool / load-balancing dimension of a deployment

A deployment may declare **upstream pools**: named sets of backends a
reverse-proxy route forwards to, together with the load-balancing policy that
selects among the healthy members. This file owns ONLY that dimension, as
standalone structures over the REAL `Reactor.Proxy.ProxyPool` health-filtered
selection algebra, so a grow lane adding balancing policies or pool options
(connection caps, slow-start warm-up, outlier ejection) edits this file alone.

A `proxy` route (`Reactor.App.Handler.proxy`) already carries its own `ProxyPool`,
and the submission-emitting side is driven by `Reactor.ProxyServe`; this dimension
is the DECLARATIVE surface that names pools a route can reference and the policy
the LB applies. A deployment with no reverse-proxy routes carries the empty pool
set.

## The knob is live, not decorative

Every declarative choice compiles to the exact artefact the PROVEN load balancer
already consumes, so selection is never re-implemented here:

* `LbPolicy` compiles to a `Proxy.Policy` chain (`selPolicies`) — the config
  policy IS the policy the tiered selector runs (`pick_is_selectChainCapped`);
* the per-pool `maxConn` cap compiles to a `Proxy.CapTable` honoured by the
  proven capped selector (`Proxy.selectChainCapped`);
* `slowStartWindow` compiles to a `Proxy.rampPool` weight transform;
* `outlier` compiles to a `Proxy.Outlier.OutlierCfg` driving the proven ejector.

The consequence is that **different configs select different backends** — a
round-robin pool and a least-connections pool over the same loaded member set
pick different members (`rr_vs_leastConn_differ`), and the deployed proxy dial
(`Reactor.ProxyDial.pickWith`) runs whichever chain the config produced. The LB
policy is a live deployment dimension, not a dead field.
-/

namespace Dsl.Cfg

open Reactor.Proxy (ProxyPool chooseUpstream)
open Proxy (Backend Status Policy Ctx selectChain selectChainCapped CapTable)

/-- The load-balancing policy applied over a pool's healthy members. Each maps to
a PROVEN `Proxy.Policy`; the hash policies (`ipHash`/`stickyCookie`/`rendezvous`)
are the same rendezvous-hash selector differing only in what feeds the affinity
`Ctx.key` (client address, session cookie, or a caller-chosen key) — a host input
the selector honours unchanged. -/
inductive LbPolicy where
  /-- Rotate through healthy members by weighted round-robin (`Proxy.Wrr`). -/
  | roundRobin
  /-- Prefer the member with the fewest in-flight connections. -/
  | leastConn
  /-- Fewest in-flight connections per unit weight (cross-multiplied ratio). -/
  | weightedLeastConn
  /-- Rendezvous hashing keyed on the client-address hash. -/
  | ipHash
  /-- Rendezvous hashing keyed on a session-cookie / sticky key. -/
  | stickyCookie
  /-- Rendezvous hashing on a caller-supplied key. -/
  | rendezvous
deriving Repr, DecidableEq

/-- The proven selector a policy chooses. -/
def LbPolicy.toProxy : LbPolicy → Policy
  | .roundRobin        => .weightedRoundRobin
  | .leastConn         => .leastConnections
  | .weightedLeastConn => .weightedLeastConnections
  | .ipHash            => .rendezvousHash
  | .stickyCookie      => .rendezvousHash
  | .rendezvous        => .rendezvousHash

/-- One named upstream pool: a backend set (the real `ProxyPool` selection
algebra) plus the balancing policy and operational options applied over its
healthy members. -/
structure UpstreamPool where
  /-- The pool name a `proxy` route references. -/
  name : String
  /-- The backend set + health-filtered selection (the real proxy algebra). -/
  pool : ProxyPool
  /-- The primary balancing policy over the healthy members. -/
  lb : LbPolicy := .roundRobin
  /-- Optional fallback policy tried when the primary selects nothing (the
  `A else B` chain the proven `Proxy.selectChain` folds). -/
  fallback : Option LbPolicy := none
  /-- Per-member concurrent-connection caps (member id → cap); a member absent is
  unlimited. Honoured by the proven capped selector `Proxy.selectChainCapped`. -/
  caps : List (Nat × Nat) := []
  /-- Slow-start warm-up window (in the member's warm-clock units); `0` disables
  ramping. Compiles to a `Proxy.rampPool` weight transform. -/
  slowStartWindow : Nat := 0
  /-- Optional passive outlier-ejection config (the proven `Proxy.Outlier`
  detector). -/
  outlier : Option Proxy.Outlier.OutlierCfg := none

/-- **The proven policy chain this pool selects with**: the primary policy, then
the optional fallback. This is the value the tiered selector runs — the config
policy, compiled to the real `Proxy.Policy` vocabulary. -/
def UpstreamPool.selPolicies (u : UpstreamPool) : List Policy :=
  match u.fallback with
  | none   => [u.lb.toProxy]
  | some q => [u.lb.toProxy, q.toProxy]

/-- The per-member connection-cap table this pool declares (member id → cap; an
uncapped member maps to `none`). -/
def UpstreamPool.capTable (u : UpstreamPool) : CapTable :=
  fun id => (u.caps.find? (fun c => c.1 == id)).map (·.2)

/-- **The pool's live selection.** Run the PROVEN capped selector over the pool's
backend set with the config-derived policy chain and cap table. `none` iff no
under-cap eligible backend exists. This is what the deployed proxy dials with. -/
def UpstreamPool.pick (u : UpstreamPool) (ctx : Ctx) : Option Backend :=
  selectChainCapped u.selPolicies ctx u.capTable u.pool.backends

/-- The slow-start-warmed backend set: the proven `Proxy.rampPool` weight ramp
under a member warm-clock, `0`-window meaning no ramp. -/
def UpstreamPool.warmBackends (u : UpstreamPool) (clock : Proxy.WarmClock) :
    List Backend :=
  Proxy.rampPool clock u.slowStartWindow u.pool.backends

/-! ## The dimension -/

/-- The upstream dimension: the named pools a deployment's reverse-proxy routes
select among. Empty for a deployment with no proxy routes. -/
structure UpstreamCfg where
  /-- The named upstream pools. -/
  pools : List UpstreamPool := []

/-- Look up a pool by name. -/
def UpstreamCfg.byName (cfg : UpstreamCfg) (name : String) : Option UpstreamPool :=
  cfg.pools.find? (fun p => p.name == name)

/-- **The deployed-proxy policy chain for a named pool** — the seam the deployed
serve reads. `Reactor.ProxyDial.pickWith` runs exactly this chain, so the backend
the deployment dials is selected by the config-declared policy. An unknown name
falls back to the deployed default (rendezvous), so a missing binding degrades to
the standard hash policy rather than failing. -/
def UpstreamCfg.dialChain (cfg : UpstreamCfg) (name : String) : List Policy :=
  match cfg.byName name with
  | some u => u.selPolicies
  | none   => [Policy.rendezvousHash]

/-! ## Inherited selection guarantees (not re-proved) -/

/-- **The config policy IS the proven selector.** A pool's `pick` is literally the
proven capped `selectChain` over the config-derived chain — no wrapper logic, no
config-side selection. -/
theorem pick_is_selectChainCapped (u : UpstreamPool) (ctx : Ctx) :
    u.pick ctx = selectChainCapped u.selPolicies ctx u.capTable u.pool.backends := rfl

/-- **A picked backend is eligible.** Any backend the config's pool selects is an
eligible member of the pool under its cap — `Proxy.selectChain_eligible` /
`Proxy.mem_capPool` transported through the config, never a config promise. -/
theorem pick_eligible (u : UpstreamPool) (ctx : Ctx) {b : Backend}
    (h : u.pick ctx = some b) :
    b ∈ u.pool.backends ∧ b.eligible = true ∧ Proxy.underCap u.capTable b = true := by
  unfold UpstreamPool.pick Proxy.selectChainCapped at h
  have hs := Proxy.selectChain_eligible h
  have hm := Proxy.mem_capPool.mp hs.1
  exact ⟨hm.1, hs.2.1, hm.2⟩

/-- **The declared cap binds.** A backend the config's pool picks is strictly below
its configured `maxConn` — `Proxy.selectChainCapped_under_cap` through the config. -/
theorem pick_under_cap (u : UpstreamPool) (ctx : Ctx) {b : Backend}
    (h : u.pick ctx = some b) : ∀ m, u.capTable b.id = some m → b.conns < m := by
  unfold UpstreamPool.pick at h
  exact Proxy.selectChainCapped_under_cap h

/-! ## A deployment the hardcoded serve could not express

The deployed proxy dial (`Reactor.ProxyDial`) hardcoded a single policy
(`[Policy.rendezvousHash]`). The declarative dimension lets each pool choose its
policy. `rrPool` and `lcPool` carry the SAME three loaded backends and differ only
in `lb` — and the proven selector picks a DIFFERENT backend for each, proving the
config knob is live. -/

/-- Three tier-0 backends, all healthy/active, with differing in-flight counts. -/
def loadedBackends : List Backend :=
  [ { id := 0, weight := 1, conns := 5, tier := 0, healthy := true, status := .active }
  , { id := 1, weight := 1, conns := 1, tier := 0, healthy := true, status := .active }
  , { id := 2, weight := 1, conns := 3, tier := 0, healthy := true, status := .active } ]

/-- The shared loaded pool (policies field is unused — selection reads `lb`). -/
def loadedPool : ProxyPool := { policies := [], backends := loadedBackends }

/-- A round-robin pool over the loaded members. -/
def rrPool : UpstreamPool := { name := "web", pool := loadedPool, lb := .roundRobin }
/-- A least-connections pool over the SAME members. -/
def lcPool : UpstreamPool := { name := "web", pool := loadedPool, lb := .leastConn }

/-- The selection context (round 0; least-conn consults neither round nor key). -/
def selCtx : Ctx := ⟨0, 0, fun _ _ => 0⟩

/-- The two pools compile to different proven chains. -/
theorem rr_chain : rrPool.selPolicies = [Policy.weightedRoundRobin] := rfl
theorem lc_chain : lcPool.selPolicies = [Policy.leastConnections] := rfl

/-- **Different config → different backend.** Round-robin (round 0) takes the
first member (id 0); least-connections takes the least-loaded (id 1). Same
members, different policy, different dial. -/
theorem rr_picks_first : (rrPool.pick selCtx).map Backend.id = some 0 := by decide
theorem lc_picks_least : (lcPool.pick selCtx).map Backend.id = some 1 := by decide

/-- The knob is not dead: the two configs disagree on the chosen backend. -/
theorem rr_vs_leastConn_differ :
    (rrPool.pick selCtx).map Backend.id ≠ (lcPool.pick selCtx).map Backend.id := by decide

/-- The named dial-chain the deployed serve reads differs between the two pool
configs — the value `Reactor.ProxyDial.pickWith` runs. -/
theorem dialChain_rr : ({ pools := [rrPool] } : UpstreamCfg).dialChain "web"
    = [Policy.weightedRoundRobin] := rfl
theorem dialChain_lc : ({ pools := [lcPool] } : UpstreamCfg).dialChain "web"
    = [Policy.leastConnections] := rfl

/-- **The declared cap excludes a full member.** Least-connections *wants* the
least-loaded member (id 0, 4 conns), but its declared cap of 4 is full (4/4), so
the proven capped selector moves to the uncapped member id 1 — the config's cap
changing the dial. Without the cap least-connections would dial id 0. -/
def cappedBackends : List Backend :=
  [ { id := 0, weight := 1, conns := 4, tier := 0, healthy := true, status := .active }
  , { id := 1, weight := 1, conns := 6, tier := 0, healthy := true, status := .active } ]

/-- id 0 is the least-loaded but AT its cap (4/4): the cap excludes it, so the
uncapped member id 1 is dialled. -/
theorem capped_excludes_full :
    (({ name := "web", pool := { policies := [], backends := cappedBackends }
        , lb := .leastConn, caps := [(0, 4)] } : UpstreamPool).pick selCtx).map Backend.id
      = some 1 := by decide

/-- Without the cap, least-connections dials the least-loaded member id 0 — so the
cap, not the policy, moved the previous selection. -/
theorem uncapped_picks_least :
    (({ name := "web", pool := { policies := [], backends := cappedBackends }
        , lb := .leastConn } : UpstreamPool).pick selCtx).map Backend.id
      = some 0 := by decide

/-! ## Runnable evidence — the config actually drives the selection -/

-- Round-robin config dials id 0; least-connections config dials id 1.
#guard (rrPool.pick selCtx).map Backend.id = some 0
#guard (lcPool.pick selCtx).map Backend.id = some 1
-- The deployed-serve dial chains differ by config.
#guard ({ pools := [rrPool] } : UpstreamCfg).dialChain "web" = [Policy.weightedRoundRobin]
#guard ({ pools := [lcPool] } : UpstreamCfg).dialChain "web" = [Policy.leastConnections]
#eval do
  IO.println s!"upstream config drives LB: roundRobin dials {(rrPool.pick selCtx).map (fun b : Backend => b.id)}, leastConn dials {(lcPool.pick selCtx).map (fun b : Backend => b.id)} (same members, different policy)"

#print axioms rr_vs_leastConn_differ
#print axioms pick_eligible

end Dsl.Cfg
