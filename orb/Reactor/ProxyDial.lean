import Proxy.Balance
import Proxy.Rendezvous

/-!
# Reactor.ProxyDial — the proven LB decision, surfaced for a native host to dial

`Reactor.Proxy` wires `Proxy.selectChain` into the reactor's submission vocabulary
(it emits a `connectUpstream` to the chosen backend). That closes the *decision*:
the reactor knows which backend to dial. It does not itself open the socket — the
sans-IO core has no IO. A native host (the Rust dataplane) owns the sockets, so the
reverse-proxy forward is a HOST/CORE split, exactly like `drorb_serve`:

  * the CORE decides which backend, honouring health / breaker / affinity — the
    PROVEN `Proxy.selectChain` over the eligible (healthy ∧ active) pool;
  * the HOST opens the TCP connection to that backend, forwards the request bytes,
    and returns the upstream's response bytes.

This module is the seam for that split. It exposes the proven selection as a pure
`ByteArray → ByteArray` the host calls per request (`@[export drorb_proxy_pick]`),
so the backend the host dials is the one the proven algebra chose — never a
host-side re-implementation.

## The live inputs

The host's active health probes and its circuit breaker produce a *live* verdict
per backend (up / ejected). Those verdicts enter selection as the `healthy` bit of
each `Proxy.Backend`, packed into a `mask` (bit `i` ⇒ backend `i` is probe-healthy
and breaker-closed). Session affinity enters as `key` (a hash of the client's
sticky cookie / address). Both are supplied by the host and consumed by the proven
selector — the host contributes *inputs*, never the decision.

The policy is `rendezvousHash` (highest-random-weight): a single proven policy that
delivers all four fabric behaviours the host needs —

  * **load balance** — distinct keys spread across the eligible backends;
  * **health eject** — a backend whose bit is clear is not eligible, so it is never
    chosen (`pick_health_ejects`);
  * **circuit breaker** — an opened breaker clears the bit, i.e. the same ejection;
  * **sticky affinity** — the choice is a pure function of `key` (`pick_is_select`),
    so one session key pins to one backend across requests, and the choice survives
    an *unrelated* backend leaving the pool (`Proxy.rendezvous`'s minimal-disruption).
-/

namespace Reactor.ProxyDial

open Proxy (Backend Status Policy Ctx selectChain select)

/-- The dial hash: a concrete integer mixing function of `(key, id)`. Rendezvous
hashing routes `key` to the backend maximising `dialHash key id`, so every key has
a stable home backend and distinct keys spread over the pool. (Every `Proxy`
theorem holds for *any* `hash : Nat → Nat → Nat`; this pins a runnable one.) -/
def dialHash (key id : Nat) : Nat :=
  (key * 2654435761 + id * 2246822519 + 2166136261) % 4294967291

/-- The per-request selection context: the affinity `key` and the dial hash. -/
def mkCtx (key : Nat) : Ctx := { round := 0, key := key, hash := dialHash }

/-- The demo backend fleet the host proxies to: three tier-0 backends whose
`healthy` bit is supplied LIVE by the host (bit `i` of `mask`). Everything else
(weights, tiers) is the config snapshot; all administratively `active`. -/
def fleet (mask : Nat) : List Backend :=
  [ { id := 0, weight := 1, conns := 0, tier := 0, healthy := mask.testBit 0, status := .active }
  , { id := 1, weight := 1, conns := 0, tier := 0, healthy := mask.testBit 1, status := .active }
  , { id := 2, weight := 1, conns := 0, tier := 0, healthy := mask.testBit 2, status := .active } ]

/-- The selection policy chain: a single proven `rendezvousHash` link. -/
def dialPolicies : List Policy := [Policy.rendezvousHash]

/-- **The proven pick (backend).** Run the REAL `Proxy.selectChain` over the
live-health-masked fleet with the request's affinity key. `none` iff no backend is
eligible (every bit clear ⇒ the whole pool is unhealthy). -/
def pickBackend (mask key : Nat) : Option Backend :=
  selectChain dialPolicies (mkCtx key) (fleet mask)

/-- **The proven pick (id).** The chosen backend's stable id — the identity the host
maps to a configured backend socket address. -/
def pick (mask key : Nat) : Option Nat :=
  (pickBackend mask key).map (·.id)

/-! ## Config-driven pick: the deployed seam honouring the DSL LB policy

`pick` above fixes the policy chain to `dialPolicies` (a single rendezvous link).
`pickWith` generalizes it to ANY policy chain — the value the DSL's
`Dsl.Cfg.UpstreamCfg.dialChain` produces from the deployment's declared
`LbPolicy`. The deployed serve threads the config chain here, so the backend the
host dials is selected by the config-declared policy (round-robin,
least-connections, …), not the hardcoded default. Every selection guarantee
survives: a chosen backend is still eligible for ANY chain
(`pickWith_health_ejects`), because eligibility is `selectChain`'s, not the
chain's. -/

/-- **The proven pick under a config chain (backend).** Run the REAL
`Proxy.selectChain` over the live-health-masked fleet with a CONFIG-supplied
policy chain. -/
def pickBackendWith (policies : List Policy) (mask key : Nat) : Option Backend :=
  selectChain policies (mkCtx key) (fleet mask)

/-- **The proven pick under a config chain (id).** -/
def pickWith (policies : List Policy) (mask key : Nat) : Option Nat :=
  (pickBackendWith policies mask key).map (·.id)

/-- The hardcoded default pick is exactly the config-driven pick at the default
chain — so `pick` is the `policies = dialPolicies` instance of the config seam. -/
theorem pick_eq_pickWith (mask key : Nat) : pick mask key = pickWith dialPolicies mask key := rfl

/-- **Health / breaker ejection holds for ANY config chain.** No matter which LB
policy the config selects, a backend whose live bit is clear is never dialled —
eligibility is `Proxy.selectChain`'s, independent of the policy chain. -/
theorem pickWith_health_ejects {policies : List Policy} {mask key i : Nat}
    (hbit : mask.testBit i = false) : pickWith policies mask key ≠ some i := by
  unfold pickWith pickBackendWith
  cases hb : selectChain policies (mkCtx key) (fleet mask) with
  | none => exact fun h => nomatch h
  | some b =>
    intro h
    injection h with h
    dsimp only at h
    obtain ⟨hmem, helig, _⟩ := Proxy.selectChain_eligible hb
    have hh : b.healthy = true := by
      simp only [Backend.eligible, Bool.and_eq_true] at helig
      exact helig.1
    have hfh : b.healthy = mask.testBit b.id := by
      simp only [fleet, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
      rcases hmem with h1 | h1 | h1 <;> subst h1 <;> rfl
    rw [hfh, h, hbit] at hh
    exact absurd hh (by decide)

/-! ### Load-aware fleet — the config policy visibly changes the dial

The default `fleet` carries no in-flight load (`conns := 0`), so load-sensitive
policies (least-connections, weighted-least-connections) coincide with
round-robin on it. `fleetC` lets the host supply a per-backend in-flight count
(exactly as `mask` supplies health), which makes the config policy choice
*observable*: over the same loaded fleet, round-robin and least-connections dial
DIFFERENT backends. -/

/-- The fleet with a host-supplied per-backend in-flight count `conns`. `fleet` is
the zero-load instance. -/
def fleetC (mask : Nat) (conns : Nat → Nat) : List Backend :=
  [ { id := 0, weight := 1, conns := conns 0, tier := 0, healthy := mask.testBit 0, status := .active }
  , { id := 1, weight := 1, conns := conns 1, tier := 0, healthy := mask.testBit 1, status := .active }
  , { id := 2, weight := 1, conns := conns 2, tier := 0, healthy := mask.testBit 2, status := .active } ]

/-- `fleet` is `fleetC` at zero load. -/
theorem fleet_eq_fleetC (mask : Nat) : fleet mask = fleetC mask (fun _ => 0) := rfl

/-- The config-driven pick over a loaded fleet. -/
def pickLoaded (policies : List Policy) (mask : Nat) (conns : Nat → Nat) (key : Nat) :
    Option Nat :=
  (selectChain policies (mkCtx key) (fleetC mask conns)).map (·.id)

/-! ## The C ABI seam the host calls per request -/

/-- Fold the affinity-key bytes into a `Nat` (the sticky session key). -/
def keyOf (bs : List UInt8) : Nat :=
  bs.foldl (fun a b => a * 31 + b.toNat) 0

/-- **`drorb_proxy_pick` — the proven LB decision as a `ByteArray → ByteArray`.**
Input: byte 0 = the live health/breaker mask (bit `i` ⇒ backend `i` is up), bytes
1.. = the affinity-key material. Output: the decimal ASCII id of the backend the
proven `Proxy.selectChain` chose, or EMPTY bytes when no backend is eligible (the
host then serves a 503 rather than dialling). The host maps the returned id to the
backend's configured socket and opens the connection. -/
@[export drorb_proxy_pick]
def proxyPickC (input : ByteArray) : ByteArray :=
  match input.toList with
  | [] => ByteArray.empty
  | m :: rest =>
    match pick m.toNat (keyOf rest) with
    | some id => (toString id).toUTF8
    | none    => ByteArray.empty

/-! ## Seam theorems -/

/-- `selectChain` over the single-link chain is exactly the `rendezvousHash`
`select` — the pick is literally the proven affinity policy, no wrapper logic. -/
theorem pickBackend_is_select (mask key : Nat) :
    pickBackend mask key = select Policy.rendezvousHash (mkCtx key) (fleet mask) := by
  unfold pickBackend dialPolicies selectChain
  cases select Policy.rendezvousHash (mkCtx key) (fleet mask) <;> rfl

/-- Every fleet member's health bit is exactly its mask bit. -/
theorem fleet_healthy {mask : Nat} {b : Backend} (h : b ∈ fleet mask) :
    b.healthy = mask.testBit b.id := by
  simp only [fleet, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with h | h | h <;> subst h <;> rfl

/-- **Chosen ⇒ eligible.** A picked backend is a healthy, active member of the
fleet in the healthiest nonempty tier — the proven `selectChain_eligible`, not a
host promise. A stub that ignored the mask could not satisfy this. -/
theorem pickBackend_eligible {mask key : Nat} {b : Backend}
    (h : pickBackend mask key = some b) :
    b ∈ fleet mask ∧ b.eligible = true :=
  let e := Proxy.selectChain_eligible h
  ⟨e.1, e.2.1⟩

/-- **Health / breaker ejection.** If backend `i`'s bit is clear (probe said down,
or the breaker opened and cleared it), the pick NEVER returns `i`. This is the
running-path meaning of "eject an unhealthy backend" / "open the circuit breaker":
the proven selector refuses an ineligible backend. -/
theorem pick_health_ejects {mask key i : Nat} (hbit : mask.testBit i = false) :
    pick mask key ≠ some i := by
  unfold pick
  cases hb : pickBackend mask key with
  | none => exact fun h => nomatch h
  | some b =>
    intro h
    injection h with h
    dsimp only at h  -- h : b.id = i
    obtain ⟨hmem, helig⟩ := pickBackend_eligible hb
    -- eligible ⇒ healthy = true; but b.id = i and the i-bit is clear.
    have hh : b.healthy = true := by
      simp only [Backend.eligible, Bool.and_eq_true] at helig
      exact helig.1
    rw [fleet_healthy hmem, h, hbit] at hh
    exact absurd hh (by decide)

/-- **Determinism / stickiness.** The pick is a pure function of `(mask, key)`, so a
fixed session key pins to one backend across requests (given a stable live health
verdict). -/
theorem pick_sticky (mask key : Nat) : pick mask key = pick mask key := rfl

/-! ## Runnable checks — the proven selector actually chooses, and honours health -/

-- All three up: key 4 homes to backend 0 (a real, deterministic LB choice).
example : pick 0b111 4 = some 0 := by decide
-- Same key + same health ⇒ same backend (sticky affinity).
example : pick 0b111 4 = pick 0b111 4 := rfl
-- Eject backend 0 (probe down / breaker open ⇒ its bit clears): the PROVEN
-- selector moves key 4 to another eligible backend — active health/breaker
-- changing the running choice, not a host-side re-route.
example : pick 0b110 4 = some 1 := by decide
-- Distinct keys spread across the pool (load balance): key 0 homes to backend 2.
example : pick 0b111 0 = some 2 := by decide
-- No backend up ⇒ no pick (the host serves 503, never dials).
example : pick 0b000 4 = none := by decide

/-! ### The config LB policy visibly changes the deployed dial

Over the SAME loaded fleet (all three up; in-flight counts 5,1,3), the deployed
`pickWith`/`pickLoaded` dials a DIFFERENT backend per config policy: weighted
round-robin (round 0) takes the first member, least-connections takes the
least-loaded. This is the DSL `LbPolicy` reaching the running dial. -/

def demoLoad : Nat → Nat := fun i => if i == 0 then 5 else if i == 1 then 1 else 3

-- Round-robin config (round 0) dials backend 0…
example : pickLoaded [Policy.weightedRoundRobin] 0b111 demoLoad 0 = some 0 := by decide
-- …least-connections config dials the least-loaded backend 1 — different dial,
-- same fleet, driven purely by the config policy.
example : pickLoaded [Policy.leastConnections] 0b111 demoLoad 0 = some 1 := by decide
-- The two config chains disagree on the dialled backend.
example : pickLoaded [Policy.weightedRoundRobin] 0b111 demoLoad 0
    ≠ pickLoaded [Policy.leastConnections] 0b111 demoLoad 0 := by decide

#eval do
  IO.println s!"deployed dial honours config LB policy: roundRobin -> {pickLoaded [Policy.weightedRoundRobin] 0b111 demoLoad 0}, leastConn -> {pickLoaded [Policy.leastConnections] 0b111 demoLoad 0} (same loaded fleet)"

#print axioms pickWith_health_ejects

end Reactor.ProxyDial
