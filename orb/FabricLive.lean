/-
# FabricLive — driving the PROVEN reverse-proxy fabric FSMs over live inputs (no crypto)

The proxy "fabric" is the set of pure, no-crypto decision machines that pick and
protect an upstream on every request:

  * `Proxy.Balance`   — the load-balancer selection algebra (tiered eligible
    pool, rendezvous / round-robin / least-connections, policy chains) with its
    soundness theorems (`select_eligible`, `select_best_tier`, `selectChain_*`);
  * `Proxy.Breaker`   — the circuit-breaker FSM (`closed → open → halfOpen`) that
    trips after `threshold` consecutive failures and short-circuits while open
    (`closed_trips_at_threshold`, `open_no_attempt`, …);
  * `Proxy.Health`    — the probe-driven up/down verdict machine with rise/fall
    hysteresis (`down_at_fall`, `up_at_rise`, the anti-flap lemmas);
  * `Reactor.ProxyDial` — the seam that surfaces the proven pick (`pick` /
    `pickWith`) over a fleet whose per-backend `healthy` bit is supplied LIVE by
    the host (bit `i` ⇒ backend `i` is usable). Its `pickWith_health_ejects`
    proves an ineligible backend is never dialled for ANY policy chain.

None of that logic was wired into a running binary. This executable is that
wiring: a `selftest` that drives ALL THREE machines over live inputs in one
process — it runs the health verdict machine to eject a backend, runs the
breaker FSM to trip open after a burst of failures, folds both into the live
mask bit the fleet consumes, and asks the PROVEN `Reactor.ProxyDial.pick` to
choose. It cross-checks the running choices against the model and against the
faithfulness theorems below.

## Honesty / realization boundary (the ControlLive / DnsResolveLive discipline)

This is **drorb-native** and, unlike the crypto live-wirings, uses NO FFI on the
running path at all: the fabric is pure decision logic, so the whole `selftest`
runs under the plain Lean interpreter (`lake env lean --run`) with no sockets and
no crypto. Everything structural is the proven Lean; the only gap the selftest
discharges by construction (not by proof) is that this exe faithfully CALLS the
proven functions on the FSM outputs. The faithfulness of the health/breaker →
mask → pick composition ITSELF is proven below: `fabric_pick_faithful` (whatever
the fabric picks is a backend whose health verdict is Up AND whose breaker is
closed), `fabric_health_ejects` (a health-ejected backend is never picked), and
`fabric_breaker_trip_ejects` (a backend whose breaker tripped open is never
picked), the last composing the actual breaker run to `open`.

The mask-bit contract (bit `i` of the mask = backend `i`'s live verdict) is the
`drorb_proxy_pick` ABI, discharged by the host that builds the mask; the theorems
are stated relative to it exactly as `Reactor.Proxy.Health` states its ejection.

Usage:
  fabric-live selftest
-/
import Reactor.Proxy.Health
import Proxy.Breaker

namespace FabricLive

/-! ## The live verdict bit: health AND breaker, composed

Each backend carries a single live `healthy` bit into selection. The host sets it
from BOTH subsystems: the backend is live iff its health verdict is Up AND its
circuit breaker is closed (an open breaker is a hard short-circuit, an
independent ejection path from a failed health probe). `liveBit` is exactly that
conjunction over the two FSM states. -/

/-- The breaker admits new dials only in the `closed` phase (an `open` breaker
short-circuits; `halfOpen` admits a single trial probe, not general traffic — for
the fleet eligibility bit it counts as not-yet-live). -/
def breakerClosed (bs : Proxy.Breaker.BState) : Bool :=
  decide (bs.phase = Proxy.Breaker.BPhase.closed)

/-- Backend `i` is LIVE (its fleet `healthy` bit set) iff the health verdict is
Up AND the breaker is closed. This is what the host packs into the mask. -/
def liveBit (hs : Proxy.HealthState) (bs : Proxy.Breaker.BState) : Bool :=
  hs.up && breakerClosed bs

/-! ## Faithfulness theorem 1 — whatever is picked passed BOTH subsystems

The strong compositional statement: under the mask-bit contract for backend `i`
(`mask.testBit i = liveBit hs bs`), if the proven pick returns `i`, then the
health verdict `hs` is Up AND the breaker `bs` is closed. The fabric never dials
a backend that either machine has ruled out — health and breaker compose, and the
proven selector honours the conjunction. Non-vacuous: the hypotheses are a
satisfiable bit contract and a real successful pick (the selftest exhibits both);
the conclusion is a genuine conjunction about the two FSM states, not `P → P`. -/
theorem fabric_pick_faithful {mask key i : Nat}
    {hs : Proxy.HealthState} {bs : Proxy.Breaker.BState}
    (hbit : mask.testBit i = liveBit hs bs)
    (h : Reactor.ProxyDial.pick mask key = some i) :
    hs.up = true ∧ bs.phase = Proxy.Breaker.BPhase.closed := by
  -- A picked backend's mask bit is set (it was eligible ⇒ healthy).
  have hset : mask.testBit i = true := by
    have hb : ∃ b, Reactor.ProxyDial.pickBackend mask key = some b ∧ b.id = i := by
      unfold Reactor.ProxyDial.pick at h
      cases hp : Reactor.ProxyDial.pickBackend mask key with
      | none => rw [hp] at h; simp at h
      | some b => rw [hp] at h; simp at h; exact ⟨b, rfl, h⟩
    obtain ⟨b, hpb, hid⟩ := hb
    obtain ⟨hmem, helig⟩ := Reactor.ProxyDial.pickBackend_eligible hpb
    have hh : b.healthy = true := by
      simp only [Proxy.Backend.eligible, Bool.and_eq_true] at helig
      exact helig.1
    rw [Reactor.ProxyDial.fleet_healthy hmem, hid] at hh
    exact hh
  -- The set bit is the live conjunction, so both conjuncts hold.
  rw [hbit] at hset
  unfold liveBit at hset
  rw [Bool.and_eq_true] at hset
  refine ⟨hset.1, ?_⟩
  have hbc := hset.2
  unfold breakerClosed at hbc
  exact of_decide_eq_true hbc

/-! ## Faithfulness theorem 2 — a health-ejected backend is never dialled

Composing `Reactor.Proxy.Health.probes_eject` (a settled-Up backend that fails
`fall` consecutive probes has verdict Down) with the live bit and the proven
ejection: whatever the backend's breaker is doing, once health has ejected it,
its live bit is clear and the pick refuses it — for ANY policy chain via `pick`'s
default rendezvous chain. -/
theorem fabric_health_ejects {g : Proxy.HealthGate} (hf : 1 ≤ g.fall)
    {mask key i : Nat} {bs : Proxy.Breaker.BState}
    (hbit : mask.testBit i
      = liveBit (Proxy.hrun g Proxy.HealthState.initUp
          (List.replicate g.fall Proxy.Probe.fail)) bs) :
    Reactor.ProxyDial.pick mask key ≠ some i := by
  apply Reactor.ProxyDial.pick_health_ejects
  rw [hbit]
  unfold liveBit
  rw [Reactor.Proxy.Health.probes_eject hf, Bool.false_and]

/-! ## Faithfulness theorem 3 — a tripped-open breaker ejects, and the trip is proven

First the breaker actually trips: from a fresh closed breaker, `threshold`
consecutive failures drive it to `open`. Then a backend whose breaker is open has
a clear live bit (regardless of its health verdict), so the pick refuses it. The
`fabric_breaker_trip_ejects` corollary composes the actual `run … open` trip into
the ejection — the breaker FSM output, not an assumed `open` state. -/

open Proxy.Breaker

private theorem run_append (cfg : BreakerCfg) (s : BState) (es fs : List BEvent) :
    run cfg s (es ++ fs) = run cfg (run cfg s es) fs := by
  induction es generalizing s with
  | nil => rfl
  | cons e rest ih => rw [List.cons_append, run_cons, run_cons, ih]

/-- A closed breaker absorbs `n` consecutive failures without tripping as long as
the running total stays below the threshold: it stays closed and its
failure counter advances by exactly `n`. -/
private theorem closed_survives (cfg : BreakerCfg) :
    ∀ (n : Nat) (s : BState), s.phase = BPhase.closed →
      s.failures + n < cfg.threshold →
      (run cfg s (List.replicate n .failure)).failures = s.failures + n
        ∧ (run cfg s (List.replicate n .failure)).phase = BPhase.closed := by
  intro n
  induction n with
  | zero => intro s hp _; exact ⟨rfl, hp⟩
  | succ n ih =>
    intro s hp hlt
    rw [List.replicate_succ, run_cons]
    have hb : ¬ cfg.threshold ≤ s.failures + 1 := by omega
    obtain ⟨hph, hfa⟩ := closed_below_threshold cfg s hp hb
    have hlt' : (step cfg s .failure).1.failures + n < cfg.threshold := by
      rw [hfa]; omega
    obtain ⟨hf2, hp2⟩ := ih (step cfg s .failure).1 hph hlt'
    exact ⟨by rw [hf2, hfa]; omega, hp2⟩

/-- **The breaker trips.** From a fresh (closed) breaker, `threshold ≥ 1`
consecutive failures drive it to the `open` phase. -/
theorem breaker_trips (cfg : BreakerCfg) (h1 : 1 ≤ cfg.threshold) :
    (run cfg BState.init (List.replicate cfg.threshold .failure)).phase
      = BPhase.open := by
  obtain ⟨hfa, hph⟩ :=
    closed_survives cfg (cfg.threshold - 1) BState.init rfl
      (by simp only [BState.init]; omega)
  have hsplit : cfg.threshold = (cfg.threshold - 1) + 1 := by omega
  rw [hsplit, List.replicate_succ', run_append, run_cons, run_nil]
  obtain ⟨hopen, _⟩ :=
    closed_trips_at_threshold cfg _ hph (by rw [hfa]; simp only [BState.init]; omega)
  exact hopen

/-- **A backend whose breaker is open is never dialled** — for any health verdict.
Composed with `breaker_trips` below into `fabric_breaker_trip_ejects`. -/
theorem fabric_breaker_ejects {mask key i : Nat}
    {hs : Proxy.HealthState} {bs : Proxy.Breaker.BState}
    (hopen : bs.phase = Proxy.Breaker.BPhase.open)
    (hbit : mask.testBit i = liveBit hs bs) :
    Reactor.ProxyDial.pick mask key ≠ some i := by
  apply Reactor.ProxyDial.pick_health_ejects
  rw [hbit]
  unfold liveBit breakerClosed
  have hnc : decide (bs.phase = Proxy.Breaker.BPhase.closed) = false := by
    rw [hopen]; decide
  rw [hnc, Bool.and_false]

/-- **The fully-composed breaker statement.** If backend `i`'s breaker took
`threshold` consecutive failures (it is now open) and the mask bit reflects the
resulting live verdict, the pick never returns `i`, for any health state. -/
theorem fabric_breaker_trip_ejects {cfg : Proxy.Breaker.BreakerCfg}
    (h1 : 1 ≤ cfg.threshold) {mask key i : Nat} {hs : Proxy.HealthState}
    (hbit : mask.testBit i
      = liveBit hs (Proxy.Breaker.run cfg Proxy.Breaker.BState.init
          (List.replicate cfg.threshold .failure))) :
    Reactor.ProxyDial.pick mask key ≠ some i :=
  fabric_breaker_ejects (breaker_trips cfg h1) hbit

#print axioms fabric_pick_faithful
#print axioms fabric_health_ejects
#print axioms fabric_breaker_trip_ejects

/-! ## The selftest — drive all three fabric FSMs over live inputs (no crypto) -/

/-- Render an `Option Nat` (a pick result). -/
def showOpt : Option Nat → String
  | some n => s!"backend {n}"
  | none   => "(none — 503, no eligible backend)"

/-- Render a breaker phase. -/
def showPhase : Proxy.Breaker.BPhase → String
  | .closed => "closed"
  | .open => "open"
  | .halfOpen => "halfOpen"

/-- Pack three live bits into the fleet mask (bit `i` = backend `i` live). The
three fleet ids are 0,1,2, so the bits are disjoint and this equals the value the
proven `Reactor.ProxyDial.pick` reads via `Nat.testBit`. -/
def buildMask (b0 b1 b2 : Bool) : Nat :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0)

def selftest : IO UInt32 := do
  IO.println "== fabric-live selftest : reverse-proxy fabric FSMs (LB pick / circuit breaker / health), live inputs, NO crypto =="

  let g   : Proxy.HealthGate := ⟨2, 3⟩            -- rise 2, fall 3
  let cfg : Proxy.Breaker.BreakerCfg := ⟨3, 5⟩    -- trip threshold 3, cooldown 5

  -- ── 1. load balance : distinct affinity keys spread across a healthy fleet ──
  IO.println "\n-- 1. load balance (all backends up, mask=0b111) --"
  for k in List.range 6 do
    IO.println s!"  affinity key {k} -> {showOpt (Reactor.ProxyDial.pick 0b111 k)}"
  let sticky :=
    (Reactor.ProxyDial.pick 0b111 4 == Reactor.ProxyDial.pick 0b111 4)
      && (Reactor.ProxyDial.pick 0b111 4 == some 0)
  IO.println s!"  sticky affinity (key 4 pins to one backend across requests) : {sticky}"

  -- ── 2. circuit breaker : consecutive failures trip it open ──
  IO.println "\n-- 2. circuit breaker (trip threshold = 3) --"
  let b2f := Proxy.Breaker.run cfg Proxy.Breaker.BState.init [.failure, .failure]
  let b3f := Proxy.Breaker.run cfg Proxy.Breaker.BState.init
              (List.replicate cfg.threshold .failure)
  IO.println s!"  after 2 failures : phase {showPhase b2f.phase} (still admitting)"
  IO.println s!"  after 3 failures : phase {showPhase b3f.phase} (TRIPPED open — short-circuits)"
  let breakerTrips := decide (b2f.phase = .closed) && decide (b3f.phase = .open)

  -- ── 3. health eject : fall consecutive failed probes eject a settled-Up backend ──
  IO.println "\n-- 3. active health check (fall = 3) --"
  let h0 := Proxy.hrun g Proxy.HealthState.initUp (List.replicate g.fall Proxy.Probe.fail)
  IO.println s!"  backend 0 after {g.fall} failed probes : up = {h0.up} (EJECTED)"
  IO.println s!"  backend 0 recovery : {(Proxy.hrun g Proxy.HealthState.initDown (List.replicate g.rise Proxy.Probe.pass)).up} after {g.rise} passes"

  -- ── 4. compose all three into the live mask, and fail over ──
  -- backend 0: health-ejected (fall fails), breaker closed        -> NOT live
  -- backend 1: health Up, breaker tripped OPEN (threshold fails)   -> NOT live
  -- backend 2: health Up, breaker closed                          -> LIVE
  IO.println "\n-- 4. health + breaker compose into the fleet mask -> failover --"
  let live0 := liveBit h0 Proxy.Breaker.BState.init
  let live1 := liveBit Proxy.HealthState.initUp b3f
  let live2 := liveBit Proxy.HealthState.initUp Proxy.Breaker.BState.init
  let liveMask := buildMask live0 live1 live2
  IO.println s!"  live bits: b0={live0} (health-ejected)  b1={live1} (breaker-open)  b2={live2} (healthy)  -> mask = {liveMask}"
  let failover := Reactor.ProxyDial.pick liveMask 4
  IO.println s!"  proven pick over the live mask (key 4) -> {showOpt failover}"

  -- ── 5. faithfulness cross-checks (realize the theorems on concrete inputs) ──
  IO.println "\n-- 5. cross-check (realizes fabric_pick_faithful / *_ejects) --"
  -- 5a. whatever is picked has its mask bit set (fabric_pick_faithful's `hset`).
  let pickedBitSet := match failover with
    | some idx => liveMask.testBit idx
    | none => false
  -- 5b. the two ejected backends are never returned, over a sweep of affinity keys.
  let picksLive := (List.range 32).map (fun k => Reactor.ProxyDial.pick liveMask k)
  let ejectedNeverPicked :=
    picksLive.all (fun p => p != some 0 && p != some 1)
  IO.println s!"  picked backend's live bit is set          : {pickedBitSet}"
  IO.println s!"  health-ejected b0 / breaker-open b1 never picked (32-key sweep) : {ejectedNeverPicked}"

  let allGood :=
    sticky && breakerTrips && (h0.up == false)
      && (liveMask == 4) && (failover == some 2)
      && pickedBitSet && ejectedNeverPicked
  if allGood then do
    IO.println "\nPASS — LB spreads affinity keys, the breaker trips open after threshold failures,"
    IO.println "       health + breaker eject compose into the fleet mask, and the PROVEN pick fails"
    IO.println "       over to the only healthy backend (realizes fabric_pick_faithful, no crypto, no FFI)."
    return 0
  else do
    IO.eprintln "\nFAIL — a fabric stage did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: fabric-live selftest"
    return 1

end FabricLive

def main (args : List String) : IO UInt32 := FabricLive.main args
