/-
LbChecks — the load-balancer decision battery, fully evaluated.

Every check below drives the PROVEN selectors (`selectChain`, `select`, the
capped/pinned/ramped variants, the smooth-WRR machine, the outlier detector)
over concrete pools and pins the exact verdicts with `#guard`: the file fails
to COMPILE if any policy picks differently from its specification. The
`#eval`s print the same evidence for the build log.

The pool used throughout unless stated: three tier-0 backends
`a = id 0, b = id 1, c = id 2`.
-/

import Proxy.Balance
import Proxy.MaxConn
import Proxy.SlowStart
import Proxy.StickyPin
import Proxy.Swrr
import Proxy.Outlier

namespace Proxy.LbChecks

open Proxy

/-- Backend builder. -/
def mkB (id w conns tier : Nat) (healthy : Bool := true)
    (status : Status := .active) : Backend :=
  { id := id, weight := w, conns := conns, tier := tier,
    healthy := healthy, status := status }

/-- A deterministic mixing hash for the rendezvous checks. -/
def h (k i : Nat) : Nat := (k * 2654435761 + i * 2246822519) % 1000003

def ctx (round key : Nat) : Ctx := ⟨round, key, h⟩

/-! ## Weighted round-robin: exact fairness, and its burstiness -/

/-- Weights {5,1,1}. -/
def skew : List Backend := [mkB 0 5 0 0, mkB 1 1 0 0, mkB 2 1 0 0]

def wrrSeq (n : Nat) : List (Option Nat) :=
  (List.range n).map fun r =>
    (selectChain [.weightedRoundRobin] (ctx r 0) skew).map (·.id)

-- One full cycle (W = 7): exactly weight-many picks each — but BURSTY:
-- five consecutive hits on backend 0.
#guard wrrSeq 7 = [some 0, some 0, some 0, some 0, some 0, some 1, some 2]
#eval do
  IO.println s!"interval WRR, weights (5,1,1), one cycle: {wrrSeq 7}"

/-! ## Smooth WRR: same shares, interleaved -/

def smoothSeq (n : Nat) : List (Option Nat) := (swrrRun n (swrrInit skew)).1

-- Same cycle, same multiset of picks (5 x id0, 1 x id1, 1 x id2) — but the
-- skewed backend is INTERLEAVED: a a b a c a a, never 5 in a row.
#guard smoothSeq 7 = [some 0, some 0, some 1, some 0, some 2, some 0, some 0]
-- Cycle closure: after one full cycle every `current` counter is back to 0,
-- so the schedule repeats exactly (concrete per-cycle fairness).
#guard (swrrRun 7 (swrrInit skew)).2.map Prod.snd = [0, 0, 0]
#guard smoothSeq 14 = smoothSeq 7 ++ smoothSeq 7
#eval do
  IO.println s!"smooth WRR,   weights (5,1,1), one cycle: {smoothSeq 7}"
  IO.println s!"smooth WRR: counters after full cycle: {(swrrRun 7 (swrrInit skew)).2.map Prod.snd}"

/-! ## Least-connections, plain and weighted -/

def loaded : List Backend := [mkB 0 1 3 0, mkB 1 4 8 0, mkB 2 1 5 0]

-- Plain least-conn: fewest in-flight wins (id 0: 3 conns).
#guard (selectChain [.leastConnections] (ctx 0 0) loaded).map (·.id) = some 0
-- Weighted least-conn: id 1 carries 8 conns but weight 4 → ratio 2,
-- beating id 0's ratio 3. The weight-aware policy picks differently.
#guard (selectChain [.weightedLeastConnections] (ctx 0 0) loaded).map (·.id)
  = some 1
#eval do
  IO.println s!"least-conn  (conns 3,8,5 / weights 1,4,1): {(selectChain [.leastConnections] (ctx 0 0) loaded).map (fun b : Backend => b.id)}"
  IO.println s!"wleast-conn (conns 3,8,5 / weights 1,4,1): {(selectChain [.weightedLeastConnections] (ctx 0 0) loaded).map (fun b : Backend => b.id)}"

/-! ## Rendezvous: minimal disruption, concretely -/

def pool3 : List Backend := [mkB 0 1 0 0, mkB 1 1 0 0, mkB 2 1 0 0]

def keyHome (key : Nat) (bs : List Backend) : Option Nat :=
  (selectChain [.rendezvousHash] (ctx 0 key) bs).map (·.id)

-- Keys spread across the pool (not all on one backend).
#guard keyHome 1 pool3 = some 0
#guard keyHome 3 pool3 = some 2
#guard keyHome 12 pool3 = some 1
-- Remove a backend a key does NOT live on: the key keeps its home.
#guard keyHome 1 [mkB 0 1 0 0, mkB 1 1 0 0] = some 0   -- id 2 left; key 1 stays
#guard keyHome 3 [mkB 0 1 0 0, mkB 2 1 0 0] = some 2   -- id 1 left; key 3 stays
#eval do
  IO.println s!"rendezvous homes (keys 1,3,12): {[keyHome 1 pool3, keyHome 3 pool3, keyHome 12 pool3]}"
  IO.println s!"rendezvous after id2 leaves, key 1: {keyHome 1 [mkB 0 1 0 0, mkB 1 1 0 0]} (unmoved)"

/-! ## Tier failover, draining, and chain fallback -/

def tiered : List Backend :=
  [mkB 0 1 0 0, mkB 1 1 0 0, mkB 2 1 0 1]  -- id 2 is the backup tier

-- Healthy primaries: the backup is never selected.
#guard (selectChain [.leastConnections] (ctx 0 0) tiered).map (·.id) = some 0
-- All primaries down: the backup engages.
#guard (selectChain [.leastConnections] (ctx 0 0)
    [mkB 0 1 0 0 false, mkB 1 1 0 0 false, mkB 2 1 0 1]).map (·.id) = some 2
-- Draining backends take no NEW selection even while healthy.
#guard (selectChain [.leastConnections] (ctx 0 0)
    [mkB 0 1 0 0 true .draining, mkB 1 1 5 0]).map (·.id) = some 1
-- Whole pool ineligible: the chain answers none (never a dead backend).
#guard selectChain [.weightedRoundRobin, .leastConnections] (ctx 0 0)
    [mkB 0 1 0 0 false, mkB 1 1 0 0 true .down] = none
-- Chain fallback: all weights 0 makes WRR fail; the chain falls through to
-- least-connections instead of failing the request.
#guard (selectChain [.weightedRoundRobin] (ctx 0 0)
    [mkB 0 0 2 0, mkB 1 0 1 0]) = none
#guard (selectChain [.weightedRoundRobin, .leastConnections] (ctx 0 0)
    [mkB 0 0 2 0, mkB 1 0 1 0]).map (·.id) = some 1
#eval do
  IO.println s!"tier failover (primaries down): {(selectChain [.leastConnections] (ctx 0 0) [mkB 0 1 0 0 false, mkB 1 1 0 0 false, mkB 2 1 0 1]).map (fun b : Backend => b.id)}"
  IO.println s!"chain fallback (wrr zero-weights -> least-conn): {(selectChain [.weightedRoundRobin, .leastConnections] (ctx 0 0) [mkB 0 0 2 0, mkB 1 0 1 0]).map (fun b : Backend => b.id)}"

/-! ## Sticky-cookie pin -/

-- Live pin: the cookie's backend wins outright, even if balancing would
-- pick someone else (id 2 has fewer conns; the pin says id 1).
#guard (selectPinned (some 1) [.leastConnections] (ctx 0 0)
    [mkB 0 1 9 0, mkB 1 1 8 0, mkB 2 1 0 0]).map (·.id) = some 1
-- Dead pin (backend went unhealthy): exact fallback to the chain.
#guard (selectPinned (some 1) [.leastConnections] (ctx 0 0)
    [mkB 0 1 9 0, mkB 1 1 8 0 false, mkB 2 1 0 0]).map (·.id) = some 2
-- Pin survives an ADDITION (where a hash key could be re-homed).
#guard (selectPinned (some 1) [.leastConnections] (ctx 0 0)
    [mkB 3 1 0 0, mkB 0 1 9 0, mkB 1 1 8 0, mkB 2 1 0 0]).map (·.id) = some 1
#eval do
  IO.println s!"sticky pin id1 (live):  {(selectPinned (some 1) [.leastConnections] (ctx 0 0) [mkB 0 1 9 0, mkB 1 1 8 0, mkB 2 1 0 0]).map (fun b : Backend => b.id)}"
  IO.println s!"sticky pin id1 (dead):  {(selectPinned (some 1) [.leastConnections] (ctx 0 0) [mkB 0 1 9 0, mkB 1 1 8 0 false, mkB 2 1 0 0]).map (fun b : Backend => b.id)} (fell back)"

/-! ## Per-upstream max-conn -/

def capTable : CapTable := fun i => if i = 0 then some 4 else none

-- id 0 is the least-loaded but AT its cap (4/4): the cap excludes it.
#guard (selectChainCapped [.leastConnections] (ctx 0 0) capTable
    [mkB 0 1 4 0, mkB 1 1 6 0]).map (·.id) = some 1
-- Below cap it participates again.
#guard (selectChainCapped [.leastConnections] (ctx 0 0) capTable
    [mkB 0 1 3 0, mkB 1 1 6 0]).map (·.id) = some 0
-- Everyone full: none — overload is surfaced, not absorbed.
#guard selectChainCapped [.leastConnections] (ctx 0 0) (fun _ => some 2)
    [mkB 0 1 2 0, mkB 1 1 2 0] = none
#eval do
  IO.println s!"max-conn: id0 at cap 4/4 -> {(selectChainCapped [.leastConnections] (ctx 0 0) capTable [mkB 0 1 4 0, mkB 1 1 6 0]).map (fun b : Backend => b.id)}; below cap 3/4 -> {(selectChainCapped [.leastConnections] (ctx 0 0) capTable [mkB 0 1 3 0, mkB 1 1 6 0]).map (fun b : Backend => b.id)}"

/-! ## Slow start -/

-- Ramp shape for configured weight 10 over a 10-unit window.
#guard (List.range 12).map (rampWeight 10 · 10) = [1,1,2,3,4,5,6,7,8,9,10,10]
-- id 0 (weight 4) just recovered (elapsed 1 of window 4 -> effective 1);
-- id 1 warm. WRR over the ramped pool gives id 0 exactly 1 of 5 rounds.
def warmPool := rampPool (fun i => if i = 0 then 1 else 100) 4
    [mkB 0 4 0 0, mkB 1 4 0 0]
#guard warmPool.map (·.weight) = [1, 4]
#guard (List.range 5).map
    (fun r => (selectChain [.weightedRoundRobin] (ctx r 0) warmPool).map (·.id))
  = [some 0, some 1, some 1, some 1, some 1]
#eval do
  IO.println s!"slow-start ramp (w=10, window=10): {(List.range 12).map (rampWeight 10 · 10)}"
  IO.println s!"slow-start WRR share (ramped 1 vs 4): {(List.range 5).map (fun r => (selectChain [.weightedRoundRobin] (ctx r 0) warmPool).map (fun b : Backend => b.id))}"

/-! ## Outlier detection -/

open Proxy.Outlier in
def ocfg : OutlierCfg := { consecutive := 3, baseEject := 10, maxEjectPercent := 34 }

open Proxy.Outlier in
def otrace (es : List OEvent) : OState := orun ocfg (OState.init [0, 1, 2]) es

open Proxy.Outlier in
def ejectedIds (s : OState) : List Nat :=
  (s.members.filter (·.ejected)).map (·.id)

open Proxy.Outlier in
-- Budget for 3 members at 34% = 1 concurrent ejection.
#guard budget ocfg 3 = 1
-- Two failures do not eject (streak below threshold)…
#guard ejectedIds (otrace [.failure 0, .failure 0]) = []
-- …the third does.
#guard ejectedIds (otrace [.failure 0, .failure 0, .failure 0]) = [0]
-- A success in between resets the streak: still nobody ejected.
#guard ejectedIds (otrace [.failure 0, .failure 0, .success 0, .failure 0]) = []
-- Budget refusal: id 1 also hits 3 consecutive failures, but the budget (1)
-- is spent on id 0 — id 1 stays in rotation instead of a 2/3 outage.
#guard ejectedIds (otrace [.failure 0, .failure 0, .failure 0,
    .failure 1, .failure 1, .failure 1]) = [0]
-- Backoff readmission: deadline = ejectedAt 0 + base 10 x count 1 = 10.
#guard ejectedIds (otrace [.failure 0, .failure 0, .failure 0, .tick 9]) = [0]
#guard ejectedIds (otrace [.failure 0, .failure 0, .failure 0, .tick 10]) = []
#eval do
  IO.println s!"outlier: 3x5xx ejects id0: {ejectedIds (otrace [.failure 0, .failure 0, .failure 0])}"
  IO.println s!"outlier: budget(34% of 3 = 1) refuses 2nd ejection: {ejectedIds (otrace [.failure 0, .failure 0, .failure 0, .failure 1, .failure 1, .failure 1])}"
  IO.println s!"outlier: tick 9 keeps ejected {ejectedIds (otrace [.failure 0, .failure 0, .failure 0, .tick 9])}, tick 10 readmits {ejectedIds (otrace [.failure 0, .failure 0, .failure 0, .tick 10])}"
  IO.println "lb-depth battery: ALL GUARDS PASSED (this file fails to compile otherwise)"

end Proxy.LbChecks
