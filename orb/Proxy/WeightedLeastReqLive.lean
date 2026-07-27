/-
# WeightedLeastReqLive — driving the PROVEN weighted least-request balancer over the byte level

Weighted least-request (the standard `LEAST_REQUEST` load-balancing policy with
per-endpoint weights) picks the backend that minimises its
*active-requests-per-weight ratio*: a backend with
weight `w` is allowed proportionally more in-flight load before it stops being
preferred, so a weight-2 endpoint tolerates twice the in-flight requests of a
weight-1 endpoint at the same preference. The comparison is done cross-multiplied,
so no division is needed and a zero-weight backend with any in-flight request
compares as infinitely loaded.

That policy is already proven, sans-IO, in `Proxy.Balance` as `wleastConn`:

  * `wleastConn`        — pick the eligible backend minimising `conns/weight`,
    ties toward the earlier list position;
  * `wleastConn_min`    — under positive weights the chosen backend's
    conns-per-weight ratio is minimal over the whole candidate list
    (`b.conns * c.weight ≤ c.conns * b.weight` for every candidate `c`);
  * `wleastConn_uniform` — over a uniform-weight pool it degenerates *exactly* to
    plain least-request (`Proxy.leastConn`), tie-breaks included.

The connection-count provenance (live open/close accounting + the probe-driven
health machine) is `Proxy.LeastConn`; the plain least-request pick and its
minimality are `Proxy.leastConn` / `leastConn_min`.

Those policies are proven but **inert** — nothing drives them over real bytes.
This lane isolates the format-agnostic, crypto-free layer: a self-delimiting
`Backend`-fleet codec built from the proven codec algebra (`putNat`/`getNat`,
`putBool`/`getBool`, `putSeq`/`getSeq` and their round-trips), and a `selftest`
that drives the WHOLE chain — serialize a fleet, decode it, run weighted
least-request over the decoded bytes, cross-check against the model — with **no
crypto whatsoever**, so it runs under `lake env lean --run`.

## Honesty / realization boundary (the ProxyLbLive / OutlierLive discipline)

This is **drorb-native** and **pure**: the encoder and decoder are our own
spec-conformant peers speaking a modelled binary framing (NOT a real proxy admin
wire, NOT live upstream request telemetry off a socket — the named residual). No
socket, no FFI call: the reused C objects are linked only to satisfy the shared
executable link line; the selftest never enters them, and it calls NO crypto.
Everything structural here is the proven Lean; the gap the selftest discharges by
construction (not by proof) is that this exe faithfully CALLS the proven policy on
real bytes. The faithfulness of the decode→select chain ITSELF is proven below as
`wlr_faithful` (composing the fleet codec round-trip with the policy), and the
policy GUARANTEE the row claims is re-derived over the on-the-wire fleet as
`wlr_picks_min_ratio`.

Residual (matching ProxyLbLive): weighted least-request is a **cold-plane**
selection policy — it runs once per request to choose an upstream, it is
config-declarable (`Dsl/Cfg/Upstream.lean`), but the chosen backend is NOT
emitted on any HTTP response wire, so there is no deployed endpoint to `curl`
whose body reveals which endpoint the ratio minimiser picked. The realization
here is byte-level (serialize → decode → select), not a live socket.

Usage:
  weighted-least-req-live selftest
-/
import Control
import Proxy.LeastConn
import Proxy.Balance

namespace Proxy.WeightedLeastReq.Live

open Control (Bytes putNat getNat putBool getBool putSeq getSeq
  getNat_putNat getBool_putBool getSeq_putSeq)
open Proxy

/-! ## §1  A self-delimiting `Backend`-fleet codec, over the proven codec algebra

`Control` gives self-delimiting, round-tripping codecs for the field types we
need (`putNat`/`getNat`, `putBool`/`getBool`, and the generic length-prefixed
`putSeq`/`getSeq`). We add a `Status` tag codec and a `Backend` record codec, and
then the fleet is just `putSeq putBackend`. Each piece carries its own round-trip
theorem, all chaining to `getFleet_put`. -/

/-- `Status` framing: a single tag byte-nat selects the arm. -/
def putStatus : Status → Bytes
  | .active   => putNat 0
  | .draining => putNat 1
  | .down     => putNat 2

def getStatus (bs : Bytes) : Option (Status × Bytes) :=
  match getNat bs with
  | some (0, r) => some (.active, r)
  | some (1, r) => some (.draining, r)
  | some (2, r) => some (.down, r)
  | _           => none

theorem getStatus_put (s : Status) (t : Bytes) :
    getStatus (putStatus s ++ t) = some (s, t) := by
  cases s <;> simp only [putStatus, getStatus, getNat_putNat]

/-- `Backend` framing: the six fields, each in its own self-delimiting field
codec (identity, weight, in-flight request count, tier, health bit, admin
status). -/
def putBackend (b : Backend) : Bytes :=
  putNat b.id ++ putNat b.weight ++ putNat b.conns ++ putNat b.tier ++
  putBool b.healthy ++ putStatus b.status

def getBackend (bs : Bytes) : Option (Backend × Bytes) := do
  let (id, r)      ← getNat bs
  let (weight, r)  ← getNat r
  let (conns, r)   ← getNat r
  let (tier, r)    ← getNat r
  let (healthy, r) ← getBool r
  let (status, r)  ← getStatus r
  some ({ id, weight, conns, tier, healthy, status }, r)

/-- **The `Backend` wire round-trip.** -/
theorem getBackend_put (b : Backend) (t : Bytes) :
    getBackend (putBackend b ++ t) = some (b, t) := by
  obtain ⟨id, weight, conns, tier, healthy, status⟩ := b
  simp only [putBackend, getBackend, List.append_assoc, getNat_putNat,
    getBool_putBool, getStatus_put, Option.bind_some, bind, Option.bind]

/-- A fleet is a length-prefixed sequence of backends. -/
def putFleet (bs : List Backend) : Bytes := putSeq putBackend bs
def getFleet (bs : Bytes) : Option (List Backend × Bytes) := getSeq getBackend bs

/-- **The fleet wire round-trip**, from the sequence codec + the backend codec. -/
theorem getFleet_put (bs : List Backend) (t : Bytes) :
    getFleet (putFleet bs ++ t) = some (bs, t) :=
  getSeq_putSeq putBackend getBackend getBackend_put bs t

/-! ## §2  Weighted least-request, over a decoded fleet

The policy runs over the eligible (healthy ∧ active) subset of the fleet — the
same gate the tiered selector uses — and picks the minimal conns-per-weight
ratio. This is the proven `Proxy.wleastConn` from `Proxy.Balance`. -/

/-- Weighted least-request over the on-the-wire fleet's eligible set. -/
def runWlr (fleet : List Backend) : Option Backend :=
  wleastConn (eligibleOf fleet)

/-! ## §3  The faithfulness theorem

The running loop's decode→select chain applies EXACTLY the proven policy. Given
any fleet serialized by `putFleet` (into a buffer with arbitrary trailing bytes
`t`), decoding it with `getFleet` and running weighted least-request over the
decoded fleet produces PRECISELY what the model computes by running the SAME
policy on the original fleet — the bytes on the wire realize the model, mediated
only by the proven codec round-trip (`getFleet_put`).

Not a `P → P`: it is inhabited (the selftest below produces such a buffer and
witnesses the equality on concrete bytes) and its content is the codec round-trip
composed with the policy — a real equation over every `fleet` and trailing `t`. -/
theorem wlr_faithful (fleet : List Backend) (t : Bytes) :
    (getFleet (putFleet fleet ++ t)).map (fun r => runWlr r.1)
      = some (runWlr fleet) := by
  rw [getFleet_put]; rfl

/-! ## §4  The policy guarantee, over the on-the-wire fleet

The faithfulness theorem says the wire realizes the model; this one says WHAT the
model guarantees, re-derived at the `runWlr` layer so it holds verbatim of the
byte-driven selection. -/

/-- **Weighted least-request picks the minimal conns-per-weight ratio.** Under
positive weights (the config-loader invariant — weight 0 is normalised to 1), the
chosen backend is eligible (healthy ∧ administratively active) and a member of the
fleet, and its active-requests-per-weight ratio is minimal over every eligible
backend, compared cross-multiplied: `b.conns * c.weight ≤ c.conns * b.weight` for
every eligible `c`. A higher-weight backend is thereby preferred even when it
carries strictly more absolute in-flight requests, in proportion to its weight;
an unhealthy/draining backend with the best ratio is provably passed over, since
ineligible backends are filtered out before the pick. -/
theorem wlr_picks_min_ratio {fleet : List Backend} {b : Backend}
    (hw : ∀ c ∈ fleet, 0 < c.weight)
    (h : runWlr fleet = some b) :
    b.eligible = true ∧ b ∈ fleet ∧
      ∀ c ∈ fleet, c.eligible = true →
        b.conns * c.weight ≤ c.conns * b.weight := by
  simp only [runWlr] at h
  have helig := mem_eligibleOf.mp (wleastConn_mem h)
  have hwe : ∀ c ∈ eligibleOf fleet, 0 < c.weight :=
    fun c hc => hw c (mem_eligibleOf.mp hc).1
  refine ⟨helig.2, helig.1, fun c hc hce => ?_⟩
  exact wleastConn_min hwe h c (mem_eligibleOf.mpr ⟨hc, hce⟩)

/-- **Totality.** If any eligible backend exists in the fleet, weighted
least-request selects one — the byte-driven pick is never a vacuous `none` when
there is a usable upstream. -/
theorem wlr_total {fleet : List Backend} {w : Backend}
    (hmem : w ∈ fleet) (helig : w.eligible = true) :
    (runWlr fleet).isSome := by
  apply wleastConn_total
  intro hnil
  have hw : w ∈ eligibleOf fleet := mem_eligibleOf.mpr ⟨hmem, helig⟩
  rw [hnil] at hw; cases hw

/-- **Conservativity.** Over a uniform-weight eligible pool, weighted
least-request is EXACTLY plain least-request (`Proxy.leastConn`), tie-breaks
included — the weight is the whole of the difference. -/
theorem wlr_uniform_eq_leastReq {fleet : List Backend} {k : Nat} (hk : 0 < k)
    (hw : ∀ c ∈ eligibleOf fleet, c.weight = k) :
    runWlr fleet = leastConn (eligibleOf fleet) :=
  wleastConn_uniform hk hw

/-! ## §5  Non-vacuity — real fleets, the weight is load-bearing

Concrete fleets exercised by `decide`, showing the pick is not trivially `none`,
that a higher-weight backend wins despite MORE absolute in-flight requests, and
that flipping the differentiator (making weights uniform, or the winner
unhealthy) changes the pick — so neither weight nor health is decorative. -/

/-- A healthy, active primary at `(id, weight, conns)`. -/
private def bk (id weight conns : Nat) : Backend :=
  ⟨id, weight, conns, 0, true, .active⟩

/-- A healthy backend but with an unhealthy verdict — the tempting minimum. -/
private def sick (id weight conns : Nat) : Backend :=
  ⟨id, weight, conns, 0, false, .active⟩

/-- **Weight is load-bearing (the headline demonstration).** Backend #1 is
weight-1 with 2 in-flight requests (ratio 2); backend #2 is weight-2 with 3
in-flight requests (ratio 1.5). Weighted least-request picks #2 — the
higher-weight endpoint — even though it carries MORE absolute in-flight requests,
because its per-weight load is lower. Plain least-request would have picked #1. -/
example : runWlr [bk 1 1 2, bk 2 2 3] = some (bk 2 2 3) := by decide

/-- **Uniform-weight mutant.** Give both backends weight 1: now #1 (2 in-flight)
beats #2 (3 in-flight) — fewer requests wins. Swapping the weight back to 2 for
#2 (above) flips the winner, so the weight is what selected #2, not the count. -/
example : runWlr [bk 1 1 2, bk 2 1 3] = some (bk 1 1 2) := by decide

/-- **Health mutant.** Backend #1 has the best ratio (weight 1, ZERO in-flight
requests) but is unhealthy; backend #2 is healthy with weight 1 and FIVE
in-flight. The pick is #2 — the ineligible minimum is provably skipped by the
eligibility gate. -/
example : runWlr [sick 1 1 0, bk 2 1 5] = some (bk 2 1 5) := by decide

/-- Were #1 healthy (best ratio), it WOULD win — confirming the exclusion above
is caused by health, not by the ratio. -/
example : runWlr [bk 1 1 0, bk 2 1 5] = some (bk 1 1 0) := by decide

/-- **Tie by ratio → earlier position.** #1 (weight 2, 4 in-flight, ratio 2) and
#2 (weight 1, 2 in-flight, ratio 2) are tied on per-weight load; the earlier one
wins. -/
example : runWlr [bk 1 2 4, bk 2 1 2] = some (bk 1 2 4) := by decide

/-- …and reversing the order reverses the winner: the tie-break is by position. -/
example : runWlr [bk 2 1 2, bk 1 2 4] = some (bk 2 1 2) := by decide

/-- The pick is genuinely `some` for a nonempty eligible fleet (not vacuous). -/
example : (runWlr [bk 1 3 7, bk 2 2 3]).isSome = true := by decide

/-! ## §6  Rendering helpers (pure) -/

def showBk (b : Backend) : String :=
  let st := match b.status with
    | .active => "active" | .draining => "draining" | .down => "down"
  s!"#{b.id} weight={b.weight} inflight={b.conns} ratio={b.conns}/{b.weight} " ++
    s!"healthy={b.healthy} status={st}"

def toHex (b : Bytes) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-! ## §7  The selftest — weighted least-request over the byte level, one process, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== weighted-least-req-live selftest : weighted least-request LB, byte-level, NO crypto =="

  -- ── the fleet ──
  -- #1 weight-1, 2 in-flight   (ratio 2.0)
  -- #2 weight-2, 3 in-flight   (ratio 1.5)  ← higher weight, MORE requests, still preferred
  -- #3 weight-1, 0 in-flight   BUT unhealthy (the tempting minimum, excluded)
  -- #4 weight-3, 6 in-flight   (ratio 2.0)  draining (excluded from selection)
  let fleet : List Backend :=
    [ bk 1 1 2, bk 2 2 3, sick 3 1 0, ⟨4, 3, 6, 0, true, .draining⟩ ]
  IO.println s!"\n-- fleet ({fleet.length} backends) --"
  for b in fleet do IO.println s!"  {showBk b}"
  let elig := eligibleOf fleet
  IO.println s!"  eligible (healthy ∧ active): {elig.map (·.id)}  (#3 unhealthy, #4 draining excluded)"

  -- ── serialize the whole fleet, decode it back over the proven codec ──
  let wire := putFleet fleet
  IO.println s!"\n-- fleet serialized (putFleet) --"
  IO.println s!"  wire bytes              : {wire.length}B  {toHex (wire.take 24)}…"
  let some (decoded, rest) := getFleet wire
    | do IO.eprintln "getFleet FAILED to decode the fleet"; return 1
  let decodeOk := rest.isEmpty && (putFleet decoded == putFleet fleet)
  IO.println s!"  getFleet∘putFleet == fleet (wire round-trip realized) : {decodeOk}"
  if !decodeOk then do IO.eprintln "fleet did NOT round-trip"; return 1

  -- ── run weighted least-request over the DECODED bytes ──
  let pick := runWlr decoded
  let pickModel := runWlr fleet
  IO.println "\n-- weighted least-request (runWlr over decoded bytes) --"
  match pick with
  | none   => IO.println "  pick                    : none"
  | some b => IO.println s!"  pick                    : {showBk b}"

  -- guarantee: the pick minimises conns/weight over the eligible set, so the
  -- higher-weight #2 (ratio 1.5) beats #1 (ratio 2.0) despite MORE in-flight.
  let picksTwo := pick == some (bk 2 2 3)
  IO.println s!"\n-- guarantee : weighted least-request picks the min conns/weight ratio --"
  IO.println s!"  #2 (weight 2, 3 in-flight, ratio 1.5) beats #1 (ratio 2.0) : {picksTwo}"

  -- weight is load-bearing: uniform-weight mutant picks the fewest-in-flight #1
  let uniformFleet : List Backend := [ bk 1 1 2, bk 2 1 3 ]
  let uniformPick := runWlr uniformFleet
  let uniformPicksOne := uniformPick == some (bk 1 1 2)
  IO.println s!"  uniform-weight mutant → fewest in-flight #1 wins           : {uniformPicksOne}"

  -- health is load-bearing: the unhealthy zero-request #3 is skipped
  let skipsSick := (pick.map (·.id)) != some 3
  IO.println s!"  unhealthy zero-inflight #3 (best ratio) is SKIPPED         : {skipsSick}"

  -- cross-check the minimality against every eligible backend explicitly
  let minOk := match pick with
    | none   => false
    | some b => elig.all (fun c => decide (b.conns * c.weight ≤ c.conns * b.weight))
  IO.println s!"  pick ratio ≤ every eligible backend ratio (cross-mult)     : {minOk}"

  -- ── the faithfulness cross-check: decode∘select == model select (wlr_faithful) ──
  let faithful := pick == pickModel
  IO.println "\n-- cross-check (realizes wlr_faithful) --"
  IO.println s!"  wire select == model select                               : {faithful}"

  if decodeOk && picksTwo && uniformPicksOne && skipsSick && minOk && faithful then do
    IO.println "\nPASS — fleet serialized, decoded; the proven weighted least-request policy"
    IO.println "       selected over the decoded bytes: the higher-weight endpoint won despite more"
    IO.println "       in-flight requests (min conns/weight ratio), unhealthy/draining excluded, cross-checked."
    IO.println "WEIGHTED LEAST-REQUEST LIVE-WIRED (drorb-native, byte-level, NO crypto, verified codec+policy)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the weighted-least-request pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: weighted-least-req-live selftest"
    return 1

end Proxy.WeightedLeastReq.Live

def main (args : List String) : IO UInt32 := Proxy.WeightedLeastReq.Live.main args
