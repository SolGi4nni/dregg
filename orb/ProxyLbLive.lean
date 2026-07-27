/-
# ProxyLbLive — driving the PROVEN load-balancer policies over the byte level

The `Proxy` foundation models a reverse proxy's **cold-plane selection algebra**
as sans-IO, proven Lean: eligibility filtering, tiered fallback, and the three
production balancing policies —

  * least-connections (`Proxy.leastConn`, deepened in `Proxy.LeastConn` with
    live active-connection accounting and the probe-driven health machine):
    the eligible backend with the fewest in-flight connections wins, ties to the
    earlier list position (`leastConn_min`, `LeastConn.leastconn_picks_min`);
  * weighted round-robin (`Proxy.wrr`, `Proxy.Wrr`): a single atomic round
    counter walks the cumulative-weight intervals; over any full weight-window a
    backend is selected EXACTLY its weight's worth of times (`wrr_window_weight`);
  * cookie-carried sticky affinity (`Proxy.selectPinned`, `Proxy.StickyPin`): a
    live pin binds a session to its backend outright, bypassing the balancer,
    and a dead pin falls back to the plain policy chain
    (`selectPinned_affinity_unique`, `selectPinned_dead_pin`).

Those policies are proven but **inert** — nothing drives them over real bytes.
This lane isolates the format-agnostic, crypto-free layer: a self-delimiting
`Backend`-fleet codec built from the proven codec algebra (`putNat`/`getNat`,
`putBool`/`getBool`, `putSeq`/`getSeq` and their round-trips), and a `selftest`
that drives the WHOLE chain — serialize a fleet, decode it, run each policy over
the decoded bytes — with **no crypto whatsoever**, so it runs under
`lake env lean --run`.

## Honesty / realization boundary (the NetmapLive / DnsResolveLive discipline)

This is **drorb-native** and **pure**: the encoder and decoder are our own
spec-conformant peers speaking a modelled binary framing (NOT a real proxy admin
wire, NOT live upstream health/connection telemetry — the named residual). No
socket, no FFI call: the reused C objects are linked only to satisfy the shared
executable link line; the selftest never enters them. Everything structural here
is the proven Lean; the gap the selftest discharges by construction (not by
proof) is that this exe faithfully CALLS the proven policy functions on real
bytes. The faithfulness of the decode→select chain ITSELF is proven below as
`proxy_lb_faithful` (composing the fleet codec round-trip with each policy), and
the three policy GUARANTEES are re-derived over the on-the-wire fleet
(`runLeastConn_picks_min`, `runWrr_respects_weights`, `runSticky_pins_key`).

Usage:
  proxy-lb-live selftest
-/
import Control
import Proxy.LeastConn
import Proxy.Wrr
import Proxy.StickyPin

namespace ProxyLbLive

open Control (Bytes putNat getNat putBool getBool putSeq getSeq
  getNat_putNat getBool_putBool getSeq_putSeq)
open Proxy

/-! ## §1  A self-delimiting `Backend`-fleet codec, over the proven codec algebra

`Control` gives self-delimiting, round-tripping codecs for the field types we
need (`putNat`/`getNat`, `putBool`/`getBool`, and the generic length-prefixed
`putSeq`/`getSeq`). We add two pieces — a `Status` tag codec and a `Backend`
record codec — and then the fleet is just `putSeq putBackend`. Each piece carries
its own round-trip theorem, all chaining to `getFleet_put`. -/

/-- `Status` framing: a single tag byte selects the arm. -/
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
codec (identity, weight, in-flight count, tier, health bit, admin status). -/
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

/-! ## §2  The three policies, over a decoded fleet

Each policy runs over the eligible (healthy ∧ active) subset of the fleet — the
same gate the tiered selector uses. `runLeastConn` and `runWrr` are the plain
policies from `Proxy.Balance`/`Proxy.Wrr`; `runSticky` is the cookie-pinned
selector from `Proxy.StickyPin`. -/

/-- Least-connections over the on-the-wire fleet's eligible set. -/
def runLeastConn (fleet : List Backend) : Option Backend :=
  leastConn (eligibleOf fleet)

/-- Weighted round-robin over the on-the-wire fleet's eligible set. -/
def runWrr (round : Nat) (fleet : List Backend) : Option Backend :=
  wrr (eligibleOf fleet) round

/-- Cookie-pinned selection over the on-the-wire fleet (the pin gate is the same
eligibility gate; a dead pin falls back to the policy chain). -/
def runSticky (pin : Option Nat) (ps : List Policy) (ctx : Ctx)
    (fleet : List Backend) : Option Backend :=
  selectPinned pin ps ctx fleet

/-! ## §3  The faithfulness theorem

The running loop's decode→select chain applies EXACTLY the proven policy. Given
any fleet serialized by `putFleet` (into a buffer with arbitrary trailing bytes
`t`), decoding it with `getFleet` and running any of the three policies over the
decoded fleet produces PRECISELY what the model computes by running the SAME
policy on the original fleet — the bytes on the wire realize the model, mediated
only by the proven codec round-trip (`getFleet_put`).

Not a `P → P`: it is inhabited (the selftest below produces such a buffer and
witnesses the equalities on concrete bytes) and its content is the codec
round-trip composed with each policy — a real equation over every `fleet`,
`round`, `pin`, `ps`, `ctx`, and trailing `t`. -/
theorem proxy_lb_faithful (fleet : List Backend) (round : Nat)
    (pin : Option Nat) (ps : List Policy) (ctx : Ctx) (t : Bytes) :
    (getFleet (putFleet fleet ++ t)).map
        (fun r => (runLeastConn r.1, runWrr round r.1, runSticky pin ps ctx r.1))
      = some (runLeastConn fleet, runWrr round fleet, runSticky pin ps ctx fleet) := by
  rw [getFleet_put]; rfl

/-! ## §4  The three policy guarantees, over the on-the-wire fleet

The faithfulness theorem says the wire realizes the model; these three say WHAT
the model guarantees, re-derived at the `runX` layer so they hold verbatim of
the byte-driven selection. -/

/-- **Least-connections picks the min-active healthy backend.** The chosen
backend is eligible (healthy ∧ administratively active) and a member of the
fleet, and its in-flight count is minimal over every eligible backend — a
lower-count but unhealthy/draining backend is provably passed over, since
ineligible backends are filtered out before the pick. -/
theorem runLeastConn_picks_min {fleet : List Backend} {b : Backend}
    (h : runLeastConn fleet = some b) :
    b.eligible = true ∧ b ∈ fleet ∧
      ∀ c ∈ fleet, c.eligible = true → b.conns ≤ c.conns := by
  have helig := mem_eligibleOf.mp (leastConn_mem h)
  refine ⟨helig.2, helig.1, fun c hc hce => ?_⟩
  exact leastConn_min h c (mem_eligibleOf.mpr ⟨hc, hce⟩)

/-- **Least-connections through the full `Proxy.LeastConn` provenance.** The same
guarantee stated against the live active-connection accounting and the
probe-driven health machine: for every node the health FSM took Up and that is
administratively active, the pick's in-flight count is ≤ that node's live count
read from the connection table. A node the health machine drove Down (its
`healthOf` is false) is excluded even at zero in-flight connections. -/
theorem leastconn_node_picks_min {ct : LeastConn.ConnTable}
    {ns : List LeastConn.Node} {b : Backend} (h : LeastConn.pick ct ns = some b) :
    ∀ n ∈ ns, LeastConn.healthOf n = true → n.status = .active →
      b.conns ≤ LeastConn.active n.id ct :=
  LeastConn.leastconn_picks_min h

/-- **Weighted round-robin respects the weights.** With pairwise-distinct
identities, over any window of `totalWeight (eligibleOf fleet)` consecutive
rounds — aligned or not — an eligible backend is selected EXACTLY its weight's
worth of times. Exact window fairness, not a ±1 proportion bound. -/
theorem runWrr_respects_weights {fleet : List Backend} {b : Backend}
    (hnd : idsNodup (eligibleOf fleet)) (hmem : b ∈ eligibleOf fleet)
    (start : Nat) :
    cnt (fun j => decide (runWrr (start + j) fleet = some b))
        (totalWeight (eligibleOf fleet)) = b.weight :=
  wrr_window_weight hnd hmem start

/-- **Sticky affinity pins a key.** While an eligible backend carries the pinned
identity, the pinned selector returns exactly that backend — the balancing policy
is bypassed entirely (under distinct ids, the very backend). -/
theorem runSticky_pins_key {bid : Nat} {ps : List Policy} {ctx : Ctx}
    {fleet : List Backend} {w : Backend} (hnd : idsNodup fleet)
    (hmem : w ∈ fleet) (hid : w.id = bid) (helig : w.eligible = true) :
    runSticky (some bid) ps ctx fleet = some w :=
  selectPinned_affinity_unique hnd hmem hid helig

/-- **A dead pin falls back to the plain policy chain.** When no eligible backend
carries the pinned identity (backend gone, unhealthy, draining, or down), the
pinned selector is literally the plain chain — re-balancing inherits every chain
theorem, and a stale cookie can never resurrect an ineligible backend. -/
theorem runSticky_dead_pin_falls_back {bid : Nat} {ps : List Policy} {ctx : Ctx}
    {fleet : List Backend}
    (hdead : ∀ b ∈ fleet, b.eligible = true → b.id ≠ bid) :
    runSticky (some bid) ps ctx fleet = selectChain ps ctx fleet :=
  selectPinned_dead_pin hdead

/-! ## §5  Rendering helpers (pure) -/

def showBackend (b : Backend) : String :=
  let st := match b.status with | .active => "active" | .draining => "draining" | .down => "down"
  s!"#{b.id} w={b.weight} conns={b.conns} tier={b.tier} healthy={b.healthy} {st}"

def showPick : Option Backend → String
  | none   => "(none)"
  | some b => showBackend b

def toHex (b : Bytes) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-! ## §6  The selftest — the LB policies over the byte level, one process, NO crypto -/

/-- A backend record with the six fields. -/
def mkBackend (id weight conns tier : Nat) (healthy : Bool) (status : Status) : Backend :=
  { id, weight, conns, tier, healthy, status }

def selftest : IO UInt32 := do
  IO.println "== proxy-lb-live selftest : reverse-proxy LB policies, byte-level, NO crypto =="

  -- ── the configured fleet ──
  -- #1,#2 healthy+active (eligible); #3 healthy min-conns but UNHEALTHY; #4 draining.
  let b1 := mkBackend 1 1 5 0 true  .active
  let b2 := mkBackend 2 2 2 0 true  .active
  let b3 := mkBackend 3 1 0 0 false .active     -- tempting min (0 conns) but ejected
  let b4 := mkBackend 4 3 9 0 true  .draining   -- excluded: not taking new work
  let fleet := [b1, b2, b3, b4]

  IO.println "\n-- fleet --"
  for b in fleet do IO.println s!"  {showBackend b}"
  IO.println s!"eligible (healthy ∧ active): {(eligibleOf fleet).map (·.id)}"

  -- ── serialize the fleet, decode it back over the proven codec ──
  let wire := putFleet fleet
  IO.println s!"\n-- fleet serialized (putFleet) --"
  IO.println s!"wire bytes             : {wire.length}B  {toHex (wire.take 20)}…"
  let some (decoded, rest) := getFleet wire
    | do IO.eprintln "getFleet FAILED to decode the fleet"; return 1
  let decodeOk := rest.isEmpty && (putFleet decoded == putFleet fleet)
  IO.println s!"getFleet∘putFleet == fleet (wire round-trip realized) : {decodeOk}"
  if !decodeOk then do IO.eprintln "fleet did NOT round-trip"; return 1

  -- ── policy 1: least-connections over the DECODED fleet ──
  let lc := runLeastConn decoded
  let lcModel := runLeastConn fleet
  IO.println "\n-- least-connections (runLeastConn over decoded bytes) --"
  IO.println s!"  pick                 : {showPick lc}"
  -- min-active-healthy: #3 has 0 conns but is unhealthy; #2 (conns 2) is the eligible min.
  let lcOk := lc == some b2
  let lcSkipsEjected := lc != some b3
  IO.println s!"  picks eligible min #2 (conns 2)        : {lcOk}"
  IO.println s!"  skips unhealthy min #3 (conns 0)       : {lcSkipsEjected}"
  IO.println s!"  wire pick == model pick                : {lc == lcModel}"

  -- ── the full LeastConn provenance: nodes + health machine (crypto-free FSM) ──
  -- node #1 has ZERO in-flight but three consecutive probe failures ⇒ health FSM
  -- takes it Down (fall=3); node #2 healthy with 5 in-flight. Pick = #2.
  let nodeEjected : LeastConn.Node :=
    ⟨1, 1, 0, .active, ⟨2, 3⟩, ⟨true, 0, 0⟩, [.fail, .fail, .fail]⟩
  let nodeOk : LeastConn.Node := ⟨2, 1, 0, .active, ⟨2, 3⟩, ⟨true, 0, 0⟩, []⟩
  let ct : LeastConn.ConnTable := [(1, 0), (2, 5)]
  let nodePick := LeastConn.pick ct [nodeEjected, nodeOk]
  let ejectedDown := LeastConn.healthOf nodeEjected == false
  let nodePicksHealthy := (nodePick.map (·.id)) == some 2
  IO.println "\n-- least-connections with health-machine provenance (LeastConn.pick) --"
  IO.println s!"  ejected node health FSM verdict Down   : {ejectedDown}"
  IO.println s!"  pick skips 0-conn ejected, takes #2    : {nodePicksHealthy}"

  -- ── policy 2: weighted round-robin over the DECODED fleet, full weight window ──
  -- eligible = [#1 (w1), #2 (w2)], totalWeight 3 ⇒ over 3 rounds: #1 once, #2 twice.
  let elig := eligibleOf decoded
  let W := totalWeight elig
  let counts := elig.map (fun bk =>
    (bk.id, (List.range W).foldl (fun acc j =>
      if runWrr j decoded == some bk then acc + 1 else acc) 0))
  IO.println "\n-- weighted round-robin (runWrr over decoded bytes) --"
  IO.println s!"  full weight window W = totalWeight     : {W}"
  IO.println s!"  selections per backend over [0,W)      : {counts}"
  let wrrSeq := (List.range W).map (fun j => (runWrr j decoded).map (·.id))
  IO.println s!"  round → pick id                        : {wrrSeq}"
  let wrrFair := counts == [(1, 1), (2, 2)]
  IO.println s!"  each backend selected == its weight    : {wrrFair}"

  -- ── policy 3: sticky pin over the DECODED fleet ──
  let ctx : Ctx := ⟨0, 0, fun _ _ => 0⟩
  let chain : List Policy := [.leastConnections]
  let pinLive := runSticky (some 2) chain ctx decoded      -- pin #2 (eligible) ⇒ binds
  let pinDead := runSticky (some 3) chain ctx decoded      -- pin #3 (unhealthy) ⇒ fallback
  let pinGone := runSticky (some 99) chain ctx decoded      -- unknown id ⇒ fallback
  let fallback := selectChain chain ctx decoded
  IO.println "\n-- sticky pin (runSticky over decoded bytes) --"
  IO.println s!"  pin #2 (eligible) binds                : {pinLive == some b2}"
  IO.println s!"  pin #3 (unhealthy) falls back to chain : {pinDead == fallback}"
  IO.println s!"  pin #99 (absent) falls back to chain   : {pinGone == fallback}"
  IO.println s!"  chain verdict (no pin)                 : {showPick fallback}"

  -- ── the faithfulness cross-check: decode∘select == model select (proxy_lb_faithful) ──
  let faithful :=
    (runLeastConn decoded == runLeastConn fleet) &&
    (runWrr 0 decoded == runWrr 0 fleet) &&
    (runWrr 1 decoded == runWrr 1 fleet) &&
    (runSticky (some 2) chain ctx decoded == runSticky (some 2) chain ctx fleet)
  IO.println "\n-- cross-check (realizes proxy_lb_faithful) --"
  IO.println s!"  wire select == model select (all 3 policies) : {faithful}"

  if decodeOk && lcOk && lcSkipsEjected && (lc == lcModel) && ejectedDown &&
      nodePicksHealthy && wrrFair && (pinLive == some b2) &&
      (pinDead == fallback) && (pinGone == fallback) && faithful then do
    IO.println "\nPASS — fleet serialized, decoded; least-connections, weighted round-robin,"
    IO.println "       and sticky pin each driven over the decoded bytes and cross-checked."
    IO.println "PROXY LB POLICIES LIVE-WIRED (drorb-native, byte-level, NO crypto, verified codec+policies)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the LB-policy pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: proxy-lb-live selftest"
    return 1

end ProxyLbLive

def main (args : List String) : IO UInt32 := ProxyLbLive.main args
