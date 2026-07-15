import Reactor.ProxyDial
import Proxy.EwmaLatency

/-!
# Reactor.LoadBalance — the config-policy, load-aware upstream pick, surfaced to the host

`Reactor.ProxyDial` exposes ONE deployed reverse-proxy pick — `drorb_proxy_pick`
(`proxyPickC`) — whose policy chain is FIXED to a single rendezvous-hash link
(`dialPolicies = [rendezvousHash]`). Its C ABI carries only `(mask, key)`, so the
running dial can honour session affinity and health, but the operator's declared LB
policy (round-robin, least-connections, weighted-least-connections, least-latency)
— each fully proven — can never reach it, and neither can live per-backend load.
That is the gap this module closes.

`drorb_lb_pick` is the SAME proven selection algebra, run over the SAME
health-masked three-backend fleet (`Reactor.ProxyDial.fleetC`), but with the extra
host-supplied inputs threaded through the C ABI:

  * the **LB-policy byte** `pol` (config-declared) — `0` weighted round-robin, `1`
    least-connections, `2` weighted-least-connections, `4` EWMA least-latency,
    anything else the rendezvous-hash default. So the config policy selects the
    dial. Bytes `0..2`/default decode to a proven `Proxy.Policy` chain via
    `policyOfByte`; byte `4` dispatches to the proven `Proxy.selectLatency`
    (least-EWMA-latency), which reads a per-backend latency vector the same way
    least-connections reads the in-flight count;
  * the live per-backend **in-flight load** `conns` (the host's own counters) —
    which makes the load-sensitive policies (least-connections) observable at the
    running dial, not just the config-invariant ones;
  * the live per-backend **EWMA latency** `lat` (the host's own moving average,
    maintained by `Proxy.ewmaStep`) — which makes the latency-aware policy dial
    the lowest-latency backend.

The frame the host writes: `pol :: round :: mask :: n :: conns[n] :: … :: key`.
`round` is the shard-local round counter weighted round-robin walks; `mask` is the
live health/breaker bitmask (bit `i` ⇒ backend `i` up); `conns[i]` is backend
`i`'s in-flight count; `key` is the sticky-affinity material. For the latency byte
(`4`) the frame is EXTENDED with a per-backend latency vector between the load
vector and the key (`… :: conns[n] :: lat[n] :: key`); for every other byte the
frame is exactly the legacy `conns[n] :: key` and the latency input is unused
(`pick_lat_irrel`), so the existing callers are byte-for-byte unaffected.

## What is proven here

  * **Health / breaker ejection holds for EVERY policy byte**
    (`pick_health_ejects`): whatever LB policy the config selects — chain-based or
    least-latency — a backend whose live bit is clear is never dialled. This is the
    load-bearing safety property; `#print axioms` at the bottom shows it rests on
    no new axioms.
  * **Chosen ⇒ eligible** (`pickBackend_eligible`): a picked backend is a healthy,
    active member of the fleet, for both the policy-chain path and the
    least-latency path (`Proxy.selectChain_eligible` / `Proxy.selectLatency_eligible`).
  * **Round-robin is cyclic / fair** (`wrr_cyclic`): over the all-up uniform fleet
    the weighted-round-robin byte dials backend `round % 3` — each of the three
    backends its exact one-third share, in strict rotation.
  * **The latency input never perturbs the non-latency policies**
    (`pick_lat_irrel`): for any byte `≠ 4`, the pick is independent of the latency
    vector — so extending the ABI leaves the round-robin / least-connections /
    rendezvous dials exactly as they were.
  * **The config byte visibly changes the dial** (runnable `#eval` + `decide`
    checks): over one loaded fleet the round-robin byte, the least-connections
    byte, and the least-latency byte dial DIFFERENT backends — each config policy
    reaching the running dial.
-/

namespace Reactor.LoadBalance

open Proxy (Backend Policy Ctx selectChain select tierPool)
open Reactor.ProxyDial (fleetC keyOf dialHash)

/-! ## The config-byte policy codec (shared convention with `Dsl.Config.policyOfByte`) -/

/-- Decode a config LB-policy byte to a proven `Proxy.Policy` (the chain-based
classes). The convention is the DSL's (`Dsl.Config.policyOfByte`): `0` weighted
round-robin, `1` least-connections, `2` weighted-least-connections, anything else
the rendezvous-hash default. The least-latency class (byte `latencyByte`) is NOT a
`Proxy.Policy` — it reads a live latency vector and is dispatched separately in
`pickBackend`. -/
def policyOfByte : Nat → Policy
  | 0 => .weightedRoundRobin
  | 1 => .leastConnections
  | 2 => .weightedLeastConnections
  | _ => .rendezvousHash

/-- The single-link policy chain a config byte denotes — the value handed to
`Proxy.selectChain`. -/
def chainOfByte (n : Nat) : List Policy := [policyOfByte n]

/-- The config byte selecting EWMA least-latency selection. Chosen as `4` (the
first value past the `0..3` the `Proxy.Policy` codec uses), so it never collides
with a chain-based policy byte and every other byte keeps its legacy meaning. -/
def latencyByte : Nat := 4

/-- The per-request selection context: the round counter (weighted round-robin),
the affinity key (rendezvous), and the concrete dial hash. -/
def lbCtx (round key : Nat) : Ctx := { round := round, key := key, hash := dialHash }

/-! ## The proven pick -/

/-- **The proven config-policy + load-aware pick (backend).** For byte
`latencyByte`, run the proven least-EWMA-latency selector `Proxy.selectLatency`
over the live health-masked, load-carrying fleet with the host's latency vector.
For every other byte, run the REAL `Proxy.selectChain` for the config-declared
policy chain over the same fleet. `none` iff no backend is eligible. -/
def pickBackend (pol round mask : Nat) (conns lat : Nat → Nat) (key : Nat) :
    Option Backend :=
  if pol = latencyByte then
    Proxy.selectLatency lat (fleetC mask conns)
  else
    selectChain (chainOfByte pol) (lbCtx round key) (fleetC mask conns)

/-- **The proven pick (id).** The chosen backend's stable id — what the host maps
to a configured backend socket. -/
def pick (pol round mask : Nat) (conns lat : Nat → Nat) (key : Nat) : Option Nat :=
  (pickBackend pol round mask conns lat key).map (·.id)

/-! ## Structural lemmas -/

/-- A single-link chain is exactly the underlying tiered `select`. -/
theorem selectChain_single (p : Policy) (ctx : Ctx) (bs : List Backend) :
    selectChain [p] ctx bs = select p ctx bs := by
  unfold selectChain
  cases select p ctx bs <;> rfl

/-- Every `fleetC` member's health bit is exactly its mask bit. -/
theorem fleetC_healthy {mask : Nat} {conns : Nat → Nat} {b : Backend}
    (h : b ∈ fleetC mask conns) : b.healthy = mask.testBit b.id := by
  simp only [fleetC, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with h | h | h <;> subst h <;> rfl

/-- For any non-latency byte, the pick reduces to the config policy chain over the
loaded fleet — independent of the latency vector. -/
theorem pick_nonLat {pol round mask : Nat} {conns lat : Nat → Nat} {key : Nat}
    (h : pol ≠ latencyByte) :
    pick pol round mask conns lat key
      = (selectChain (chainOfByte pol) (lbCtx round key) (fleetC mask conns)).map (·.id) := by
  unfold pick pickBackend
  rw [if_neg h]

/-- **The latency input never perturbs a non-latency policy.** For any byte `≠
latencyByte`, the pick is the same whatever the latency vector — so extending the
ABI with a latency vector leaves the round-robin / least-connections / rendezvous
dials byte-for-byte unchanged. -/
theorem pick_lat_irrel {pol round mask key : Nat} {conns lat lat' : Nat → Nat}
    (h : pol ≠ latencyByte) :
    pick pol round mask conns lat key = pick pol round mask conns lat' key := by
  rw [pick_nonLat h, pick_nonLat h]

/-! ## Seam theorems -/

/-- **Chosen ⇒ eligible.** A picked backend is a healthy, active member of the
fleet — for both the policy-chain path (`Proxy.selectChain_eligible`) and the
least-latency path (`Proxy.selectLatency_eligible`), for ANY config byte. -/
theorem pickBackend_eligible {pol round mask key : Nat} {conns lat : Nat → Nat}
    {b : Backend} (h : pickBackend pol round mask conns lat key = some b) :
    b ∈ fleetC mask conns ∧ b.eligible = true := by
  unfold pickBackend at h
  split at h
  · exact Proxy.selectLatency_eligible h
  · exact let e := Proxy.selectChain_eligible h; ⟨e.1, e.2.1⟩

/-- **Health / breaker ejection for EVERY policy byte.** Whatever LB policy the
config selects — chain-based or least-latency — a backend whose live mask bit is
clear (probe down, or breaker open and the bit cleared) is NEVER dialled —
eligibility is the selector's, independent of which policy the byte chose. The
running-path meaning of "eject an unhealthy backend". -/
theorem pick_health_ejects {pol round mask key i : Nat} {conns lat : Nat → Nat}
    (hbit : mask.testBit i = false) : pick pol round mask conns lat key ≠ some i := by
  unfold pick
  cases hb : pickBackend pol round mask conns lat key with
  | none => exact fun h => nomatch h
  | some b =>
    intro h
    injection h with h
    dsimp only at h
    obtain ⟨hmem, helig⟩ := pickBackend_eligible hb
    have hh : b.healthy = true := by
      simp only [Backend.eligible, Bool.and_eq_true] at helig
      exact helig.1
    rw [fleetC_healthy hmem, h, hbit] at hh
    exact absurd hh (by decide)

/-- **Round-robin is cyclic and fair.** Over the all-up uniform fleet, the
weighted-round-robin byte (`0`) dials backend `round % 3` — strict rotation, each
of the three backends its exact one-third share. -/
theorem wrr_cyclic (round : Nat) :
    pick 0 round 0b111 (fun _ => 0) (fun _ => 0) 0 = some (round % 3) := by
  have h3 : round % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [pick_nonLat (by decide)]
  simp only [chainOfByte, policyOfByte, selectChain_single,
    Proxy.select, Proxy.applyPolicy, lbCtx]
  -- The tier pool of the all-up uniform fleet is the fleet itself, in order.
  have hpool : tierPool (fleetC 0b111 (fun _ => 0)) =
      [ ⟨0, 1, 0, 0, true, .active⟩, ⟨1, 1, 0, 0, true, .active⟩,
        ⟨2, 1, 0, 0, true, .active⟩ ] := by decide
  rw [hpool]
  -- Weighted round-robin over three unit-weight backends: residue = round % 3.
  simp only [Proxy.wrr, Proxy.totalWeight]
  rw [if_neg (by decide)]
  show (Proxy.pickByResidue _ (round % (1 + (1 + (1 + 0))))).map _ = _
  have h1 : (1 + (1 + (1 + 0))) = 3 := by decide
  rw [h1]
  -- Case on the three residues (`round % 3 < 3`); no residue ≥ 3 survives.
  revert h3
  generalize round % 3 = r
  intro h3
  obtain _ | _ | _ | r := r
  · decide
  · decide
  · decide
  · omega

/-! ## The C ABI seam the host calls per request -/

/-- **`drorb_lb_pick` — the proven config-policy + load-aware pick as a
`ByteArray → ByteArray`.** Input frame: byte 0 = the config LB-policy byte, byte 1
= the round counter, byte 2 = the live health/breaker mask, byte 3 = the number
`n` of per-backend bytes, bytes `4 .. 4+n` = the in-flight counts. For the
latency byte (`4`) the frame continues with `n` per-backend EWMA-latency bytes and
then the sticky key; for every other byte the rest is the sticky key directly (the
legacy frame). Output: the decimal-ASCII chosen backend id, or EMPTY bytes when no
backend is eligible (the host then serves a 503). -/
@[export drorb_lb_pick]
def lbPickC (input : ByteArray) : ByteArray :=
  match input.toList with
  | pol :: round :: mask :: n :: rest =>
      let k := n.toNat
      let load := rest.take k
      let conns := fun i => (load.get? i).map (·.toNat) |>.getD 0
      if pol.toNat = latencyByte then
        -- extended frame: conns[k] :: lat[k] :: key
        let rest2 := rest.drop k
        let latB := rest2.take k
        let lat := fun i => (latB.get? i).map (·.toNat) |>.getD 0
        let key := keyOf (rest2.drop k)
        match pick pol.toNat round.toNat mask.toNat conns lat key with
        | some id => (toString id).toUTF8
        | none    => ByteArray.empty
      else
        -- legacy frame: conns[k] :: key   (latency unused, `pick_lat_irrel`)
        let key := keyOf (rest.drop k)
        match pick pol.toNat round.toNat mask.toNat conns (fun _ => 0) key with
        | some id => (toString id).toUTF8
        | none    => ByteArray.empty
  | _ => ByteArray.empty

/-! ## Runnable checks — the config policy reaches the dial and honours health -/

-- Weighted round-robin (byte 0) over the all-up uniform fleet cycles 0,1,2,0,…
example : pick 0 0 0b111 (fun _ => 0) (fun _ => 0) 0 = some 0 := by decide
example : pick 0 1 0b111 (fun _ => 0) (fun _ => 0) 0 = some 1 := by decide
example : pick 0 2 0b111 (fun _ => 0) (fun _ => 0) 0 = some 2 := by decide
example : pick 0 3 0b111 (fun _ => 0) (fun _ => 0) 0 = some 0 := by decide

/-- A loaded fleet: backend 0 has 5 in-flight, backend 1 has 1, backend 2 has 3. -/
def demoLoad : Nat → Nat := fun i => if i == 0 then 5 else if i == 1 then 1 else 3

/-- A latency fleet: backend 0's EWMA is 30ms, backend 1's is 50ms, backend 2's is
10ms — so least-latency prefers backend 2. -/
def demoLat : Nat → Nat := fun i => if i == 0 then 30 else if i == 1 then 50 else 10

-- Least-connections (byte 1) dials the least-loaded backend 1…
example : pick 1 0 0b111 demoLoad (fun _ => 0) 0 = some 1 := by decide
-- …while round-robin (byte 0), load-blind, dials backend 0 over the SAME fleet.
example : pick 0 0 0b111 demoLoad (fun _ => 0) 0 = some 0 := by decide
-- The config byte visibly changes the dial.
example : pick 0 0 0b111 demoLoad (fun _ => 0) 0 ≠ pick 1 0 0b111 demoLoad (fun _ => 0) 0 := by decide

-- EWMA least-latency (byte 4) dials the lowest-latency backend 2…
example : pick 4 0 0b111 (fun _ => 0) demoLat 0 = some 2 := by decide
-- …a DIFFERENT backend than least-connections (byte 1 → backend 1) over the
-- SAME loaded fleet: the latency policy reaches the running dial.
example : pick 4 0 0b111 demoLoad demoLat 0 = some 2 := by decide
example : pick 1 0 0b111 demoLoad demoLat 0 = some 1 := by decide
example : pick 4 0 0b111 demoLoad demoLat 0 ≠ pick 1 0 0b111 demoLoad demoLat 0 := by decide

-- Eject backend 0 (its bit clear): least-connections moves to the next
-- least-loaded ELIGIBLE backend (with 0 gone the eligible are 1 (load 1) and
-- 2 (load 3) ⇒ backend 1).
example : pick 1 0 0b110 demoLoad (fun _ => 0) 0 = some 1 := by decide
-- Eject backend 2 (the lowest-latency one, bit clear): least-latency moves to the
-- next lowest-latency ELIGIBLE backend (0 at 30ms beats 1 at 50ms) ⇒ backend 0.
example : pick 4 0 0b011 (fun _ => 0) demoLat 0 = some 0 := by decide
-- Whole pool down ⇒ no pick (the host serves 503, never dials) — every policy.
example : pick 0 0 0b000 (fun _ => 0) (fun _ => 0) 0 = none := by decide
example : pick 4 0 0b000 (fun _ => 0) demoLat 0 = none := by decide

#eval do
  IO.println s!"drorb_lb_pick honours the config LB byte: roundRobin(round 0..3) -> \
    {[0,1,2,3].map (fun r => pick 0 r 0b111 (fun _ => 0) (fun _ => 0) 0)}, \
    leastConn(loaded) -> {pick 1 0 0b111 demoLoad (fun _ => 0) 0}, \
    roundRobin(loaded) -> {pick 0 0 0b111 demoLoad (fun _ => 0) 0}, \
    leastLatency(demoLat) -> {pick 4 0 0b111 (fun _ => 0) demoLat 0}"

#print axioms pick_health_ejects
#print axioms pickBackend_eligible

end Reactor.LoadBalance
