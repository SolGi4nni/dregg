import Control.Join
import Control.Register
import Control.Store
import Control.Admin

/-!
# Control.Expiry — node-key expiry ENFORCED in the served netmap (+ re-auth signal)

`Control` already MODELS node-key expiry (`Node.keyExpiry`, `Register.expire`,
`expired_gets_no_netmap`) and the durable store carries the operator actions
(`Event.nodeExpired`, and — new here — `Event.nodeExpirySet` for
`set-expiry`/`--disable-expiry`). But the WIRE serve (`Control.Join.servedNetMapWire`)
projected `buildNetMap` over the *stored* status only: it never applied the
wall-clock expiry check at serve time, so a node whose `keyExpiry` had passed but
whose stored status was still `.authorized` would still be handed to its peers.

This module closes that: `servedNetMapWireExpiringAt now` materialises the
clock-driven expiry (`Register.expire now`) BEFORE the wire projection, so

  * an EXPIRED node (`0 < keyExpiry < now`) is dropped from EVERY other node's
    served peers — **fail-closed**, no routing to an expired node
    (`served_peers_live`, `expired_peer_not_served`);
  * the expired node's OWN poll gets `reauthResponse` — no netmap, self node
    `MachineAuthorized := false` — the wire re-auth signal (`expired_self_reauth`,
    `served_expired_self_reauths`);
  * a never-expiring node (`keyExpiry = 0`, tailscale's "the zero value if this
    node does not expire") or a not-yet-expired node stays served
    (`disabled_expiry_persists`).

CROSS-VERIFIED (PUBLIC sources, WebFetch):
  * tailscale `tailcfg.Node.KeyExpiry` doc: "the zero value if this node does not
    expire" — a zero expiry disables expiry. `RegisterResponse.NodeKeyExpired`:
    "if true, the NodeKey needs to be replaced" — the re-auth signal.
    (github.com/tailscale/tailscale, tailcfg/tailcfg.go)
  * headscale `nodes expire`: no `--expiry` ⇒ expire immediately (set expiry to
    now), `--disable`/`-d` ⇒ "node will never expire". Help: "Expiring a node
    will keep the node in the database and force it to reauthenticate."
    (github.com/juanfont/headscale, cmd/headscale/cli/nodes.go)

The GATE at the bottom drives the REAL `Control.Store.replay` over the REAL
drorb-ctl event constructors (`registerNodeEvent` / `setExpiryEvent` /
`expireNodeEvent`): two nodes register, one is force-expired, and the other's
served netmap no longer lists it, while a `--disable-expiry` node stays.

Public Tailscale protocol shape only; no external provenance.
-/

namespace Control.Expiry

open Control Control.Join Control.Store

/-! ## §1  The re-auth signal for an expired self -/

/-- The `MapResponse` an EXPIRED (or not-yet-authorized) node receives on its own
poll: **no peers, no netmap**, and its self node marked `machineAuthorized := false`
and `online := some false`. This is the wire re-auth signal — the map-path analogue
of `RegisterResponse.NodeKeyExpired` ("the NodeKey needs to be replaced"): a stock
client reading `MachineAuthorized = false` on its own node re-authenticates. -/
def reauthResponse (r : Registration) : Control.Tailcfg.MapResponse :=
  { node  := some { nodeToWire r.node with machineAuthorized := false, online := some false }
  , peers := none }

/-! ## §2  The time-aware wire serve -/

/-- **The expiry-enforcing wire serve.** Materialise clock-driven key expiry
(`Register.expire now`) over the coordination state BEFORE projecting the netmap,
then serve exactly like `Control.Join.servedNetMapWireAt`. An authorized, live
self gets its full netmap (peers already exclude every expired node, since
`authorizedPeers` keeps only `.isAuthorized` registrations and `expire` demotes
expired keys to `.expired`); an expired/unauthorized self gets `reauthResponse`. -/
def servedNetMapWireExpiringAt (now : Nat) (dm : Derp.DerpMap)
    (st : ControlState) (k : NodeKey) : Control.Tailcfg.MapResponse :=
  let st' := Register.expire now st
  match lookupReg st'.nodes k with
  | some r =>
    if r.status.isAuthorized then
      netMapToWire (buildNetMap st' r) dm (st'.dns.domains.head?.map asciiStr)
    else
      reauthResponse r
  | none => {}

/-- The default serve over drorb's own DERP relay (loopback). -/
def servedNetMapWireExpiring (now : Nat) (st : ControlState) (k : NodeKey) :
    Control.Tailcfg.MapResponse :=
  servedNetMapWireExpiringAt now drorbDerpMap st k

/-! ## §3  Fail-closed: no routing to an expired node -/

/-- **FAIL-CLOSED — every served peer is live.** After the expiry check, every peer
in a node's served netmap has a live key: `keyExpiry = 0` (never expires) or an
expiry not yet reached (`now ≤ keyExpiry`). An expired key is NEVER present as a
served peer, so its addresses are never routed to. -/
theorem served_peers_live (now : Nat) (st : ControlState) (r : Registration)
    (p : Node) (hp : p ∈ (buildNetMap (Register.expire now st) r).peers) :
    p.keyExpiry = 0 ∨ now ≤ p.keyExpiry := by
  simp only [buildNetMap, authorizedPeers, List.mem_map, List.mem_filter] at hp
  obtain ⟨rp, ⟨hmem, hcond⟩, hnode⟩ := hp
  have hauth : rp.status.isAuthorized = true := by
    simp only [Bool.and_eq_true] at hcond; exact hcond.1
  simp only [Register.expire, List.mem_map] at hmem
  obtain ⟨r0, _hr0, hrp⟩ := hmem
  by_cases hc : 0 < r0.node.keyExpiry ∧ r0.node.keyExpiry < now
  · exfalso
    have hst : rp.status = NodeStatus.expired := by
      rw [← hrp]; simp only [Register.expireReg, if_pos hc]
    rw [hst] at hauth
    exact absurd hauth (by decide)
  · have hn : rp.node = r0.node := by
      rw [← hrp]; simp only [Register.expireReg]; split <;> rfl
    rw [hn] at hnode
    rw [← hnode]
    omega

/-- **An expired node is not a served peer.** A node whose key has a nonzero, past
expiry (`0 < keyExpiry < now`) appears in NO node's served peers — the direct
fail-closed corollary of `served_peers_live`. -/
theorem expired_peer_not_served (now : Nat) (st : ControlState) (r : Registration)
    (re : Node) (hexp : 0 < re.keyExpiry) (hlt : re.keyExpiry < now) :
    re ∉ (buildNetMap (Register.expire now st) r).peers := by
  intro hp
  rcases served_peers_live now st r re hp with h | h <;> omega

/-- **A never-expiring node persists across the expiry check.** A registration with
`keyExpiry = 0` (headscale `--disable-expiry` / tailscale's zero expiry) is in the
registry unchanged after `expire now` — so it is still served. -/
theorem disabled_expiry_persists (now : Nat) (st : ControlState) (r : Registration)
    (hmem : r ∈ st.nodes) (h0 : r.node.keyExpiry = 0) :
    r ∈ (Register.expire now st).nodes :=
  Register.expire_preserves_live now st r hmem (Or.inl h0)

/-! ## §4  The re-auth signal is delivered to the expired self -/

/-- **The re-auth response carries no netmap and signals `MachineAuthorized = false`.** -/
theorem expired_self_reauth (r : Registration) :
    (reauthResponse r).peers = none
    ∧ (reauthResponse r).node.map (·.machineAuthorized) = some false := by
  constructor <;> rfl

/-- **An expired self is served the re-auth response.** If, after the expiry check,
the polling node is registered but `.expired`, `servedNetMapWireExpiringAt` returns
exactly `reauthResponse` — no netmap, re-auth signalled. -/
theorem served_expired_self_reauths (now : Nat) (dm : Derp.DerpMap)
    (st : ControlState) (k : NodeKey) (r : Registration)
    (hlk : lookupReg (Register.expire now st).nodes k = some r)
    (hexp : r.status = NodeStatus.expired) :
    servedNetMapWireExpiringAt now dm st k = reauthResponse r := by
  simp only [servedNetMapWireExpiringAt, hlk, hexp, NodeStatus.isAuthorized]
  rfl

/-! ## §5  THE GATE — a real 2-node tailnet, force-expired through the Store

Driven end-to-end through the REAL `Control.Store.replay` over the REAL drorb-ctl
event constructors. `nodeA` never expires (`keyExpiry = 0`); `nodeB` expires at
`t = 100`; `nodeC` would expire at `t = 50` but is `--disable-expiry`'d (keyExpiry
set to 0) by the operator. The operator then force-expires B (`expireNodeEvent 101`,
clock past B's `keyExpiry = 100`). We serve each node's netmap at `now = 101`. -/

def gkeyA : NodeKey := Control.Join.keyA
def gkeyB : NodeKey := Control.Join.keyB
def gkeyC : NodeKey := ⟨List.replicate 32 0xC3⟩

/-- A register request stamping `nodeKey` and its scheduled `keyExpiry`. -/
def greq (k : NodeKey) (expiry : Nat) : RegisterRequest :=
  { version := 1, nodeKey := k, oldNodeKey := ⟨[]⟩, machineKey := ⟨List.replicate 32 0⟩,
    authKey := [], expiry := expiry, ephemeral := false, followup := false }

/-- The durable log the drorb-ctl commands produce:
`nodes register A --expiry 0` (never), `nodes register B --expiry 100`,
`nodes register C --expiry 50`, `nodes set-expiry C --disable-expiry` (keyExpiry→0),
`nodes expire B` (clock advanced to 101, past B's 100). Each node also IPAM-allocated. -/
def gLog : List Event :=
  [ Control.Admin.registerNodeEvent (greq gkeyA 0),   Control.Admin.allocEvent gkeyA Control.Ipam.ip1
  , Control.Admin.registerNodeEvent (greq gkeyB 100), Control.Admin.allocEvent gkeyB Control.Ipam.ip2
  , Control.Admin.registerNodeEvent (greq gkeyC 50),  Control.Admin.allocEvent gkeyC Control.Ipam.ip3
  , Control.Admin.setExpiryEvent gkeyC 0             -- drorb-ctl nodes set-expiry C --disable-expiry
  , Control.Admin.expireNodeEvent 101 ]              -- drorb-ctl nodes expire B  (now=101 > 100)

/-- The coordination state a fresh process reconstructs from the log. -/
def gSt : CoordState := replay gLog

/-- The served wire (at `now = 101`) each node receives. -/
def gWireA : Control.Tailcfg.MapResponse := servedNetMapWireExpiring 101 gSt.control gkeyA
def gWireB : Control.Tailcfg.MapResponse := servedNetMapWireExpiring 101 gSt.control gkeyB

/-- The addresses B and C carry on the wire (`100.64.0.2/32`, `100.64.0.3/32`). -/
def bWireAddr : String := "100.64.0.2/32"
def cWireAddr : String := "100.64.0.3/32"

/-- Does any served peer of A carry `addr` in its AllowedIPs? -/
def peerHasAddr (w : Control.Tailcfg.MapResponse) (addr : String) : Bool :=
  (w.peers.getD []).any (fun p => (p.allowedIPs.getD []).contains addr)

/-! ### Runtime evidence — the gate, demonstrated over the REAL replay -/

-- Expired B is GONE from A's served netmap: its AllowedIP is not routed.
#guard peerHasAddr gWireA bWireAddr == false
-- The --disable-expiry node C stays: A still routes to it.
#guard peerHasAddr gWireA cWireAddr == true
-- Expired B's own poll gets NO netmap …
#guard gWireB.peers == none
-- … and the re-auth signal: MachineAuthorized = false on its self node.
#guard gWireB.node.map (·.machineAuthorized) == some false
-- The persisted registry (drorb-ctl `nodes list`) shows B expired, A/C authorized.
#guard (lookupReg gSt.control.nodes gkeyB).map (·.status) == some NodeStatus.expired
#guard (lookupReg gSt.control.nodes gkeyA).map (·.status) == some NodeStatus.authorized
#guard (lookupReg gSt.control.nodes gkeyC).map (·.status) == some NodeStatus.authorized
-- C's keyExpiry was disabled (set to 0 = never), B's scheduled expiry persisted.
#guard (lookupReg gSt.control.nodes gkeyC).map (·.node.keyExpiry) == some 0
#guard (lookupReg gSt.control.nodes gkeyB).map (·.node.keyExpiry) == some 100

/-- **THE GATE, as a theorem.** Over the real replayed 2-node (+disabled) tailnet at
`now = 101`: A's served netmap does NOT route to the force-expired B, DOES route to
the `--disable-expiry` node C, and B's own poll carries no netmap and the
`MachineAuthorized = false` re-auth signal. -/
theorem gate_expire_then_gone :
    peerHasAddr gWireA bWireAddr = false
    ∧ peerHasAddr gWireA cWireAddr = true
    ∧ gWireB.peers = none
    ∧ gWireB.node.map (·.machineAuthorized) = some false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ### `#eval` narrative — the my-hand demonstration (prints during `lake build`) -/

/-- Render a looked-up status for the narrative (no `ToString NodeStatus` in core). -/
def stStr : Option NodeStatus → String
  | some .authorized => "authorized"
  | some .registered => "registered"
  | some .expired    => "expired"
  | none             => "-"

def demoExpiry : IO Unit := do
  IO.println "── drorb node-key expiry: serve-path enforcement (now = 101) ──"
  IO.println s!"  registry: A={stStr ((lookupReg gSt.control.nodes gkeyA).map (·.status))}  \
    B={stStr ((lookupReg gSt.control.nodes gkeyB).map (·.status))}  \
    C={stStr ((lookupReg gSt.control.nodes gkeyC).map (·.status))}"
  IO.println s!"  A's served peers route to B ({bWireAddr})?  {peerHasAddr gWireA bWireAddr}  (expected false — B force-expired)"
  IO.println s!"  A's served peers route to C ({cWireAddr})?  {peerHasAddr gWireA cWireAddr}  (expected true — C --disable-expiry)"
  IO.println s!"  B's own poll: peers={gWireB.peers.isSome} machineAuthorized={(gWireB.node.map (·.machineAuthorized)).getD true}  (re-auth: no netmap, false)"

#eval demoExpiry

#print axioms served_peers_live
#print axioms expired_peer_not_served
#print axioms disabled_expiry_persists
#print axioms expired_self_reauth
#print axioms served_expired_self_reauths
#print axioms gate_expire_then_gone

end Control.Expiry
