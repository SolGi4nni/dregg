import Control
import Control.Acl
import Control.Dns
import Control.Derp
import Control.Tailcfg
import Control.TailcfgBridge
import Hygiene

/-!
# Control.Join — the coordination JOIN: the served `MapResponse` is a FUNCTION of the
proven ACL compilation, the proven netmap, and drorb's OWN verified DERP relay.

The coordination server (`Control.step` / `Control.buildNetMap`) hands each authorized
node a full `MapResponse` carrying (public `tailcfg.MapResponse`, cross-checked against
`tailscale/tailcfg/tailcfg.go`):

  * `PacketFilter : [FilterRule]` — the compiled ACL. **This is wired to
    `Control.Acl.compile`** (`policy_default_deny`, `policy_allow_iff_entry`), not
    hand-set. `Control.Acl` speaks `IpFilter.Cidr` (family + MSB-first bit-string);
    the coordination core speaks byte-addressed `Control.Prefix`. `cidrToPrefix` bridges
    the two representations (packing the bit-string MSB-first into big-endian octets,
    the order `Wireguard.Peer.bitAt` reads), and `compiledPacketFilter` is literally
    `(Acl.compile p).map ruleConv` — the served ACL is a function of the proven object.

  * `DERPMap` — a region that **NAMES drorb's own verified DERP relay** (inc-1,
    `Derp.Server.dispatch` / `forward_to_addressed_only` / `relay_blind`, live on the
    socket via `DerpRelayLive.forwardLoop`). The region's node endpoint is exactly the
    `127.0.0.1:3340` that `DerpRelayLive.runRelay` binds (`tcpListen 3340`), so a
    registered node relays THROUGH drorb's proven relay. This is the inc-1 ↔ inc-2 JOIN.
    (public `tailcfg.DERPRegion` = `RegionID`/`RegionCode`/`Nodes`; `DERPNode`
    `HostName`/`IPv4` + `DERPPort` abstracted to `Control.Endpoint`.)

  * `Peers` / `DNSConfig` — from the proven netmap (`authorizedPeers`, the "netmap only
    names authorized peers" invariant) and MagicDNS (`Control.Dns.buildDns`).

The GATE (below) drives the REAL `Control.step` on a 2-node tailnet and inspects the
served `MapResponse`: node B appears as a Peer, `PacketFilter = compiledPacketFilter`
of the policy (a definitional equality — `served_filter_is_acl_compile`), the served
filter is default-deny on real packets in drorb's own byte representation
(`served_allows_in_policy` / `served_denies_wrong_port` / `served_denies_out_of_policy`,
matching `Control.Acl`'s upstream `tt_*` verdicts), and the DERPMap region points at
drorb-as-relay (`served_derp_names_drorb`, `served_derp_valid`). The `Control.Acl`,
`Control.Dns`, `Control.Derp` theorems are UNCHANGED and load-bearing.

Everything is public Tailscale protocol shape (`tailcfg`, `DERP`, MagicDNS); no external
provenance.
-/

namespace Control.Join

open Control

/-! ## §1  `IpFilter.Cidr` → `Control.Prefix` — the representation bridge

`Control.Acl` compiles to `IpFilter.Cidr` (an address family plus an MSB-first Boolean
network prefix of length `len`). The coordination core's `Prefix` is byte-addressed
(`addr : List UInt8` big-endian, `bits : Nat`). The bridge packs the bit-string into
`familyWidthBits/8` octets, MSB-first, so bit `i` of the packed bytes equals `net[i]`
under `Wireguard.Peer.bitAt` (`(byte >>> (7 - i%8)) % 2`). -/

/-- Address-family bit width: v4 = 32, v6 = 128 (public tailcfg IP families). -/
def familyWidthBits : IpFilter.Family → Nat
  | .v4 => 32
  | .v6 => 128

/-- Pack an MSB-first Boolean prefix into `width/8` big-endian octets, zero-padding any
bit position beyond the supplied list (only the first `len` bits are ever compared by
`Prefix.matches`). Bit `i` of the result is `net.getD i false`, matching
`Wireguard.Peer.bitAt`. -/
def packBits (width : Nat) (net : List Bool) : Bytes :=
  (List.range (width / 8)).map (fun k =>
    (List.range 8).foldl (fun acc j =>
      acc * 2 + (if net.getD (8 * k + j) false then 1 else 0)) (0 : UInt8))

/-- Convert a compiled `IpFilter.Cidr` to the coordination core's `Prefix`. -/
def cidrToPrefix (c : IpFilter.Cidr) : Prefix :=
  { addr := packBits (familyWidthBits c.family) c.net, bits := c.len }

/-- Convert an ACL destination `NetPortRange` (Cidr:ports) to the core's shape. -/
def netPortRangeConv (npr : Acl.NetPortRange) : NetPortRange :=
  { net := cidrToPrefix npr.dst
  , ports := { first := npr.ports.first, last := npr.ports.last } }

/-- Convert one compiled `Acl.FilterRule` to the coordination core's `FilterRule`
(field-for-field: `srcs ↦ srcIPs`, `dsts ↦ dstPorts`, `protos ↦ protos`). -/
def ruleConv (r : Acl.FilterRule) : FilterRule :=
  { srcIPs := r.srcs.map cidrToPrefix
  , dstPorts := r.dsts.map netPortRangeConv
  , protos := r.protos }

/-- **The served `PacketFilter` IS `Control.Acl.compile`.** The coordination server's
ACL is `(Acl.compile p).map ruleConv` — a function of the PROVEN default-deny
compilation (`Control.Acl.policy_default_deny` / `policy_allow_iff_entry` are
load-bearing about `Acl.compile p`), not a hand-set list. -/
def compiledPacketFilter (p : Acl.Policy) : PacketFilter :=
  (Acl.compile p).map ruleConv

/-! ## §2  The DERPMap region that NAMES drorb's own verified relay (inc-1) -/

/-- drorb's OWN verified DERP relay endpoint: the `127.0.0.1:3340` that
`DerpRelayLive.runRelay` binds (`tcpListen 3340`) and on which the proven router
`Derp.Server.dispatch` (`forward_to_addressed_only` / `relay_blind`) runs. -/
def drorbDerpHost : Bytes := [127, 0, 0, 1]
def drorbDerpPort : Nat := 3340
def drorbDerpEndpoint : Endpoint := { addr := drorbDerpHost, port := drorbDerpPort }

/-- drorb's DERP region id — the home region every served netmap node points at. -/
def drorbRegionID : Nat := 1

/-- The DERP region NAMING drorb's own relay: one node whose endpoint is
`drorbDerpEndpoint`. `regionCode` is the ASCII `"drorb"`. -/
def drorbDerpRegion : Derp.DerpRegion :=
  { regionID := drorbRegionID
  , regionCode := [0x64, 0x72, 0x6f, 0x72, 0x62]  -- "drorb"
  , nodes := [drorbDerpEndpoint] }

/-- The served DERPMap: drorb's own relay as its single region. -/
def drorbDerpMap : Derp.DerpMap := { regions := [drorbDerpRegion] }

/-! ### The ROUTABLE-advertised generalization (inc: cross-host reach)

`drorbDerpHost` (`127.0.0.1`) is the *advertised* endpoint IP a client dials to reach
the relay. It is pure config: the region id, region code, and port are fixed, so the
region STILL names drorb region 1 and STILL forms a valid distribution for EVERY host —
`validDistribution` / `lookup` inspect only `regionID`, never the endpoint bytes. The
routable serve advertises the reachable host IP (`DRORB_DERP_ADDR`) instead of loopback;
these `∀ host` theorems witness that swapping the advertised IP preserves every DERP
invariant, and the loopback defs above are just `…At drorbDerpHost`.

**The advertised PORT is a parameter too** (`…AtPort host port`, from `DRORB_DERP_PORT`).
The relay's BIND port is operator config (`DERP_PORT` in `scripts/run-tailnet.sh`); if the
advertised port stayed the `3340` literal, a plane bound on any other port would hand every
client a DEAD endpoint. The region id / region code are what carry the routing invariant —
`validDistribution` / `lookup` never read the endpoint at all — so the `∀ host, ∀ port`
theorems below are the same invariants, now load-bearing over BOTH knobs. The `…At host`
defs are the defaulted alias `…AtPort host drorbDerpPort`, definitionally, so every
existing site and every `rfl` proof about them is unchanged. -/
def drorbDerpEndpointAtPort (host : Bytes) (port : Nat) : Endpoint := { addr := host, port := port }

/-! #### The STUN knob — the third parameter, and the one that makes a DIRECT path possible

A stock `tailscale` client's `netcheck` learns its own **reflexive** transport address
(the `host:port` a peer on the other side of the NAT actually sees) by sending a STUN
Binding request to the STUN service of each DERP region in the served map. With no
STUN port advertised it probes tailscale's default `3478`; if nothing answers there it
reports `udp=false` and its endpoint set contains **only** local interface addresses —
so a direct path can be attempted only between peers that already share a link.

drorb has the proven Binding server (`Stun.respond`, `Stun.respond_success_correct`).
This third knob is what lets the served netmap NAME where it listens, so the client can
find it. `stun = 0` ⇒ not advertised (the pre-existing behaviour, definitionally). -/
/-! #### The CERTNAME knob — the fourth parameter, and the one that makes the relay
DIALABLE by a stock client

A stock `tailscale` client dials its home DERP region over HTTPS
(`https://<host>:<DERPPort>/derp`). A self-hosted relay presents a certificate no
public CA signed, so verification against the system roots can only fail. `derphttp`
has exactly one escape for this: when the served `DERPNode` carries
`CertName = "sha256-raw:<hex sha256 of the leaf DER>"` it PINS the certificate by that
hash (`tlsdial.SetConfigExpectedCertHash`) and builds no path at all.

So this knob is to the TLS front what `stun` is to the direct path: without it the
relay is unreachable to a stock client no matter what is listening. `[]` ⇒ not
advertised (the pre-existing behaviour, definitionally). -/
def drorbDerpRegionAtPortStunCert (host : Bytes) (port stun : Nat) (certName : Bytes) :
    Derp.DerpRegion :=
  { regionID := drorbRegionID
  , regionCode := [0x64, 0x72, 0x6f, 0x72, 0x62]  -- "drorb"
  , nodes := [drorbDerpEndpointAtPort host port]
  , stunPort := stun
  , certName := certName }

def drorbDerpMapAtPortStunCert (host : Bytes) (port stun : Nat) (certName : Bytes) :
    Derp.DerpMap :=
  { regions := [drorbDerpRegionAtPortStunCert host port stun certName] }

/-- The three-knob defs ARE the four-knob ones with no certificate name advertised —
definitionally, so every existing theorem and every `rfl` about them stands verbatim. -/
def drorbDerpRegionAtPortStun (host : Bytes) (port stun : Nat) : Derp.DerpRegion :=
  drorbDerpRegionAtPortStunCert host port stun []

def drorbDerpMapAtPortStun (host : Bytes) (port stun : Nat) : Derp.DerpMap :=
  drorbDerpMapAtPortStunCert host port stun []

/-- The two-knob defs ARE the three-knob ones with STUN unadvertised — definitionally,
so every existing theorem and every `rfl` about them stands verbatim. -/
def drorbDerpRegionAtPort (host : Bytes) (port : Nat) : Derp.DerpRegion :=
  drorbDerpRegionAtPortStun host port 0

def drorbDerpMapAtPort (host : Bytes) (port : Nat) : Derp.DerpMap :=
  drorbDerpMapAtPortStun host port 0

/-- The defaulted alias: advertise the host on drorb's default relay port. -/
def drorbDerpEndpointAt (host : Bytes) : Endpoint := drorbDerpEndpointAtPort host drorbDerpPort

def drorbDerpRegionAt (host : Bytes) : Derp.DerpRegion := drorbDerpRegionAtPort host drorbDerpPort

def drorbDerpMapAt (host : Bytes) : Derp.DerpMap := drorbDerpMapAtPort host drorbDerpPort

/-- The host-only defs ARE the two-knob generalization at `drorbDerpPort` (definitional). -/
theorem drorbDerpMapAt_eq_atPort (host : Bytes) :
    drorbDerpMapAt host = drorbDerpMapAtPort host drorbDerpPort := rfl

/-- The loopback defs ARE the generalization at `drorbDerpHost` (definitional). -/
theorem drorbDerpMap_eq_at : drorbDerpMap = drorbDerpMapAt drorbDerpHost := rfl

/-- **For EVERY advertised host, the region still names drorb region 1.** -/
theorem drorbDerpMapAt_names_drorb (host : Bytes) :
    (drorbDerpMapAt host).lookup drorbRegionID = some (drorbDerpRegionAt host) := rfl

/-- **For EVERY advertised host AND port, the region still names drorb region 1.** The
routing invariant reads `regionID` only, so moving the advertised port cannot break it. -/
theorem drorbDerpMapAtPort_names_drorb (host : Bytes) (port : Nat) :
    (drorbDerpMapAtPort host port).lookup drorbRegionID
      = some (drorbDerpRegionAtPort host port) := rfl

/-- **The advertised port IS the parameter.** The single region node's endpoint port is
exactly the `port` passed in — this is the field a stock client dials, so the served
DERPMap can no longer disagree with the relay's bind port. -/
theorem drorbDerpMapAtPort_port (host : Bytes) (port : Nat) :
    ((drorbDerpMapAtPort host port).regions.head?.bind (·.nodes.head?)).map (·.port)
      = some port := rfl

/-- **The two-knob map IS the three-knob map at `stun = 0`** (definitional). -/
theorem drorbDerpMapAtPort_eq_stun0 (host : Bytes) (port : Nat) :
    drorbDerpMapAtPort host port = drorbDerpMapAtPortStun host port 0 := rfl

/-- **For EVERY advertised host, port AND STUN port, the region still names drorb
region 1.** The routing invariant reads `regionID` only, so advertising a STUN service
cannot break it. -/
theorem drorbDerpMapAtPortStun_names_drorb (host : Bytes) (port stun : Nat) :
    (drorbDerpMapAtPortStun host port stun).lookup drorbRegionID
      = some (drorbDerpRegionAtPortStun host port stun) := rfl

/-- **The advertised STUN port IS the parameter.** The region's `stunPort` is exactly the
`stun` passed in — the value the live serve threads from `DRORB_STUN_PORT`, which is the
same value the STUN Binding server binds. -/
theorem drorbDerpMapAtPortStun_stun (host : Bytes) (port stun : Nat) :
    ((drorbDerpMapAtPortStun host port stun).regions.head?).map (·.stunPort)
      = some stun := rfl

/-- **The STUN knob does not move the relay endpoint.** Advertising a STUN port leaves
the region node's dialled `addr`/`port` exactly where the two-knob map put them. -/
theorem drorbDerpMapAtPortStun_relay_unmoved (host : Bytes) (port stun : Nat) :
    ((drorbDerpMapAtPortStun host port stun).regions.head?.bind (·.nodes.head?))
      = ((drorbDerpMapAtPort host port).regions.head?.bind (·.nodes.head?)) := rfl

/-! ## §3  The coordination server state, with the proven pieces wired in

The hand-set `ControlState.filter` / `.dns` are replaced by the ACL-compiled filter and
the MagicDNS-built config; every node's home DERP is drorb's region. `Control.step` /
`Control.buildNetMap` are UNCHANGED — they carry these values into the served netmap. -/

/-- Wire the proven coordination into a `ControlState`: `filter` = the ACL compilation,
`dns` = the MagicDNS build over the registered nodes. -/
def coordState (aclPol : Acl.Policy) (domains : List Bytes)
    (regs : List Registration) : ControlState :=
  { nodes := regs
  , filter := compiledPacketFilter aclPol
  , dns := Dns.buildDns domains (regs.map (·.node)) }

/-! ## §4  The GATE — a concrete 2-node tailnet, driven through the REAL `Control.step`

`node-a` (`10.0.0.1`) and `node-b` (`10.0.0.2`), both authorized, both homed on drorb's
DERP region. The ACL is `Control.Acl.demoPolicy` (`group:eng = 10.0.0.0/8`;
`accept src group:eng dst 10.0.0.0/8:22`) — the very policy `Control.Acl` proves its
four-corner truth table on. We poll as A and inspect the served `MapResponse`. -/

/-- Any-auth login policy (the map-poll path never consults it; registration is already
authorized in `demoCoord`). -/
def demoPol : Policy := { authorizes := fun _ _ => true }

def keyA : NodeKey := ⟨List.replicate 32 0xA1⟩
def keyB : NodeKey := ⟨List.replicate 32 0xB2⟩

/-- A netmap `Node`: named, addressed, homed on drorb's DERP region. -/
def mkNode (id : Nat) (nm ip : Bytes) (k : NodeKey) : Node :=
  { id := id, stableID := nm, name := nm, user := 1, key := k
  , machine := ⟨List.replicate 32 0⟩, disco := ⟨List.replicate 32 0⟩
  , addresses := [⟨ip, 32⟩], allowedIPs := [⟨ip, 32⟩], endpoints := []
  , derp := drorbRegionID, online := true, keyExpiry := 0, authorized := true }

def nodeA : Node := mkNode 1 [0x6e, 0x6f, 0x64, 0x65, 0x2d, 0x61] [10, 0, 0, 1] keyA  -- "node-a"
def nodeB : Node := mkNode 2 [0x6e, 0x6f, 0x64, 0x65, 0x2d, 0x62] [10, 0, 0, 2] keyB  -- "node-b"

def regA : Registration := { nodeKey := keyA, node := nodeA, status := .authorized }
def regB : Registration := { nodeKey := keyB, node := nodeB, status := .authorized }

/-- MagicDNS search domain `"ts.net"`. -/
def demoDomains : List Bytes := [[0x74, 0x73, 0x2e, 0x6e, 0x65, 0x74]]

/-- The wired coordination state for the 2-node tailnet. -/
def demoCoord : ControlState := coordState Acl.demoPolicy demoDomains [regA, regB]

/-- A map-poll `MapRequest` from node key `k` (long-poll stream). -/
def pollReq (k : NodeKey) : MapRequest :=
  { version := 1, nodeKey := k, discoKey := ⟨[]⟩, endpoints := []
  , stream := true, omitPeers := false, readOnly := false }

/-- The served netmap A receives (= `buildNetMap demoCoord regA`). -/
def servedNetMapA : NetMap := buildNetMap demoCoord regA

/-- The served packet filter A receives. -/
def servedFilter : PacketFilter := compiledPacketFilter Acl.demoPolicy

/-! ### The gate theorems -/

/-- **The real coord transition serves A's full netmap.** Driving `Control.step` on the
map-poll produces exactly `MapResponse.full servedNetMapA`. -/
theorem served_reply_is_full :
    (Control.step demoPol demoCoord (.mapPoll (pollReq keyA))).2
      = Reply.mapResp (MapResponse.full servedNetMapA) := rfl

/-- **Self.** The served netmap's own record is node A. -/
theorem served_self_is_A : servedNetMapA.self = nodeA := rfl

/-- **Peer B is served to A.** Node B appears as a Peer in A's served netmap. -/
theorem served_peer_has_B : nodeB ∈ servedNetMapA.peers := by decide

/-- **PacketFilter = the ACL compiler output.** The served `PacketFilter` is
definitionally `compiledPacketFilter Acl.demoPolicy` = `(Acl.compile demoPolicy).map
ruleConv` — a function of `Control.Acl.compile`, not hand-set. -/
theorem served_filter_is_acl_compile :
    servedNetMapA.packetFilter = compiledPacketFilter Acl.demoPolicy := rfl

/-- **DNS: B's MagicDNS record is served.** `node-b`'s name resolves to its overlay
address `10.0.0.2` in the served `DNSConfig` (built by `Control.Dns.buildDns`). -/
theorem served_dns_has_B :
    (nodeB.name, ([10, 0, 0, 2] : Bytes)) ∈ servedNetMapA.dns.records := by decide

/-- **DERPMap names drorb's own relay.** The served map's region resolves to
`drorbDerpRegion`, whose single node endpoint is drorb's verified relay
(`127.0.0.1:3340`). -/
theorem served_derp_names_drorb :
    drorbDerpMap.lookup drorbRegionID = some drorbDerpRegion := by decide

theorem served_derp_region_endpoint :
    drorbDerpRegion.nodes = [drorbDerpEndpoint] := rfl

/-- **Every served node routes to drorb's relay.** Self and every peer in A's served
netmap have a home DERP region that is a genuine member of the served DERPMap — a valid
distribution over drorb-as-relay (`Control.Derp.validDistribution`). -/
theorem served_derp_valid : Derp.validDistribution drorbDerpMap servedNetMapA := by
  refine ⟨by decide, ?_⟩
  intro p hp
  have : servedNetMapA.peers = [nodeB] := by decide
  rw [this] at hp
  simp only [List.mem_singleton] at hp
  subst hp
  decide

/-- **For EVERY advertised host, the served netmap is a valid distribution.** The
advertised IP is irrelevant to the routing invariant — `validDistribution` / `lookup`
inspect only `regionID`, so advertising the routable host IP (not loopback) preserves
the DERP-distribution invariant. -/
theorem drorbDerpMapAt_valid (host : Bytes) :
    Derp.validDistribution (drorbDerpMapAt host) servedNetMapA := by
  refine ⟨rfl, ?_⟩
  intro p hp
  have hpe : servedNetMapA.peers = [nodeB] := by decide
  rw [hpe] at hp
  simp only [List.mem_singleton] at hp
  subst hp
  rfl

/-- **For EVERY advertised host AND port, the served netmap is a valid distribution.**
Neither knob is read by the routing invariant (`validDistribution` / `lookup` inspect
only `regionID`), so an operator moving the relay's port — and the advertised port with
it — preserves the DERP-distribution invariant. `drorbDerpMapAt_valid` is this at
`drorbDerpPort`. -/
theorem drorbDerpMapAtPort_valid (host : Bytes) (port : Nat) :
    Derp.validDistribution (drorbDerpMapAtPort host port) servedNetMapA := by
  refine ⟨rfl, ?_⟩
  intro p hp
  have hpe : servedNetMapA.peers = [nodeB] := by decide
  rw [hpe] at hp
  simp only [List.mem_singleton] at hp
  subst hp
  rfl

/-- **For EVERY advertised host, port AND STUN port, the served netmap is a valid
distribution.** None of the three knobs is read by the routing invariant, so advertising
drorb's STUN Binding server preserves the DERP-distribution invariant exactly. -/
theorem drorbDerpMapAtPortStun_valid (host : Bytes) (port stun : Nat) :
    Derp.validDistribution (drorbDerpMapAtPortStun host port stun) servedNetMapA := by
  refine ⟨rfl, ?_⟩
  intro p hp
  have hpe : servedNetMapA.peers = [nodeB] := by decide
  rw [hpe] at hp
  simp only [List.mem_singleton] at hp
  subst hp
  rfl

/-! ### The served filter is default-deny on real packets — in drorb's byte
representation, matching `Control.Acl`'s upstream `tt_*` verdicts. This witnesses that
`cidrToPrefix` preserves the ACL semantics: the served bytes enforce the proven policy. -/

/-- **In-policy flow allowed.** `10.0.0.1 → 10.0.0.2 : 22` (tcp) is admitted by the
served filter — same verdict as `Control.Acl.tt_in_policy_allowed`. -/
theorem served_allows_in_policy :
    packetFilterAllows servedFilter [10, 0, 0, 1] [10, 0, 0, 2] 22 6 = true := by decide

/-- **Wrong port dropped.** `10.0.0.1 → 10.0.0.2 : 80` is dropped (policy opens only 22)
— same verdict as `Control.Acl.tt_wrong_port_dropped`. -/
theorem served_denies_wrong_port :
    packetFilterAllows servedFilter [10, 0, 0, 1] [10, 0, 0, 2] 80 6 = false := by decide

/-- **Out-of-policy source dropped (default-deny).** `192.0.0.1 → 10.0.0.2 : 22` matches
no rule and is dropped — same verdict as `Control.Acl.tt_out_of_policy_src_dropped`. -/
theorem served_denies_out_of_policy :
    packetFilterAllows servedFilter [192, 0, 0, 1] [10, 0, 0, 2] 22 6 = false := by decide

/-- **Empty-policy default-deny survives the wiring.** Compiling the empty ACL yields the
deny-all served filter. -/
theorem served_empty_denies :
    compiledPacketFilter { groups := [], acls := [] } = [] := rfl

/-! ## §5  Runtime evidence (`#guard`) and the axiom audit -/

#guard (Control.step demoPol demoCoord (.mapPoll (pollReq keyA))).2
  matches Reply.mapResp (MapResponse.full _)
#guard servedNetMapA.peers.map (·.id) = [2]
#guard servedNetMapA.packetFilter = compiledPacketFilter Acl.demoPolicy
#guard drorbDerpMap.lookup drorbRegionID = some drorbDerpRegion
#guard (drorbDerpRegion.nodes.head?.map (·.port)) = some 3340
-- a NON-default advertised port is carried verbatim (the operator moved DERP_PORT):
#guard ((drorbDerpMapAtPort [192, 168, 50, 39] 3999).regions.head?.bind (·.nodes.head?)).map (·.port)
  = some 3999
#guard packetFilterAllows servedFilter [10, 0, 0, 1] [10, 0, 0, 2] 22 6 = true
#guard packetFilterAllows servedFilter [10, 0, 0, 1] [10, 0, 0, 2] 80 6 = false
#guard packetFilterAllows servedFilter [192, 0, 0, 1] [10, 0, 0, 2] 22 6 = false

/-! ## Axiom audit — ASSERTED, not printed

These were `#print axioms`, which writes to the *info* stream and can never fail
a build. They are now `#assert_axioms` (see `Hygiene`), which throws when a proof
depends on more than it advertises. `stdAxioms` = `propext` / `Classical.choice`
/ `Quot.sound`.

★ Six of the §6 wire theorems declare `nativeDecide`, not `stdAxioms`: they are
closed by `native_decide`, i.e. by RUNNING COMPILED CODE, so the Lean compiler,
the C toolchain and the evaluator are in their trusted base — the kernel alone
did not check them. That was already true; `#print axioms` printed it on every
build and nothing ever failed. Now the set is written down and a proof cannot
quietly acquire (or shed) it. -/

#assert_axioms served_reply_is_full ⊆ [stdAxioms]
#assert_axioms served_peer_has_B ⊆ [stdAxioms]
#assert_axioms served_filter_is_acl_compile ⊆ [stdAxioms]
#assert_axioms served_dns_has_B ⊆ [stdAxioms]
#assert_axioms served_derp_names_drorb ⊆ [stdAxioms]
#assert_axioms served_derp_valid ⊆ [stdAxioms]
#assert_axioms drorbDerpMapAt_names_drorb ⊆ [stdAxioms]
#assert_axioms drorbDerpMapAt_valid ⊆ [stdAxioms]
#assert_axioms drorbDerpMapAtPort_names_drorb ⊆ [stdAxioms]
#assert_axioms drorbDerpMapAtPort_valid ⊆ [stdAxioms]
#assert_axioms drorbDerpMapAtPort_port ⊆ [stdAxioms]
#assert_axioms drorbDerpMapAtPortStun_names_drorb ⊆ [stdAxioms]
#assert_axioms drorbDerpMapAtPortStun_valid ⊆ [stdAxioms]
#assert_axioms drorbDerpMapAtPortStun_stun ⊆ [stdAxioms]
#assert_axioms drorbDerpMapAtPortStun_relay_unmoved ⊆ [stdAxioms]
#assert_axioms drorbDerpMapAtPort_eq_stun0 ⊆ [stdAxioms]
#assert_axioms served_allows_in_policy ⊆ [stdAxioms]
#assert_axioms served_denies_wrong_port ⊆ [stdAxioms]
#assert_axioms served_denies_out_of_policy ⊆ [stdAxioms]
#assert_axioms served_empty_denies ⊆ [stdAxioms]

/-! ## §6  THE WIRE REFINEMENT — `servedNetMapWire : ControlState → NodeKey →
       Tailcfg.MapResponse`

The gate above establishes the served netmap as a FUNCTION of the proven ACL
compilation (`served_filter_is_acl_compile` : `NetMap.packetFilter =
compiledPacketFilter Acl.demoPolicy`), the proven DERPMap (drorb-as-relay), and
the proven peers. But that lives in the coordination core's *byte-addressed*
model (`Control.Node` / `Control.NetMap` / `Control.FilterRule`). The stock
`tailscale` client consumes the PUBLIC `tailcfg.MapResponse` JSON wire shape
(`Control.Tailcfg`, PascalCase codec, proven roundtrip). H2Noise (the compose
lane) currently HAND-BUILDS that wire view (`H2Noise.mapResponseWire`: a self
node + drorb DERP + `PacketFilters{base := []}` — the served ACL is a hand-set
empty base filter, NOT the theorem).

This section closes that gap: `servedNetMapWire` PROJECTS the proven core
`NetMap` (`buildNetMap` over the wired `coordState`) into a real
`Tailcfg.MapResponse`, and the refinement theorems below prove the projected
wire's `PacketFilters["base"]` IS the ACL-compiler output (`compiledPacketFilter`
= `(Acl.compile p).map ruleConv`), the peers ARE the netmap peers (with their
IPAM addresses and ACL tags), and the whole message roundtrips through the proven
`Control.Tailcfg` codec. The compose lane swaps `H2Noise.mapResponseWire` for
`servedNetMapWire`, so the ACL the client receives is the proven default-deny
compilation, not a hand-built base filter.

WIRE-SHAPE GROUND TRUTH: a real control server carries the ACL in the newer
`PacketFilters` map keyed `"base"` (NOT the legacy `PacketFilter` array), each
rule `{SrcIPs:[cidr-string], DstPorts:[{IP:cidr-string, Ports:{First,Last}}]}`,
`SrcIPs`/`DstPorts[].IP` as CIDR strings ("10.0.0.0/8") or "*". This is the shape
captured from a live server in `Control/RealMapKat.lean` (`realMapResponseFull`,
`mapResponse_packetFilters_base` : the decoded map has key `["base"]`). The leaf
string codecs (`"nodekey:<hex>"`, `"a.b.c.d/bits"`, `"a.b.c.d:port"`) are the
proven inverses in `Control/TailcfgBridge.lean`. -/

/-! ### §6.1  Leaf projections (core bytes → the marshaled JSON strings) -/

/-- A 4-byte address as a `Bridge.Ip4` (v4; the demo tailnet is v4-only). -/
def ip4Of (bs : Bytes) : Control.Bridge.Ip4 :=
  { a := bs.getD 0 0, b := bs.getD 1 0, c := bs.getD 2 0, d := bs.getD 3 0 }

/-- A core `Prefix` → the `netip.Prefix` marshal string `"a.b.c.d/bits"` (v4).
Uses the proven `Bridge.Prefix4` renderer. (v6 prefixes are a named residual —
the served demo tailnet is v4-only, matching `Control.Acl`'s v4 family policy.) -/
def prefixToWire (p : Prefix) : String :=
  Control.Bridge.Prefix4.toText { addr := ip4Of p.addr, bits := p.bits }

/-- A bare v4 address as a dotted-quad string (for a DERP node hostname/IPv4). -/
def ipToWire (bs : Bytes) : String := String.ofList (Control.Bridge.Ip4.render (ip4Of bs))

/-- A core `Endpoint` → the `netip.AddrPort` marshal string `"a.b.c.d:port"`. -/
def endpointToWire (e : Endpoint) : String :=
  Control.Bridge.AddrPort4.toText { addr := ip4Of e.addr, port := e.port }

/-- ASCII bytes → `String` (MagicDNS names, stable-ids, region codes, tags are
ASCII on the wire). -/
def asciiStr (bs : Bytes) : String := String.ofList (bs.map (fun b => Char.ofNat b.toNat))

/-! ### §6.2  Filter projection (core `FilterRule` → `Tailcfg.FilterRule`) -/

/-- A core destination `NetPortRange` → the wire `tailcfg.NetPortRange`: the CIDR
carried in `IP` (`Bits` omitted — the CIDR string already carries the mask, as
the real server does), the inclusive port range verbatim. -/
def netPortRangeToWire (npr : NetPortRange) : Control.Tailcfg.NetPortRange :=
  { ip := prefixToWire npr.net
  , bits := none
  , ports := { first := npr.ports.first, last := npr.ports.last } }

/-- A core `FilterRule` → the wire `tailcfg.FilterRule`: `srcIPs` as CIDR strings,
`dstPorts` as `NetPortRange`s, `protos` → `IPProto` (empty ⇒ absent, tailcfg's
"any protocol"). **This is the projection whose fixed point is the served ACL.** -/
def filterRuleToWire (r : FilterRule) : Control.Tailcfg.FilterRule :=
  { srcIPs := r.srcIPs.map prefixToWire
  , dstPorts := r.dstPorts.map netPortRangeToWire
  , ipProto := if r.protos.isEmpty then none else some r.protos }

/-! ### §6.3  Node / DNS / DERP projections -/

/-- A core netmap `Node` → the wire `tailcfg.Node`. Identity keys via the proven
`Bridge` key codecs; addresses/allowedIPs/endpoints via the proven prefix/addrport
renderers; `derp` region → `HomeDERP`; `authorized` → `MachineAuthorized`; ACL
`tags` → `Tags` (empty ⇒ absent). `keyExpiry` (unix seconds) → RFC3339 is a
separate leaf bridge (`Control/TailcfgBridge` carries timestamps as marshaled
strings) — a NAMED residual; the served demo nodes never expire (`keyExpiry = 0`,
absent). -/
def nodeToWire (n : Node) : Control.Tailcfg.Node :=
  { id                := n.id
  , stableID          := if n.stableID.isEmpty then none else some (asciiStr n.stableID)
  , name              := asciiStr n.name
  , user              := n.user
  , key               := Control.Bridge.NodeKey.toText n.key.pub
  , machine           := some (Control.Bridge.MachineKey.toText n.machine.pub)
  , discoKey          := if n.disco.pub.isEmpty then none else some (Control.Bridge.DiscoKey.toText n.disco.pub)
  , addresses         := n.addresses.map prefixToWire
  , allowedIPs        := some (n.allowedIPs.map prefixToWire)
  , endpoints         := if n.endpoints.isEmpty then none else some (n.endpoints.map endpointToWire)
  , derp              := none
  , homeDERP          := n.derp
  -- A stock tailscale client dereferences `peer.Hostinfo().Hostname()` /`.OS()`
  -- unconditionally in `populatePeerStatusLocked` (localapi `serveStatus`); a
  -- peer with a nil `Hostinfo` nil-panics its status handler. Real control
  -- servers always send a `Hostinfo`, so emit a minimal valid one (OS + the
  -- node hostname) for every served node.
  , hostinfo          := some { os := some "linux", hostname := some (asciiStr n.name) }
  , keyExpiry         := none
  , online            := some n.online
  , machineAuthorized := n.authorized
  , tags              := if n.tags.isEmpty then none else some (n.tags.map asciiStr) }

/-- A core `DnsConfig` → the wire `tailcfg.DNSConfig` (search domains). -/
def dnsToWire (d : DnsConfig) : Control.Tailcfg.DnsConfig :=
  { domains := if d.domains.isEmpty then none else some (d.domains.map asciiStr) }

/-- A verified DERP `Endpoint` → the wire `tailcfg.DERPNode` (drorb's relay), carrying
the region's STUN port. `stun = 0` ⇒ `STUNPort` is OMITTED (tailcfg `,omitempty`), which
is what every plane served before drorb ran a STUN service. -/
def derpNodeToWire (rid : Nat) (stun : Nat) (certName : Bytes) (e : Endpoint) :
    Control.Tailcfg.DERPNode :=
  { name := "drorb1", regionID := rid, hostName := ipToWire e.addr
  , ipv4 := some (ipToWire e.addr), port := some e.port
  , stunPort := if stun = 0 then none else some stun
  , certName := if certName = [] then none else some (asciiStr certName) }

/-- A core `Derp.DerpRegion` → the wire `tailcfg.DERPRegion`. -/
def derpRegionToWire (r : Derp.DerpRegion) : Control.Tailcfg.DERPRegion :=
  { regionID := r.regionID, regionCode := asciiStr r.regionCode
  , nodes := r.nodes.map (derpNodeToWire r.regionID r.stunPort r.certName) }

/-- A core `Derp.DerpMap` → the wire `tailcfg.DERPMap` (region-id keyed by its
decimal string, as `map[int]*DERPRegion` marshals). -/
def derpMapToWire (dm : Derp.DerpMap) : Control.Tailcfg.DERPMap :=
  { regions := dm.regions.map (fun r => (toString r.regionID, derpRegionToWire r)) }

/-! ### §6.4  The netmap → MapResponse projection -/

/-- Project a proven core `NetMap` (plus drorb's DERPMap and the tailnet domain)
into the wire `tailcfg.MapResponse`. The ACL goes in `PacketFilters["base"]` (the
newer map the real server sends); the legacy `PacketFilter` array is left empty
(absent), exactly as `Control/RealMapKat.lean` observed on the wire. -/
def netMapToWire (nm : NetMap) (dm : Derp.DerpMap) (domain : Option String) :
    Control.Tailcfg.MapResponse :=
  { node          := some (nodeToWire nm.self)
  , peers         := some (nm.peers.map nodeToWire)
  , dnsConfig     := some (dnsToWire nm.dns)
  , packetFilters := some [("base", nm.packetFilter.map filterRuleToWire)]
  , derpMap       := some (derpMapToWire dm)
  , domain        := domain }

/-- **`servedNetMapWire` — the exposed wire refinement.** Look the polling node's
registration up in the coordination state, build its proven netmap
(`buildNetMap`, carrying `coordState`'s ACL-compiled filter + MagicDNS + peers),
and project it into the real `tailcfg.MapResponse` over drorb's DERPMap. An
unknown key gets the empty response (no netmap — mirrors `Reply.reject`).
**The compose lane swaps `H2Noise.mapResponseWire` for this.** -/
def servedNetMapWire (st : ControlState) (k : NodeKey) : Control.Tailcfg.MapResponse :=
  match lookupReg st.nodes k with
  | some r => netMapToWire (buildNetMap st r) drorbDerpMap (st.dns.domains.head?.map asciiStr)
  | none   => {}

/-- **`servedNetMapWireAt` — the same wire refinement over an ARBITRARY advertised
DERPMap.** `servedNetMapWire` is exactly this at `drorbDerpMap` (loopback); the routable
serve passes `drorbDerpMapAt <host>` so the stock client dials the reachable relay. Only
the advertised DERP endpoint IP changes — the netmap, ACL, and DNS projections are
identical. -/
def servedNetMapWireAt (dm : Derp.DerpMap) (st : ControlState) (k : NodeKey) :
    Control.Tailcfg.MapResponse :=
  match lookupReg st.nodes k with
  | some r => netMapToWire (buildNetMap st r) dm (st.dns.domains.head?.map asciiStr)
  | none   => {}

/-- `servedNetMapWire` is `servedNetMapWireAt drorbDerpMap` (definitional). -/
theorem servedNetMapWire_eq_at : servedNetMapWire = servedNetMapWireAt drorbDerpMap := rfl

/-- **The wire DERPMap carries the advertised host as the node IPv4 the client dials.**
For every host, the projected `tailcfg.DERPMap` has one region (`"1"`) whose single
node advertises `ipToWire host` in both `HostName` and `IPv4`, on `drorbDerpPort`. This
is the exact field a stock client reads to reach the relay. -/
theorem derpMapToWireAt_ipv4 (host : Bytes) :
    ((derpMapToWire (drorbDerpMapAt host)).regions.head?.map
      (fun kv => kv.2.nodes.map (fun n => (n.ipv4, n.port))))
      = some [(some (ipToWire host), some drorbDerpPort)] := rfl

/-- **★ The wire DERPMap carries the advertised host AND PORT the client dials.** For
every host and every port, the projected `tailcfg.DERPMap`'s single region-1 node has
`IPv4 = ipToWire host` and `DERPPort = port`. This is the exact pair a stock client reads
to reach the relay, so it is the theorem that pins "advertised == bound": the live serve
threads `DRORB_DERP_PORT` (the same value `scripts/run-tailnet.sh` passes as the relay's
BIND port) into this `port`, and no `3340` literal survives on the path. -/
theorem derpMapToWireAtPort_ipv4 (host : Bytes) (port : Nat) :
    ((derpMapToWire (drorbDerpMapAtPort host port)).regions.head?.map
      (fun kv => kv.2.nodes.map (fun n => (n.ipv4, n.port))))
      = some [(some (ipToWire host), some port)] := rfl

-- The non-default port, on the concrete wire: a plane bound on 3999 at the LAN IP
-- advertises exactly 192.168.50.39:3999 in DERPMap.Regions["1"].Nodes[0].
#guard ((derpMapToWire (drorbDerpMapAtPort [192, 168, 50, 39] 3999)).regions.head?.map
    (fun kv => kv.2.nodes.map (fun n => (n.ipv4, n.port))))
  = some [(some "192.168.50.39", some 3999)]

/-- **★ The wire DERPMap carries the advertised STUN port.** For every host, relay port
and NONZERO STUN port, the projected region-1 node has `STUNPort = stun`. This is the
exact field `netcheck` reads to find where to send its Binding request — the field whose
absence made every stock client report `udp=false` and never learn a reflexive endpoint.
The live serve threads `DRORB_STUN_PORT` (the same value `scripts/run-tailnet.sh` passes
as the STUN server's BIND port) into this `stun`, so advertised == bound here too. -/
theorem derpMapToWireAtPortStun_stunPort (host : Bytes) (port stun : Nat) (h : stun ≠ 0) :
    ((derpMapToWire (drorbDerpMapAtPortStun host port stun)).regions.head?.map
      (fun kv => kv.2.nodes.map (fun n => n.stunPort)))
      = some [some stun] := by
  simp [derpMapToWire, drorbDerpMapAtPortStun, drorbDerpRegionAtPortStun,
    drorbDerpMapAtPortStunCert, drorbDerpRegionAtPortStunCert,
    derpRegionToWire, derpNodeToWire, h]

/-- **★ The wire DERPMap carries the advertised CERTNAME.** For every host, relay port,
STUN port and NONEMPTY certificate name, the projected region-1 node has
`CertName = asciiStr cn`. This is the exact field `derphttp` reads to decide it may pin
the relay's self-signed leaf by hash instead of failing PKI verification — the field
whose absence made every stock client's HTTPS dial to the relay unverifiable. The live
serve threads `DRORB_DERP_CERTNAME`, which `scripts/run-tailnet.sh` derives from the
SHA-256 of the very certificate file the TLS front presents, so advertised == presented
here exactly as advertised == bound holds for the ports. -/
theorem derpMapToWireAtPortStunCert_certName (host : Bytes) (port stun : Nat) (cn : Bytes)
    (h : ¬ cn = []) :
    ((derpMapToWire (drorbDerpMapAtPortStunCert host port stun cn)).regions.head?.map
      (fun kv => kv.2.nodes.map (fun n => n.certName)))
      = some [some (asciiStr cn)] := by
  simp [derpMapToWire, drorbDerpMapAtPortStunCert, drorbDerpRegionAtPortStunCert,
    derpRegionToWire, derpNodeToWire, h]

/-- **The CERTNAME knob does not move the dialled relay.** For every host, port, STUN
port and certificate name the region-1 node still advertises `IPv4 = ipToWire host` and
`DERPPort = port` — the pair `derpMapToWireAtPort_ipv4` pins, unchanged by advertising
a certificate pin. -/
theorem derpMapToWireAtPortStunCert_ipv4 (host : Bytes) (port stun : Nat) (cn : Bytes) :
    ((derpMapToWire (drorbDerpMapAtPortStunCert host port stun cn)).regions.head?.map
      (fun kv => kv.2.nodes.map (fun n => (n.ipv4, n.port))))
      = some [(some (ipToWire host), some port)] := rfl

/-- **Unadvertised stays unadvertised (certificate name).** With no certificate name the
wire node omits `CertName` entirely — the pre-existing served shape, so a plane whose
relay is plaintext (or fronted by a publicly-trusted certificate) hands its clients
exactly what it handed them before this knob existed. -/
theorem derpMapToWireAtPortStun_no_certName (host : Bytes) (port stun : Nat) :
    ((derpMapToWire (drorbDerpMapAtPortStun host port stun)).regions.head?.map
      (fun kv => kv.2.nodes.map (fun n => n.certName)))
      = some [none] := rfl

/-- **Unadvertised stays unadvertised.** At `stun = 0` the wire node omits `STUNPort`
entirely — the pre-existing served shape, so this extension cannot change what a plane
that runs no STUN service hands its clients. -/
theorem derpMapToWireAtPort_no_stunPort (host : Bytes) (port : Nat) :
    ((derpMapToWire (drorbDerpMapAtPort host port)).regions.head?.map
      (fun kv => kv.2.nodes.map (fun n => n.stunPort)))
      = some [none] := rfl

/-- **The STUN knob does not move the dialled relay.** For every host, port and STUN
port the region-1 node still advertises `IPv4 = ipToWire host` and `DERPPort = port` —
the pair `derpMapToWireAtPortStun_ipv4` pins, unchanged by advertising STUN. -/
theorem derpMapToWireAtPortStun_ipv4 (host : Bytes) (port stun : Nat) :
    ((derpMapToWire (drorbDerpMapAtPortStun host port stun)).regions.head?.map
      (fun kv => kv.2.nodes.map (fun n => (n.ipv4, n.port))))
      = some [(some (ipToWire host), some port)] := rfl

-- The concrete served wire for the LAN plane this was demonstrated on: relay
-- 192.168.50.39:3340, STUN 192.168.50.39:3478.
#guard ((derpMapToWire (drorbDerpMapAtPortStun [192, 168, 50, 39] 3340 3478)).regions.head?.map
    (fun kv => kv.2.nodes.map (fun n => (n.ipv4, n.port, n.stunPort))))
  = some [(some "192.168.50.39", some 3340, some 3478)]

#assert_axioms derpMapToWireAtPort_ipv4 ⊆ [stdAxioms]
#assert_axioms derpMapToWireAtPortStun_stunPort ⊆ [stdAxioms]
#assert_axioms derpMapToWireAtPortStun_ipv4 ⊆ [stdAxioms]
#assert_axioms derpMapToWireAtPortStunCert_certName ⊆ [stdAxioms]
#assert_axioms derpMapToWireAtPortStunCert_ipv4 ⊆ [stdAxioms]
#assert_axioms derpMapToWireAtPortStun_no_certName ⊆ [stdAxioms]
#assert_axioms derpMapToWireAtPort_no_stunPort ⊆ [stdAxioms]

/-! ### §6.5  THE REFINEMENT THEOREMS — the served wire ACL IS the proven compile -/

/-- **General refinement: the served wire `PacketFilters["base"]` is the state's
compiled filter, projected.** For any authorized key, `servedNetMapWire` carries
`st.filter` (which `coordState` sets to `compiledPacketFilter` = the ACL compiler
output) into `PacketFilters["base"]` field-for-field via `filterRuleToWire` — the
served ACL is a FUNCTION of `Control.Acl.compile`, never hand-set. -/
theorem servedNetMapWire_filters (st : ControlState) (k : NodeKey) (r : Registration)
    (h : lookupReg st.nodes k = some r) :
    (servedNetMapWire st k).packetFilters
      = some [("base", st.filter.map filterRuleToWire)] := by
  simp only [servedNetMapWire, h, netMapToWire, buildNetMap]

/-- **The served wire netmap is a PROJECTION of the proven `servedNetMapA`.** No
hand-built self/peer/filter view: `servedNetMapWire demoCoord keyA` is literally
`netMapToWire` applied to `buildNetMap demoCoord regA` (= `servedNetMapA`, the
object all the §4 gate theorems are about). -/
theorem servedNetMapWire_projects_servedNetMapA :
    servedNetMapWire demoCoord keyA
      = netMapToWire servedNetMapA drorbDerpMap (demoCoord.dns.domains.head?.map asciiStr) := rfl

/-- The served wire `MapResponse` A receives. -/
def servedWireA : Control.Tailcfg.MapResponse := servedNetMapWire demoCoord keyA

/-- **★ THE ACL-IS-SERVED THEOREM (wire).** The served wire `PacketFilters["base"]`
equals the ACL-compiler output `(compiledPacketFilter Acl.demoPolicy)` — i.e.
`(Acl.compile demoPolicy).map ruleConv` (`Control.Acl.policy_default_deny` /
`policy_allow_iff_entry` are load-bearing about `Acl.compile demoPolicy`) —
projected to the wire. The client receives the PROVEN default-deny compilation. -/
theorem servedWireA_filter_is_acl_compile :
    servedWireA.packetFilters
      = some [("base", (compiledPacketFilter Acl.demoPolicy).map filterRuleToWire)] := rfl

/-- **★ The served base filter, as concrete wire bytes.** The `PacketFilters["base"]`
the client receives is exactly the demo policy's compiled default-deny rule
(`accept src group:eng(10.0.0.0/8) dst 10.0.0.0/8:22`) in real marshaled strings —
demonstrating the compilation is not vacuous: SrcIPs `["10.0.0.0/8"]`, one
DstPort `{IP:"10.0.0.0/8", Ports:{22,22}}`. -/
theorem servedWireA_base_srcIPs :
    servedWireA.packetFilters.map (·.map (fun kv => (kv.1, kv.2.map (·.srcIPs))))
      = some [("base", [["10.0.0.0/8"]])] := by native_decide

theorem servedWireA_base_dstIP :
    servedWireA.packetFilters.map (·.map (fun kv => (kv.1, kv.2.map (fun r => r.dstPorts.map (·.ip)))))
      = some [("base", [["10.0.0.0/8"]])] := by native_decide

theorem servedWireA_base_ports :
    servedWireA.packetFilters.map
        (·.map (fun kv => (kv.1, kv.2.map (fun r => r.dstPorts.map (fun d => (d.ports.first, d.ports.last))))))
      = some [("base", [[(22, 22)]])] := by native_decide

/-! ### §6.6  Peers, addresses, tags, DERP, domain — the rest of the served map -/

/-- **Self is node A, addressed by IPAM.** The wire self node is `node-a` at its
IPAM-allocated `10.0.0.1/32`. -/
theorem servedWireA_self_name : servedWireA.node.map (·.name) = some "node-a" := rfl
theorem servedWireA_self_addr : servedWireA.node.map (·.addresses) = some ["10.0.0.1/32"] := by native_decide

/-- **Peer B is served, addressed by IPAM.** The wire peers carry `node-b` at its
IPAM-allocated `10.0.0.2/32` (the `Control.Ipam` distinct-allocation invariant). -/
theorem servedWireA_peer_names : servedWireA.peers.map (·.map (·.name)) = some ["node-b"] := rfl
theorem servedWireA_peer_addrs :
    servedWireA.peers.map (·.map (·.addresses)) = some [["10.0.0.2/32"]] := by native_decide

/-- **Peer tags flow through (untagged demo node ⇒ absent, Go omitempty).** -/
theorem servedWireA_peer_tags : servedWireA.peers.map (·.map (·.tags)) = some [none] := rfl

/-- **Tags ARE projected when present.** A tagged node's `Tags` carries its ACL
tags as wire strings — witnessing `nodeToWire` preserves `Control.Node.Tags`. -/
def taggedB : Node := { nodeB with tags := [[0x74, 0x61, 0x67, 0x3a, 0x65, 0x6e, 0x67]] }  -- "tag:eng"
theorem nodeToWire_tags : (nodeToWire taggedB).tags = some ["tag:eng"] := rfl

/-- **Every served node homes on drorb's DERP region.** Self and peer both carry
`HomeDERP = 1` (drorb's region), and the served DERPMap names region `"1"`. -/
theorem servedWireA_self_homederp : servedWireA.node.map (·.homeDERP) = some drorbRegionID := rfl
theorem servedWireA_peer_homederp :
    servedWireA.peers.map (·.map (·.homeDERP)) = some [drorbRegionID] := rfl
theorem servedWireA_derp_regions :
    servedWireA.derpMap.map (·.regions.map (·.1)) = some ["1"] := rfl
theorem servedWireA_derp_endpoint :
    (servedWireA.derpMap.bind (·.regions.head?)).map (fun kv => kv.2.nodes.map (·.port))
      = some [some drorbDerpPort] := rfl

/-- **The tailnet domain is served.** -/
theorem servedWireA_domain : servedWireA.domain = some "ts.net" := rfl

/-! ### §6.7  The served wire message ROUNDTRIPS through the proven codec

`servedWireA` decodes to itself through `Control.Tailcfg.MapResponse`'s proven
value-level codec — no field is dropped, mis-keyed, or mis-typed by the
projection. (Instantiates the general `MapResponse.fromJson?_toJson`.) -/
theorem servedWireA_roundtrips :
    Control.Tailcfg.MapResponse.fromJson? (Control.Tailcfg.MapResponse.toJson servedWireA)
      = some servedWireA :=
  Control.Tailcfg.MapResponse.fromJson?_toJson servedWireA

/-! ### §6.8  Unknown-key rejection -/

/-- An unregistered key gets the empty response (no netmap). -/
def keyUnknown : NodeKey := ⟨List.replicate 32 0xCC⟩
theorem servedWire_unknown_empty : (servedNetMapWire demoCoord keyUnknown).node = none := rfl

/-! ### §6.9  Runtime evidence and the axiom audit -/

#guard servedWireA.packetFilters
  == some [("base", (compiledPacketFilter Acl.demoPolicy).map filterRuleToWire)]
#guard servedWireA.node.map (·.name) == some "node-a"
#guard servedWireA.peers.map (·.map (·.name)) == some ["node-b"]
#guard servedWireA.peers.map (·.map (·.addresses)) == some [["10.0.0.2/32"]]
#guard servedWireA.node.map (·.homeDERP) == some 1
#guard servedWireA.derpMap.map (·.regions.map (·.1)) == some ["1"]
#guard servedWireA.domain == some "ts.net"
#guard (nodeToWire taggedB).tags == some ["tag:eng"]
#guard (Control.Tailcfg.MapResponse.fromJson? (Control.Tailcfg.MapResponse.toJson servedWireA)).isSome

#assert_axioms servedNetMapWire_filters ⊆ [stdAxioms]
#assert_axioms servedNetMapWire_eq_at ⊆ [stdAxioms]
#assert_axioms derpMapToWireAt_ipv4 ⊆ [stdAxioms]
#assert_axioms servedNetMapWire_projects_servedNetMapA ⊆ [stdAxioms]
#assert_axioms servedWireA_filter_is_acl_compile ⊆ [stdAxioms]
#assert_axioms servedWireA_base_srcIPs ⊆ [stdAxioms, nativeDecide]
#assert_axioms servedWireA_base_dstIP ⊆ [stdAxioms, nativeDecide]
#assert_axioms servedWireA_base_ports ⊆ [stdAxioms, nativeDecide]
#assert_axioms servedWireA_self_addr ⊆ [stdAxioms, nativeDecide]
#assert_axioms servedWireA_peer_addrs ⊆ [stdAxioms, nativeDecide]
#assert_axioms servedWireA_peer_tags ⊆ [stdAxioms]
#assert_axioms nodeToWire_tags ⊆ [stdAxioms]
#assert_axioms servedWireA_derp_regions ⊆ [stdAxioms]
#assert_axioms servedWireA_roundtrips ⊆ [stdAxioms]
#assert_axioms servedWire_unknown_empty ⊆ [stdAxioms]

/-! ## §7  Per-node DISCO + ENDPOINTS — storing the client's reported NAT state and
serving it faithfully to peers (so magicsock can build a path)

`nodeToWire` (§6.3) already PROJECTS a node's `disco`/`endpoints`/`derp` into the wire
peer's `DiscoKey`/`Endpoints`/`HomeDERP` — but the served core `Node` carried an EMPTY
disco (`⟨[]⟩`) and no endpoints, because nothing stored what the stock client reports.
A real `tailscale` client sends its `DiscoKey` and current `Endpoints` in every
`MapRequest` (`Control.Tailcfg.MapRequest.discoKey`/`.endpoints`, pinned on real capture
bytes by `Control.RealMapKat.mapRequestPoll_endpoints`/`_discoKey`); the coordinator must
STORE them per node and SERVE them to that node's peers, so magicsock can seal DISCO
probes to the peer's real disco key and attempt a direct path to its endpoints (falling
back to drorb's DERP home region otherwise).

This section is the verified core of that: the per-node NAT state, the overlay onto a
`ControlState`, and the theorems that the wire peer `nodeToWire` projects carries EXACTLY
the stored disco key + endpoints. The live capture/upsert IO is `ControlLive` (it CALLS
these), exactly as the record/handshake shims realize the proven FSMs. -/

/-- The NAT state a node reports in its `MapRequest`: its DISCO probe key and its
currently-known direct endpoints. magicsock seals DISCO probes to `disco` and attempts
direct UDP paths to `endpoints` (else the home DERP region). -/
structure NatReport where
  disco     : DiscoKey
  endpoints : List Endpoint
deriving Repr, DecidableEq

/-- Overlay a node with a reported DISCO key + endpoints (magicsock's live view). -/
def _root_.Control.Node.withNat (n : Node) (r : NatReport) : Node :=
  { n with disco := r.disco, endpoints := r.endpoints }

/-- The per-tailnet disco/endpoints table: node key → its last-reported NAT state. -/
abbrev NatTable := List (NodeKey × NatReport)

/-- First-match lookup of a node's reported NAT state. -/
def natLookup : NatTable → NodeKey → Option NatReport
  | [], _ => none
  | (k, r) :: t, key => if k = key then some r else natLookup t key

/-- Merge a newly-reported NAT state over the stored one, field-by-field: a report
that OMITS a field (empty disco or empty endpoints) keeps the previously-stored value.
The stock client sends its `DiscoKey` on the streaming `MapRequest` (no `Endpoints`) and
its `Endpoints` on the short non-streaming poll — so a naive last-write-wins would let
the disco-only stream request clobber the endpoints. Merging keeps both. -/
def natMerge (old new : NatReport) : NatReport :=
  { disco     := if new.disco.pub.isEmpty then old.disco else new.disco
  , endpoints := if new.endpoints.isEmpty then old.endpoints else new.endpoints }

/-- Insert or MERGE a node's reported NAT state (a field the new report omits keeps the
stored value — `natMerge`). -/
def natUpsert (tbl : NatTable) (k : NodeKey) (r : NatReport) : NatTable :=
  let merged := match natLookup tbl k with
    | some old => natMerge old r
    | none     => r
  (k, merged) :: tbl.filter (fun p => p.1 ≠ k)

/-! ### §7.0b  A BATCH of reports is chronological — the newest one decides

`natUpsert` is last-write-wins, and that is only sound if the coordinator feeds it reports
in the order the client SENT them. It did not. The verified h2 engine keeps a completed
request body in `H2.Conn.ConnState.streams` forever and `H2.Conn.setStream` PREPENDS, so
the live list is newest-FIRST and every drain re-offers a node's whole `MapRequest`
history. Folding that list left to right applied the OLDEST report LAST, so a node whose
NAT mapping had changed went on being served under its DEAD endpoint for the rest of the
connection. On one L2 that is invisible — the endpoint set never changes. Across two NATs
it is the whole difference between a punched direct path and a permanent relay: measured
2026-07-25, client B reported `[10.77.2.2:23845, 10.77.2.2:41641, 10.77.12.2:41641]` after
its NAT remapped, and the coordinator immediately overwrote it with the stale
`[10.77.2.2:41641, 10.77.12.2:41641]` replayed off an older stream.

The batch fold is named here so the ordering obligation is a THEOREM, not a comment:
`natUpsertAll` consumes a batch oldest-first and `natUpsertAll_last_endpoints` says the
LAST report's (nonempty) endpoint set is exactly what the table then serves. The caller's
obligation — hand it a CHRONOLOGICAL batch — is discharged at the seam by
`ControlLive.natReportsOf_setStream_newest_last`. -/

/-- Fold a CHRONOLOGICALLY-ORDERED batch of NAT reports into the table: oldest first,
newest last. This is exactly what the coordinator's per-connection drain loop does. -/
def natUpsertAll (tbl : NatTable) : List (NodeKey × NatReport) → NatTable
  | []          => tbl
  | (k, r) :: t => natUpsertAll (natUpsert tbl k r) t

/-- Upserting `k` puts `k`'s merged entry exactly where `natLookup` finds it FIRST. -/
theorem natLookup_natUpsert_self (tbl : NatTable) (k : NodeKey) (r : NatReport) :
    natLookup (natUpsert tbl k r) k
      = some (match natLookup tbl k with | some old => natMerge old r | none => r) := by
  simp [natUpsert, natLookup]

/-- A batch fold splits over `++`: folding `a` then `b` is folding `a ++ b`. -/
theorem natUpsertAll_append (tbl : NatTable) (a b : List (NodeKey × NatReport)) :
    natUpsertAll tbl (a ++ b) = natUpsertAll (natUpsertAll tbl a) b := by
  induction a generalizing tbl with
  | nil => rfl
  | cons hd t ih =>
      cases hd with
      | mk k r => simpa [natUpsertAll] using ih (natUpsert tbl k r)

/-- Folding a one-element batch is a single upsert. -/
theorem natUpsertAll_singleton (tbl : NatTable) (k : NodeKey) (r : NatReport) :
    natUpsertAll tbl [(k, r)] = natUpsert tbl k r := rfl

/-- ★ **The LAST report in a chronological batch is the one served.** If the batch ends
with node `k` reporting a NONEMPTY endpoint set, then after the fold the table's entry for
`k` carries EXACTLY that set — no earlier, staler report in the same batch survives. This
is precisely the property the live coordinator violated by folding newest-first. Compose
with `withNat_endpoints_served` and the served wire peer carries them. -/
theorem natUpsertAll_last_endpoints
    (tbl : NatTable) (pre : List (NodeKey × NatReport)) (k : NodeKey) (r : NatReport)
    (h : r.endpoints ≠ []) :
    (natLookup (natUpsertAll tbl (pre ++ [(k, r)])) k).map (fun q => q.endpoints)
      = some r.endpoints := by
  have hb : r.endpoints.isEmpty = false := by
    cases hp : r.endpoints with
    | nil => exact absurd hp h
    | cons a t => rfl
  rw [natUpsertAll_append, natUpsertAll_singleton, natLookup_natUpsert_self]
  cases hl : natLookup (natUpsertAll tbl pre) k with
  | none   => simp [natMerge, hb]
  | some o => simp [natMerge, hb]

/-- The same for the DISCO key: the batch's last NONEMPTY disco key wins. -/
theorem natUpsertAll_last_disco
    (tbl : NatTable) (pre : List (NodeKey × NatReport)) (k : NodeKey) (r : NatReport)
    (h : r.disco.pub ≠ []) :
    (natLookup (natUpsertAll tbl (pre ++ [(k, r)])) k).map (fun q => q.disco)
      = some r.disco := by
  have hb : r.disco.pub.isEmpty = false := by
    cases hp : r.disco.pub with
    | nil => exact absurd hp h
    | cons a t => rfl
  rw [natUpsertAll_append, natUpsertAll_singleton, natLookup_natUpsert_self]
  cases hl : natLookup (natUpsertAll tbl pre) k with
  | none   => simp [natMerge, hb]
  | some o => simp [natMerge, hb]

/-- **The ordering is NOT vacuous** — the exact live batch that broke cross-NAT traversal.
One node, two reports in one drain: the stale mapping first, the fresh one last, which is
the order `ControlLive.natReportsOf` now emits them in. The fold serves `:23845`. Under
the old newest-first order the stale `:41641` was last and won, and that dead port is what
the peer punched at, forever. -/
theorem natUpsertAll_fresh_endpoint_wins :
    (natLookup
      (natUpsertAll []
        [ (⟨[104]⟩, { disco := ⟨[126]⟩, endpoints := [{ addr := [10,77,2,2], port := 41641 }] })
        , (⟨[104]⟩, { disco := ⟨[126]⟩, endpoints := [{ addr := [10,77,2,2], port := 23845 }] }) ])
      ⟨[104]⟩).map (fun q => q.endpoints)
      = some [{ addr := [10,77,2,2], port := 23845 }] := by decide

/-- ...and the OLD order is what produced the dead port, shown as the counter-fact: the
same two reports offered newest-first serve `:41641`, the mapping the NAT had already
moved off. -/
theorem natUpsertAll_reversed_serves_the_stale_port :
    (natLookup
      (natUpsertAll []
        [ (⟨[104]⟩, { disco := ⟨[126]⟩, endpoints := [{ addr := [10,77,2,2], port := 23845 }] })
        , (⟨[104]⟩, { disco := ⟨[126]⟩, endpoints := [{ addr := [10,77,2,2], port := 41641 }] }) ])
      ⟨[104]⟩).map (fun q => q.endpoints)
      = some [{ addr := [10,77,2,2], port := 41641 }] := by decide

/-! ### §7.0c  What the fold looks like once the drain PRUNES its consumed bodies

`natUpsertAll_last_endpoints` above is the strong statement: over a batch of ANY length,
the last nonempty report wins. It had to be, because the live drain was handed a node's
whole `MapRequest` history on every record — `H2.Conn.ConnState.streams` never pruned a
completed body, so the batch grew without bound and the fold's ORDER was the only thing
standing between a peer and a dead endpoint.

`ControlLive.pruneConsumed` removes the history rather than ordering it: a body is folded
once, at the drain where it completed, and then cleared
(`ControlLive.natReportsOf_pruneConsumed` — no consumed stream contributes to a later
batch). The batch a steady-state drain hands this fold is therefore a SINGLETON
(`ControlLive.natReportsOf_pruneConsumed_singleton`), and on a singleton "the last report
wins" degenerates to "the only report is stored" — stated here so the degeneration is on
the record and not assumed. The general theorem is NOT weakened: it still holds verbatim
and still covers a drain that legitimately sees two completions in one record. -/

/-- Filtering `k` out of the table cannot change what a DIFFERENT key looks up. -/
theorem natLookup_filter_ne (tbl : NatTable) (k key : NodeKey) (h : key ≠ k) :
    natLookup (tbl.filter (fun p => p.1 ≠ k)) key = natLookup tbl key := by
  induction tbl with
  | nil => rfl
  | cons hd t ih =>
      obtain ⟨a, b⟩ := hd
      by_cases ha : a = k
      · have hdrop : ((a, b) :: t).filter (fun p => p.1 ≠ k) = t.filter (fun p => p.1 ≠ k) := by
          simp [List.filter_cons, ha]
        have hne : ¬ a = key := by rw [ha]; exact fun hc => h hc.symm
        rw [hdrop, ih]
        simp [natLookup, hne]
      · have hkeep : ((a, b) :: t).filter (fun p => p.1 ≠ k)
            = (a, b) :: t.filter (fun p => p.1 ≠ k) := by
          simp [List.filter_cons, ha]
        rw [hkeep]
        by_cases hak : a = key
        · simp [natLookup, hak]
        · simp only [natLookup, if_neg hak]
          exact ih

/-- ★ **A report that merges to what is ALREADY stored serves exactly the same table.**
At every key, `natLookup` after the upsert agrees with `natLookup` before it — the upsert
only reorders. So a coordinator that SKIPS such an upsert (and skips the tailnet
generation bump + changelog append it would otherwise trigger) has not taken a shortcut:
there is nothing for the netmap push to announce. This is what licenses
`ControlLive.storeNat` to report the DELTA rather than re-announce the state on every
record a client happens to send. -/
theorem natUpsert_lookup_noop (tbl : NatTable) (k : NodeKey) (r old : NatReport)
    (hm : natLookup tbl k = some old) (hmerge : natMerge old r = old) (key : NodeKey) :
    natLookup (natUpsert tbl k r) key = natLookup tbl key := by
  unfold natUpsert
  rw [hm]
  by_cases hk : key = k
  · subst hk
    simp [natLookup, hmerge, hm]
  · have hk' : ¬ k = key := fun hc => hk hc.symm
    simp only [natLookup, if_neg hk']
    exact natLookup_filter_ne tbl k key hk

/-- ★ **The singleton case of `natUpsertAll_last_endpoints`** — the shape a pruning drain
actually folds. One report in, that report served. -/
theorem natUpsertAll_one_report_endpoints
    (tbl : NatTable) (k : NodeKey) (r : NatReport) (h : r.endpoints ≠ []) :
    (natLookup (natUpsertAll tbl [(k, r)]) k).map (fun q => q.endpoints) = some r.endpoints :=
  natUpsertAll_last_endpoints tbl [] k r h

/-- The same for the DISCO key. -/
theorem natUpsertAll_one_report_disco
    (tbl : NatTable) (k : NodeKey) (r : NatReport) (h : r.disco.pub ≠ []) :
    (natLookup (natUpsertAll tbl [(k, r)]) k).map (fun q => q.disco) = some r.disco :=
  natUpsertAll_last_disco tbl [] k r h

/-- Apply the reported NAT state to a registration if the table has an entry for it;
otherwise leave the registration untouched. -/
def applyNatReg (tbl : NatTable) (rg : Registration) : Registration :=
  match natLookup tbl rg.nodeKey with
  | some r => { rg with node := rg.node.withNat r }
  | none   => rg

/-- Overlay a whole `ControlState`'s registrations with their reported NAT state. The
served netmap (`buildNetMap` / `servedNetMapWire`) then carries each node's real disco +
endpoints. -/
def applyNatState (tbl : NatTable) (st : ControlState) : ControlState :=
  { st with nodes := st.nodes.map (applyNatReg tbl) }

/-! ### §7.1  Faithfulness: the wire peer carries EXACTLY the stored disco + endpoints -/

/-- **nodeToWire serves a nonempty disco key faithfully.** A node whose (stored) disco
key is nonempty projects to the wire `DiscoKey = "discokey:<hex>"` of exactly that key
(via the proven `Control.Bridge.DiscoKey.toText`). -/
theorem nodeToWire_disco_faithful (n : Node) (h : n.disco.pub ≠ []) :
    (nodeToWire n).discoKey = some (Control.Bridge.DiscoKey.toText n.disco.pub) := by
  have hb : n.disco.pub.isEmpty = false := by
    cases hp : n.disco.pub with
    | nil => exact absurd hp h
    | cons a t => rfl
  simp [nodeToWire, hb]

/-- **nodeToWire serves nonempty endpoints faithfully.** A node with (stored) endpoints
projects to the wire `Endpoints` = each endpoint rendered as `"a.b.c.d:port"` (via the
proven `Control.Bridge.AddrPort4.toText`). -/
theorem nodeToWire_endpoints_faithful (n : Node) (h : n.endpoints ≠ []) :
    (nodeToWire n).endpoints = some (n.endpoints.map endpointToWire) := by
  have hb : n.endpoints.isEmpty = false := by
    cases hp : n.endpoints with
    | nil => exact absurd hp h
    | cons a t => rfl
  simp [nodeToWire, hb]

/-- **nodeToWire always serves the home DERP region** (drorb's region for every served
node): the wire `HomeDERP` is the node's core `derp` region unconditionally. -/
theorem nodeToWire_homeDERP (n : Node) : (nodeToWire n).homeDERP = n.derp := rfl

/-- **★ The served peer wire DISCO IS the stored one.** After overlaying a node with a
reported NAT state whose disco is nonempty, the wire peer `nodeToWire` projects carries
exactly `discokey:<hex>` of the STORED disco key. -/
theorem withNat_disco_served (n : Node) (r : NatReport) (h : r.disco.pub ≠ []) :
    (nodeToWire (n.withNat r)).discoKey = some (Control.Bridge.DiscoKey.toText r.disco.pub) :=
  nodeToWire_disco_faithful (n.withNat r) (by simpa [Node.withNat] using h)

/-- **★ The served peer wire ENDPOINTS ARE the stored ones.** After overlaying a node
with a reported NAT state whose endpoints are nonempty, the wire peer carries exactly the
STORED endpoints, each rendered `"a.b.c.d:port"`. -/
theorem withNat_endpoints_served (n : Node) (r : NatReport) (h : r.endpoints ≠ []) :
    (nodeToWire (n.withNat r)).endpoints = some (r.endpoints.map endpointToWire) :=
  nodeToWire_endpoints_faithful (n.withNat r) (by simpa [Node.withNat] using h)

/-- **The overlay stamps the reported state onto the matching registration's node.** If
the table has an entry `r` for `rg`'s key, `applyNatReg` yields a registration whose node
is `rg.node.withNat r` — the disco + endpoints the client reported. -/
theorem applyNatReg_hit (tbl : NatTable) (rg : Registration) (r : NatReport)
    (h : natLookup tbl rg.nodeKey = some r) :
    (applyNatReg tbl rg).node = rg.node.withNat r := by
  simp [applyNatReg, h]

/-! ### §7.2  A concrete demonstration — a real disco + endpoint, served on the wire

Node B reports the disco key + endpoint the stock 1.98.8 client carried in its captured
`MapRequest` poll (`Control.RealMapKat.realMapRequestPoll`: `discokey:b10f…e555`, endpoint
`73.4.118.165:41999`). The overlay stores it; the wire peer B carries it verbatim so
magicsock can path-build. (Disco key here as raw bytes; the wire-string bridge round-trip
is `Control.Bridge.DiscoKey.ofText_toText`.) -/

/-- A real reported NAT state: a 32-byte disco key + one direct endpoint. -/
def demoNat : NatReport :=
  { disco := ⟨List.replicate 32 0x7e⟩
  , endpoints := [{ addr := [73, 4, 118, 165], port := 41999 }] }

theorem demoNat_disco_served :
    (nodeToWire (nodeB.withNat demoNat)).discoKey
      = some (Control.Bridge.DiscoKey.toText demoNat.disco.pub) :=
  withNat_disco_served nodeB demoNat (by decide)

theorem demoNat_endpoints_served :
    (nodeToWire (nodeB.withNat demoNat)).endpoints = some ["73.4.118.165:41999"] := by
  native_decide

theorem demoNat_homederp_served :
    (nodeToWire (nodeB.withNat demoNat)).homeDERP = drorbRegionID := rfl

#guard (nodeToWire (nodeB.withNat demoNat)).discoKey.isSome
#guard (nodeToWire (nodeB.withNat demoNat)).endpoints == some ["73.4.118.165:41999"]
#guard (nodeToWire (nodeB.withNat demoNat)).homeDERP == 1

#assert_axioms nodeToWire_disco_faithful ⊆ [stdAxioms]
#assert_axioms nodeToWire_endpoints_faithful ⊆ [stdAxioms]
#assert_axioms nodeToWire_homeDERP ⊆ [stdAxioms]
#assert_axioms withNat_disco_served ⊆ [stdAxioms]
#assert_axioms withNat_endpoints_served ⊆ [stdAxioms]
#assert_axioms natLookup_natUpsert_self ⊆ [stdAxioms]
#assert_axioms natUpsertAll_append ⊆ [stdAxioms]
#assert_axioms natUpsertAll_last_endpoints ⊆ [stdAxioms]
#assert_axioms natUpsertAll_last_disco ⊆ [stdAxioms]
#assert_axioms natUpsertAll_fresh_endpoint_wins ⊆ [stdAxioms]
#assert_axioms natUpsertAll_reversed_serves_the_stale_port ⊆ [stdAxioms]
#assert_axioms applyNatReg_hit ⊆ [stdAxioms]
#assert_axioms demoNat_endpoints_served ⊆ [stdAxioms, nativeDecide]


end Control.Join
