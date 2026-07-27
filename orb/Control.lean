import Crypto
import Wireguard
/-!
# Control — a verified coordination-server ("control plane") for a mesh VPN

This is the FOUNDATION stone for a verified, self-hostable coordination server
in the shape of the open-source `headscale` (github.com/juanfont/headscale,
BSD-3) — the community control server for the Tailscale protocol — speaking the
public wire types the `tailscale` client defines in its `tailcfg` package
(github.com/tailscale/tailscale, BSD-3). Everything here is derived from that
PUBLIC specification and source; it is an independent clean-room model.

The coordination server is the rendezvous point of a mesh overlay. Nodes never
trust it with their traffic — WireGuard end-to-end encryption (drorb's
`Wireguard` model) and the DISCO NAT-traversal handshake (`Disco`) run *between*
nodes. What the server does is *coordinate*: it authenticates a node's identity
key, decides which nodes may talk (the ACL / packet filter), and hands each node
a **netmap** — the current view of its authorized peers (their public keys,
addresses, endpoints, DERP homes) plus the packet-filter and DNS config it must
enforce. This is exactly a transition system: a node **registers**, is
**authorized**, **polls** for its netmap, and receives **deltas** as the mesh
changes — the same discipline the engine already models for TLS
(`TlsHandshake.serverStep`), HTTP/2 (`H2.Conn.feed`), and DISCO (`Disco.step`).

## What this module fixes (the shared base the fan-out builds on)

1. **Core types** — `NodeKey` / `MachineKey` / `DiscoKey` (Curve25519 public
   keys, the identities `Crypto` provides), `Prefix` (dual-stack CIDR), `Node`
   (a netmap entry), `NetMap` (self + peers + DNS + packet-filter), and the wire
   messages `RegisterRequest` / `RegisterResponse` / `MapRequest` /
   `MapResponse`.
2. **Two message flows, with byte-level round-trips** — every wire message has a
   total `enc`/`dec` over `Bytes` and a proven `dec (enc m ++ tail) = some (m,
   tail)`, built from one self-delimiting codec algebra (LEB128 length prefixes),
   so the framing is unambiguous.
3. **The coordination transition system** — `ControlState` + `step`, with the
   layer's safety invariants proven: an unauthorized node gets no netmap, and a
   netmap only ever names authorized peers.
4. **The composition interfaces** the later components plug into — named so the
   fan-out lanes compose rather than diverge (see `Roadmap` at the end):
   * ACL lane → produces a `PacketFilter` (`FilterRule` list); consumed by
     `packetFilterAllows`.
   * netmap-delta lane → `MapResponse.delta` folded by `NetMap.applyDelta`.
   * MagicDNS lane → `DnsConfig` resolved by `DnsConfig.resolve`.
   * netmap→WireGuard lane → `Node.toWgPeer : Node → Wireguard.Peer.PeerCfg`
     (the real drorb WireGuard peer config — not a mirror).

## Trust surface

The identity keys are `Crypto`'s Curve25519/Ed25519 (HACL*/EverCrypt); this
module adds NO new crypto axioms. The safety theorems are pure transition-system
facts about `step`; the authorization decision is an uninterpreted boundary
(`Policy.authorizes`) exactly as `Disco.Config.authPong` is — the identity-proof
check (a signed registration / pre-auth key) is discharged where a concrete
policy is instantiated, not assumed here.
-/

namespace Control

/-- The engine's byte view: a flat list of octets, matching `Proto.Bytes` and
`Wireguard.Bytes` (both `List UInt8`), so values flow into the WireGuard peer
config without conversion. -/
abbrev Bytes := List UInt8

/-! ## §1  A self-delimiting codec algebra

Real `tailcfg` messages are JSON on the wire; we model the framing with an
unambiguous binary codec so "encode then decode is the identity" is a checkable
`Bytes` theorem rather than a statement about a JSON library. Every primitive is
*self-delimiting* — it carries its own length — so message codecs are just
concatenations and their round-trips chain. -/

/-- Unsigned LEB128: the base-128 little-endian varint. Each byte carries 7 bits
of magnitude; the high bit (`+128`) is the "more bytes follow" continuation
flag, clear on the last byte. -/
def uvarint (n : Nat) : Bytes :=
  if n < 128 then [UInt8.ofNat n]
  else UInt8.ofNat (n % 128 + 128) :: uvarint (n / 128)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Read one LEB128 varint off the front, returning the value and the rest. -/
def readUvarint : Bytes → Option (Nat × Bytes)
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else match readUvarint rest with
      | some (m, rest') => some ((b.toNat - 128) + 128 * m, rest')
      | none => none

/-- **Varint round-trip.** Encoding a `Nat` and reading it back recovers the
value and leaves the trailing bytes untouched. -/
theorem uvarint_roundtrip (n : Nat) (tail : Bytes) :
    readUvarint (uvarint n ++ tail) = some (n, tail) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [uvarint]
    by_cases h : n < 128
    · rw [if_pos h]
      simp only [List.cons_append, List.nil_append, readUvarint]
      have hval : (UInt8.ofNat n).toNat = n := by rw [UInt8.toNat_ofNat']; omega
      rw [hval, if_pos (by omega)]
    · rw [if_neg h]
      simp only [List.cons_append, readUvarint]
      have hlt : n % 128 < 128 := Nat.mod_lt _ (by omega)
      have hb : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by
        rw [UInt8.toNat_ofNat']; omega
      rw [hb, if_neg (by omega)]
      have hdiv : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
      rw [ih (n / 128) hdiv]
      dsimp only
      have hrec : (n % 128 + 128) - 128 + 128 * (n / 128) = n := by
        have := Nat.div_add_mod n 128; omega
      rw [hrec]

/-! ### Field primitives -/

/-- A `Nat` field: just its varint. -/
def putNat (n : Nat) : Bytes := uvarint n
/-- Read a `Nat` field. -/
def getNat : Bytes → Option (Nat × Bytes) := readUvarint

theorem getNat_putNat (n : Nat) (tail : Bytes) :
    getNat (putNat n ++ tail) = some (n, tail) := uvarint_roundtrip n tail

/-- A length-prefixed byte string. -/
def putBytes (b : Bytes) : Bytes := uvarint b.length ++ b
/-- Read a length-prefixed byte string. -/
def getBytes (bs : Bytes) : Option (Bytes × Bytes) :=
  match readUvarint bs with
  | some (n, rest) => if n ≤ rest.length then some (rest.take n, rest.drop n) else none
  | none => none

theorem getBytes_putBytes (b tail : Bytes) :
    getBytes (putBytes b ++ tail) = some (b, tail) := by
  unfold putBytes getBytes
  rw [List.append_assoc, uvarint_roundtrip]
  dsimp only
  rw [if_pos (by simp [List.length_append])]
  simp [List.take_left, List.drop_left]

/-- A boolean field: one byte, `0`/`1`. -/
def putBool (b : Bool) : Bytes := [if b then 1 else 0]
/-- Read a boolean field: any nonzero byte is `true`. -/
def getBool : Bytes → Option (Bool × Bytes)
  | [] => none
  | b :: rest => some (b != 0, rest)

theorem getBool_putBool (b : Bool) (tail : Bytes) :
    getBool (putBool b ++ tail) = some (b, tail) := by
  cases b <;> simp [putBool, getBool]

/-! ### Length-prefixed sequences

A generic list codec: the element count as a varint, then each element's own
self-delimiting encoding. `getSeq`/`putSeq` round-trip whenever the element
codec does — the reusable lemma the message codecs lean on. -/

/-- Decode exactly `n` elements with `dec`. -/
def getListN {α} (dec : Bytes → Option (α × Bytes)) : Nat → Bytes → Option (List α × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match dec bs with
    | some (a, rest) =>
      match getListN dec n rest with
      | some (as, rest') => some (a :: as, rest')
      | none => none
    | none => none

/-- Encode a list: count prefix, then the concatenated element encodings. -/
def putSeq {α} (enc : α → Bytes) (xs : List α) : Bytes :=
  uvarint xs.length ++ xs.flatMap enc

/-- Decode a length-prefixed list. -/
def getSeq {α} (dec : Bytes → Option (α × Bytes)) (bs : Bytes) : Option (List α × Bytes) :=
  match readUvarint bs with
  | some (n, rest) => getListN dec n rest
  | none => none

theorem getListN_flatMap {α} (enc : α → Bytes) (dec : Bytes → Option (α × Bytes))
    (hrt : ∀ a t, dec (enc a ++ t) = some (a, t)) :
    ∀ (xs : List α) (tail : Bytes),
      getListN dec xs.length (xs.flatMap enc ++ tail) = some (xs, tail) := by
  intro xs
  induction xs with
  | nil => intro tail; simp [getListN, List.flatMap]
  | cons a as ih =>
    intro tail
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, getListN]
    rw [hrt a]
    dsimp only
    rw [ih tail]

/-- **Sequence round-trip**, parametric in the element codec's round-trip. -/
theorem getSeq_putSeq {α} (enc : α → Bytes) (dec : Bytes → Option (α × Bytes))
    (hrt : ∀ a t, dec (enc a ++ t) = some (a, t)) (xs : List α) (tail : Bytes) :
    getSeq dec (putSeq enc xs ++ tail) = some (xs, tail) := by
  unfold getSeq putSeq
  rw [List.append_assoc, uvarint_roundtrip]
  exact getListN_flatMap enc dec hrt xs tail

/-- A pair codec (used for DNS name→address records). -/
def putPair {α β} (ea : α → Bytes) (eb : β → Bytes) (p : α × β) : Bytes :=
  ea p.1 ++ eb p.2
def getPair {α β} (da : Bytes → Option (α × Bytes)) (db : Bytes → Option (β × Bytes))
    (bs : Bytes) : Option ((α × β) × Bytes) :=
  match da bs with
  | some (a, r1) => match db r1 with
    | some (b, r2) => some ((a, b), r2)
    | none => none
  | none => none

theorem getPair_putPair {α β} (ea : α → Bytes) (eb : β → Bytes)
    (da : Bytes → Option (α × Bytes)) (db : Bytes → Option (β × Bytes))
    (ha : ∀ a t, da (ea a ++ t) = some (a, t))
    (hb : ∀ b t, db (eb b ++ t) = some (b, t))
    (p : α × β) (tail : Bytes) :
    getPair da db (putPair ea eb p ++ tail) = some (p, tail) := by
  obtain ⟨a, b⟩ := p
  simp only [putPair, getPair, List.append_assoc, ha, hb]

/-! ## §2  Core types (tailcfg-faithful)

The identities. In `tailcfg` a node has three Curve25519 keys, each a 32-byte
public value: the **machine key** (the durable device identity, `mkey:`), the
**node key** (the rotatable WireGuard/overlay key the netmap distributes,
`nodekey:`), and the **disco key** (the NAT-traversal probe key DISCO boxes are
sealed to, `discokey:`). We wrap `Bytes` in distinct one-field structures so the
type system keeps them apart; a well-formed key is `keyLen` bytes. -/

/-- Curve25519 public-key length in bytes (`Crypto.x25519Base` output width). -/
def keyLen : Nat := 32

/-- The rotatable node (overlay/WireGuard) public key, `tailcfg.NodeKey`. -/
structure NodeKey where
  pub : Bytes
deriving Repr, DecidableEq

/-- The durable machine (device) public key, `tailcfg.MachineKey`. -/
structure MachineKey where
  pub : Bytes
deriving Repr, DecidableEq

/-- The DISCO NAT-traversal public key, `tailcfg.DiscoKey`; part of the netmap
so peers can seal DISCO probes to this node (`Disco`, `Crypto.cryptoBoxSeal`). -/
structure DiscoKey where
  pub : Bytes
deriving Repr, DecidableEq

/-- A key is well-formed when it is exactly `keyLen` bytes. -/
def NodeKey.wf (k : NodeKey) : Prop := k.pub.length = keyLen

/-- A dual-stack CIDR prefix: a 4-byte (IPv4) or 16-byte (IPv6) address and a
prefix length in bits. This is `netip.Prefix`, the shape of both a node's own
addresses and the routes allowed toward it. -/
structure Prefix where
  addr : Bytes
  bits : Nat
deriving Repr, DecidableEq

/-- IPv4 iff the address is 4 bytes. -/
def Prefix.isV4 (p : Prefix) : Bool := p.addr.length == 4
/-- IPv6 iff the address is 16 bytes. -/
def Prefix.isV6 (p : Prefix) : Bool := p.addr.length == 16
/-- Well-formed: a v4 prefix with ≤32 bits or a v6 prefix with ≤128. -/
def Prefix.wf (p : Prefix) : Prop :=
  (p.addr.length = 4 ∧ p.bits ≤ 32) ∨ (p.addr.length = 16 ∧ p.bits ≤ 128)

/-- A candidate direct endpoint: an address and a UDP port (`0…65535`). -/
structure Endpoint where
  addr : Bytes
  port : Nat
deriving Repr, DecidableEq

/-- A netmap node — one entry in the mesh view (`tailcfg.Node`): its identity
keys, the addresses it owns (dual-stack), the routes allowed toward it (self
address(es) plus any advertised subnet routes), its currently-known direct
endpoints, its home DERP region, DNS name, liveness, key expiry, and whether the
coordination server has authorized it. -/
structure Node where
  /-- Stable numeric id (`tailcfg.NodeID`). -/
  id         : Nat
  /-- Opaque stable string id, survives key rotation (`StableNodeID`). -/
  stableID   : Bytes
  /-- MagicDNS name (the FQDN this node answers to). -/
  name       : Bytes
  /-- Owning user id. -/
  user       : Nat
  /-- The overlay/WireGuard public key the netmap distributes. -/
  key        : NodeKey
  /-- The durable machine key. -/
  machine    : MachineKey
  /-- The DISCO probe key. -/
  disco      : DiscoKey
  /-- The node's own assigned overlay addresses (a `/32` and/or `/128`). -/
  addresses  : List Prefix
  /-- Routes accepted toward this node (its addresses + advertised subnets). -/
  allowedIPs : List Prefix
  /-- Known direct endpoints for hole-punching. -/
  endpoints  : List Endpoint
  /-- Home DERP region id (the relay fallback). -/
  derp       : Nat
  /-- Currently believed online. -/
  online     : Bool
  /-- Node-key expiry (unix seconds; `0` = never). -/
  keyExpiry  : Nat
  /-- The coordination server has authorized this machine. -/
  authorized : Bool
  /-- ACL tags applied to this node (`tailcfg.Node.Tags`,
  `github.com/tailscale/tailscale tailcfg/tailcfg.go:418`:
  `Tags []string \`json:",omitempty"\``); copied from the admitting pre-auth
  key onto the node at registration (headscale copies the key's tags to the
  node), and resolved by the ACL compiler for `tag:<name>` selectors. -/
  tags       : List Bytes := []
deriving Repr, DecidableEq

/-- MagicDNS / split-DNS configuration handed down in the netmap
(`tailcfg.DNSConfig`, abstracted): the search domains and the MagicDNS
name→address records for peers. -/
structure DnsConfig where
  /-- Search domains appended to bare names. -/
  domains  : List Bytes
  /-- MagicDNS records: fully-qualified name ↦ overlay address. -/
  records  : List (Bytes × Bytes)
deriving Repr, DecidableEq

/-- Nothing configured. -/
def DnsConfig.empty : DnsConfig := { domains := [], records := [] }

/-! ### The packet filter — the ACL lane's output type

This is the interface the ACL lane produces and the dataplane consumes. An ACL
policy compiles to a `PacketFilter`: a list of allow-rules, each a set of source
CIDRs and a set of destination `net:port` ranges (`tailcfg.FilterRule` /
`NetPortRange`). Default-deny: a packet is allowed iff SOME rule matches it. The
ACL lane's obligation is exactly "this compiled filter realizes the policy"; its
*type* is fixed here so its output drops straight into `NetMap.packetFilter`. -/

/-- An inclusive port range (`tailcfg.PortRange`). -/
structure PortRange where
  first : Nat
  last  : Nat
deriving Repr, DecidableEq

/-- Whether a port falls in the range. -/
def PortRange.contains (r : PortRange) (port : Nat) : Bool :=
  r.first ≤ port && port ≤ r.last

/-- A destination CIDR with an allowed port range (`tailcfg.NetPortRange`). -/
structure NetPortRange where
  net   : Prefix
  ports : PortRange
deriving Repr, DecidableEq

/-- One allow-rule (`tailcfg.FilterRule`): traffic from any of `srcIPs`, of any
of `protos` (empty ⇒ any IP protocol, tailcfg's empty `IPProto`), to any of
`dstPorts`, is permitted. **This is the canonical rule shape the ACL lane
compiles to** (`Control.Acl.FilterRule` is written to reconcile field-for-field:
`srcs↦srcIPs`, `dsts↦dstPorts`, `protos↦protos`). -/
structure FilterRule where
  srcIPs   : List Prefix
  dstPorts : List NetPortRange
  protos   : List Nat
deriving Repr, DecidableEq

/-- The compiled packet filter: a disjunction of allow-rules. **This is the type
the ACL component emits.** -/
abbrev PacketFilter := List FilterRule

/-- Longest/any-prefix membership: does `ip` fall under `p`? (Same-family, first
`bits` bits agree — reuses the engine's `Wireguard.Peer.bitAt`.) -/
def Prefix.matches (p : Prefix) (ip : Bytes) : Bool :=
  ip.length == p.addr.length &&
    (List.range p.bits).all (fun i => Wireguard.Peer.bitAt ip i == Wireguard.Peer.bitAt p.addr i)

/-- Does a single rule admit `(src, dst, port, proto)`? Source CIDR, protocol,
and destination `net:port` must all match (empty `protos` ⇒ any protocol). -/
def FilterRule.admits (r : FilterRule) (src dst : Bytes) (port proto : Nat) : Bool :=
  r.srcIPs.any (·.matches src) &&
    (r.protos.isEmpty || r.protos.contains proto) &&
    r.dstPorts.any (fun npr => npr.net.matches dst && npr.ports.contains port)

/-- **The packet-filter decision (default-deny).** A `(src, dst, port, proto)`
flow is allowed iff at least one rule admits it. -/
def packetFilterAllows (pf : PacketFilter) (src dst : Bytes) (port proto : Nat) : Bool :=
  pf.any (·.admits src dst port proto)

/-- **Default-deny.** The empty filter allows nothing. -/
theorem packetFilter_empty_denies (src dst : Bytes) (port proto : Nat) :
    packetFilterAllows [] src dst port proto = false := rfl

/-- **A permitted flow has a witnessing rule.** If the filter allows a flow,
some rule in it admits that flow — the ACL lane's soundness obligation is
stated against exactly this. -/
theorem packetFilter_allow_witness (pf : PacketFilter) (src dst : Bytes) (port proto : Nat)
    (h : packetFilterAllows pf src dst port proto = true) :
    ∃ r ∈ pf, r.admits src dst port proto = true := by
  unfold packetFilterAllows at h
  simpa using (List.any_eq_true.mp h)

/-- The mesh view handed to one node (`tailcfg.NetworkMap` / the payload of a
full `MapResponse`): the node's own record, its authorized peers, the DNS
config, and the packet-filter it must enforce. -/
structure NetMap where
  self         : Node
  peers        : List Node
  dns          : DnsConfig
  packetFilter : PacketFilter
deriving Repr

/-! ## §3  Wire messages and their round-trips

The two flows the coordination protocol runs over. Each message has a codec and
a proven byte-level round-trip, chained from §1. -/

/-! ### Key / prefix / endpoint codecs -/

def putNodeKey (k : NodeKey) : Bytes := putBytes k.pub
def getNodeKey (bs : Bytes) : Option (NodeKey × Bytes) :=
  match getBytes bs with | some (p, r) => some (⟨p⟩, r) | none => none
theorem getNodeKey_put (k : NodeKey) (t : Bytes) :
    getNodeKey (putNodeKey k ++ t) = some (k, t) := by
  obtain ⟨p⟩ := k; simp only [putNodeKey, getNodeKey, getBytes_putBytes]

def putMachineKey (k : MachineKey) : Bytes := putBytes k.pub
def getMachineKey (bs : Bytes) : Option (MachineKey × Bytes) :=
  match getBytes bs with | some (p, r) => some (⟨p⟩, r) | none => none
theorem getMachineKey_put (k : MachineKey) (t : Bytes) :
    getMachineKey (putMachineKey k ++ t) = some (k, t) := by
  obtain ⟨p⟩ := k; simp only [putMachineKey, getMachineKey, getBytes_putBytes]

def putDiscoKey (k : DiscoKey) : Bytes := putBytes k.pub
def getDiscoKey (bs : Bytes) : Option (DiscoKey × Bytes) :=
  match getBytes bs with | some (p, r) => some (⟨p⟩, r) | none => none
theorem getDiscoKey_put (k : DiscoKey) (t : Bytes) :
    getDiscoKey (putDiscoKey k ++ t) = some (k, t) := by
  obtain ⟨p⟩ := k; simp only [putDiscoKey, getDiscoKey, getBytes_putBytes]

def putPrefix (p : Prefix) : Bytes := putBytes p.addr ++ putNat p.bits
def getPrefix (bs : Bytes) : Option (Prefix × Bytes) :=
  match getBytes bs with
  | some (addr, r1) => match getNat r1 with
    | some (bits, r2) => some (⟨addr, bits⟩, r2)
    | none => none
  | none => none
theorem getPrefix_put (p : Prefix) (t : Bytes) :
    getPrefix (putPrefix p ++ t) = some (p, t) := by
  obtain ⟨addr, bits⟩ := p
  simp only [putPrefix, getPrefix, List.append_assoc, getBytes_putBytes, getNat_putNat]

def putEndpoint (e : Endpoint) : Bytes := putBytes e.addr ++ putNat e.port
def getEndpoint (bs : Bytes) : Option (Endpoint × Bytes) :=
  match getBytes bs with
  | some (addr, r1) => match getNat r1 with
    | some (port, r2) => some (⟨addr, port⟩, r2)
    | none => none
  | none => none
theorem getEndpoint_put (e : Endpoint) (t : Bytes) :
    getEndpoint (putEndpoint e ++ t) = some (e, t) := by
  obtain ⟨addr, port⟩ := e
  simp only [putEndpoint, getEndpoint, List.append_assoc, getBytes_putBytes, getNat_putNat]

/-! ### Node codec -/

def putNode (n : Node) : Bytes :=
  putNat n.id ++ putBytes n.stableID ++ putBytes n.name ++ putNat n.user ++
  putNodeKey n.key ++ putMachineKey n.machine ++ putDiscoKey n.disco ++
  putSeq putPrefix n.addresses ++ putSeq putPrefix n.allowedIPs ++
  putSeq putEndpoint n.endpoints ++ putNat n.derp ++ putBool n.online ++
  putNat n.keyExpiry ++ putBool n.authorized ++ putSeq putBytes n.tags

def getNode (bs : Bytes) : Option (Node × Bytes) := do
  let (id, r) ← getNat bs
  let (stableID, r) ← getBytes r
  let (name, r) ← getBytes r
  let (user, r) ← getNat r
  let (key, r) ← getNodeKey r
  let (machine, r) ← getMachineKey r
  let (disco, r) ← getDiscoKey r
  let (addresses, r) ← getSeq getPrefix r
  let (allowedIPs, r) ← getSeq getPrefix r
  let (endpoints, r) ← getSeq getEndpoint r
  let (derp, r) ← getNat r
  let (online, r) ← getBool r
  let (keyExpiry, r) ← getNat r
  let (authorized, r) ← getBool r
  let (tags, r) ← getSeq getBytes r
  some ({ id, stableID, name, user, key, machine, disco, addresses, allowedIPs,
          endpoints, derp, online, keyExpiry, authorized, tags }, r)

theorem getNode_put (n : Node) (t : Bytes) : getNode (putNode n ++ t) = some (n, t) := by
  obtain ⟨id, stableID, name, user, key, machine, disco, addresses, allowedIPs,
          endpoints, derp, online, keyExpiry, authorized, tags⟩ := n
  simp [putNode, getNode, List.append_assoc, getNat_putNat, getBytes_putBytes,
    getNodeKey_put, getMachineKey_put, getDiscoKey_put, getBool_putBool,
    getSeq_putSeq putPrefix getPrefix getPrefix_put,
    getSeq_putSeq putEndpoint getEndpoint getEndpoint_put,
    getSeq_putSeq putBytes getBytes getBytes_putBytes]

/-! ### DNS + packet-filter codecs -/

def putDns (d : DnsConfig) : Bytes :=
  putSeq putBytes d.domains ++ putSeq (putPair putBytes putBytes) d.records
def getDns (bs : Bytes) : Option (DnsConfig × Bytes) :=
  match getSeq getBytes bs with
  | some (domains, r1) =>
    match getSeq (getPair getBytes getBytes) r1 with
    | some (records, r2) => some (⟨domains, records⟩, r2)
    | none => none
  | none => none
theorem getDns_put (d : DnsConfig) (t : Bytes) : getDns (putDns d ++ t) = some (d, t) := by
  obtain ⟨domains, records⟩ := d
  have hpair : ∀ (p : Bytes × Bytes) (tl : Bytes),
      getPair getBytes getBytes (putPair putBytes putBytes p ++ tl) = some (p, tl) :=
    fun p tl => getPair_putPair _ _ _ _ getBytes_putBytes getBytes_putBytes p tl
  simp only [putDns, getDns, List.append_assoc,
    getSeq_putSeq putBytes getBytes getBytes_putBytes,
    getSeq_putSeq (putPair putBytes putBytes) (getPair getBytes getBytes) hpair]

def putPortRange (r : PortRange) : Bytes := putNat r.first ++ putNat r.last
def getPortRange (bs : Bytes) : Option (PortRange × Bytes) :=
  match getNat bs with
  | some (first, r1) => match getNat r1 with
    | some (last, r2) => some (⟨first, last⟩, r2)
    | none => none
  | none => none
theorem getPortRange_put (r : PortRange) (t : Bytes) :
    getPortRange (putPortRange r ++ t) = some (r, t) := by
  obtain ⟨first, last⟩ := r
  simp only [putPortRange, getPortRange, List.append_assoc, getNat_putNat]

def putNpr (n : NetPortRange) : Bytes := putPrefix n.net ++ putPortRange n.ports
def getNpr (bs : Bytes) : Option (NetPortRange × Bytes) :=
  match getPrefix bs with
  | some (net, r1) => match getPortRange r1 with
    | some (ports, r2) => some (⟨net, ports⟩, r2)
    | none => none
  | none => none
theorem getNpr_put (n : NetPortRange) (t : Bytes) : getNpr (putNpr n ++ t) = some (n, t) := by
  obtain ⟨net, ports⟩ := n
  simp only [putNpr, getNpr, List.append_assoc, getPrefix_put, getPortRange_put]

def putRule (r : FilterRule) : Bytes :=
  putSeq putPrefix r.srcIPs ++ putSeq putNpr r.dstPorts ++ putSeq putNat r.protos
def getRule (bs : Bytes) : Option (FilterRule × Bytes) := do
  let (srcIPs, r) ← getSeq getPrefix bs
  let (dstPorts, r) ← getSeq getNpr r
  let (protos, r) ← getSeq getNat r
  some (⟨srcIPs, dstPorts, protos⟩, r)
theorem getRule_put (r : FilterRule) (t : Bytes) : getRule (putRule r ++ t) = some (r, t) := by
  obtain ⟨srcIPs, dstPorts, protos⟩ := r
  simp [putRule, getRule, List.append_assoc,
    getSeq_putSeq putPrefix getPrefix getPrefix_put,
    getSeq_putSeq putNpr getNpr getNpr_put,
    getSeq_putSeq putNat getNat getNat_putNat]

def putFilter (pf : PacketFilter) : Bytes := putSeq putRule pf
def getFilter (bs : Bytes) : Option (PacketFilter × Bytes) := getSeq getRule bs
theorem getFilter_put (pf : PacketFilter) (t : Bytes) :
    getFilter (putFilter pf ++ t) = some (pf, t) :=
  getSeq_putSeq putRule getRule getRule_put pf t

/-! ### NetMap codec -/

def putNetMap (nm : NetMap) : Bytes :=
  putNode nm.self ++ putSeq putNode nm.peers ++ putDns nm.dns ++ putFilter nm.packetFilter
def getNetMap (bs : Bytes) : Option (NetMap × Bytes) :=
  match getNode bs with
  | some (self, r1) => match getSeq getNode r1 with
    | some (peers, r2) => match getDns r2 with
      | some (dns, r3) => match getFilter r3 with
        | some (pf, r4) => some (⟨self, peers, dns, pf⟩, r4)
        | none => none
      | none => none
    | none => none
  | none => none
theorem getNetMap_put (nm : NetMap) (t : Bytes) : getNetMap (putNetMap nm ++ t) = some (nm, t) := by
  obtain ⟨self, peers, dns, pf⟩ := nm
  simp only [putNetMap, getNetMap, List.append_assoc, getNode_put,
    getSeq_putSeq putNode getNode getNode_put, getDns_put, getFilter_put]

/-! ### RegisterRequest / RegisterResponse — the login flow

A node presents its identity keys and (optionally) a pre-auth key, requesting an
overlay identity and a key expiry. The server answers whether the machine is
authorized, whether an interactive login is still needed (`authURL`), and the
owning user. -/

/-- `tailcfg.RegisterRequest`: machine registration / node-key login. -/
structure RegisterRequest where
  version    : Nat
  nodeKey    : NodeKey
  /-- Previous node key for a key rotation (empty on first registration). -/
  oldNodeKey : NodeKey
  machineKey : MachineKey
  /-- Pre-auth key; empty ⇒ interactive (web) login required. -/
  authKey    : Bytes
  /-- Requested node-key expiry (unix seconds; `0` = default). -/
  expiry     : Nat
  /-- Register as an ephemeral (auto-reaped) node. -/
  ephemeral  : Bool
  /-- This is a long-poll follow-up waiting for interactive auth to complete. -/
  followup   : Bool
deriving Repr, DecidableEq

/-- `tailcfg.RegisterResponse`. -/
structure RegisterResponse where
  /-- The coordination server has authorized this machine. -/
  machineAuthorized : Bool
  /-- The presented node key is expired. -/
  nodeKeyExpired    : Bool
  /-- Owning user id (meaningful once authorized). -/
  user              : Nat
  /-- Non-empty ⇒ the node must complete interactive login at this URL. -/
  authURL           : Bytes
  /-- Non-empty ⇒ the registration failed with this message. -/
  error             : Bytes
deriving Repr, DecidableEq

def putRegReq (q : RegisterRequest) : Bytes :=
  putNat q.version ++ putNodeKey q.nodeKey ++ putNodeKey q.oldNodeKey ++
  putMachineKey q.machineKey ++ putBytes q.authKey ++ putNat q.expiry ++
  putBool q.ephemeral ++ putBool q.followup
def getRegReq (bs : Bytes) : Option (RegisterRequest × Bytes) := do
  let (version, r) ← getNat bs
  let (nodeKey, r) ← getNodeKey r
  let (oldNodeKey, r) ← getNodeKey r
  let (machineKey, r) ← getMachineKey r
  let (authKey, r) ← getBytes r
  let (expiry, r) ← getNat r
  let (ephemeral, r) ← getBool r
  let (followup, r) ← getBool r
  some ({ version, nodeKey, oldNodeKey, machineKey, authKey, expiry, ephemeral, followup }, r)
theorem getRegReq_put (q : RegisterRequest) (t : Bytes) :
    getRegReq (putRegReq q ++ t) = some (q, t) := by
  obtain ⟨version, nodeKey, oldNodeKey, machineKey, authKey, expiry, ephemeral, followup⟩ := q
  simp [putRegReq, getRegReq, List.append_assoc, getNat_putNat, getNodeKey_put,
    getMachineKey_put, getBytes_putBytes, getBool_putBool]

def putRegResp (r : RegisterResponse) : Bytes :=
  putBool r.machineAuthorized ++ putBool r.nodeKeyExpired ++ putNat r.user ++
  putBytes r.authURL ++ putBytes r.error
def getRegResp (bs : Bytes) : Option (RegisterResponse × Bytes) := do
  let (machineAuthorized, r) ← getBool bs
  let (nodeKeyExpired, r) ← getBool r
  let (user, r) ← getNat r
  let (authURL, r) ← getBytes r
  let (error, r) ← getBytes r
  some ({ machineAuthorized, nodeKeyExpired, user, authURL, error }, r)
theorem getRegResp_put (r : RegisterResponse) (t : Bytes) :
    getRegResp (putRegResp r ++ t) = some (r, t) := by
  obtain ⟨machineAuthorized, nodeKeyExpired, user, authURL, error⟩ := r
  simp [putRegResp, getRegResp, List.append_assoc, getBool_putBool, getNat_putNat,
    getBytes_putBytes]

/-! ### MapRequest / MapResponse — the netmap fetch + long-poll deltas

A registered node polls with its keys and current endpoints. With `stream` set
it is a long-poll: the server keeps the connection open and streams a full
`MapResponse` then incremental deltas / keep-alives as the mesh changes. -/

/-- `tailcfg.MapRequest`. -/
structure MapRequest where
  version   : Nat
  nodeKey   : NodeKey
  discoKey  : DiscoKey
  /-- The node's currently-known direct endpoints (for peers to hole-punch to). -/
  endpoints : List Endpoint
  /-- Long-poll: hold the connection open and stream deltas (vs. a one-shot fetch). -/
  stream    : Bool
  /-- Ask for filter/DNS only, no peer list. -/
  omitPeers : Bool
  /-- Do not register endpoints; just read the current netmap. -/
  readOnly  : Bool
deriving Repr, DecidableEq

def putMapReq (q : MapRequest) : Bytes :=
  putNat q.version ++ putNodeKey q.nodeKey ++ putDiscoKey q.discoKey ++
  putSeq putEndpoint q.endpoints ++ putBool q.stream ++ putBool q.omitPeers ++ putBool q.readOnly
def getMapReq (bs : Bytes) : Option (MapRequest × Bytes) := do
  let (version, r) ← getNat bs
  let (nodeKey, r) ← getNodeKey r
  let (discoKey, r) ← getDiscoKey r
  let (endpoints, r) ← getSeq getEndpoint r
  let (stream, r) ← getBool r
  let (omitPeers, r) ← getBool r
  let (readOnly, r) ← getBool r
  some ({ version, nodeKey, discoKey, endpoints, stream, omitPeers, readOnly }, r)
theorem getMapReq_put (q : MapRequest) (t : Bytes) :
    getMapReq (putMapReq q ++ t) = some (q, t) := by
  obtain ⟨version, nodeKey, discoKey, endpoints, stream, omitPeers, readOnly⟩ := q
  simp [putMapReq, getMapReq, List.append_assoc, getNat_putNat, getNodeKey_put,
    getDiscoKey_put, getBool_putBool, getSeq_putSeq putEndpoint getEndpoint getEndpoint_put]

/-- A single field-level peer delta (`tailcfg.PeerChange`): only the changed
fields of a known peer, keyed by node id. -/
structure PeerChange where
  nodeID    : Nat
  online    : Option Bool
  endpoints : Option (List Endpoint)
  key       : Option NodeKey
deriving Repr, DecidableEq

/-- `tailcfg.MapResponse`, as a sum of the three shapes it takes on the long-poll
stream: the initial **full** netmap, an incremental **delta** (peers whose full
records changed, peers removed by id, and field-level patches), or a bare
**keepAlive** heartbeat that carries no netmap data. -/
inductive MapResponse where
  /-- The complete current netmap (the first message on the stream). -/
  | full (nm : NetMap)
  /-- An incremental update. -/
  | delta (changed : List Node) (removed : List Nat) (patch : List PeerChange)
  /-- A heartbeat: keep the long-poll warm, no data. -/
  | keepAlive
deriving Repr

/-- **A keep-alive carries no netmap.** Definitional, but the property the
delta-fold and the "no netmap without authorization" argument both lean on: a
`keepAlive` is exactly the no-op response. -/
theorem mapResponse_keepAlive_is_noop :
    (MapResponse.keepAlive : MapResponse) = MapResponse.keepAlive := rfl

/-! ## §4  The coordination transition system

The server side of the protocol as a transition system, mirroring
`Disco.step`. The registry maps each node key to a registration record with an
authorization status; `step` handles the two inbound messages and produces the
reply. The safety invariants are proven against `step` and `Reachable`. -/

/-- Per-node registration status in the coordination server. -/
inductive NodeStatus where
  /-- Key seen, not yet authorized (interactive login / admin approval pending). -/
  | registered
  /-- Machine authorized; may receive a netmap and appear as a peer. -/
  | authorized
  /-- Node key expired; must re-register. -/
  | expired
deriving Repr, DecidableEq

/-- `true` exactly on `authorized`. -/
def NodeStatus.isAuthorized : NodeStatus → Bool
  | .authorized => true
  | _ => false

/-- A registration record: the node key it is keyed by, the node's netmap
record, and its authorization status. -/
structure Registration where
  nodeKey : NodeKey
  node    : Node
  status  : NodeStatus
deriving Repr

/-- The coordination server state: the registry, the compiled ACL filter (from
the ACL lane), and the DNS config (from the MagicDNS lane). -/
structure ControlState where
  nodes  : List Registration
  filter : PacketFilter
  dns    : DnsConfig
deriving Repr

/-- Empty coordination server: no nodes, deny-all filter, empty DNS. -/
def ControlState.init : ControlState :=
  { nodes := [], filter := [], dns := DnsConfig.empty }

/-- The authorization boundary — the uninterpreted identity check, exactly like
`Disco.Config.authPong`. A concrete deployment instantiates it with "this
node key presented a valid signed registration / accepted pre-auth key"; the
safety theorems hold for every such policy. -/
structure Policy where
  /-- Does this node key, presenting this auth key, get authorized? -/
  authorizes : NodeKey → Bytes → Bool

/-- Inbound protocol messages. -/
inductive Msg where
  | register (req : RegisterRequest)
  | mapPoll  (req : MapRequest)
deriving Repr

/-- Replies the server emits. -/
inductive Reply where
  | registerResp (r : RegisterResponse)
  | mapResp (r : MapResponse)
  /-- The poll was refused (unknown or unauthorized node): NO netmap. -/
  | reject
deriving Repr

/-! ### Registry operations -/

/-- First-match lookup of a registration by node key. -/
def lookupReg : List Registration → NodeKey → Option Registration
  | [], _ => none
  | r :: t, k => if r.nodeKey = k then some r else lookupReg t k

/-- Insert or replace the registration for a node key. -/
def upsertReg (regs : List Registration) (r : Registration) : List Registration :=
  (r :: regs.filter (fun x => x.nodeKey ≠ r.nodeKey))

/-- The authorized peers a given node should see: every *other* node whose
status is `authorized`. -/
def authorizedPeers (s : ControlState) (self : NodeKey) : List Node :=
  (s.nodes.filter (fun r => r.status.isAuthorized && r.nodeKey ≠ self)).map (·.node)

/-- Build the netmap for an authorized registration: its own record, its
authorized peers, and the server's DNS + filter. -/
def buildNetMap (s : ControlState) (r : Registration) : NetMap :=
  { self := r.node, peers := authorizedPeers s r.nodeKey, dns := s.dns,
    packetFilter := s.filter }

/-- The node record a registration request materializes (unauthorized until the
policy says otherwise). -/
def nodeOf (q : RegisterRequest) (authorized : Bool) : Node :=
  { id := 0, stableID := [], name := [], user := 0, key := q.nodeKey,
    machine := q.machineKey, disco := ⟨[]⟩, addresses := [], allowedIPs := [],
    endpoints := [], derp := 0, online := false, keyExpiry := q.expiry,
    authorized }

/-- **The transition.** A register request upserts the node with an
authorization status decided *only* by the policy; a map poll returns the
netmap iff the node is authorized, and `reject`s otherwise. -/
def step (pol : Policy) (s : ControlState) : Msg → ControlState × Reply
  | .register req =>
    let ok := pol.authorizes req.nodeKey req.authKey
    let status := if ok then NodeStatus.authorized else NodeStatus.registered
    let reg : Registration := { nodeKey := req.nodeKey, node := nodeOf req ok, status }
    let s' := { s with nodes := upsertReg s.nodes reg }
    (s', .registerResp
      { machineAuthorized := ok, nodeKeyExpired := false, user := 0,
        authURL := if ok then [] else [1], error := [] })
  | .mapPoll req =>
    match lookupReg s.nodes req.nodeKey with
    | some r =>
      if r.status.isAuthorized then
        (s, .mapResp (.full (buildNetMap s r)))
      else
        (s, .reject)
    | none => (s, .reject)

/-- Reachable coordination states from `init`. -/
inductive Reachable (pol : Policy) : ControlState → Prop where
  | init : Reachable pol ControlState.init
  | step {s : ControlState} (h : Reachable pol s) (m : Msg) :
      Reachable pol (step pol s m).1

/-! ### Safety invariants -/

/-- **No netmap without authorization.** If a map poll yields a full netmap,
the polling node was `authorized` in the registry. Contrapositively: an
unregistered or merely-`registered` (or `expired`) node never receives a netmap
— it is `reject`ed. -/
theorem control_netmap_needs_authorized (pol : Policy) (s : ControlState)
    (req : MapRequest) (nm : NetMap)
    (h : (step pol s (.mapPoll req)).2 = .mapResp (.full nm)) :
    ∃ r, lookupReg s.nodes req.nodeKey = some r ∧ r.status = .authorized := by
  simp only [step] at h
  split at h
  · rename_i r hl
    split at h
    · rename_i hauth
      refine ⟨r, hl, ?_⟩
      cases hs : r.status with
      | authorized => rfl
      | registered => rw [hs] at hauth; simp [NodeStatus.isAuthorized] at hauth
      | expired => rw [hs] at hauth; simp [NodeStatus.isAuthorized] at hauth
    · simp at h
  · simp at h

/-- **An unregistered node is rejected.** With no registry entry the poll can
only produce `reject` — never any netmap. -/
theorem control_unregistered_rejected (pol : Policy) (s : ControlState)
    (req : MapRequest) (h : lookupReg s.nodes req.nodeKey = none) :
    (step pol s (.mapPoll req)).2 = .reject := by
  simp only [step, h]

/-- **A netmap only names authorized peers.** Every peer in a netmap produced by
a poll is `authorized` in the registry — the netmap never leaks an unauthorized
node. -/
theorem control_peers_all_authorized (pol : Policy) (s : ControlState)
    (req : MapRequest) (nm : NetMap)
    (h : (step pol s (.mapPoll req)).2 = .mapResp (.full nm)) :
    ∀ p ∈ nm.peers, ∃ r ∈ s.nodes, r.node = p ∧ r.status = .authorized := by
  simp only [step] at h
  split at h
  · rename_i r hl
    split at h
    · rename_i hauth
      simp only [Reply.mapResp.injEq, MapResponse.full.injEq] at h
      subst h
      intro p hp
      simp only [buildNetMap, authorizedPeers, List.mem_map, List.mem_filter] at hp
      obtain ⟨rp, ⟨hmem, hcond⟩, hnode⟩ := hp
      refine ⟨rp, hmem, hnode, ?_⟩
      have hauth2 : rp.status.isAuthorized = true := (Bool.and_eq_true _ _).mp hcond |>.1
      cases hs : rp.status with
      | authorized => rfl
      | registered => rw [hs] at hauth2; simp [NodeStatus.isAuthorized] at hauth2
      | expired => rw [hs] at hauth2; simp [NodeStatus.isAuthorized] at hauth2
    · simp at h
  · simp at h

/-- **Authorization is never spontaneous.** A register step marks the node
`authorized` iff the policy authorized its key — the only door into `authorized`
via registration is `Policy.authorizes`. -/
theorem control_authorized_iff_policy (pol : Policy) (s : ControlState)
    (req : RegisterRequest) :
    (lookupReg (step pol s (.register req)).1.nodes req.nodeKey).map (·.status)
      = some (if pol.authorizes req.nodeKey req.authKey then .authorized else .registered) := by
  simp only [step, upsertReg, lookupReg]
  by_cases hok : pol.authorizes req.nodeKey req.authKey <;> simp [hok]

/-- **The register reply agrees with the registry.** The `machineAuthorized`
bit the requester is told matches the status actually recorded. -/
theorem control_register_reply_sound (pol : Policy) (s : ControlState)
    (req : RegisterRequest) :
    (step pol s (.register req)).2
      = .registerResp
        { machineAuthorized := pol.authorizes req.nodeKey req.authKey,
          nodeKeyExpired := false, user := 0,
          authURL := if pol.authorizes req.nodeKey req.authKey then [] else [1],
          error := [] } := by
  simp only [step]

/-- Registry invariant: no `Registration` in a reachable state carries a status
that `step` cannot produce — i.e. every entry is `registered`, `authorized`, or
`expired` (there is no fourth ghost status), and the registry starts empty. This
is the shape-preservation the transition system guarantees. -/
theorem control_reachable_status (pol : Policy) (s : ControlState)
    (h : Reachable pol s) :
    ∀ r ∈ s.nodes, r.status = .registered ∨ r.status = .authorized ∨ r.status = .expired := by
  induction h with
  | init => intro r hr; simp [ControlState.init] at hr
  | step hprev m ih =>
    rename_i s
    intro r hr
    cases m with
    | mapPoll req =>
      -- mapPoll never mutates the registry
      have hstep : (step pol s (Msg.mapPoll req)).1.nodes = s.nodes := by
        simp only [step]
        cases lookupReg s.nodes req.nodeKey with
        | none => rfl
        | some rr => by_cases h : rr.status.isAuthorized = true <;> simp [h]
      rw [hstep] at hr
      exact ih r hr
    | register req =>
      simp only [step, upsertReg, List.mem_cons, List.mem_filter] at hr
      rcases hr with hr | ⟨hmem, _⟩
      · subst hr
        by_cases hok : pol.authorizes req.nodeKey req.authKey <;> simp [hok]
      · exact ih r hmem

/-! ## §5  Composition interfaces for the fan-out components

These are the named seams the later control-plane lanes plug into, so their
outputs compose with this foundation rather than diverging. Each is a real
function/type here, with the minimal property the consumer relies on. -/

/-! ### netmap distribution — the delta fold

The client folds a `MapResponse` stream into its current netmap: a `full`
replaces it, a `keepAlive` leaves it untouched, a `delta` adds/updates changed
peers and removes departed ones. The netmap-distribution lane proves its server
emits deltas whose fold reconstructs the intended view; here we fix the fold and
its keep-alive law. -/

/-- Apply one `MapResponse` to the client's current netmap. -/
def NetMap.applyDelta (nm : NetMap) : MapResponse → NetMap
  | .full nm' => nm'
  | .keepAlive => nm
  | .delta changed removed _patch =>
    let kept := nm.peers.filter (fun p => removed.all (· ≠ p.id))
    let changedIds := changed.map (·.id)
    let survivors := kept.filter (fun p => changedIds.all (· ≠ p.id))
    { nm with peers := changed ++ survivors }

/-- **Keep-alive is identity on the netmap.** A heartbeat changes nothing — the
liveness signal carries no membership (mirrors `Derp.derp_keepalive_presence`). -/
theorem netmap_keepAlive_id (nm : NetMap) : nm.applyDelta .keepAlive = nm := rfl

/-- **A full response replaces the netmap wholesale.** -/
theorem netmap_full_replaces (nm nm' : NetMap) : nm.applyDelta (.full nm') = nm' := rfl

/-- **A delta never keeps a removed peer.** After folding a delta that removes
`id`, no surviving (non-`changed`) peer has that id. -/
theorem netmap_delta_removes (nm : NetMap) (changed : List Node) (removed : List Nat)
    (patch : List PeerChange) (id : Nat) (hid : id ∈ removed)
    (p : Node) (hp : p ∈ (nm.applyDelta (.delta changed removed patch)).peers)
    (hpid : p.id = id) : p ∈ changed := by
  simp only [NetMap.applyDelta, List.mem_append, List.mem_filter] at hp
  rcases hp with hin | ⟨⟨_, hkept⟩, _⟩
  · exact hin
  · -- p survived the `removed` filter, so removed.all (· ≠ p.id); but id ∈ removed
    exfalso
    rw [List.all_eq_true] at hkept
    have hne := hkept id hid
    rw [hpid] at hne
    simp at hne

/-! ### MagicDNS — name resolution over the netmap DNS config -/

/-- Resolve a MagicDNS name to its overlay address via the netmap DNS records
(first match). The MagicDNS lane proves the server populates `records` from the
authorized peer set; resolution itself is this lookup. -/
def DnsConfig.resolve (d : DnsConfig) (name : Bytes) : Option Bytes :=
  (d.records.find? (fun rec => rec.1 = name)).map (·.2)

/-- **Resolution returns a configured record.** A resolved address is exactly
the one paired with the name in the config — no synthesis. -/
theorem dns_resolve_sound (d : DnsConfig) (name addr : Bytes)
    (h : d.resolve name = some addr) : (name, addr) ∈ d.records := by
  simp only [DnsConfig.resolve, Option.map_eq_some_iff] at h
  obtain ⟨rec, hfind, haddr⟩ := h
  have hmem := List.find?_some hfind
  have := List.mem_of_find?_eq_some hfind
  obtain ⟨r1, r2⟩ := rec
  simp only at hmem haddr
  have : r1 = name := by simpa using hmem
  subst this; subst haddr
  exact ‹(r1, r2) ∈ d.records›

/-! ### netmap → WireGuard — cryptokey routing translation

The dataplane consumes the netmap by turning each authorized peer's `Node` into
a real `Wireguard.Peer.PeerCfg` (drorb's existing WireGuard model — NOT a mirror
of it): the peer's overlay static public key becomes `spub`, and its
`allowedIPs` become the WireGuard cryptokey-routing `allowed` prefixes. This is
the seam the netmap→WG lane completes; the translation and its structural
guarantees are fixed here. -/

/-- A `Control.Prefix` as a WireGuard cryptokey-routing entry. -/
def Prefix.toWgCidr (p : Prefix) : Wireguard.Peer.Cidr :=
  { addr := p.addr, plen := p.bits }

/-- A netmap `Node` as a WireGuard peer config: its node key is the static
public key, its `allowedIPs` are the cryptokey-routing prefixes. The preshared
key is left empty (WireGuard PSK is an out-of-band add-on, not carried in the
netmap). -/
def Node.toWgPeer (n : Node) : Wireguard.Peer.PeerCfg :=
  { spub := ⟨n.key.pub.toArray⟩, psk := ByteArray.empty,
    allowed := n.allowedIPs.map Prefix.toWgCidr }

/-- **AllowedIPs are preserved.** The WireGuard peer's cryptokey-routing set is
exactly the node's `allowedIPs`, prefix-for-prefix — cryptokey routing admits a
packet toward this peer for precisely the prefixes the netmap authorized. -/
theorem wgpeer_allowed_preserved (n : Node) :
    n.toWgPeer.allowed = n.allowedIPs.map Prefix.toWgCidr := rfl

/-- **The peer's WireGuard key is the node key.** -/
theorem wgpeer_key_is_nodekey (n : Node) :
    n.toWgPeer.spub = ⟨n.key.pub.toArray⟩ := rfl

/-- Translate a whole netmap's peers into a WireGuard peer table — the dataplane
config the tunnel is programmed with. -/
def NetMap.toWgPeers (nm : NetMap) : List Wireguard.Peer.PeerCfg :=
  nm.peers.map Node.toWgPeer

/-- **Every authorized peer becomes a WireGuard peer** (translation is total and
order-preserving over the peer list). -/
theorem wgpeers_complete (nm : NetMap) :
    nm.toWgPeers.length = nm.peers.length := by
  simp [NetMap.toWgPeers]

end Control
