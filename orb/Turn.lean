import Stun
/-!
# TURN — Traversal Using Relays around NAT (RFC 8656)

TURN is the relay extension of STUN (RFC 5389 / RFC 8489): when two peers cannot
reach each other directly, a client asks a TURN server to **allocate** a relayed
transport address, and the server forwards datagrams between the client and its
peers. TURN's whole security posture is a *default-deny relay*: the server relays
a datagram to a peer only if the client first installed a **permission** (or a
**channel binding**) for that peer. Without that discipline a TURN server is an
open reflector/amplifier.

This module extends the proven STUN codec in `Stun.lean` (message parse/build,
attribute TLVs, XOR-MAPPED-ADDRESS, HMAC-SHA1 MESSAGE-INTEGRITY) with:

1. **TURN messages** — the ALLOCATE / REFRESH / CREATE-PERMISSION / CHANNEL-BIND
   requests, the Send/Data indications, the ChannelData framing, and the TURN
   attributes (LIFETIME, XOR-RELAYED-ADDRESS, XOR-PEER-ADDRESS,
   REQUESTED-TRANSPORT, CHANNEL-NUMBER, DATA). Encode/decode round-trips proven.

2. **The allocation state machine** — a transition system over a set of
   allocations keyed by the client's 5-tuple. Each allocation carries the relayed
   transport address, an absolute lifetime, a set of permitted peer IPs, and a
   set of channel bindings. `allocate` / `refresh` / `createPermission` /
   `channelBind` are the client-driven transitions; `relayOutbound` /
   `relayInbound` / `channelSend` are the server's relay decisions.

3. **The security theorems** — `turn_relay_needs_permission` (a peer with no
   permission is never relayed — default-deny), `permission_needed_both_ways`
   (both directions default-deny), `turn_channel_binds_peer` (ChannelData on a
   channel number reaches exactly the bound peer), `turn_alloc_expires` (a
   past-lifetime allocation is gone), each with non-vacuous truth-table checks on
   real 5-tuples and peers.

4. **Message integrity** — TURN authenticates with the long-term credential
   (RFC 8489 §9.2): USERNAME / REALM / NONCE and a MESSAGE-INTEGRITY whose key is
   `MD5(username ":" realm ":" password)`. The HMAC-SHA1 signing/verification is
   exactly `Stun.withMessageIntegrity` / `Stun.messageIntegrityOk`; a signed
   Allocate request verifies by `Stun.messageIntegrity_roundtrip`. The MD5 key
   derivation itself is named as a follow-on (no MD5 in the crypto core yet).

Everything below reuses the `Stun` codec verbatim — no forked parser.
-/

namespace Turn

open Stun

/-! ## Message types (RFC 8656 §12, RFC 5389 §6)

A STUN 16-bit message type interleaves a 12-bit *method* with a 2-bit *class*
(request/indication/success/error) per RFC 5389 §6:

```
  0                 1
  2  3  4 5 6 7 8 9 0 1 2 3 4 5
 +--+--+-+-+-+-+-+-+-+-+-+-+-+-+
 |M |M |M|M|M|C|M|M|M|C|M|M|M|M|
 |11|10|9|8|7|1|6|5|4|0|3|2|1|0|
 +--+--+-+-+-+-+-+-+-+-+-+-+-+-+
```

`stunType` computes that interleaving arithmetically (no bit ops), and the
concrete method/class constants below are pinned to the RFC values by the
`stunType_*` theorems. -/

def clsRequest : Nat := 0
def clsIndication : Nat := 1
def clsSuccess : Nat := 2
def clsError : Nat := 3

def methodAllocate : Nat := 0x003
def methodRefresh : Nat := 0x004
def methodSend : Nat := 0x006
def methodData : Nat := 0x007
def methodCreatePermission : Nat := 0x008
def methodChannelBind : Nat := 0x009

/-- The RFC 5389 §6 type encoding: 5 method bits → type bits 13..9, 3 → 7..5,
4 → 3..0; class bit 1 → type bit 8, class bit 0 → type bit 4. -/
def stunType (method cls : Nat) : Nat :=
  (method / 128 % 32) * 512 + (method / 16 % 8) * 32 + (method % 16)
    + (cls / 2 % 2) * 256 + (cls % 2) * 16

def allocateRequest : Nat := 0x0003
def allocateSuccess : Nat := 0x0103
def allocateError : Nat := 0x0113
def refreshRequest : Nat := 0x0004
def refreshSuccess : Nat := 0x0104
def refreshError : Nat := 0x0114
def createPermissionRequest : Nat := 0x0008
def createPermissionSuccess : Nat := 0x0108
def createPermissionError : Nat := 0x0118
def channelBindRequest : Nat := 0x0009
def channelBindSuccess : Nat := 0x0109
def channelBindError : Nat := 0x0119
def sendIndication : Nat := 0x0016
def dataIndication : Nat := 0x0017

theorem stunType_allocate_request : stunType methodAllocate clsRequest = allocateRequest := by decide
theorem stunType_allocate_success : stunType methodAllocate clsSuccess = allocateSuccess := by decide
theorem stunType_allocate_error : stunType methodAllocate clsError = allocateError := by decide
theorem stunType_refresh_request : stunType methodRefresh clsRequest = refreshRequest := by decide
theorem stunType_create_permission_request :
    stunType methodCreatePermission clsRequest = createPermissionRequest := by decide
theorem stunType_channel_bind_request :
    stunType methodChannelBind clsRequest = channelBindRequest := by decide
theorem stunType_send_indication : stunType methodSend clsIndication = sendIndication := by decide
theorem stunType_data_indication : stunType methodData clsIndication = dataIndication := by decide

/-! ## TURN attributes (RFC 8656 §14) -/

def attrChannelNumber : Nat := 0x000C
def attrLifetime : Nat := 0x000D
def attrXorPeerAddress : Nat := 0x0012
def attrData : Nat := 0x0013
def attrXorRelayedAddress : Nat := 0x0016
def attrRequestedTransport : Nat := 0x0019
def attrDontFragment : Nat := 0x001A
def attrEvenPort : Nat := 0x0018
def attrRequestedAddressFamily : Nat := 0x0017
def attrReservationToken : Nat := 0x0022

/-- The IANA transport-protocol number carried by REQUESTED-TRANSPORT (§14.7).
TURN relays UDP (17). -/
def protoUDP : Nat := 17
def protoTCP : Nat := 6

/-- Valid channel-number range (§12): `0x4000 ≤ n ≤ 0x7FFF`. -/
def channelNumberValid (ch : Nat) : Bool := decide (0x4000 ≤ ch ∧ ch ≤ 0x7FFF)

/-! ### 32-bit big-endian codec (LIFETIME is a 4-byte unsigned) -/

def enc32 (n : Nat) : Bytes :=
  [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256), UInt8.ofNat n]

def be32 : Bytes → Nat
  | a :: b :: c :: d :: _ => a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat
  | _ => 0

theorem enc32_length (n : Nat) : (enc32 n).length = 4 := rfl

theorem be32_enc32 (n : Nat) (h : n < 4294967296) : be32 (enc32 n) = n := by
  simp only [enc32, be32, UInt8.toNat_ofNat']
  omega

/-! ### LIFETIME (§14.5) -/

def lifetimeAttr (secs : Nat) : Attr := { type := attrLifetime, value := enc32 secs }

def decodeLifetime (v : Bytes) : Option Nat :=
  if v.length = 4 then some (be32 v) else none

/-- **LIFETIME round-trip (§14.5).** -/
theorem lifetime_roundtrip (secs : Nat) (h : secs < 4294967296) :
    decodeLifetime (lifetimeAttr secs).value = some secs := by
  simp only [lifetimeAttr, decodeLifetime, enc32_length, if_pos]
  rw [be32_enc32 secs h]

/-! ### CHANNEL-NUMBER (§14.1): a 16-bit channel number + 16 bits RFFU (zero). -/

def channelNumberAttr (ch : Nat) : Attr :=
  { type := attrChannelNumber, value := enc16 ch ++ [0, 0] }

def decodeChannelNumber (v : Bytes) : Option Nat :=
  match v with
  | c1 :: c0 :: _ :: _ :: [] => some (be16 c1 c0)
  | _ => none

/-- **CHANNEL-NUMBER round-trip (§14.1).** -/
theorem channelNumber_roundtrip (ch : Nat) (h : ch < 65536) :
    decodeChannelNumber (channelNumberAttr ch).value = some ch := by
  have hv : (channelNumberAttr ch).value
      = [UInt8.ofNat (ch / 256), UInt8.ofNat (ch % 256), 0, 0] := by
    simp [channelNumberAttr, enc16]
  rw [hv]
  simp only [decodeChannelNumber]
  rw [be16_enc16 ch h]

/-! ### REQUESTED-TRANSPORT (§14.7): 1 protocol byte + 3 reserved. -/

def requestedTransportAttr (proto : Nat) : Attr :=
  { type := attrRequestedTransport, value := [UInt8.ofNat proto, 0, 0, 0] }

def decodeRequestedTransport (v : Bytes) : Option Nat :=
  match v with
  | p :: _ :: _ :: _ :: [] => some p.toNat
  | _ => none

/-- **REQUESTED-TRANSPORT round-trip (§14.7).** -/
theorem requestedTransport_roundtrip (proto : Nat) (h : proto < 256) :
    decodeRequestedTransport (requestedTransportAttr proto).value = some proto := by
  simp only [requestedTransportAttr, decodeRequestedTransport, UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt h]

/-! ### XOR-PEER-ADDRESS / XOR-RELAYED-ADDRESS (§14.3, §14.6)

Both reuse the STUN XOR-MAPPED-ADDRESS wire form verbatim, so their round-trip
is exactly `Stun.xorMapped_roundtrip`. -/

def xorPeerAttr (txid : Bytes) (ep : Endpoint) : Attr :=
  { type := attrXorPeerAddress, value := xorMappedValue txid ep }

def xorRelayedAttr (txid : Bytes) (ep : Endpoint) : Attr :=
  { type := attrXorRelayedAddress, value := xorMappedValue txid ep }

/-- **XOR-PEER-ADDRESS round-trip (§14.3).** -/
theorem xorPeer_roundtrip (txid : Bytes) (ep : Endpoint)
    (htx : txid.length = 12) (hport : ep.port < 65536)
    (hfam : (ep.family = 1 ∧ ep.addr.length = 4) ∨ (ep.family = 2 ∧ ep.addr.length = 16)) :
    decodeXorMapped txid (xorPeerAttr txid ep).value = some ep :=
  xorMapped_roundtrip txid ep htx hport hfam

/-- **XOR-RELAYED-ADDRESS round-trip (§14.6).** -/
theorem xorRelayed_roundtrip (txid : Bytes) (ep : Endpoint)
    (htx : txid.length = 12) (hport : ep.port < 65536)
    (hfam : (ep.family = 1 ∧ ep.addr.length = 4) ∨ (ep.family = 2 ∧ ep.addr.length = 16)) :
    decodeXorMapped txid (xorRelayedAttr txid ep).value = some ep :=
  xorMapped_roundtrip txid ep htx hport hfam

/-! ### DATA (§14.4): the opaque application payload. -/

def dataAttr (payload : Bytes) : Attr := { type := attrData, value := payload }

/-! ## TURN messages (reusing `Stun.encode`) -/

/-- Allocate request (§7.1): REQUESTED-TRANSPORT then LIFETIME. -/
def allocateRequestMsg (txid : Bytes) (proto lifetime : Nat) : Bytes :=
  Stun.encode allocateRequest txid [requestedTransportAttr proto, lifetimeAttr lifetime]

/-- Allocate success (§7.3): XOR-RELAYED-ADDRESS and the granted LIFETIME. -/
def allocateSuccessMsg (txid : Bytes) (relayed : Endpoint) (lifetime : Nat) : Bytes :=
  Stun.encode allocateSuccess txid [xorRelayedAttr txid relayed, lifetimeAttr lifetime]

/-- Refresh request (§8): the requested LIFETIME (0 tears the allocation down). -/
def refreshRequestMsg (txid : Bytes) (lifetime : Nat) : Bytes :=
  Stun.encode refreshRequest txid [lifetimeAttr lifetime]

/-- CreatePermission request (§9.1): one XOR-PEER-ADDRESS per peer to permit. -/
def createPermissionRequestMsg (txid : Bytes) (peers : List Endpoint) : Bytes :=
  Stun.encode createPermissionRequest txid (peers.map (xorPeerAttr txid))

/-- ChannelBind request (§11.1): CHANNEL-NUMBER and XOR-PEER-ADDRESS. -/
def channelBindRequestMsg (txid : Bytes) (ch : Nat) (peer : Endpoint) : Bytes :=
  Stun.encode channelBindRequest txid [channelNumberAttr ch, xorPeerAttr txid peer]

/-- Send indication (§10.1): client → server, carrying XOR-PEER-ADDRESS + DATA. -/
def sendIndicationMsg (txid : Bytes) (peer : Endpoint) (payload : Bytes) : Bytes :=
  Stun.encode sendIndication txid [xorPeerAttr txid peer, dataAttr payload]

/-- Data indication (§10.2): server → client, carrying XOR-PEER-ADDRESS + DATA. -/
def dataIndicationMsg (txid : Bytes) (peer : Endpoint) (payload : Bytes) : Bytes :=
  Stun.encode dataIndication txid [xorPeerAttr txid peer, dataAttr payload]

/-- **Allocate-request round-trip (§7.1).** The fixed-size REQUESTED-TRANSPORT +
LIFETIME body parses back to exactly the emitted attributes. -/
theorem allocate_request_roundtrip (txid : Bytes) (proto lifetime : Nat) (htx : txid.length = 12) :
    Stun.parse (allocateRequestMsg txid proto lifetime) =
      some { typ := allocateRequest, length := 16, txid := txid,
             attrs := [requestedTransportAttr proto, lifetimeAttr lifetime] } := by
  have hwf : ∀ a ∈ [requestedTransportAttr proto, lifetimeAttr lifetime],
      a.type < 65536 ∧ a.value.length < 65536 := by
    intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with h | h <;> subst h <;>
      refine ⟨?_, ?_⟩ <;>
      simp [requestedTransportAttr, lifetimeAttr, attrRequestedTransport, attrLifetime, enc32]
  have hlen : (encodeAttrs [requestedTransportAttr proto, lifetimeAttr lifetime]).length = 16 := by
    simp [encodeAttrs, encodeAttr, requestedTransportAttr, lifetimeAttr, enc16, enc32, padLen]
  have h := parse_encode allocateRequest txid [requestedTransportAttr proto, lifetimeAttr lifetime]
    (by decide) htx (by rw [hlen]; decide) hwf
  rw [allocateRequestMsg, h, hlen]

/-- **Refresh-request round-trip (§8).** -/
theorem refresh_request_roundtrip (txid : Bytes) (lifetime : Nat) (htx : txid.length = 12) :
    Stun.parse (refreshRequestMsg txid lifetime) =
      some { typ := refreshRequest, length := 8, txid := txid,
             attrs := [lifetimeAttr lifetime] } := by
  have hwf : ∀ a ∈ [lifetimeAttr lifetime], a.type < 65536 ∧ a.value.length < 65536 := by
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha; refine ⟨?_, ?_⟩ <;> simp [lifetimeAttr, attrLifetime, enc32]
  have hlen : (encodeAttrs [lifetimeAttr lifetime]).length = 8 := by
    simp [encodeAttrs, encodeAttr, lifetimeAttr, enc16, enc32, padLen]
  have h := parse_encode refreshRequest txid [lifetimeAttr lifetime]
    (by decide) htx (by rw [hlen]; decide) hwf
  rw [refreshRequestMsg, h, hlen]

/-! ## ChannelData framing (RFC 8656 §12.4)

A ChannelData message is **not** a STUN message: a 16-bit channel number, a
16-bit length, the application data, padded to a 4-byte boundary. The high two
bits of the first byte (`0b01`) distinguish it from STUN (`0b00`) on a shared
socket. -/

def channelData (ch : Nat) (payload : Bytes) : Bytes :=
  enc16 ch ++ enc16 payload.length ++ payload ++ zeros (padLen payload.length)

def decodeChannelData (b : Bytes) : Option (Nat × Bytes) :=
  match b with
  | c1 :: c0 :: l1 :: l0 :: rest =>
    let len := be16 l1 l0
    if len ≤ rest.length then some (be16 c1 c0, rest.take len) else none
  | _ => none

/-- **ChannelData round-trip (§12.4).** -/
theorem channelData_roundtrip (ch : Nat) (payload : Bytes)
    (hch : ch < 65536) (hlen : payload.length < 65536) :
    decodeChannelData (channelData ch payload) = some (ch, payload) := by
  have hshape : channelData ch payload =
      UInt8.ofNat (ch / 256) :: UInt8.ofNat (ch % 256) ::
      UInt8.ofNat (payload.length / 256) :: UInt8.ofNat (payload.length % 256) ::
      (payload ++ zeros (padLen payload.length)) := by
    simp [channelData, enc16, List.append_assoc]
  rw [hshape]
  simp only [decodeChannelData]
  rw [be16_enc16 ch hch, be16_enc16 payload.length hlen]
  have hle : payload.length ≤ (payload ++ zeros (padLen payload.length)).length := by
    simp [List.length_append]
  rw [if_pos hle]
  have htk : (payload ++ zeros (padLen payload.length)).take payload.length = payload :=
    List.take_left' rfl
  rw [htk]

/-- A ChannelData frame is recognised on a shared socket by its top two bits
(§12.4): the first byte lies in `0x40..0x7F` for a valid channel number. -/
def isChannelData (b : Bytes) : Bool :=
  match b with
  | c1 :: _ => decide (0x40 ≤ c1.toNat ∧ c1.toNat ≤ 0x7F)
  | _ => false

/-! ## The allocation state machine (RFC 8656 §2.2, §6–§11)

The server's view: a set of **allocations** keyed by the client's 5-tuple
(client transport address, server transport address, transport protocol). Each
allocation holds the relayed transport address it handed the client, an absolute
expiry time, the set of permitted peer **IP addresses** (§9 permissions are
per-IP), and the channel bindings (§12, a channel number bound to a full peer
transport address). -/

/-- The 5-tuple that identifies an allocation (§2.2). -/
structure FiveTuple where
  client : Endpoint
  server : Endpoint
  proto : Nat
deriving Repr, DecidableEq

/-- A single allocation's server-side state. -/
structure Allocation where
  /-- The relayed transport address handed to the client (§6.2). -/
  relayed : Endpoint
  /-- Absolute time the allocation expires (§6.2, refreshed by §8). -/
  expiry : Nat
  /-- Permitted peer IP addresses (§9). -/
  perms : List Bytes
  /-- Channel bindings: channel number → peer transport address (§12). -/
  channels : List (Nat × Endpoint)
deriving Repr, DecidableEq

/-- The server's whole relay state: an allocation map keyed by 5-tuple. -/
structure TurnState where
  allocs : List (FiveTuple × Allocation)
deriving Repr

def TurnState.empty : TurnState := { allocs := [] }

def TurnState.lookup (s : TurnState) (ft : FiveTuple) : Option Allocation :=
  (s.allocs.find? (fun p => decide (p.1 = ft))).map (·.2)

def TurnState.insert (s : TurnState) (ft : FiveTuple) (a : Allocation) : TurnState :=
  { allocs := (ft, a) :: s.allocs.filter (fun p => decide (p.1 ≠ ft)) }

def TurnState.remove (s : TurnState) (ft : FiveTuple) : TurnState :=
  { allocs := s.allocs.filter (fun p => decide (p.1 ≠ ft)) }

/-- Looking up a 5-tuple right after inserting it returns the inserted
allocation (the fresh binding shadows any prior one). -/
theorem lookup_insert (s : TurnState) (ft : FiveTuple) (a : Allocation) :
    (s.insert ft a).lookup ft = some a := by
  simp [TurnState.insert, TurnState.lookup, List.find?_cons]

/-! ### Predicates -/

/-- Whether an allocation permits a given peer **IP** (§9). -/
def hasPermission (a : Allocation) (peerIP : Bytes) : Bool := a.perms.contains peerIP

/-- The peer bound to a channel number, if any (§12). -/
def channelPeer (a : Allocation) (ch : Nat) : Option Endpoint :=
  (a.channels.find? (fun p => decide (p.1 = ch))).map (·.2)

/-- The channel number bound to a peer, if any (§12). -/
def channelForPeer (a : Allocation) (peer : Endpoint) : Option Nat :=
  (a.channels.find? (fun p => decide (p.2 = peer))).map (·.1)

/-! ### Transitions (client-driven) -/

/-- **Allocate (§6.2).** Create an allocation with a relayed address and a
lifetime; it starts with no permissions and no channels (default-deny). -/
def allocate (s : TurnState) (ft : FiveTuple) (relayed : Endpoint) (now lifetime : Nat) :
    TurnState :=
  s.insert ft { relayed := relayed, expiry := now + lifetime, perms := [], channels := [] }

/-- **Refresh (§8).** A positive lifetime extends the allocation; a zero
lifetime deletes it. A refresh of a non-existent allocation is a no-op. -/
def refresh (s : TurnState) (ft : FiveTuple) (now lifetime : Nat) : TurnState :=
  match s.lookup ft with
  | none => s
  | some a => if lifetime = 0 then s.remove ft else s.insert ft { a with expiry := now + lifetime }

/-- **CreatePermission (§9).** Install a permission for a peer IP (idempotent).
No allocation ⇒ no-op. -/
def createPermission (s : TurnState) (ft : FiveTuple) (peerIP : Bytes) : TurnState :=
  match s.lookup ft with
  | none => s
  | some a =>
    s.insert ft { a with perms := if a.perms.contains peerIP then a.perms else peerIP :: a.perms }

/-- **ChannelBind (§11).** Bind a channel number to a peer, replacing any prior
binding of that channel or that peer, and (per §11.9) install a permission for
the peer's IP. No allocation ⇒ no-op. -/
def channelBind (s : TurnState) (ft : FiveTuple) (ch : Nat) (peer : Endpoint) : TurnState :=
  match s.lookup ft with
  | none => s
  | some a =>
    s.insert ft
      { a with
        perms := if a.perms.contains peer.addr then a.perms else peer.addr :: a.perms,
        channels := (ch, peer) ::
          a.channels.filter (fun p => decide (p.1 ≠ ch) && decide (p.2 ≠ peer)) }

/-- An allocation is *live* at `now` only while it has not expired (§6.2). -/
def active (s : TurnState) (ft : FiveTuple) (now : Nat) : Option Allocation :=
  match s.lookup ft with
  | none => none
  | some a => if decide (now < a.expiry) then some a else none

/-! ### Relay decisions (server-driven) — the default-deny core -/

/-- **Outbound relay (client → peer), §10.1 / §12.** A Send indication or
ChannelData from the client is forwarded to the peer *only if* the allocation is
live and a permission exists for the peer's IP. Otherwise the datagram is
dropped. Returns the `(destination peer, payload)` to emit from the relayed
address, or `none` on a drop. -/
def relayOutbound (s : TurnState) (ft : FiveTuple) (peer : Endpoint) (payload : Bytes)
    (now : Nat) : Option (Endpoint × Bytes) :=
  match s.lookup ft with
  | none => none
  | some a =>
    if decide (now < a.expiry) && hasPermission a peer.addr then some (peer, payload) else none

/-- The classification of an inbound datagram (peer → client), §10.2 / §12. -/
inductive Inbound
  /-- Dropped: no live allocation, or no permission/channel for the peer. -/
  | drop
  /-- Delivered to the client as a Data indication carrying the peer address. -/
  | dataInd (peer : Endpoint) (payload : Bytes)
  /-- Delivered to the client as ChannelData on the bound channel. -/
  | channelData (ch : Nat) (payload : Bytes)
deriving Repr, DecidableEq

/-- **Inbound relay (peer → client), §10.2 / §12.** A datagram received on the
relayed address from a peer is relayed to the client *only if* the allocation is
live and the peer has a channel binding (→ ChannelData) or a permission
(→ Data indication). Otherwise it is dropped. -/
def relayInbound (s : TurnState) (ft : FiveTuple) (peer : Endpoint) (payload : Bytes)
    (now : Nat) : Inbound :=
  match s.lookup ft with
  | none => .drop
  | some a =>
    if decide (now < a.expiry) then
      match channelForPeer a peer with
      | some ch => .channelData ch payload
      | none => if hasPermission a peer.addr then .dataInd peer payload else .drop
    else .drop

/-- **Channel send (§12).** A ChannelData frame from the client is relayed to
the peer bound to its channel number, if the allocation is live. -/
def channelSend (s : TurnState) (ft : FiveTuple) (frame : Bytes) (now : Nat) :
    Option (Endpoint × Bytes) :=
  match decodeChannelData frame with
  | none => none
  | some (ch, payload) =>
    match s.lookup ft with
    | none => none
    | some a =>
      if decide (now < a.expiry) then
        match channelPeer a ch with
        | some peer => some (peer, payload)
        | none => none
      else none

/-! ## Security theorems -/

/-- **`turn_relay_needs_permission` — default-deny (§9, §10).** An outbound
datagram to a peer for which no permission exists is never relayed. This is the
core anti-reflector discipline: a fresh allocation relays to no one. -/
theorem turn_relay_needs_permission (s : TurnState) (ft : FiveTuple) (a : Allocation)
    (peer : Endpoint) (payload : Bytes) (now : Nat)
    (hlook : s.lookup ft = some a) (hperm : hasPermission a peer.addr = false) :
    relayOutbound s ft peer payload now = none := by
  simp [relayOutbound, hlook, hperm]

/-- **`permission_needed_both_ways` (§9, §10).** With neither a permission nor a
channel for the peer, the datagram is dropped in *both* directions. -/
theorem permission_needed_both_ways (s : TurnState) (ft : FiveTuple) (a : Allocation)
    (peer : Endpoint) (payload : Bytes) (now : Nat)
    (hlook : s.lookup ft = some a) (hperm : hasPermission a peer.addr = false)
    (hchan : channelForPeer a peer = none) :
    relayOutbound s ft peer payload now = none ∧
      relayInbound s ft peer payload now = Inbound.drop := by
  refine ⟨turn_relay_needs_permission s ft a peer payload now hlook hperm, ?_⟩
  simp [relayInbound, hlook, hchan, hperm]

/-- **`turn_alloc_expires` (§6.2).** A past-lifetime allocation is gone: it is not
live, and both relay directions deny. -/
theorem turn_alloc_expires (s : TurnState) (ft : FiveTuple) (a : Allocation)
    (peer : Endpoint) (payload : Bytes) (now : Nat)
    (hlook : s.lookup ft = some a) (hexp : a.expiry ≤ now) :
    active s ft now = none ∧
      relayOutbound s ft peer payload now = none ∧
      relayInbound s ft peer payload now = Inbound.drop := by
  have hd : decide (now < a.expiry) = false := by
    rw [decide_eq_false_iff_not]; omega
  refine ⟨?_, ?_, ?_⟩
  · simp [active, hlook, hd]
  · simp [relayOutbound, hlook, hd]
  · simp [relayInbound, hlook, hd]

/-- **`turn_channel_binds_peer` (§11, §12).** After binding channel `ch` to
`peer`, that channel resolves to exactly `peer`, and a ChannelData frame on `ch`
is relayed to `peer` (while the allocation is live). ChannelData on channel N
goes to exactly the bound peer. -/
theorem turn_channel_binds_peer (s : TurnState) (ft : FiveTuple) (a : Allocation)
    (ch : Nat) (peer : Endpoint) (hlook : s.lookup ft = some a) :
    ∃ a', (channelBind s ft ch peer).lookup ft = some a' ∧ channelPeer a' ch = some peer := by
  refine ⟨{ a with
      perms := if a.perms.contains peer.addr then a.perms else peer.addr :: a.perms,
      channels := (ch, peer) ::
        a.channels.filter (fun p => decide (p.1 ≠ ch) && decide (p.2 ≠ peer)) }, ?_, ?_⟩
  · simp only [channelBind, hlook]; exact lookup_insert _ _ _
  · simp [channelPeer, List.find?_cons]

/-- After ChannelBind, a permission for the peer's IP is installed (§11.9): a
channel binding implies a permission. -/
theorem channelBind_installs_permission (s : TurnState) (ft : FiveTuple) (a : Allocation)
    (ch : Nat) (peer : Endpoint) (hlook : s.lookup ft = some a) :
    ∃ a', (channelBind s ft ch peer).lookup ft = some a' ∧ hasPermission a' peer.addr = true := by
  refine ⟨{ a with
      perms := if a.perms.contains peer.addr then a.perms else peer.addr :: a.perms,
      channels := (ch, peer) ::
        a.channels.filter (fun p => decide (p.1 ≠ ch) && decide (p.2 ≠ peer)) }, ?_, ?_⟩
  · simp only [channelBind, hlook]; exact lookup_insert _ _ _
  · simp only [hasPermission]
    by_cases hc : a.perms.contains peer.addr = true
    · rw [if_pos hc]; exact hc
    · rw [if_neg hc]; simp [List.contains_cons]

/-- **CreatePermission grants relay (§9).** After a permission is installed for a
peer IP, that peer is permitted — the positive counterpart of default-deny that
shows the discipline is not vacuously always-deny. -/
theorem createPermission_grants (s : TurnState) (ft : FiveTuple) (a : Allocation)
    (peerIP : Bytes) (hlook : s.lookup ft = some a) :
    ∃ a', (createPermission s ft peerIP).lookup ft = some a' ∧ hasPermission a' peerIP = true := by
  refine ⟨{ a with perms := if a.perms.contains peerIP then a.perms else peerIP :: a.perms }, ?_, ?_⟩
  · simp only [createPermission, hlook]; exact lookup_insert _ _ _
  · simp only [hasPermission]
    by_cases hc : a.perms.contains peerIP = true
    · rw [if_pos hc]; exact hc
    · rw [if_neg hc]; simp [List.contains_cons]

/-- **Channel frame routes to the bound peer (§12).** A ChannelData frame on a
bound channel is relayed to exactly that peer while the allocation is live. -/
theorem channelSend_channelData (s : TurnState) (ft : FiveTuple) (a : Allocation)
    (ch : Nat) (peer : Endpoint) (payload : Bytes) (now : Nat)
    (hlook : s.lookup ft = some a) (hactive : now < a.expiry)
    (hbound : channelPeer a ch = some peer)
    (hch : ch < 65536) (hlen : payload.length < 65536) :
    channelSend s ft (channelData ch payload) now = some (peer, payload) := by
  simp only [channelSend, channelData_roundtrip ch payload hch hlen, hlook,
    decide_eq_true hactive, Bool.true_and, if_true, hbound]

/-! ## Message integrity (RFC 8489 §9.2, long-term credential)

A TURN request authenticates with USERNAME / REALM / NONCE and a
MESSAGE-INTEGRITY whose HMAC-SHA1 key is the long-term credential
`MD5(username ":" realm ":" password)`. The HMAC signing and verification are
exactly the STUN primitives; a signed Allocate request verifies with the same
key. The MD5 key derivation is a **follow-on** (no MD5 in the crypto core yet):
here `key` is the derived long-term key, supplied by the caller. -/

/-- An Allocate request signed with a long-term-credential key (§7.1, §9.2). -/
def signedAllocateRequest (key txid : Bytes) (proto lifetime : Nat) : Bytes :=
  Stun.withMessageIntegrity key allocateRequest txid
    [requestedTransportAttr proto, lifetimeAttr lifetime]

/-- **TURN auth round-trip (§9.2).** A signed Allocate request verifies under the
same long-term key — a statement about the real HMAC-SHA1 computation. -/
theorem signedAllocate_integrity (key txid : Bytes) (proto lifetime : Nat) (htx : txid.length = 12) :
    Stun.messageIntegrityOk key (signedAllocateRequest key txid proto lifetime) = true := by
  have hwf : ∀ a ∈ [requestedTransportAttr proto, lifetimeAttr lifetime],
      a.type < 65536 ∧ a.value.length < 65536 := by
    intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with h | h <;> subst h <;>
      refine ⟨?_, ?_⟩ <;>
      simp [requestedTransportAttr, lifetimeAttr, attrRequestedTransport, attrLifetime, enc32]
  have hno : ∀ a ∈ [requestedTransportAttr proto, lifetimeAttr lifetime],
      a.type ≠ Stun.attrMessageIntegrity := by
    intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with h | h <;> subst h <;>
      simp [requestedTransportAttr, lifetimeAttr, attrRequestedTransport, attrLifetime,
        Stun.attrMessageIntegrity]
  have hlen : (encodeAttrs [requestedTransportAttr proto, lifetimeAttr lifetime]).length = 16 := by
    simp [encodeAttrs, encodeAttr, requestedTransportAttr, lifetimeAttr, enc16, enc32, padLen]
  exact Stun.messageIntegrity_roundtrip key allocateRequest txid
    [requestedTransportAttr proto, lifetimeAttr lifetime]
    (by decide) htx (by rw [hlen]; decide) hwf hno

/-! ## Non-vacuous truth tables on real 5-tuples and peers

A concrete allocation: a client behind a NAT, a TURN server, a relayed address,
and two peers. The client permits only peer A. These `by decide` checks evaluate
the real transition system on real byte-level addresses. -/

def epClient : Endpoint := { family := 1, port := 51000, addr := [10, 0, 0, 1] }
def epServer : Endpoint := { family := 1, port := 3478, addr := [10, 0, 0, 254] }
def epRelay : Endpoint := { family := 1, port := 49152, addr := [203, 0, 113, 7] }
def epPeerA : Endpoint := { family := 1, port := 6000, addr := [198, 51, 100, 20] }
def epPeerB : Endpoint := { family := 1, port := 7000, addr := [198, 51, 100, 99] }
def ft0 : FiveTuple := { client := epClient, server := epServer, proto := protoUDP }
def samplePayload : Bytes := [0xDE, 0xAD, 0xBE, 0xEF]

/-- Allocate at t=0 for 600 s, then permit only peer A. -/
def stAllocated : TurnState := allocate TurnState.empty ft0 epRelay 0 600
def stPermitted : TurnState := createPermission stAllocated ft0 epPeerA.addr

-- Permitted peer A is relayed; unpermitted peer B is dropped (default-deny).
example : relayOutbound stPermitted ft0 epPeerA samplePayload 5 = some (epPeerA, samplePayload) := by
  decide
example : relayOutbound stPermitted ft0 epPeerB samplePayload 5 = none := by decide
example : relayInbound stPermitted ft0 epPeerA samplePayload 5
    = Inbound.dataInd epPeerA samplePayload := by decide
example : relayInbound stPermitted ft0 epPeerB samplePayload 5 = Inbound.drop := by decide

-- A fresh allocation (no permission yet) relays to no one.
example : relayOutbound stAllocated ft0 epPeerA samplePayload 5 = none := by decide
example : relayInbound stAllocated ft0 epPeerA samplePayload 5 = Inbound.drop := by decide

-- Past the 600 s lifetime, the allocation is gone and everything denies.
example : active stPermitted ft0 700 = none := by decide
example : relayOutbound stPermitted ft0 epPeerA samplePayload 700 = none := by decide
example : relayInbound stPermitted ft0 epPeerA samplePayload 700 = Inbound.drop := by decide

/-- Bind channel 0x4001 to peer B (which also installs a permission). -/
def stBound : TurnState := channelBind stPermitted ft0 0x4001 epPeerB

-- Now peer B is reachable inbound via its channel, and a ChannelData frame on
-- 0x4001 routes to exactly peer B.
example : relayInbound stBound ft0 epPeerB samplePayload 5
    = Inbound.channelData 0x4001 samplePayload := by decide
example : channelSend stBound ft0 (channelData 0x4001 samplePayload) 5
    = some (epPeerB, samplePayload) := by decide
-- Peer A still reaches the client via its (data-indication) permission.
example : relayInbound stBound ft0 epPeerA samplePayload 5
    = Inbound.dataInd epPeerA samplePayload := by decide

-- A zero-lifetime Refresh tears the allocation down.
example : active (refresh stPermitted ft0 5 0) ft0 5 = none := by decide
-- A positive Refresh extends the lifetime past the original expiry.
example : active (refresh stPermitted ft0 500 600) ft0 700 = some
    { relayed := epRelay, expiry := 1100, perms := [epPeerA.addr], channels := [] } := by decide

def version : String := "0.1.0"

end Turn
