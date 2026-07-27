import Derp.Relay
/-!
# DERP mesh — presence gossip and cross-relay forwarding, proven

`Derp.Relay` proves the *single* relay: a routing table (`peerKey → connection`)
and the blind peer-to-peer forward, with the forwarding discipline
(`forward_to_addressed_only`, `relay_blind`) closed. That relay can only reach a
destination connected to *itself*.

A production DERP deployment runs a **mesh** of relays. A client connected to
relay `R1` must still be able to reach a peer connected to a *different* relay
`R2`. The relays make this work by gossiping presence: when a peer `B` connects
to `R2`, `R2` announces `PeerPresent(B)` to its mesh siblings, who record
`B → R2` in a mesh map. When `A` (on `R1`) sends a packet addressed to `B`, `R1`
finds `B`'s home relay `R2` in that map and forwards the packet to `R2` over the
mesh link (a `ForwardPacket` frame carrying `srcKey ‖ dstKey ‖ packet`); `R2`
then delivers it to `B`'s local connection as an ordinary `RecvPacket`. When `B`
departs, `R2` gossips `PeerGone(B)` and the siblings drop the `B → R2` entry.
This is the public Tailscale-style DERP mesh: `WatchConns` subscribes a sibling
to presence, `PeerPresent`/`PeerGone` carry the deltas.

This module **composes** the single-relay theorems across the two hops — it does
not modify `Derp.Relay`. The mesh forward reuses the relay's `connOf` routing
decision on the destination relay, so the second hop delivers by exactly the same
`forward_to_addressed_only` discipline the single relay already proves.

## The state

* `MeshState` — a set of relays (each a `Derp.Relay.RelayState`, indexed by a
  `RelayId`) plus the gossip map `home : peerKey → RelayId` (which relay currently
  hosts a peer, learned via `PeerPresent` / `PeerGone`).

## The gossip operations

* `connect r k c` — peer `k` connects to relay `r` on connection `c`: register
  `k → c` in `r`'s local table (the real login) *and* record `home[k] = r` (the
  `PeerPresent` gossip the siblings apply). `disconnect r k` is the mirror: drop
  the local binding and clear `home[k]` (the `PeerGone` gossip).

## The forward

* `MeshState.forward srcRelay srcConn dstKey packet` — a `SendPacket` for `dstKey`
  arriving on `srcConn` at `srcRelay`. If `dstKey` is local to `srcRelay`, deliver
  there (single-relay hop, reusing `RelayState.forward`). Otherwise look up
  `home[dstKey] = r2`, and deliver on `r2` to `dstKey`'s local connection — the
  mesh hop. Either way at most one delivery, to the addressed peer only.

## The proven properties (0 sorries)

* `mesh_forward_reaches` — a packet for a peer on a *different* relay reaches that
  peer's connection: composing the single-relay routing decision on the far relay
  with the gossip map on the near one. (`_local` is the same-relay corollary.)
* `mesh_no_leak` — every delivery the mesh emits lands on the one connection
  registered for `dstKey` on the relay it is delivered to — never a broadcast,
  never a third party, even across the relay→relay hop.
* `mesh_blind` — the payload crosses both hops verbatim: the delivered
  `RecvPacket` splits back into the source key and the *identical* packet bytes.
* `connect_home` / `connect_registers` / `disconnect_clears_home` — gossip
  consistency: a peer present in the mesh map is genuinely connected to the named
  relay, and `PeerGone` removes it.
-/

namespace Derp.Mesh

open Derp.Relay

/-! ## The `ForwardPacket` wire hop (`srcKey ‖ dstKey ‖ packet`)

The frame a relay puts on a mesh link. The receiving relay splits it back into the
source key, the destination key, and the verbatim packet, then delivers locally. -/

/-- A `ForwardPacket` payload: source key ‖ destination key ‖ the packet. Grouped
`src ‖ (dst ‖ packet)` so the sibling's split is the exact inverse. -/
def forwardPacketPayload (srcKey dstKey packet : Derp.Bytes) : Derp.Bytes :=
  srcKey ++ (dstKey ++ packet)

/-- The `FrameForwardPacket` a relay emits onto a mesh link for a remote peer. -/
def forwardPacketFrame (srcKey dstKey packet : Derp.Bytes) : Derp.Frame :=
  { ftype := .forwardPacket, payload := forwardPacketPayload srcKey dstKey packet }

/-- The sibling relay's split: recover `(srcKey, dstKey, packet)` from a
`ForwardPacket` payload, using the shared `Derp.splitKeyed` twice. -/
def splitForwarded (payload : Derp.Bytes) : Option (Derp.Bytes × Derp.Bytes × Derp.Bytes) :=
  match Derp.splitKeyed payload with
  | some (srcKey, rest) =>
    match Derp.splitKeyed rest with
    | some (dstKey, packet) => some (srcKey, dstKey, packet)
    | none => none
  | none => none

/-- Splitting a `keyLen`-prefixed payload recovers the prefix and the tail exactly
(the `Derp.splitKeyed` inverse, specialized to a genuine 32-byte key). -/
theorem splitKeyed_append (k r : Derp.Bytes) (hk : k.length = Derp.keyLen) :
    Derp.splitKeyed (k ++ r) = some (k, r) := by
  unfold Derp.splitKeyed
  have hle : Derp.keyLen ≤ (k ++ r).length := by
    rw [List.length_append, hk]; omega
  rw [if_pos hle]
  have ht : (k ++ r).take Derp.keyLen = k := by rw [← hk]; exact List.take_left' rfl
  have hd : (k ++ r).drop Derp.keyLen = r := by rw [← hk]; exact List.drop_left' rfl
  rw [ht, hd]

/-- **The mesh hop is faithful.** The `ForwardPacket` a relay puts on the mesh link
splits back on the sibling into *exactly* the source key, destination key, and the
verbatim packet — the two keys and the packet cross the relay→relay hop unchanged. -/
theorem splitForwarded_build (srcKey dstKey packet : Derp.Bytes)
    (hs : srcKey.length = Derp.keyLen) (hd : dstKey.length = Derp.keyLen) :
    splitForwarded (forwardPacketPayload srcKey dstKey packet)
      = some (srcKey, dstKey, packet) := by
  simp only [splitForwarded, forwardPacketPayload,
    splitKeyed_append srcKey (dstKey ++ packet) hs, splitKeyed_append dstKey packet hd]

/-! ## The mesh state -/

/-- A relay's identity within the mesh fabric. -/
abbrev RelayId := Nat

/-- The mesh: a set of relays (each a single-relay `RelayState`, indexed by
`RelayId`) and the gossip map `home` — which relay currently hosts a peer,
learned via `PeerPresent` / `PeerGone`. A relay id and a peer key each appear at
most once (the setters filter any prior binding). -/
structure MeshState where
  relays : List (RelayId × RelayState)
  home : List (Key × RelayId)
deriving Repr, DecidableEq

/-- An empty mesh: no relays, no presence. -/
def MeshState.empty : MeshState := { relays := [], home := [] }

/-- The state of relay `r`, if it is a member of the mesh. -/
def MeshState.relayOf (m : MeshState) (r : RelayId) : Option RelayState :=
  (m.relays.find? (fun p => p.1 == r)).map (·.2)

/-- The relay that currently hosts peer `k`, per the gossip map. -/
def MeshState.homeOf (m : MeshState) (k : Key) : Option RelayId :=
  (m.home.find? (fun p => p.1 == k)).map (·.2)

/-- Install/replace relay `r`'s state. -/
def MeshState.setRelay (m : MeshState) (r : RelayId) (s : RelayState) : MeshState :=
  { m with relays := (r, s) :: m.relays.filter (fun p => p.1 != r) }

/-- Record (or replace) the gossip entry `home[k] = r`. -/
def MeshState.setHome (m : MeshState) (k : Key) (r : RelayId) : MeshState :=
  { m with home := (k, r) :: m.home.filter (fun p => p.1 != k) }

/-- Drop the gossip entry for `k` (`PeerGone`). -/
def MeshState.clearHome (m : MeshState) (k : Key) : MeshState :=
  { m with home := m.home.filter (fun p => p.1 != k) }

/-- **Peer `k` connects to relay `r` on connection `c`.** Register `k → c` in `r`'s
local routing table (the real DERP login) and record `home[k] = r` — the
`PeerPresent(k)` gossip the mesh siblings apply. -/
def MeshState.connect (m : MeshState) (r : RelayId) (k : Key) (c : ConnId) : MeshState :=
  let s := (m.relayOf r).getD RelayState.empty
  (m.setRelay r (s.register k c)).setHome k r

/-- **Peer `k` departs relay `r`.** Drop `k`'s local binding and clear `home[k]` —
the `PeerGone(k)` gossip. -/
def MeshState.disconnect (m : MeshState) (r : RelayId) (k : Key) : MeshState :=
  let s := (m.relayOf r).getD RelayState.empty
  (m.setRelay r (s.unregister k)).clearHome k

/-- A mesh forwarding action: the exact relay, destination connection, and frame. -/
structure MeshDelivery where
  relay : RelayId
  dst : ConnId
  frame : Derp.Frame
deriving Repr, DecidableEq

/-- Lift a single-relay delivery onto relay `r`. -/
def liftDelivery (r : RelayId) (d : Delivery) : MeshDelivery :=
  { relay := r, dst := d.dst, frame := d.frame }

/-- The receiving-relay side of a mesh hop: a `ForwardPacket` carrying `srcKey`
addressed to `dstKey` is delivered to `dstKey`'s *local* connection on this relay
as a `RecvPacket` (source key ‖ verbatim packet), or dropped if `dstKey` is not
connected here. The source key is carried in the frame, not looked up — the
originator lives on another relay. Zero or one delivery. -/
def deliverForwarded (s : RelayState) (srcKey dstKey packet : Key) : List Delivery :=
  match s.connOf dstKey with
  | some dstConn =>
    [{ dst := dstConn, frame := { ftype := .recvPacket, payload := srcKey ++ packet } }]
  | none => []

/-- **The mesh forward.** A `SendPacket` for `dstKey` arriving on `srcConn` at
`srcRelay`. The source must be registered on `srcRelay` (to stamp its key). If
`dstKey` is local to `srcRelay`, deliver there (the single-relay hop). Otherwise
consult the gossip map: `home[dstKey] = r2`, and deliver on `r2` to `dstKey`'s
local connection (the mesh hop). Zero or one delivery, to the addressed peer. -/
def MeshState.forward (m : MeshState) (srcRelay : RelayId) (srcConn : ConnId)
    (dstKey packet : Key) : List MeshDelivery :=
  match m.relayOf srcRelay with
  | none => []
  | some s1 =>
    match s1.keyOf srcConn with
    | none => []
    | some srcKey =>
      match s1.connOf dstKey with
      | some _ => (s1.forward srcConn dstKey packet).map (liftDelivery srcRelay)
      | none =>
        match m.homeOf dstKey with
        | none => []
        | some r2 =>
          match m.relayOf r2 with
          | none => []
          | some s2 => (deliverForwarded s2 srcKey dstKey packet).map (liftDelivery r2)

/-! ## The far-relay hop respects the single-relay discipline -/

/-- **Addressed delivery on the receiving relay.** Every delivery the mesh hop
produces on the far relay targets the one connection registered there for `dstKey`
— the same discipline `Derp.Relay.forward_to_addressed_only` proves for a local
send, now on the far side of the relay→relay hop. -/
theorem deliverForwarded_addressed (s : RelayState) (srcKey dstKey packet : Key) :
    ∀ d ∈ deliverForwarded s srcKey dstKey packet, s.connOf dstKey = some d.dst := by
  intro d hd
  unfold deliverForwarded at hd
  cases hc : s.connOf dstKey with
  | none => rw [hc] at hd; simp at hd
  | some dstConn =>
    rw [hc] at hd
    simp only [List.mem_singleton] at hd
    subst hd
    rfl

/-- **The far hop is blind.** The `RecvPacket` the receiving relay delivers carries
the source key followed by the packet **unchanged** — splitting it back recovers
exactly the source key and the identical packet bytes. The mesh forwards the
payload verbatim across the relay→relay hop. -/
theorem deliverForwarded_blind (s : RelayState) (srcKey dstKey packet : Key)
    (hlen : srcKey.length = Derp.keyLen) :
    ∀ d ∈ deliverForwarded s srcKey dstKey packet,
      d.frame.ftype = .recvPacket ∧
      Derp.splitKeyed d.frame.payload = some (srcKey, packet) := by
  intro d hd
  unfold deliverForwarded at hd
  cases hc : s.connOf dstKey with
  | none => rw [hc] at hd; simp at hd
  | some dstConn =>
    rw [hc] at hd
    simp only [List.mem_singleton] at hd
    subst hd
    exact ⟨rfl, splitKeyed_append srcKey packet hlen⟩

/-! ## Mesh connectivity: the forward reaches the destination -/

/-- **Cross-relay reachability (the mesh property).** A packet for `dstKey` reaches
`dstKey`'s connection even when it lives on a *different* relay. If the source is
registered on `srcRelay`, `dstKey` is not local there, the gossip map routes
`dstKey → r2`, and `dstKey` is registered on `r2` as `dstConn`, then the mesh
forward delivers to `(r2, dstConn)` a `RecvPacket` stamped with the source's key.
Composes the far relay's routing decision (`connOf` on `s2`) with the near relay's
gossip map. -/
theorem mesh_forward_reaches
    (m : MeshState) (srcRelay : RelayId) (srcConn : ConnId)
    (dstKey packet srcKey : Key) (r2 : RelayId) (s1 s2 : RelayState) (dstConn : ConnId)
    (hr1 : m.relayOf srcRelay = some s1)
    (hsk : s1.keyOf srcConn = some srcKey)
    (hlocal : s1.connOf dstKey = none)
    (hhome : m.homeOf dstKey = some r2)
    (hr2 : m.relayOf r2 = some s2)
    (hc2 : s2.connOf dstKey = some dstConn) :
    (⟨r2, dstConn, { ftype := .recvPacket, payload := srcKey ++ packet }⟩ : MeshDelivery)
      ∈ m.forward srcRelay srcConn dstKey packet := by
  simp only [MeshState.forward, hr1, hsk, hlocal, hhome, hr2, deliverForwarded, hc2,
    liftDelivery, List.map_cons, List.map_nil, List.mem_singleton]

/-- **Same-relay reachability (the local corollary).** If `dstKey` is local to
`srcRelay`, the mesh forward delivers there directly — the single-relay hop lifted
into the mesh. -/
theorem mesh_forward_reaches_local
    (m : MeshState) (srcRelay : RelayId) (srcConn : ConnId)
    (dstKey packet srcKey : Key) (s1 : RelayState) (dstConn : ConnId)
    (hr1 : m.relayOf srcRelay = some s1)
    (hsk : s1.keyOf srcConn = some srcKey)
    (hc1 : s1.connOf dstKey = some dstConn) :
    (⟨srcRelay, dstConn, { ftype := .recvPacket, payload := srcKey ++ packet }⟩ : MeshDelivery)
      ∈ m.forward srcRelay srcConn dstKey packet := by
  simp only [MeshState.forward, hr1, hsk, hc1, Derp.Relay.RelayState.forward,
    liftDelivery, List.map_cons, List.map_nil, List.mem_singleton]

/-! ## No leak across the mesh -/

/-- **No leak / no broadcast in the mesh.** Every delivery the mesh forward emits
lands on the connection registered for `dstKey` on the relay it is delivered to —
never any other connection, never a broadcast, even across the relay→relay hop.
Both hops route by the same `connOf` discipline, so the mesh never widens the
audience of a packet beyond the one addressed peer. -/
theorem mesh_no_leak (m : MeshState) (srcRelay : RelayId) (srcConn : ConnId)
    (dstKey packet : Key) :
    ∀ d ∈ m.forward srcRelay srcConn dstKey packet,
      ∃ s : RelayState, m.relayOf d.relay = some s ∧ s.connOf dstKey = some d.dst := by
  intro d hd
  unfold MeshState.forward at hd
  cases h1 : m.relayOf srcRelay with
  | none => simp [h1] at hd
  | some s1 =>
    cases hk : s1.keyOf srcConn with
    | none => simp [h1, hk] at hd
    | some srcKey =>
      cases hloc : s1.connOf dstKey with
      | some c =>
        simp only [h1, hk, hloc, List.mem_map] at hd
        obtain ⟨d0, hd0, hde⟩ := hd
        have haddr := Derp.Relay.forward_to_addressed_only s1 srcConn dstKey packet d0 hd0
        subst hde
        exact ⟨s1, h1, haddr⟩
      | none =>
        cases hh : m.homeOf dstKey with
        | none => simp [h1, hk, hloc, hh] at hd
        | some r2 =>
          cases hr2 : m.relayOf r2 with
          | none => simp [h1, hk, hloc, hh, hr2] at hd
          | some s2 =>
            simp only [h1, hk, hloc, hh, hr2, List.mem_map] at hd
            obtain ⟨d0, hd0, hde⟩ := hd
            have haddr := deliverForwarded_addressed s2 srcKey dstKey packet d0 hd0
            subst hde
            exact ⟨s2, hr2, haddr⟩

/-- **The mesh is blind end to end.** Every delivery the mesh emits carries the
source key followed by the packet **unchanged** — splitting the delivered
`RecvPacket` recovers exactly the source key and the identical packet the sender
supplied, whether the delivery took the local hop or crossed the mesh. (`srcKey`
is a genuine 32-byte key on both paths; the hypothesis names that.) -/
theorem mesh_blind (m : MeshState) (srcRelay : RelayId) (srcConn : ConnId)
    (dstKey packet srcKey : Key) (s1 : RelayState)
    (hr1 : m.relayOf srcRelay = some s1)
    (hsk : s1.keyOf srcConn = some srcKey)
    (hlen : srcKey.length = Derp.keyLen) :
    ∀ d ∈ m.forward srcRelay srcConn dstKey packet,
      d.frame.ftype = .recvPacket ∧
      Derp.splitKeyed d.frame.payload = some (srcKey, packet) := by
  intro d hd
  unfold MeshState.forward at hd
  simp only [hr1, hsk] at hd
  cases hloc : s1.connOf dstKey with
  | some c =>
    simp only [hloc, List.mem_map] at hd
    obtain ⟨d0, hd0, hde⟩ := hd
    have hb := Derp.Relay.relay_blind s1 srcConn dstKey packet srcKey hsk hlen d0 hd0
    subst hde
    exact hb
  | none =>
    cases hh : m.homeOf dstKey with
    | none => simp [hloc, hh] at hd
    | some r2 =>
      cases hr2 : m.relayOf r2 with
      | none => simp [hloc, hh, hr2] at hd
      | some s2 =>
        simp only [hloc, hh, hr2, List.mem_map] at hd
        obtain ⟨d0, hd0, hde⟩ := hd
        have hb := deliverForwarded_blind s2 srcKey dstKey packet hlen d0 hd0
        subst hde
        exact hb

/-! ## Gossip consistency -/

/-- Looking up the relay just installed returns exactly it. -/
theorem relayOf_setRelay_self (m : MeshState) (r : RelayId) (s : RelayState) :
    (m.setRelay r s).relayOf r = some s := by
  simp [MeshState.setRelay, MeshState.relayOf]

/-- Looking up the gossip entry just recorded returns exactly it. -/
theorem homeOf_setHome_self (m : MeshState) (k : Key) (r : RelayId) :
    (m.setHome k r).homeOf k = some r := by
  simp [MeshState.setHome, MeshState.homeOf]

/-- After clearing `k`'s gossip entry, the lookup for `k` is empty. -/
theorem homeOf_clearHome_self (m : MeshState) (k : Key) :
    (m.clearHome k).homeOf k = none := by
  unfold MeshState.clearHome MeshState.homeOf
  have hnone : List.find? (fun p => p.1 == k) (m.home.filter (fun p => p.1 != k)) = none := by
    rw [List.find?_eq_none]
    intro x hx
    rw [List.mem_filter] at hx
    have hb : (x.1 == k) = false := by simpa [bne] using hx.2
    simp [hb]
  rw [hnone]; rfl

/-- **Gossip records presence.** After `k` connects to relay `r`, the mesh map
names `r` as `k`'s home — the `PeerPresent(k)` gossip took effect. -/
theorem connect_home (m : MeshState) (r : RelayId) (k : Key) (c : ConnId) :
    (m.connect r k c).homeOf k = some r := by
  unfold MeshState.connect
  exact homeOf_setHome_self _ _ _

/-- **Gossip is consistent with genuine registration.** A peer the mesh map lists
as home on relay `r` is *actually connected there*: right after `connect r k c`,
relay `r` is a mesh member and its local routing table resolves `k` to the
connection `c`. The map is not a free-floating claim — it shadows a real login. -/
theorem connect_registers (m : MeshState) (r : RelayId) (k : Key) (c : ConnId) :
    ∃ s : RelayState, (m.connect r k c).relayOf r = some s ∧ s.connOf k = some c := by
  refine ⟨((m.relayOf r).getD RelayState.empty).register k c, ?_,
          Derp.Relay.register_binds _ _ _⟩
  unfold MeshState.connect
  -- `setHome` touches only `home`; `relayOf` reads only `relays`.
  show (((m.setRelay r (((m.relayOf r).getD RelayState.empty).register k c)).setHome k r)).relayOf r
        = some _
  simp only [MeshState.setHome, MeshState.relayOf]
  exact relayOf_setRelay_self m r _

/-- **`PeerGone` removes presence.** After `k` disconnects from relay `r`, the mesh
map no longer lists a home for `k` — the `PeerGone(k)` gossip took effect. -/
theorem disconnect_clears_home (m : MeshState) (r : RelayId) (k : Key) :
    (m.disconnect r k).homeOf k = none := by
  unfold MeshState.disconnect
  exact homeOf_clearHome_self _ _

/-! ## Non-vacuous evaluation — a 2-relay mesh exercised on concrete data

Two relays: `R1` (id 1) and `R2` (id 2). Peer `A` (`keyA`) logs into `R1` on
connection 10; peer `B` (`keyB`) logs into `R2` on connection 20. The gossip map
learns `A → R1`, `B → R2`. `A`'s packet to `B` — a peer on the *other* relay —
is delivered on `R2` to connection 20 ONLY, as a `RecvPacket` carrying `A`'s key
and the verbatim payload; it reaches no connection on `R1` and no other conn. The
reverse (`B → A`) reaches `A` on `R1`. A packet to an unknown key is dropped. -/

/-- A 32-byte key that is all `n` — a genuine `keyLen` key. -/
private def demoKey (n : UInt8) : Key := List.replicate Derp.keyLen n

private def keyA : Key := demoKey 0xA1
private def keyB : Key := demoKey 0xB2
private def keyGhost : Key := demoKey 0xC3

/-- The 2-relay mesh after both peers log in. -/
private def meshDemo : MeshState :=
  (MeshState.empty.connect 1 keyA 10).connect 2 keyB 20

-- The gossip map: A homes on relay 1, B on relay 2, a ghost nowhere.
#guard meshDemo.homeOf keyA = some 1
#guard meshDemo.homeOf keyB = some 2
#guard meshDemo.homeOf keyGhost = none

-- Each relay's local table resolves its own peer.
#guard (meshDemo.relayOf 1).bind (·.connOf keyA) = some 10
#guard (meshDemo.relayOf 2).bind (·.connOf keyB) = some 20
-- B is NOT local to R1 (that is why the mesh hop is needed).
#guard (meshDemo.relayOf 1).bind (·.connOf keyB) = none

-- A (on R1, conn 10) sends "hi" to B (on R2): exactly one delivery, on relay 2,
-- to conn 20, as a RecvPacket carrying A's key ++ the verbatim payload.
#guard (meshDemo.forward 1 10 keyB [0x68, 0x69]).length = 1
#guard (meshDemo.forward 1 10 keyB [0x68, 0x69]).head?.map (·.relay) = some 2
#guard (meshDemo.forward 1 10 keyB [0x68, 0x69]).head?.map (·.dst) = some 20
#guard ((meshDemo.forward 1 10 keyB [0x68, 0x69]).head?.map
          (fun d => Derp.splitKeyed d.frame.payload))
        = some (some (keyA, [0x68, 0x69]))
-- Nothing lands on R1 and nothing lands on any conn but B's 20 (no leak / no broadcast).
#guard (meshDemo.forward 1 10 keyB [0x68, 0x69]).all (fun d => d.relay == 2 && d.dst == 20)

-- The reverse direction: B → A reaches A on relay 1, conn 10.
#guard (meshDemo.forward 2 20 keyA [0x01]).head?.map (fun d => (d.relay, d.dst)) = some (1, 10)

-- A packet to a peer connected to no relay in the mesh is dropped.
#guard meshDemo.forward 1 10 keyGhost [0x68, 0x69] = []
-- An unregistered source connection cannot forward.
#guard meshDemo.forward 1 99 keyB [0x68, 0x69] = []

-- Gossip removal: after B departs R2, the map no longer homes B, and A's packet
-- to B is dropped (no stale route).
#guard (meshDemo.disconnect 2 keyB).homeOf keyB = none
#guard (meshDemo.disconnect 2 keyB).forward 1 10 keyB [0x68, 0x69] = []

-- The ForwardPacket wire hop round-trips: build src‖dst‖pkt, split it back exactly.
#guard splitForwarded (forwardPacketPayload keyA keyB [0x68, 0x69])
        = some (keyA, keyB, [0x68, 0x69])

end Derp.Mesh
