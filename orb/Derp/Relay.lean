import Derp
/-!
# DERP relay-forwarding server — the proven forwarding state machine

The `Derp` module models the DERP wire framing and the login handshake (both
directions) as a *client* would drive it. This module adds the missing half: the
**relay server** — the transition system a relay runs to accept many client
connections and forward encrypted packet frames *between* them, peer to peer,
without ever decrypting the payload it carries.

A relay is a pure router. Each connection, after its login handshake, announces
its own Curve25519 public key (the relay learns it by opening the client's
`FrameClientInfo`); the relay records `key → connection` in a routing table. When
a connection `A` sends a `FrameSendPacket` addressed to a destination public key
`B`, the relay looks `B` up in the table and re-frames the *verbatim* payload as a
`FrameRecvPacket` stamped with `A`'s source key, delivering it to `B`'s connection
and to no other. If `B` is not connected, the frame is dropped — never broadcast,
never misrouted. The relay is *blind*: the packet bytes pass through unchanged; it
routes on the addressing envelope alone.

This is the DERP analogue of a switch's forwarding table, and the security
properties below are the switch's forwarding discipline made precise.

## The state

* `RelayState` — the routing table, a list of `(peerKey, connId)` registrations.
  A key is bound to at most one connection (re-registration replaces the prior
  binding); `connOf` reads `key → conn` for the *destination* lookup and `keyOf`
  reads `conn → key` for stamping the *source* on a forwarded frame.

## The step relation

* `Event` — what a relay reacts to: a connection registering its key
  (`clientInfo`), a `sendPacket` addressed to a peer key, and a departure
  (`peerGone`). `step` folds an event into `(state', deliveries)` where a
  `Delivery` names the exact destination connection and the exact frame put on it.

## The forwarding discipline (proven, 0 sorries)

* `forward_to_addressed_only` — a `SendPacket` for `dstKey` is delivered ONLY to
  the connection registered for `dstKey`; every delivery it produces targets that
  one connection, never any other, never a broadcast.
* `relay_blind` — the relay forwards the payload bytes UNCHANGED: the delivered
  `RecvPacket` payload splits back into the source key and the *identical* packet
  the sender supplied. The relay does not read, decrypt, or alter the packet.
* `absent_dst_dropped` — a packet addressed to an unregistered peer produces no
  delivery and leaves the table unchanged: dropped, not misrouted.
* `unregistered_src_dropped` — a connection that has not registered its key
  cannot inject a forwarded frame; the relay stamps a genuine source or drops.
* `delivery_dst_registered` — registration soundness: any connection that
  RECEIVES a forwarded frame is one that had registered a key first.
* `register_binds` / `register_rebinds` — the table honors a fresh registration
  and a re-registration replaces the old binding.

## Boundary / follow-on

* The **mesh** — multiple relays gossiping presence with `peerPresent` /
  `peerGone` / `watchConns` broadcasts across a relay fabric — is named
  follow-on. This module proves the *single-relay* peer-to-peer forwarding, which
  is the core discipline; the mesh layers presence propagation on top of it and
  reuses the same routing table and the same blind-forward invariant per hop.
-/

namespace Derp.Relay

/-- A connection identity assigned by the relay's accept loop. -/
abbrev ConnId := Nat

/-- A peer public key on the wire — 32 raw bytes (Curve25519), reusing the
`Derp` byte model so the frame codec and this router speak one representation. -/
abbrev Key := Derp.Bytes

/-- The relay's routing table: the currently-registered `(peerKey, connId)`
bindings. A key appears at most once (registration filters any prior binding of
the same key before prepending), so `connOf` is a genuine function. -/
structure RelayState where
  routes : List (Key × ConnId)
deriving Repr, DecidableEq

/-- A relay holding no connections. -/
def RelayState.empty : RelayState := { routes := [] }

/-- Destination lookup: the connection currently registered for `k`, if any.
This is the routing decision — a `SendPacket` for `k` goes exactly here. -/
def RelayState.connOf (s : RelayState) (k : Key) : Option ConnId :=
  (s.routes.find? (fun p => p.1 == k)).map (·.2)

/-- Source lookup: the key a connection registered, if any. Used to stamp the
source key on a forwarded `RecvPacket` — a connection that never registered has
no key and cannot originate a forward. -/
def RelayState.keyOf (s : RelayState) (c : ConnId) : Option Key :=
  (s.routes.find? (fun p => p.2 == c)).map (·.1)

/-- Register (or re-register) `conn` under `key`: drop any prior binding of `key`,
then bind it to `conn`. Re-registration of a key replaces the old connection. -/
def RelayState.register (s : RelayState) (key : Key) (conn : ConnId) : RelayState :=
  { routes := (key, conn) :: s.routes.filter (fun p => p.1 != key) }

/-- Remove a peer's binding (a `peerGone` / disconnect). -/
def RelayState.unregister (s : RelayState) (key : Key) : RelayState :=
  { routes := s.routes.filter (fun p => p.1 != key) }

/-- A forwarding action the relay emits: the exact destination connection and the
exact frame written to it. The relay's *only* externally-visible output. -/
structure Delivery where
  dst : ConnId
  frame : Derp.Frame
deriving Repr, DecidableEq

/-- The events a relay steps on. `sendPacket conn dstKey payload` is a
`FrameSendPacket` arriving on connection `conn`, addressed to peer key `dstKey`,
carrying `payload` (the opaque, possibly end-to-end-encrypted packet). -/
inductive Event where
  /-- Connection `conn` completed login and announced its public `key`. -/
  | clientInfo (conn : ConnId) (key : Key)
  /-- Connection `conn` sends `payload` addressed to peer key `dstKey`. -/
  | sendPacket (conn : ConnId) (dstKey : Key) (payload : Derp.Bytes)
  /-- Peer `key` departed. -/
  | peerGone (key : Key)
deriving Repr

/-- The blind forward: given a `sendPacket` on `srcConn` addressed to `dstKey`
with `payload`, produce the deliveries. A forward happens iff BOTH ends are
registered — the source has a key to stamp and the destination has a connection
to reach. The delivered frame is a `RecvPacket` whose payload is `srcKey`
prepended to the *verbatim* `payload`; the relay copies the packet bytes and
never inspects them. Zero or one delivery (single-relay peer-to-peer). -/
def RelayState.forward (s : RelayState) (srcConn : ConnId) (dstKey : Key)
    (payload : Derp.Bytes) : List Delivery :=
  match s.keyOf srcConn, s.connOf dstKey with
  | some srcKey, some dstConn =>
    [{ dst := dstConn,
       frame := { ftype := .recvPacket, payload := srcKey ++ payload } }]
  | _, _ => []

/-- One transition of the relay: fold an event into the next state and the
deliveries it emits. Registration and departure change the table and emit
nothing; a `sendPacket` leaves the table unchanged and emits the forward. -/
def step (s : RelayState) (e : Event) : RelayState × List Delivery :=
  match e with
  | .clientInfo conn key => (s.register key conn, [])
  | .sendPacket conn dstKey payload => (s, s.forward conn dstKey payload)
  | .peerGone key => (s.unregister key, [])

/-! ## Routing-table lemmas -/

/-- `find?` with a boolean key predicate returns a member of the list. -/
theorem find?_mem {p : Key × ConnId} {l : List (Key × ConnId)}
    {f : Key × ConnId → Bool} (h : l.find? f = some p) : p ∈ l :=
  List.mem_of_find?_eq_some h

/-- **Registration binds.** Immediately after registering `conn` under `key`, the
destination lookup for `key` resolves to `conn`. -/
theorem register_binds (s : RelayState) (key : Key) (conn : ConnId) :
    (s.register key conn).connOf key = some conn := by
  simp [RelayState.register, RelayState.connOf]

/-- **Registration is a rebind, not an alias.** After registering `key` to a new
`conn`, the destination lookup for `key` is exactly the new `conn` — any earlier
binding of the same key is gone (there is never a stale second route for a key). -/
theorem register_rebinds (s : RelayState) (key : Key) (conn old : ConnId)
    (h : (s.register key conn).connOf key = some old) : old = conn := by
  rw [register_binds] at h
  exact (Option.some.inj h).symm

/-! ## The forwarding discipline -/

/-- **Addressed delivery only.** Every delivery a `SendPacket` for `dstKey`
produces targets the one connection registered for `dstKey` — never any other
connection, never a broadcast. If `dstKey` maps to `c`, all deliveries go to `c`;
in particular the relay does not leak the frame to a third party. -/
theorem forward_to_addressed_only (s : RelayState) (srcConn : ConnId) (dstKey : Key)
    (payload : Derp.Bytes) :
    ∀ d ∈ s.forward srcConn dstKey payload, s.connOf dstKey = some d.dst := by
  intro d hd
  unfold RelayState.forward at hd
  cases hsrc : s.keyOf srcConn with
  | none => rw [hsrc] at hd; simp at hd
  | some srcKey =>
    cases hdst : s.connOf dstKey with
    | none => rw [hsrc, hdst] at hd; simp at hd
    | some dstConn =>
      rw [hsrc, hdst] at hd
      simp only [List.mem_singleton] at hd
      subst hd
      rfl

/-- **The relay is blind.** A forwarded `RecvPacket` carries the sender's key
followed by the packet **unchanged**: splitting the delivered payload back
recovers exactly the source key and the *identical* bytes the sender supplied.
The relay copies the packet across; it does not decrypt, truncate, or rewrite it.
(`srcKey.length = keyLen` because a registered key is a 32-byte Curve25519 key.) -/
theorem relay_blind (s : RelayState) (srcConn : ConnId) (dstKey : Key)
    (payload srcKey : Derp.Bytes)
    (hkey : s.keyOf srcConn = some srcKey) (hlen : srcKey.length = Derp.keyLen) :
    ∀ d ∈ s.forward srcConn dstKey payload,
      d.frame.ftype = .recvPacket ∧
      Derp.splitKeyed d.frame.payload = some (srcKey, payload) := by
  intro d hd
  unfold RelayState.forward at hd
  rw [hkey] at hd
  cases hdst : s.connOf dstKey with
  | none => rw [hdst] at hd; simp at hd
  | some dstConn =>
    rw [hdst] at hd
    simp only [List.mem_singleton] at hd
    subst hd
    refine ⟨rfl, ?_⟩
    -- splitKeyed (srcKey ++ payload) = some (srcKey, payload) when |srcKey| = keyLen
    show Derp.splitKeyed (srcKey ++ payload) = some (srcKey, payload)
    unfold Derp.splitKeyed
    have hle : Derp.keyLen ≤ (srcKey ++ payload).length := by
      rw [List.length_append, hlen]; omega
    rw [if_pos hle]
    have ht : (srcKey ++ payload).take Derp.keyLen = srcKey := by
      rw [← hlen]; exact List.take_left' rfl
    have hdrp : (srcKey ++ payload).drop Derp.keyLen = payload := by
      rw [← hlen]; exact List.drop_left' rfl
    rw [ht, hdrp]

/-- **Absent destination is dropped.** A `SendPacket` addressed to a key that is
not registered produces no delivery, and the routing table is unchanged. Dropped,
never misrouted to some other connection. -/
theorem absent_dst_dropped (s : RelayState) (conn : ConnId) (dstKey : Key)
    (payload : Derp.Bytes) (h : s.connOf dstKey = none) :
    step s (.sendPacket conn dstKey payload) = (s, []) := by
  show (s, s.forward conn dstKey payload) = (s, [])
  simp only [RelayState.forward, h]
  cases s.keyOf conn <;> rfl

/-- **Unregistered source is dropped.** A connection that never announced its key
cannot originate a forwarded frame — `forward` emits nothing when the source has
no registered key, so the relay never stamps a forged source onto the mesh. -/
theorem unregistered_src_dropped (s : RelayState) (srcConn : ConnId) (dstKey : Key)
    (payload : Derp.Bytes) (h : s.keyOf srcConn = none) :
    s.forward srcConn dstKey payload = [] := by
  unfold RelayState.forward
  rw [h]

/-- **Registration soundness.** Any connection that RECEIVES a forwarded frame is
one that had already registered a key — the destination of every delivery has a
binding in the routing table. A connection gets packets only after it registered. -/
theorem delivery_dst_registered (s : RelayState) (srcConn : ConnId) (dstKey : Key)
    (payload : Derp.Bytes) :
    ∀ d ∈ s.forward srcConn dstKey payload,
      ∃ k : Key, (k, d.dst) ∈ s.routes := by
  intro d hd
  have hlk : s.connOf dstKey = some d.dst := forward_to_addressed_only s srcConn dstKey payload d hd
  unfold RelayState.connOf at hlk
  cases hf : s.routes.find? (fun p => p.1 == dstKey) with
  | none => rw [hf] at hlk; simp at hlk
  | some p =>
    rw [hf] at hlk
    simp only [Option.map_some, Option.some.injEq] at hlk
    exact ⟨p.1, by rw [← hlk]; exact find?_mem hf⟩

/-! ## Non-vacuous evaluation — the forwarding table exercised on concrete data

These `#guard` checks evaluate the state machine on real keys and connections so
the theorems above cannot be read as vacuous. Two peers register; A's packet to B
is delivered to B's connection ONLY, with the payload verbatim; a packet to an
unknown key yields nothing. -/

/-- A 32-byte key that is all `n` — long enough to be a genuine `keyLen` key. -/
private def demoKey (n : UInt8) : Key := List.replicate Derp.keyLen n

private def keyA : Key := demoKey 0xAA
private def keyB : Key := demoKey 0xBB
private def keyGhost : Key := demoKey 0xCC

/-- After A(conn 1) and B(conn 2) register, the relay routes B by key to conn 2. -/
private def relay2 : RelayState :=
  (RelayState.empty.register keyA 1).register keyB 2

-- B's key resolves to B's connection; A's to A's; a ghost key to nothing.
#guard relay2.connOf keyB = some 2
#guard relay2.connOf keyA = some 1
#guard relay2.connOf keyGhost = none

-- A (conn 1) sends "hi" to B: exactly one delivery, to conn 2, as a RecvPacket
-- carrying A's key ++ the verbatim payload.
#guard (relay2.forward 1 keyB [0x68, 0x69]).length = 1
#guard (relay2.forward 1 keyB [0x68, 0x69]).head?.map (·.dst) = some 2
#guard ((relay2.forward 1 keyB [0x68, 0x69]).head?.map
          (fun d => Derp.splitKeyed d.frame.payload))
        = some (some (keyA, [0x68, 0x69]))

-- A packet addressed to a peer that is not connected is dropped (no delivery).
#guard relay2.forward 1 keyGhost [0x68, 0x69] = []

-- An unregistered connection (conn 9) cannot forward anything.
#guard relay2.forward 9 keyB [0x68, 0x69] = []

-- The full step: a sendPacket leaves the table unchanged and emits the forward;
-- a clientInfo grows the table and emits nothing.
#guard (step relay2 (.sendPacket 1 keyB [0x68, 0x69])).1 = relay2
#guard (step relay2 (.sendPacket 1 keyB [0x68, 0x69])).2.length = 1
#guard (step RelayState.empty (.clientInfo 1 keyA)).2 = []
#guard ((step RelayState.empty (.clientInfo 1 keyA)).1).connOf keyA = some 1

end Derp.Relay
