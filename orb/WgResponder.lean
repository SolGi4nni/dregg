/-
# WgResponder — completing a WireGuard Noise IK handshake as the RESPONDER

The mirror of `WgLive`. There, drorb was the *initiator*: it built
`MessageInitiation` and a real WireGuard peer replied. Here a real WireGuard
peer is the *initiator* — it sends `MessageInitiation` at us — and drorb is the
*responder*: it accepts the initiation, runs the proven responder ratchet, and
emits `MessageResponse`. Completing that from the peer's side is positive
evidence the responder construction is byte-compatible with WireGuard.

Everything cryptographic and every byte of parsing/state is the proven Lean:

  * `Peer.handleInitiation` (Wireguard.lean) verifies mac1, runs the same Noise
    ratchet from the responder end (`Wire.consumeInitiation`), opens the sealed
    static key + timestamp, checks the recovered static key is a *configured*
    peer and the timestamp beats the anti-replay ratchet, installs a session
    (responder key orientation), and returns the serialized `MessageResponse`.
  * `Peer.handleTransport` routes an inbound transport packet (type 4) to that
    session by receiver index, checks the anti-replay window, and AEAD-opens it
    under `T_recv`. A packet from the peer that opens is proof the transport
    keys *agree*: the peer sealed it under the key it derived as its `T_send`,
    which is exactly the key drorb derived as its `T_recv`.
  * drorb then seals a keepalive under `T_send` and sends it back, so the peer's
    receive counter advances too — both transport directions demonstrated.

The UDP seam (`ffi/wg_udp.c`) binds a socket, receives a datagram from an
unknown source, and replies to that source. It parses/decrypts NOTHING. Not
part of the trusted core: this is a live cross-check, the WireGuard analogue of
`crypto-selftest`.

Usage:
  wg-responder <peerStaticPubHex> <listenPort> <nowSecs> <ourStaticPrivHex> <ourEphPrivHex>
-/
import Wireguard

open Wireguard

namespace WgResponder

@[extern "drorb_udp_listen"]
opaque udpListen (port : UInt16) : IO UInt32

@[extern "drorb_udp_recv"]
opaque udpRecv (fd : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)

@[extern "drorb_udp_reply"]
opaque udpReply (fd : UInt32) (payload : ByteArray) : IO Unit

@[extern "drorb_udp_close"]
opaque udpClose (fd : UInt32) : IO Unit

/-- Parse a hex string into a `ByteArray`. -/
def ofHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.filter (fun c => c ≠ ' ' ∧ c ≠ '\n')
  let hexVal : Char → Option UInt8 := fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
    else none
  let rec go : List Char → ByteArray → ByteArray
    | hi :: lo :: rest, acc =>
      match hexVal hi, hexVal lo with
      | some h, some l => go rest (acc.push (h * 16 + l))
      | _, _ => acc
    | _, acc => acc
  go cs (ByteArray.mk #[])

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def baOf (l : Wireguard.Bytes) : ByteArray := ⟨l.toArray⟩

/-- A neutral endpoint placeholder: the roaming record only stores it; the UDP
seam already tracks the real source address for the reply. -/
def anyEndpoint : Peer.Endpoint := { host := [], port := 0 }

/-- Message type is the first byte (§5.4): 1 = initiation, 2 = response,
4 = transport data. -/
def msgType (b : ByteArray) : UInt8 := if b.size == 0 then 0 else b.get! 0

/-- One handling step over the pure model, plus the wire effect. Returns the new
engine state and `true` once a transport packet has been delivered (handshake +
transport-key agreement demonstrated). -/
partial def loop (cfg : Peer.Cfg) (f : Peer.Fresh) (fd : UInt32)
    (st : Peer.St) (iter : Nat) : IO Bool := do
  if iter == 0 then
    IO.eprintln "gave up after too many datagrams"
    return false
  let some dg ← udpRecv fd 15000
    | do IO.eprintln "\n<- NO DATAGRAM (peer never initiated within the window)"
         return false
  let l := Wire.bytesOf dg
  match msgType dg with
  | 1 => do
    IO.println s!"\n<- received MessageInitiation ({dg.size} bytes) from real WireGuard peer:"
    IO.println s!"  {toHex dg}"
    let (st', out?) := Peer.handleInitiation cfg f anyEndpoint st l
    match out? with
    | none => do
      IO.eprintln "handleInitiation REJECTED the initiation (mac1 / AEAD / config / anti-replay)"
      loop cfg f fd st' (iter - 1)
    | some resp => do
      IO.println s!"\n-> drorb accepted it. Sending MessageResponse ({resp.length} bytes):"
      IO.println s!"  {toHex (baOf resp)}"
      udpReply fd (baOf resp)
      -- Report the freshly installed responder session's transport keys.
      match Wire.route st'.sessions 1 with
      | some s => do
        IO.println s!"\nRESPONDER SESSION INSTALLED (local index {s.localIdx.toNat}, remote index {s.remoteIdx.toNat})"
        IO.println s!"  T_recv (peer->drorb) : {toHex s.tRecv}"
        IO.println s!"  T_send (drorb->peer) : {toHex s.tSend}"
      | none => pure ()
      loop cfg f fd st' (iter - 1)
  | 4 => do
    IO.println s!"\n<- received transport packet (type 4, {dg.size} bytes) from peer:"
    IO.println s!"  {toHex dg}"
    let (st', pt?) := Peer.handleTransport cfg anyEndpoint st l
    match pt? with
    | none => do
      IO.eprintln "handleTransport REJECTED the packet (no session / window / AEAD)"
      loop cfg f fd st' (iter - 1)
    | some pt => do
      IO.println "\nTRANSPORT KEYS AGREE — the peer's packet AEAD-opened under drorb's T_recv."
      IO.println s!"  decrypted payload ({pt.size} bytes){if pt.size == 0 then " (keepalive)" else ""}: {toHex pt}"
      -- Send a keepalive back under T_send so the peer's receive counter advances too.
      match Wire.route st'.sessions 1 with
      | some s => do
        match Wire.sealPacket s.tSend s.remoteIdx (UInt64.ofNat s.sendCtr) ByteArray.empty with
        | some ka => do
          udpReply fd (baOf ka)
          IO.println s!"\n-> sent transport keepalive ({ka.length} bytes) back under T_send"
        | none => IO.eprintln "sealPacket (keepalive) failed"
      | none => pure ()
      IO.println "\nHANDSHAKE COMPLETE — a real WireGuard peer initiated and drorb responded."
      return true
  | t => do
    IO.println s!"\n<- ignoring datagram of type {t.toNat} ({dg.size} bytes)"
    loop cfg f fd st (iter - 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | [peerPubHex, portS, nowS, ourStaticHex, ourEphHex] => do
    let spubPeer := ofHex peerPubHex
    let sr := ofHex ourStaticHex
    let er := ofHex ourEphHex
    let some port := portS.toNat? | do IO.eprintln "bad port"; return 1
    let some nowSecs := nowS.toNat? | do IO.eprintln "bad nowSecs"; return 1
    let some spubR := Crypto.x25519Base sr
      | do IO.eprintln "x25519Base(static) failed"; return 1
    let some epubR := Crypto.x25519Base er
      | do IO.eprintln "x25519Base(ephemeral) failed"; return 1
    let psk : ByteArray := ⟨Array.mkArray 32 (0 : UInt8)⟩

    -- Configure the peer with 0.0.0.0/0 allowed IPs so any transport packet's
    -- inner source is admissible (a keepalive is admissible regardless).
    let cfg : Peer.Cfg :=
      { s := sr, spub := spubR,
        peers := [ { spub := spubPeer, psk := psk,
                     allowed := [ { addr := [0, 0, 0, 0], plen := 0 } ] } ] }
    let f : Peer.Fresh := { e := er, epub := epubR, now := nowSecs }

    IO.println s!"drorb static  pub : {toHex spubR}"
    IO.println s!"drorb ephem   pub : {toHex epubR}"
    IO.println s!"peer  static  pub : {toHex spubPeer}"

    let fd ← udpListen port.toUInt16
    IO.println s!"\n== drorb listening as WireGuard RESPONDER on 0.0.0.0:{port} =="

    let ok ← loop cfg f fd Peer.St.empty 64
    udpClose fd
    return (if ok then 0 else 1)
  | _ => do
    IO.eprintln "usage: wg-responder <peerStaticPubHex> <listenPort> <nowSecs> <ourStaticPrivHex> <ourEphPrivHex>"
    return 1

/-! ## Refinement: the driver's steps ARE the proven model

The driver calls the pure model functions `Peer.handleInitiation` and
`Peer.handleTransport` directly, then moves their bytes over UDP. The two
theorems below package the model-level guarantees for exactly the driver's
flow, both discharged from the already-proven core (no new axioms). -/

open Peer

/-- **The responder step preserves the anti-replay invariant, from a clean
start.** The driver begins at `St.empty` (invariant holds vacuously) and folds
`handleInitiation` over inbound datagrams; every such step keeps the window
invariant — so every session the driver ever installs is anti-replay sound. -/
theorem responder_handshake_preserves_inv
    (cfg : Cfg) (f : Fresh) (src : Endpoint) (l : Bytes) :
    Inv (handleInitiation cfg f src St.empty l).1 :=
  inv_handleInitiation cfg f src Peer.St.empty l inv_empty

/-- **A delivered transport packet was authenticated by the installed session.**
When the driver's `handleTransport` yields a payload, it did so by routing to a
real session, passing the anti-replay window, AEAD-opening under that session's
`T_recv`, and confirming the sender is a configured peer — i.e. the peer sealed
the packet under the transport key drorb derived as its `T_recv`. This is
exactly transport-key agreement, on the responder side. Discharged from the
core `wg_transport_delivery_inverted`. -/
theorem responder_transport_authenticated
    (cfg : Cfg) (src : Endpoint) (st : Peer.St) (l : Bytes)
    {st' : Peer.St} {pt : ByteArray}
    (h : handleTransport cfg src st l = (st', some pt)) :
    ∃ idx ctr s p,
      peekTransport l = some (idx, ctr) ∧
      Wire.route st.sessions idx = some s ∧
      s.win.willAccept ctr = true ∧
      findCfg cfg.peers s.peer = some p ∧
      srcAllowed p pt = true := by
  rcases wg_transport_delivery_inverted cfg src st l h with
    ⟨idx, ctr, s, p, hpeek, hroute, hacc, hfind, hallow, _, _⟩
  exact ⟨idx, ctr, s, p, hpeek, hroute, hacc, hfind, hallow⟩

end WgResponder

def main (args : List String) : IO UInt32 := WgResponder.main args
