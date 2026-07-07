/-
# WgLive — driving the WireGuard Noise IK handshake against a real peer

The `Wireguard` model is sans-IO: `Wire.mkInitiation`, `Wire.consumeResponse`,
`Wire.sealPacket` are pure functions computing the exact bytes of a WireGuard
handshake and transport, on the verified `Crypto` X25519 / ChaCha20-Poly1305 and
the pure-Lean RFC-7693 BLAKE2s ratchet. This executable takes those bytes to a
real UDP socket (`ffi/wg_udp.c`) so the construction can be checked against a
real WireGuard implementation (kernel WireGuard / wireguard-go / boringtun):

  * drorb is the INITIATOR. It builds `MessageInitiation` (type 1, 148 bytes) for
    a configured responder public key and sends it over UDP.
  * A real responder that accepts the initiation (mac1 valid, DH chain valid, the
    AEAD-sealed static key and timestamp open) replies with `MessageResponse`
    (type 2, 92 bytes). A responder that rejects it stays SILENT — so a reply is
    positive evidence the whole construction is byte-compatible with WireGuard.
  * drorb runs `consumeResponse` on the reply, deriving the transport keys, then
    seals a transport keepalive (type 4) under the send key and sends it — which
    the real peer decrypts and counts, completing the handshake both ways.

Not part of the trusted core: this is a live cross-check, the WireGuard analogue
of `crypto-selftest`. Everything cryptographic is the proven/verified Lean.

Usage:
  wg-live <peerPubHex> <host> <port> <nowSecs> <staticPrivHex> <ephPrivHex>
-/
import Wireguard

open Wireguard

namespace WgLive

@[extern "drorb_udp_socket"]
opaque udpSocket (host : String) (port : UInt16) : IO UInt32

@[extern "drorb_udp_send_recv"]
opaque udpSendRecv (fd : UInt32) (payload : ByteArray) (timeoutMs : UInt32) :
    IO (Option ByteArray)

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

def main (args : List String) : IO UInt32 := do
  match args with
  | [peerPubHex, host, portS, nowS, staticHex, ephHex] => do
    let spubR := ofHex peerPubHex
    let si := ofHex staticHex
    let ei := ofHex ephHex
    let some port := portS.toNat? | do IO.eprintln "bad port"; return 1
    let some nowSecs := nowS.toNat? | do IO.eprintln "bad nowSecs"; return 1
    let some spubI := Crypto.x25519Base si
      | do IO.eprintln "x25519Base(static) failed"; return 1
    let some epubI := Crypto.x25519Base ei
      | do IO.eprintln "x25519Base(ephemeral) failed"; return 1
    let psk : ByteArray := ⟨Array.mkArray 32 (0 : UInt8)⟩
    let sender : UInt32 := 0x11223344
    let ts := baOf (Wire.tai64n (UInt64.ofNat nowSecs) 0)

    IO.println s!"drorb static  pub : {toHex spubI}"
    IO.println s!"drorb ephem   pub : {toHex epubI}"
    IO.println s!"peer  static  pub : {toHex spubR}"

    let some (m, stI) := Wire.mkInitiation si spubI ei epubI spubR ts sender
      | do IO.eprintln "mkInitiation failed"; return 1
    let initBytes := baOf (Wire.serializeInitiation m)
    IO.println s!"\nMessageInitiation ({initBytes.size} bytes):"
    IO.println s!"  {toHex initBytes}"

    let fd ← udpSocket host port.toUInt16
    IO.println s!"\n-> sent initiation to {host}:{port}"
    let reply ← udpSendRecv fd initBytes 3000
    match reply with
    | none => do
      IO.eprintln "\n<- NO REPLY (peer silently dropped the initiation)"
      udpClose fd
      return 1
    | some resp => do
      IO.println s!"\n<- received {resp.size} bytes from real WireGuard peer:"
      IO.println s!"  {toHex resp}"
      let respL := (Wire.bytesOf resp)
      match Wire.consumeResponse si ei spubI psk respL stI with
      | none => do
        IO.eprintln "\nconsumeResponse REJECTED the reply (not a valid MessageResponse)"
        udpClose fd
        return 1
      | some (r, stF) => do
        let (tSend, tRecv) := Wire.sessionKeys stF
        IO.println "\nHANDSHAKE COMPLETE — drorb accepted the real peer's MessageResponse."
        IO.println s!"  responder index : {r.sender.toNat}"
        IO.println s!"  T_send (initiator->responder) : {toHex tSend}"
        IO.println s!"  T_recv (responder->initiator) : {toHex tRecv}"
        -- Seal a transport keepalive (type 4, empty payload) under T_send and
        -- send it; the real peer decrypts+counts it, completing both directions.
        match Wire.sealPacket tSend r.sender 0 ByteArray.empty with
        | none => do IO.eprintln "sealPacket failed"; udpClose fd; return 1
        | some ka => do
          let _ ← udpSendRecv fd (baOf ka) 1000
          IO.println s!"\n-> sent transport keepalive ({ka.length} bytes) under T_send"
          udpClose fd
          return 0
  | _ => do
    IO.eprintln "usage: wg-live <peerPubHex> <host> <port> <nowSecs> <staticPrivHex> <ephPrivHex>"
    return 1

end WgLive

def main (args : List String) : IO UInt32 := WgLive.main args
