/-
# DerpLive — driving the DERP relay handshake + a real frame relay against a real relay

The `Derp` model is sans-IO: `buildClientInfo`, `openServerInfo`, `serializeFrame`,
`parseFrame` compute the exact bytes of the DERP login handshake and relay frames
on the verified `Crypto` crypto_box (X25519 + XSalsa20-Poly1305) and the proven
length-prefixed framing. This executable takes those bytes to a real TCP socket
(ffi/derp_net.c) and drives them against a real DERP relay (`derper`):

  * Two clients A and B each open a TCP connection, send the DERP HTTP Upgrade
    (with Derp-Fast-Start so the relay goes straight to frames), read the relay's
    FrameServerKey greeting, seal a FrameClientInfo to the relay with the proven
    `Derp.buildClientInfo`, and open the relay's FrameServerInfo reply with the
    proven `Derp.openServerInfo`. A reply that opens is positive evidence the
    crypto_box handshake is byte-compatible with the real relay — the relay only
    replies to a client whose sealed ClientInfo it could decrypt.
  * Client A then sends a FrameSendPacket addressed to B's public key; the relay
    forwards it, and client B reads a FrameRecvPacket carrying A's public key and
    the verbatim packet — a real frame relayed through a real relay.

Not part of the trusted core: this is a live cross-check, the DERP analogue of
crypto-selftest. Everything cryptographic/structural is the proven/verified Lean.

Usage:
  derp-live <host> <port> [privAHex] [privBHex]
-/
import Derp

open Crypto (x25519Base)

namespace DerpLive

@[extern "drorb_tcp_connect"]
opaque tcpConnect (host : String) (port : UInt16) : IO UInt32

@[extern "drorb_tcp_send"]
opaque tcpSend (fd : UInt32) (payload : ByteArray) : IO Unit

@[extern "drorb_tcp_recv_exact"]
opaque tcpRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) :
    IO (Option ByteArray)

@[extern "drorb_tcp_close"]
opaque tcpClose (fd : UInt32) : IO Unit

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

def recvTimeout : UInt32 := 5000

/-- Render a buffer as UTF-8 text if it decodes, else as hex. -/
def utf8OrHex (b : ByteArray) : String := (String.fromUTF8? b).getD (toHex b)

/-- Read one complete DERP frame off the stream: the 5-byte header, then the
declared payload, reassembled and parsed by the proven `Derp.parseFrame`. -/
def readFrame (fd : UInt32) : IO (Option Derp.Frame) := do
  match ← tcpRecvExact fd 5 recvTimeout with
  | none => return none
  | some hb =>
    let len := Derp.be32 (hb.get! 1) (hb.get! 2) (hb.get! 3) (hb.get! 4)
    let payload ← if len == 0 then pure (some ByteArray.empty)
                  else tcpRecvExact fd (UInt32.ofNat len) recvTimeout
    match payload with
    | none => return none
    | some pb =>
      match Derp.parseFrame 70000 (hb ++ pb).toList with
      | some (f, _) => return some f
      | none => return none

/-- Read frames until one of `want` type arrives (skipping keepAlive/health/etc.),
up to `fuel` frames. -/
def readFrameOfType (fd : UInt32) (want : Derp.FrameType) : Nat → IO (Option Derp.Frame)
  | 0 => return none
  | fuel + 1 => do
    match ← readFrame fd with
    | none => return none
    | some f =>
      if f.ftype = want then return some f
      else do
        IO.println s!"    (skipped {repr f.ftype} frame, {f.payload.length}B)"
        readFrameOfType fd want fuel

/-- The DERP HTTP Upgrade request (Derp-Fast-Start suppresses the HTTP response
so the relay begins the framed protocol immediately). -/
def upgradeRequest (host : String) : ByteArray :=
  ("GET /derp HTTP/1.1\r\nHost: " ++ host ++
   "\r\nUpgrade: DERP\r\nConnection: Upgrade\r\nDerp-Fast-Start: 1\r\n\r\n").toUTF8

/-- A fixed 24-byte nonce for the client's ClientInfo box (one box per key). -/
def clientNonce : ByteArray := ⟨Array.mkArray 24 (0x2a : UInt8)⟩

/-- Run the full DERP login handshake on a fresh connection for one client;
returns `(fd, serverPub, opened-ServerInfo-JSON)`. -/
def handshake (label host : String) (port : UInt16)
    (priv pub : ByteArray) : IO (Option (UInt32 × ByteArray × ByteArray)) := do
  let fd ← tcpConnect host port
  tcpSend fd (upgradeRequest host)
  IO.println s!"[{label}] -> sent DERP HTTP Upgrade to {host}:{port}"
  -- 1. FrameServerKey greeting
  match ← readFrameOfType fd Derp.FrameType.serverKey 8 with
  | none => IO.eprintln s!"[{label}] no FrameServerKey"; tcpClose fd; return none
  | some skf =>
    match Derp.parseServerKey skf.payload with
    | none => IO.eprintln s!"[{label}] bad FrameServerKey magic"; tcpClose fd; return none
    | some serverPubL =>
      let serverPub := Derp.baOf serverPubL
      IO.println s!"[{label}] <- FrameServerKey  relay pub : {toHex serverPub}"
      -- 2. seal + send FrameClientInfo (proven Derp.buildClientInfo)
      let info := "{\"version\":2}".toUTF8
      match Derp.buildClientInfo pub serverPub priv clientNonce info with
      | none => IO.eprintln s!"[{label}] buildClientInfo failed"; tcpClose fd; return none
      | some cif =>
        let cib := Derp.baOf (Derp.serializeFrame cif)
        tcpSend fd cib
        IO.println s!"[{label}] -> FrameClientInfo ({cib.size}B): {toHex cib}"
        -- 3. read + open FrameServerInfo (proven Derp.openServerInfo)
        match ← readFrameOfType fd Derp.FrameType.serverInfo 8 with
        | none => IO.eprintln s!"[{label}] no FrameServerInfo"; tcpClose fd; return none
        | some sif =>
          match Derp.openServerInfo serverPub priv sif.payload with
          | none =>
            IO.eprintln s!"[{label}] openServerInfo REJECTED (box did not open)"
            tcpClose fd; return none
          | some infoJson =>
            IO.println s!"[{label}] <- FrameServerInfo opened: {utf8OrHex (Derp.baOf infoJson)}"
            return some (fd, serverPub, Derp.baOf infoJson)

def main (args : List String) : IO UInt32 := do
  let host := args.getD 0 "127.0.0.1"
  let portS := args.getD 1 "3340"
  let some port := portS.toNat? | do IO.eprintln "bad port"; return 1
  -- Two distinct client static keys (curve25519 clamping not required for the box).
  let privA := ofHex (args.getD 2 "a01111111111111111111111111111111111111111111111111111111111111a")
  let privB := ofHex (args.getD 3 "b02222222222222222222222222222222222222222222222222222222222222b")
  let some pubA := x25519Base privA | do IO.eprintln "x25519Base(A) failed"; return 1
  let some pubB := x25519Base privB | do IO.eprintln "x25519Base(B) failed"; return 1
  IO.println s!"client A pub : {toHex pubA}"
  IO.println s!"client B pub : {toHex pubB}\n"

  IO.println "=== client B: DERP login handshake ==="
  match ← handshake "B" host port.toUInt16 privB pubB with
  | none => IO.eprintln "client B handshake failed"; return 1
  | some (fdB, _, _) =>
    IO.println "\n=== client A: DERP login handshake ==="
    match ← handshake "A" host port.toUInt16 privA pubA with
    | none => IO.eprintln "client A handshake failed"; tcpClose fdB; return 1
    | some (fdA, _, _) =>
      IO.println "\n=== relay a real frame: A -> (relay) -> B ==="
      -- Build FrameSendPacket: 32B dest pubkey (B) ++ packet.
      let packet := "hello-through-a-real-DERP-relay".toUTF8
      let sendFrame : Derp.Frame :=
        { ftype := .sendPacket, payload := Derp.bytesOf pubB ++ Derp.bytesOf packet }
      let sfb := Derp.baOf (Derp.serializeFrame sendFrame)
      tcpSend fdA sfb
      IO.println s!"[A] -> FrameSendPacket ({sfb.size}B) to B: {toHex sfb}"
      -- B reads until FrameRecvPacket.
      match ← readFrameOfType fdB Derp.FrameType.recvPacket 12 with
      | none =>
        IO.eprintln "[B] no FrameRecvPacket arrived"; tcpClose fdA; tcpClose fdB; return 1
      | some rf =>
        match Derp.splitKeyed rf.payload with
        | none =>
          IO.eprintln "[B] RecvPacket payload too short"; tcpClose fdA; tcpClose fdB; return 1
        | some (srcPub, relayed) =>
          IO.println s!"[B] <- FrameRecvPacket  src pub : {toHex (Derp.baOf srcPub)}"
          IO.println s!"[B]    relayed packet   : {utf8OrHex (Derp.baOf relayed)}"
          let okSrc := srcPub == Derp.bytesOf pubA
          let okPkt := relayed == Derp.bytesOf packet
          IO.println s!"\n    src == A pubkey  : {okSrc}"
          IO.println s!"    packet verbatim  : {okPkt}"
          tcpClose fdA; tcpClose fdB
          if okSrc ∧ okPkt then
            IO.println "\nRELAY COMPLETE — a real frame traversed a real DERP relay, A -> B."
            return 0
          else
            IO.eprintln "\nrelayed frame did not match"; return 1

end DerpLive

def main (args : List String) : IO UInt32 := DerpLive.main args
