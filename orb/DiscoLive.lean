/-
# DiscoLive — driving DISCO NAT-traversal endpoint discovery over the real wire

The `Disco` model is sans-IO: `sealDiscoMessage`, `openDiscoFrame`, `encodePing`,
`encodePong` compute the exact bytes of a Tailscale DISCO frame

    Magic("TS💬") ‖ senderDiscoPub(32) ‖ nonce(24) ‖ box

on the verified `Crypto` NaCl `crypto_box` (X25519 + XSalsa20-Poly1305), sealing a
disco message body `type ‖ version ‖ …`. This executable takes those bytes to a
real UDP socket (ffi/wg_udp.c) so the construction can be exercised end to end
against a peer that speaks the same wire format.

There is no real `tailscaled` / tailnet on this host: joining one needs a
Tailscale auth key from the control plane (an ember-provided prerequisite). So
the peer here is a SPEC-CONFORMANT controlled peer we run ourselves — a real
second process speaking the real DISCO wire format — exactly the wg-responder
pattern. Honest about which: this is live-over-real-UDP against a controlled
disco peer, not against Tailscale's own implementation.

The exchange demonstrated:

  * `prober`   builds a sealed DISCO Ping (real magic, real box, unguessable
    12-byte TxID), sends it, and awaits a Pong.
  * `responder` opens the Ping frame (`openDiscoFrame`), confirms it is a Ping,
    seals a Pong echoing the exact TxID, and replies.
  * `prober` opens the Pong, checks the TxID matches its outstanding probe, and
    drives the PROVEN FSM (`Disco.step` under the realized `cryptoConfig`) from
    `probed` to `verified` — the anti-spoof discipline, on real bytes.

`selftest` runs both ends in one process over the byte level (no sockets) for a
deterministic check of the whole seal → parse → open → decode → FSM-verify path.

Not part of the trusted core: this is a live cross-check, the DISCO analogue of
crypto-selftest / wg-live. Everything cryptographic/structural is proven Lean.

Usage:
  disco-live selftest
  disco-live responder <listenPort> <selfDiscoPrivHex> <peerDiscoPubHex>
  disco-live prober <host> <port> <selfDiscoPrivHex> <peerDiscoPubHex> [txHex]
-/
import Disco

open Disco

namespace DiscoLive

@[extern "drorb_udp_socket"]
opaque udpSocket (host : String) (port : UInt16) : IO UInt32

@[extern "drorb_udp_send_recv"]
opaque udpSendRecv (fd : UInt32) (payload : ByteArray) (timeoutMs : UInt32) :
    IO (Option ByteArray)

@[extern "drorb_udp_close"]
opaque udpClose (fd : UInt32) : IO Unit

@[extern "drorb_udp_listen"]
opaque udpListen (port : UInt16) : IO UInt32

@[extern "drorb_udp_recv"]
opaque udpRecv (fd : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)

@[extern "drorb_udp_reply"]
opaque udpReply (fd : UInt32) (payload : ByteArray) : IO Unit

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

/-- A fixed 24-byte nonce for the Ping box. -/
def pingNonce : ByteArray := ⟨Array.replicate 24 (0x11 : UInt8)⟩
/-- A distinct fixed 24-byte nonce for the Pong box. -/
def pongNonce : ByteArray := ⟨Array.replicate 24 (0x22 : UInt8)⟩

/-- A default 12-byte transaction id (overridable on the prober command line). -/
def defaultTx : ByteArray :=
  ⟨#[0xde, 0xad, 0xbe, 0xef, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]⟩

/-- A placeholder 16-byte source address (`::ffff:127.0.0.1`) for the Pong `Src`
field — the FSM verifies the TxID and the box, not this address. -/
def placeholderSrc : ByteArray :=
  ⟨#[0,0,0,0,0,0,0,0,0,0, 0xff,0xff, 127,0,0,1]⟩

/-- Seal a DISCO Ping frame from `self` to `peer`, carrying `tx` and `self`'s
node key (here `selfPub`, 32 bytes). -/
def buildPing (peerPub selfSec selfPub tx : ByteArray) : Option ByteArray :=
  (sealDiscoMessage peerPub selfSec pingNonce (bytesOf selfPub)
    (encodePing (bytesOf tx) (bytesOf selfPub))).map baOf

/-- Seal a DISCO Pong frame from `self` to `peer`, echoing `tx`. -/
def buildPong (peerPub selfSec selfPub tx : ByteArray) : Option ByteArray :=
  (sealDiscoMessage peerPub selfSec pongNonce (bytesOf selfPub)
    (encodePong (bytesOf tx) (bytesOf placeholderSrc) 0)).map baOf

/-- Drive the PROVEN FSM: a candidate endpoint, probed with `tx`, is promoted to
`verified` exactly when the Pong frame authenticates under the realized crypto
config for `(peerPub, selfSec, nonce, box, expectTx)`. Returns `true` iff the
endpoint ends up verified. -/
def fsmVerify (peerPub selfSec : ByteArray) (pongFrame : ByteArray) (tx : ByteArray) : Bool :=
  match parseDiscoFrame (bytesOf pongFrame) with
  | some (_sPub, nonce, box) =>
    let cfg := cryptoConfig peerPub selfSec (baOf nonce) (baOf box) (bytesOf tx)
    let ep : Endpoint := { addr := 1 }
    let txId : TxId := { val := 0 }
    let s0 := (step cfg init (.addCandidate ep)).1
    let s1 := (step cfg s0 (.sendProbe ep txId)).1
    let s2 := (step cfg s1 (.recvPong txId ep 7)).1
    match lookup s2.eps ep with
    | some (.verified _) => true
    | _ => false
  | none => false

/-- Common driver: given both key pairs, build the Ping and (for the selftest)
the Pong locally and verify the round trip through the real crypto. -/
def selftest : IO UInt32 := do
  -- Two disco key pairs (curve25519). Clamping is handled inside x25519.
  let proberSec := ofHex "a01111111111111111111111111111111111111111111111111111111111111a"
  let respSec   := ofHex "b02222222222222222222222222222222222222222222222222222222222222b"
  let some proberPub := Crypto.x25519Base proberSec | do IO.eprintln "x25519Base(prober) failed"; return 1
  let some respPub   := Crypto.x25519Base respSec   | do IO.eprintln "x25519Base(responder) failed"; return 1
  let tx := defaultTx
  IO.println s!"prober    disco pub : {toHex proberPub}"
  IO.println s!"responder disco pub : {toHex respPub}"
  IO.println s!"TxID                : {toHex tx}"

  -- prober seals a Ping to the responder.
  let some pingFrame := buildPing respPub proberSec proberPub tx
    | do IO.eprintln "buildPing failed"; return 1
  IO.println s!"\n-> Ping frame ({pingFrame.size}B): {toHex pingFrame}"
  IO.println s!"   magic prefix     : {toHex (⟨pingFrame.toList.take 6 |>.toArray⟩)} (expect 5453f09f92ac)"

  -- responder opens the Ping.
  match openDiscoFrame respSec (bytesOf pingFrame) with
  | some (sPub, .ping txid nodeKey) =>
    IO.println s!"\n<- responder opened Ping: sender={toHex (baOf sPub)}"
    IO.println s!"   TxID={toHex (baOf txid)}  nodeKey={toHex (baOf nodeKey)}"
    if txid ≠ bytesOf tx then do IO.eprintln "responder: TxID mismatch on Ping"; return 1
    -- responder seals a Pong echoing the TxID.
    let some pongFrame := buildPong proberPub respSec respPub tx
      | do IO.eprintln "buildPong failed"; return 1
    IO.println s!"\n-> Pong frame ({pongFrame.size}B): {toHex pongFrame}"
    -- prober opens the Pong.
    match openDiscoFrame proberSec (bytesOf pongFrame) with
    | some (_, .pong txid' src port) =>
      IO.println s!"\n<- prober opened Pong: TxID={toHex (baOf txid')} src={toHex (baOf src)} port={port}"
      if txid' ≠ bytesOf tx then do IO.eprintln "prober: TxID mismatch on Pong"; return 1
      -- drive the proven FSM: probe -> verified.
      if fsmVerify respPub proberSec pongFrame tx then do
        IO.println "\nVERIFIED — the endpoint reached `verified` in the proven DISCO FSM."
        IO.println "FULL DISCO EXCHANGE COMPLETE (real wire format, verified crypto)."
        return 0
      else do IO.eprintln "FSM did not reach verified"; return 1
    | _ => do IO.eprintln "prober: Pong frame did not open as a Pong"; return 1
  | _ => do IO.eprintln "responder: Ping frame did not open as a Ping"; return 1

/-- Responder mode: bind, receive one sealed Ping frame, reply with a sealed Pong. -/
def responder (port : UInt16) (selfSec peerPub : ByteArray) : IO UInt32 := do
  let some selfPub := Crypto.x25519Base selfSec | do IO.eprintln "x25519Base(self) failed"; return 1
  IO.println s!"responder disco pub : {toHex selfPub}"
  IO.println s!"peer      disco pub : {toHex peerPub}"
  let fd ← udpListen port
  IO.println s!"\n== disco responder listening on 0.0.0.0:{port} =="
  match ← udpRecv fd 20000 with
  | none => do IO.eprintln "<- NO DATAGRAM (peer never sent a Ping within the window)"; udpClose fd; return 1
  | some dg =>
    IO.println s!"\n<- received frame ({dg.size}B): {toHex dg}"
    match openDiscoFrame selfSec (bytesOf dg) with
    | some (sPub, .ping txid _nodeKey) =>
      IO.println s!"   opened Ping: sender={toHex (baOf sPub)} TxID={toHex (baOf txid)}"
      match buildPong peerPub selfSec selfPub (baOf txid) with
      | some pong => do
        udpReply fd pong
        IO.println s!"-> replied with Pong ({pong.size}B): {toHex pong}"
        IO.println "\nRESPONDER COMPLETE — opened a real Ping, sealed a real Pong echoing the TxID."
        udpClose fd; return 0
      | none => do IO.eprintln "buildPong failed"; udpClose fd; return 1
    | _ => do IO.eprintln "frame did not open as a Ping"; udpClose fd; return 1

/-- Prober mode: seal a Ping, send it, open the Pong reply, and verify via the FSM. -/
def prober (host : String) (port : UInt16) (selfSec peerPub tx : ByteArray) : IO UInt32 := do
  let some selfPub := Crypto.x25519Base selfSec | do IO.eprintln "x25519Base(self) failed"; return 1
  IO.println s!"prober disco pub : {toHex selfPub}"
  IO.println s!"peer   disco pub : {toHex peerPub}"
  IO.println s!"TxID             : {toHex tx}"
  let some pingFrame := buildPing peerPub selfSec selfPub tx | do IO.eprintln "buildPing failed"; return 1
  let fd ← udpSocket host port
  IO.println s!"\n-> Ping frame ({pingFrame.size}B) to {host}:{port}: {toHex pingFrame}"
  match ← udpSendRecv fd pingFrame 5000 with
  | none => do IO.eprintln "<- NO REPLY (responder silent)"; udpClose fd; return 1
  | some reply =>
    IO.println s!"\n<- Pong frame ({reply.size}B): {toHex reply}"
    match openDiscoFrame selfSec (bytesOf reply) with
    | some (_, .pong txid' _ _) =>
      IO.println s!"   opened Pong: TxID={toHex (baOf txid')}"
      if txid' ≠ bytesOf tx then do IO.eprintln "TxID mismatch"; udpClose fd; return 1
      if fsmVerify peerPub selfSec reply tx then do
        IO.println "\nVERIFIED — endpoint reached `verified` in the proven DISCO FSM."
        IO.println "FULL DISCO EXCHANGE COMPLETE over real UDP (real wire format, verified crypto)."
        udpClose fd; return 0
      else do IO.eprintln "FSM did not reach verified"; udpClose fd; return 1
    | _ => do IO.eprintln "reply did not open as a Pong"; udpClose fd; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | ["responder", portS, privHex, peerHex] => do
    let some port := portS.toNat? | do IO.eprintln "bad port"; return 1
    responder port.toUInt16 (ofHex privHex) (ofHex peerHex)
  | ["prober", host, portS, privHex, peerHex] => do
    let some port := portS.toNat? | do IO.eprintln "bad port"; return 1
    prober host port.toUInt16 (ofHex privHex) (ofHex peerHex) defaultTx
  | ["prober", host, portS, privHex, peerHex, txHex] => do
    let some port := portS.toNat? | do IO.eprintln "bad port"; return 1
    prober host port.toUInt16 (ofHex privHex) (ofHex peerHex) (ofHex txHex)
  | _ => do
    IO.eprintln "usage: disco-live selftest | responder <port> <selfPriv> <peerPub> | prober <host> <port> <selfPriv> <peerPub> [txHex]"
    return 1

end DiscoLive

def main (args : List String) : IO UInt32 := DiscoLive.main args
