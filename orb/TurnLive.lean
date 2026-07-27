/-
# TurnLive — driving the PROVEN TURN relay over the byte level

The `Turn` foundation models a TURN relay (RFC 8656) as sans-IO, proven Lean: the
STUN/TURN wire codec (`allocateRequestMsg`, `createPermissionRequestMsg`,
`channelBindRequestMsg`, `sendIndicationMsg`, `channelData`, with their
round-trip lemmas over the `Stun` parser), the allocation transition system
(`allocate` / `createPermission` / `channelBind` / `refresh`), and the
default-deny relay decisions (`relayOutbound` / `relayInbound` / `channelSend`)
with the security theorems (`turn_relay_needs_permission`,
`turn_channel_binds_peer`, `turn_alloc_expires`).

None of that logic was wired into a running binary. This executable is that
wiring: a `selftest` that drives a **relay server** and a **client** over the
byte level in one process (no sockets), so the whole proven relay pipeline is
EXERCISED end to end:

  1. the client builds an ALLOCATE request (`allocateRequestMsg`); the server
     parses it (`Stun.parse`), reads REQUESTED-TRANSPORT + LIFETIME, and runs
     `allocate` — a fresh allocation permits no one (default-deny);
  2. the client builds a CREATE-PERMISSION request for peer A only
     (`createPermissionRequestMsg`); the server parses it, decodes the
     XOR-PEER-ADDRESS (`decodeXorMapped`), and runs `createPermission`;
  3. the client emits SEND indications (`sendIndicationMsg`); the server decodes
     the peer + DATA off the wire and runs `relayOutbound` — the permitted peer A
     is relayed the verbatim payload; the *unpermitted* peer B is DROPPED (no
     leak — the anti-reflector discipline);
  4. inbound from A resolves to a Data indication; inbound from B drops;
  5. the client CHANNEL-BINDs peer B (`channelBindRequestMsg`); a ChannelData
     frame on the bound channel routes to exactly B (`channelSend`);
  6. it prints each relay decision and a PASS/FAIL cross-check against the model —
     the realization of `turn_relay_faithful`.

## Honesty / realization boundary (the ControlLive / DiscoLive discipline)

This is **drorb-native**: the client and relay are our own spec-conformant peers
speaking the modelled RFC 8656 wire format over the byte level in one process —
NOT a real UDP interop against a third-party TURN client/server (which
additionally needs the MD5 long-term-credential key derivation, named as a
follow-on in `Turn.lean §Message integrity`, and a real UDP three-party
topology; the named residual below). Like ControlLive / DiscoLive this is a live
cross-check, not part of the trusted core: everything structural/codec/relay is
the proven Lean. The gap the selftest discharges (by construction, not by proof)
is that this exe faithfully CALLS the proven Lean functions on real bytes; the
faithfulness of the decode→relay chain ITSELF is proven below as
`turn_relay_faithful`.

Usage:
  turn-live selftest
-/
import Turn

namespace TurnLive

open Stun (Bytes Endpoint Attr Message)
open Turn

/-! ## The decode→relay faithfulness theorem

The running loop's decode→relay chain applies EXACTLY the proven relay decision.
Given a peer transport address carried in a SEND indication's XOR-PEER-ADDRESS
(the exact wire form the client emits with `sendIndicationMsg`), the server's
`decodeXorMapped` recovers PRECISELY that peer (`xorPeer_roundtrip`, itself the
STUN `xorMapped_roundtrip`), and — for a live allocation that has a permission
for the peer's IP — `relayOutbound` delivers the verbatim payload to exactly that
peer, and to NO other. The "no leak" clause is universally quantified: any peer
whose IP is *not* permitted is dropped in the same state, so the relay never
forwards to an unpermitted address — the anti-reflector discipline realized on
the bytes on the wire.

Not a `P → P`: the hypotheses are the satisfiable well-formedness of the peer
address (family/length, port < 2^16, 12-byte txid) plus a live, permitted
allocation (the selftest below inhabits exactly this state); the conclusions are
concrete equalities about `decodeXorMapped` and `relayOutbound`'s outputs, and
the negative clause forbids delivery to every unpermitted peer. It composes the
proven codec round-trip (`xorPeer_roundtrip`) with the proven relay decisions
(`relayOutbound`, `turn_relay_needs_permission`). -/
theorem turn_relay_faithful
    (s : TurnState) (ft : FiveTuple) (a : Allocation)
    (txid : Bytes) (ep : Endpoint) (payload : Bytes) (now : Nat)
    (htx : txid.length = 12) (hport : ep.port < 65536)
    (hfam : (ep.family = 1 ∧ ep.addr.length = 4) ∨ (ep.family = 2 ∧ ep.addr.length = 16))
    (hlook : s.lookup ft = some a) (hlive : now < a.expiry)
    (hperm : hasPermission a ep.addr = true) :
    -- the peer decoded off the wire is exactly `ep`
    Stun.decodeXorMapped txid (xorPeerAttr txid ep).value = some ep
    -- and relaying to it delivers the verbatim payload to exactly that permitted peer
    ∧ relayOutbound s ft ep payload now = some (ep, payload)
    -- and NO unpermitted peer is ever relayed (no leak / anti-reflector)
    ∧ (∀ (ep' : Endpoint) (pl' : Bytes),
        hasPermission a ep'.addr = false → relayOutbound s ft ep' pl' now = none) := by
  refine ⟨xorPeer_roundtrip txid ep htx hport hfam, ?_, ?_⟩
  · have hd : decide (now < a.expiry) = true := decide_eq_true hlive
    simp [relayOutbound, hlook, hd, hperm]
  · intro ep' pl' hp'
    exact turn_relay_needs_permission s ft a ep' pl' now hlook hp'

#print axioms turn_relay_faithful

/-! ## Byte helpers (mirrors ControlLive/DiscoLive) -/

def toHex (b : Bytes) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def ipStr (b : Bytes) : String := ".".intercalate (b.map (fun x => toString x.toNat))

/-- Find the first attribute of a given type in a parsed message. -/
def findAttr (m : Message) (ty : Nat) : Option Bytes :=
  (m.attrs.find? (fun a => decide (a.type = ty))).map (·.value)

/-! ## The relay server: decode a parsed TURN message, drive the proven transition -/

/-- A fixed 12-byte STUN transaction id for this drorb-native test. -/
def txid0 : Bytes := (List.range 12).map (fun i => UInt8.ofNat (0xA0 + i))

/-! ## The selftest — client + relay over the byte level, one process -/

def selftest : IO UInt32 := do
  IO.println "== turn-live selftest : RFC 8656 relay, byte-level, client + server =="

  -- The client 5-tuple and two peers (the drorb-native test topology).
  let epClient : Endpoint := { family := 1, port := 51000, addr := [10, 0, 0, 1] }
  let epServer : Endpoint := { family := 1, port := 3478, addr := [10, 0, 0, 254] }
  let epRelay  : Endpoint := { family := 1, port := 49152, addr := [203, 0, 113, 7] }
  let epPeerA  : Endpoint := { family := 1, port := 6000, addr := [198, 51, 100, 20] }
  let epPeerB  : Endpoint := { family := 1, port := 7000, addr := [198, 51, 100, 99] }
  let ft : FiveTuple := { client := epClient, server := epServer, proto := protoUDP }
  let payload : Bytes := [0xDE, 0xAD, 0xBE, 0xEF]

  -- ── 1. ALLOCATE : client builds the request bytes; server parses + allocates ──
  let allocBytes := allocateRequestMsg txid0 protoUDP 600
  let some allocMsg := Stun.parse allocBytes
    | do IO.eprintln "server: could not parse ALLOCATE request"; return 1
  let some rtVal := findAttr allocMsg attrRequestedTransport
    | do IO.eprintln "server: ALLOCATE missing REQUESTED-TRANSPORT"; return 1
  let some proto := decodeRequestedTransport rtVal
    | do IO.eprintln "server: bad REQUESTED-TRANSPORT"; return 1
  let some ltVal := findAttr allocMsg attrLifetime
    | do IO.eprintln "server: ALLOCATE missing LIFETIME"; return 1
  let some lifetime := decodeLifetime ltVal
    | do IO.eprintln "server: bad LIFETIME"; return 1
  IO.println s!"\n-- allocate --"
  IO.println s!"client -> ALLOCATE ({allocBytes.length}B): proto={proto} (UDP={proto == protoUDP}), lifetime={lifetime}s"
  let s0 := allocate TurnState.empty ft epRelay 0 lifetime
  let some a0 := s0.lookup ft
    | do IO.eprintln "server: allocation missing after allocate"; return 1
  IO.println s!"server: allocated relay={ipStr epRelay.addr}:{epRelay.port}, expiry={a0.expiry}, perms={a0.perms.length} (default-deny)"

  -- fresh allocation relays to NO ONE
  let freshDrop := relayOutbound s0 ft epPeerA payload 5 == none
  IO.println s!"server: fresh allocation, relayOutbound to A = drop : {freshDrop}"

  -- ── 2. CREATE-PERMISSION for peer A only : client bytes -> server installs ──
  let permBytes := createPermissionRequestMsg txid0 [epPeerA]
  let some permMsg := Stun.parse permBytes
    | do IO.eprintln "server: could not parse CREATE-PERMISSION"; return 1
  let some peerVal := findAttr permMsg attrXorPeerAddress
    | do IO.eprintln "server: CREATE-PERMISSION missing XOR-PEER-ADDRESS"; return 1
  let some permPeer := Stun.decodeXorMapped txid0 peerVal
    | do IO.eprintln "server: bad XOR-PEER-ADDRESS"; return 1
  let permOk := permPeer == epPeerA
  IO.println s!"\n-- create-permission --"
  IO.println s!"client -> CREATE-PERMISSION ({permBytes.length}B) for {ipStr permPeer.addr}, decoded == sent : {permOk}"
  if !permOk then do IO.eprintln "server: permitted peer did not round-trip"; return 1
  let s1 := createPermission s0 ft permPeer.addr
  let some a1 := s1.lookup ft
    | do IO.eprintln "server: allocation missing after permission"; return 1
  IO.println s!"server: permission installed; perms now = {a1.perms.map ipStr}"

  -- ── 3. SEND indications : permitted A relayed, unpermitted B dropped (no leak) ──
  let sendA := sendIndicationMsg txid0 epPeerA payload
  let some sendMsgA := Stun.parse sendA
    | do IO.eprintln "server: could not parse SEND(A)"; return 1
  let some peerAVal := findAttr sendMsgA attrXorPeerAddress
    | do IO.eprintln "server: SEND(A) missing XOR-PEER-ADDRESS"; return 1
  let some dataAVal := findAttr sendMsgA attrData
    | do IO.eprintln "server: SEND(A) missing DATA"; return 1
  let some sendPeerA := Stun.decodeXorMapped txid0 peerAVal
    | do IO.eprintln "server: bad SEND(A) peer"; return 1
  let outA := relayOutbound s1 ft sendPeerA dataAVal 5
  let outB := relayOutbound s1 ft epPeerB dataAVal 5
  IO.println s!"\n-- outbound relay (client -> peer) --"
  match outA with
  | some (dst, pl) =>
    IO.println s!"SEND to A permitted  -> relay to {ipStr dst.addr}:{dst.port}, payload={toHex pl} (verbatim={pl == payload})"
  | none => IO.println "SEND to A permitted  -> DROP (UNEXPECTED)"
  match outB with
  | some (dst, _) => IO.println s!"SEND to B unpermitted -> relay to {ipStr dst.addr} (LEAK — UNEXPECTED)"
  | none => IO.println "SEND to B unpermitted -> DROP (no leak, default-deny)"

  let aRelayed := outA == some (epPeerA, payload)
  let bDropped := outB == none

  -- ── 4. inbound relay : A -> Data indication, B -> drop ──
  let inA := relayInbound s1 ft epPeerA payload 5
  let inB := relayInbound s1 ft epPeerB payload 5
  IO.println s!"\n-- inbound relay (peer -> client) --"
  IO.println s!"inbound from A -> {repr inA}"
  IO.println s!"inbound from B -> {repr inB}"
  let inAok := inA == Inbound.dataInd epPeerA payload
  let inBok := inB == Inbound.drop

  -- ── 5. CHANNEL-BIND peer B : channel frame routes to exactly B ──
  let ch : Nat := 0x4001
  let bindBytes := channelBindRequestMsg txid0 ch epPeerB
  let some bindMsg := Stun.parse bindBytes
    | do IO.eprintln "server: could not parse CHANNEL-BIND"; return 1
  let some chVal := findAttr bindMsg attrChannelNumber
    | do IO.eprintln "server: CHANNEL-BIND missing CHANNEL-NUMBER"; return 1
  let some chNum := decodeChannelNumber chVal
    | do IO.eprintln "server: bad CHANNEL-NUMBER"; return 1
  let some bpeerVal := findAttr bindMsg attrXorPeerAddress
    | do IO.eprintln "server: CHANNEL-BIND missing XOR-PEER-ADDRESS"; return 1
  let some bindPeer := Stun.decodeXorMapped txid0 bpeerVal
    | do IO.eprintln "server: bad CHANNEL-BIND peer"; return 1
  IO.println s!"\n-- channel-bind --"
  IO.println s!"client -> CHANNEL-BIND ({bindBytes.length}B): ch=0x{Nat.toDigits 16 chNum |>.asString} valid={channelNumberValid chNum}, peer={ipStr bindPeer.addr}"
  let s2 := channelBind s1 ft chNum bindPeer
  -- a ChannelData frame on the bound channel routes to exactly B
  let cdFrame := channelData chNum payload
  let cdOut := channelSend s2 ft cdFrame 5
  match cdOut with
  | some (dst, pl) =>
    IO.println s!"ChannelData on 0x{Nat.toDigits 16 chNum |>.asString} -> routes to {ipStr dst.addr}:{dst.port}, payload={toHex pl}"
  | none => IO.println "ChannelData -> DROP (UNEXPECTED)"
  let cdOk := cdOut == some (epPeerB, payload)
  -- B is now reachable inbound as ChannelData
  let inBchan := relayInbound s2 ft epPeerB payload 5 == Inbound.channelData chNum payload

  -- ── 6. faithfulness cross-check (realizes turn_relay_faithful) ──
  IO.println "\n-- cross-check (realizes turn_relay_faithful) --"
  IO.println s!"fresh allocation drops (default-deny)      : {freshDrop}"
  IO.println s!"permitted A -> verbatim payload to exactly A: {aRelayed}"
  IO.println s!"unpermitted B -> dropped (no leak)          : {bDropped}"
  IO.println s!"inbound A = Data indication                 : {inAok}"
  IO.println s!"inbound B = drop                            : {inBok}"
  IO.println s!"ChannelData routes to exactly bound peer B  : {cdOk}"
  IO.println s!"inbound B (post-bind) = ChannelData         : {inBchan}"

  if freshDrop && permOk && aRelayed && bDropped && inAok && inBok && cdOk && inBchan then do
    IO.println "\nPASS — allocate, permit-A, relay-A / drop-B, channel-bind-B, channel-route-B;"
    IO.println "       the decode→relay chain equals the proven default-deny model decision."
    IO.println "FULL TURN RELAY EXCHANGE COMPLETE (drorb-native, byte-level, no leak)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the TURN relay pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do IO.eprintln "usage: turn-live selftest"; return 1

end TurnLive

def main (args : List String) : IO UInt32 := TurnLive.main args
