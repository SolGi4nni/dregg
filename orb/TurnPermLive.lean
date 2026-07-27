/-
# TurnPermLive — driving the PROVEN TURN permission + channel-bind grants over bytes

`TurnLive` wired the ALLOCATE half of the RFC 8656 relay: a fresh allocation
permits no one (default-deny), and `turn_relay_faithful` cross-checked the
outbound decode→relay chain *given* an already-permitted state as a hypothesis.

This lane wires the transitions that GRANT the permission in the first place —
`createPermission` (§9/§10) and `channelBind` (§11/§12) — driven off the wire,
and proves that installing a grant is exactly what makes a peer relayable while
every un-granted peer stays dropped (relay only to permitted peers). The
security posture of TURN is a *default-deny relay* (RFC 8656 §3.3): the server
forwards a datagram to a peer only if the client first installed a permission or
a channel binding for that peer; without that discipline a TURN server is an open
reflector/amplifier (§21.1.3, §21.2.1).

The `selftest` runs a relay server and a client over the byte level in ONE
process (no sockets), exercising the grant pipeline end to end:

  1. ALLOCATE (client bytes → server `allocate`): a fresh allocation permits no
     one; `relayOutbound` to any peer drops (default-deny);
  2. CREATE-PERMISSION for peer A only (client `createPermissionRequestMsg` →
     server decodes XOR-PEER-ADDRESS with `decodeXorMapped`, runs
     `createPermission`): peer A becomes relayable with the verbatim payload;
     peer B — never permitted — is still DROPPED (no leak);
  3. CHANNEL-BIND peer B (client `channelBindRequestMsg` → server decodes
     CHANNEL-NUMBER + XOR-PEER-ADDRESS, runs `channelBind`, which per §11.9 also
     installs a permission for B): a ChannelData frame on the bound channel
     routes to exactly B, and B is now reachable inbound as ChannelData;
  4. it prints each grant decision and a PASS/FAIL cross-check against the model —
     the realization of `turn_perm_faithful` and `turn_channel_bind_faithful`.

## Honesty / realization boundary (the ControlLive / DnsResolveLive discipline)

This is **drorb-native**: the client and relay are our own spec-conformant peers
speaking the modelled RFC 8656 wire format over the byte level in one process —
NOT a real UDP interop against a third-party TURN client/server (which
additionally needs the MD5 long-term-credential key derivation, named as a
follow-on in `Turn.lean §Message integrity`, and a real three-party UDP
topology; the named residual below). Like ControlLive / DnsResolveLive this is a
live cross-check, not part of the trusted core: everything structural/codec/relay
is the proven Lean. The selftest calls the proven Lean functions on real bytes;
the faithfulness of the decode→grant→relay chain ITSELF is proven below as
`turn_perm_faithful` (create-permission) and `turn_channel_bind_faithful`
(channel-bind). No MESSAGE-INTEGRITY is exercised here, so the selftest runs
under the Lean interpreter (`lean --run`) with no linked crypto.

Usage:
  turn-perm-live selftest
-/
import Turn

namespace TurnPermLive

open Stun (Bytes Endpoint Attr Message)
open Turn

/-! ## The create-permission faithfulness theorem

Driving `createPermission` off the wire is exactly what turns a peer from
dropped to relayable, while leaving every un-granted peer dropped. Given a live
allocation `a` for the 5-tuple `ft` and a peer `ep` whose XOR-PEER-ADDRESS is
carried in the CREATE-PERMISSION request (the exact wire form the client emits
with `createPermissionRequestMsg`), the server's `decodeXorMapped` recovers
PRECISELY `ep` (`xorPeer_roundtrip`), and after `createPermission` installs the
permission:

* the resulting allocation `a1` is exactly `a` with `ep.addr` in its permission
  set (`s1.lookup ft = some a1`);
* `ep` is now permitted (`hasPermission a1 ep.addr = true`), so `relayOutbound`
  delivers the verbatim payload to exactly `ep`;
* and — the anti-reflector clause — EVERY peer that is still not in `a1.perms`
  is dropped (`relayOutbound … = none`): relay only to permitted peers.

Not a `P → P`: the hypotheses are the satisfiable well-formedness of the peer
address (family/length, port < 2^16, 12-byte txid) plus a live allocation; the
conclusions are concrete equalities about the post-grant state, the positive
relay, and a universally-quantified negative that forbids delivery to every
un-permitted peer. It composes the proven codec round-trip (`xorPeer_roundtrip`)
with the proven grant/relay decisions (`createPermission`, `lookup_insert`,
`turn_relay_needs_permission`). -/
theorem turn_perm_faithful
    (s : TurnState) (ft : FiveTuple) (a : Allocation)
    (txid : Bytes) (ep : Endpoint) (payload : Bytes) (now : Nat)
    (htx : txid.length = 12) (hport : ep.port < 65536)
    (hfam : (ep.family = 1 ∧ ep.addr.length = 4) ∨ (ep.family = 2 ∧ ep.addr.length = 16))
    (hlook : s.lookup ft = some a) (hlive : now < a.expiry) :
    let a1 : Allocation :=
      { a with perms := if a.perms.contains ep.addr then a.perms else ep.addr :: a.perms }
    -- the permitted peer decoded off the wire is exactly `ep`
    Stun.decodeXorMapped txid (xorPeerAttr txid ep).value = some ep
    -- installing the permission yields exactly `a1`
    ∧ (createPermission s ft ep.addr).lookup ft = some a1
    -- and `ep` is now permitted, so relaying to it delivers the verbatim payload
    ∧ hasPermission a1 ep.addr = true
    ∧ relayOutbound (createPermission s ft ep.addr) ft ep payload now = some (ep, payload)
    -- and EVERY peer still not permitted is dropped (relay only to permitted peers)
    ∧ (∀ (ep' : Endpoint) (pl' : Bytes),
        hasPermission a1 ep'.addr = false →
        relayOutbound (createPermission s ft ep.addr) ft ep' pl' now = none) := by
  intro a1
  have hl1 : (createPermission s ft ep.addr).lookup ft = some a1 := by
    simp only [createPermission, hlook]; exact lookup_insert _ _ _
  have hperm1 : hasPermission a1 ep.addr = true := by
    simp only [a1, hasPermission]
    by_cases hc : a.perms.contains ep.addr = true
    · rw [if_pos hc]; exact hc
    · rw [if_neg hc]; simp [List.contains_cons]
  refine ⟨xorPeer_roundtrip txid ep htx hport hfam, hl1, hperm1, ?_, ?_⟩
  · have hd : decide (now < a1.expiry) = true := decide_eq_true hlive
    simp [relayOutbound, hl1, hd, hperm1]
  · intro ep' pl' hp'
    exact turn_relay_needs_permission _ ft a1 ep' pl' now hl1 hp'

#print axioms turn_perm_faithful

/-! ## The channel-bind faithfulness theorem

`channelBind` (§11) is the second grant path: it binds a channel number to a
peer and (per §11.9) installs a permission for that peer's IP. Driven off the
wire (CHANNEL-NUMBER + XOR-PEER-ADDRESS in `channelBindRequestMsg`), after the
bind the resulting allocation `a2` binds the channel to exactly `peer`, permits
`peer.addr`, and a ChannelData frame on that channel routes to exactly `peer`
while the allocation is live.

Not a `P → P`: the hypotheses are a live allocation plus the satisfiable size
bounds on the channel number and payload; the conclusions are concrete equalities
about the post-bind channel binding, the installed permission, and the
`channelSend` route. It composes `lookup_insert`, `channelData_roundtrip`, and
`channelSend_channelData`. -/
theorem turn_channel_bind_faithful
    (s : TurnState) (ft : FiveTuple) (a : Allocation)
    (ch : Nat) (peer : Endpoint) (payload : Bytes) (now : Nat)
    (hch : ch < 65536) (hlen : payload.length < 65536)
    (hlook : s.lookup ft = some a) (hlive : now < a.expiry) :
    let a2 : Allocation :=
      { a with
        perms := if a.perms.contains peer.addr then a.perms else peer.addr :: a.perms,
        channels := (ch, peer) ::
          a.channels.filter (fun p => decide (p.1 ≠ ch) && decide (p.2 ≠ peer)) }
    (channelBind s ft ch peer).lookup ft = some a2
    ∧ channelPeer a2 ch = some peer
    ∧ hasPermission a2 peer.addr = true
    ∧ channelSend (channelBind s ft ch peer) ft (channelData ch payload) now
        = some (peer, payload) := by
  intro a2
  have hl2 : (channelBind s ft ch peer).lookup ft = some a2 := by
    simp only [channelBind, hlook]; exact lookup_insert _ _ _
  have hbound : channelPeer a2 ch = some peer := by
    simp [a2, channelPeer, List.find?_cons]
  have hperm2 : hasPermission a2 peer.addr = true := by
    simp only [a2, hasPermission]
    by_cases hc : a.perms.contains peer.addr = true
    · rw [if_pos hc]; exact hc
    · rw [if_neg hc]; simp [List.contains_cons]
  refine ⟨hl2, hbound, hperm2, ?_⟩
  exact channelSend_channelData _ ft a2 ch peer payload now hl2 hlive hbound hch hlen

#print axioms turn_channel_bind_faithful

/-! ## Byte helpers (mirrors TurnLive/ControlLive) -/

def toHex (b : Bytes) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def ipStr (b : Bytes) : String := ".".intercalate (b.map (fun x => toString x.toNat))

/-- Find the first attribute of a given type in a parsed message. -/
def findAttr (m : Message) (ty : Nat) : Option Bytes :=
  (m.attrs.find? (fun a => decide (a.type = ty))).map (·.value)

/-- A fixed 12-byte STUN transaction id for this drorb-native test. -/
def txid0 : Bytes := (List.range 12).map (fun i => UInt8.ofNat (0xB0 + i))

/-! ## The selftest — client + relay over the byte level, one process -/

def selftest : IO UInt32 := do
  IO.println "== turn-perm-live selftest : RFC 8656 grants (permission + channel-bind), byte-level =="

  -- The client 5-tuple, the relayed address, and two peers (drorb-native topology).
  let epClient : Endpoint := { family := 1, port := 51000, addr := [10, 0, 0, 1] }
  let epServer : Endpoint := { family := 1, port := 3478, addr := [10, 0, 0, 254] }
  let epRelay  : Endpoint := { family := 1, port := 49152, addr := [203, 0, 113, 7] }
  let epPeerA  : Endpoint := { family := 1, port := 6000, addr := [198, 51, 100, 20] }
  let epPeerB  : Endpoint := { family := 1, port := 7000, addr := [198, 51, 100, 99] }
  let ft : FiveTuple := { client := epClient, server := epServer, proto := protoUDP }
  let payload : Bytes := [0xC0, 0xFF, 0xEE, 0x00]

  -- ── 1. ALLOCATE : client builds the request bytes; server parses + allocates ──
  let allocBytes := allocateRequestMsg txid0 protoUDP 600
  let some allocMsg := Stun.parse allocBytes
    | do IO.eprintln "server: could not parse ALLOCATE request"; return 1
  let some rtVal := findAttr allocMsg attrRequestedTransport
    | do IO.eprintln "server: ALLOCATE missing REQUESTED-TRANSPORT"; return 1
  let some proto := decodeRequestedTransport rtVal
    | do IO.eprintln "server: bad REQUESTED-TRANSPORT"; return 1
  IO.println s!"\n-- allocate --"
  IO.println s!"client -> ALLOCATE ({allocBytes.length}B): proto={proto} (UDP={proto == protoUDP})"
  let s0 := allocate TurnState.empty ft epRelay 0 600
  let some a0 := s0.lookup ft
    | do IO.eprintln "server: allocation missing after allocate"; return 1
  IO.println s!"server: allocated relay={ipStr epRelay.addr}:{epRelay.port}, expiry={a0.expiry}, perms={a0.perms.length} (default-deny)"

  -- fresh allocation relays to NO ONE (neither A nor B)
  let freshDropA := relayOutbound s0 ft epPeerA payload 5 == none
  let freshDropB := relayOutbound s0 ft epPeerB payload 5 == none
  IO.println s!"server: fresh allocation, relayOutbound A/B = drop/drop : {freshDropA}/{freshDropB}"

  -- ── 2. CREATE-PERMISSION for peer A only : client bytes -> server installs ──
  let permBytes := createPermissionRequestMsg txid0 [epPeerA]
  let some permMsg := Stun.parse permBytes
    | do IO.eprintln "server: could not parse CREATE-PERMISSION"; return 1
  let some peerVal := findAttr permMsg attrXorPeerAddress
    | do IO.eprintln "server: CREATE-PERMISSION missing XOR-PEER-ADDRESS"; return 1
  let some permPeer := Stun.decodeXorMapped txid0 peerVal
    | do IO.eprintln "server: bad XOR-PEER-ADDRESS"; return 1
  let permDecodeOk := permPeer == epPeerA
  IO.println s!"\n-- create-permission (grant for A only) --"
  IO.println s!"client -> CREATE-PERMISSION ({permBytes.length}B) for {ipStr permPeer.addr}, decoded == sent : {permDecodeOk}"
  if !permDecodeOk then do IO.eprintln "server: permitted peer did not round-trip"; return 1
  let s1 := createPermission s0 ft permPeer.addr
  let some a1 := s1.lookup ft
    | do IO.eprintln "server: allocation missing after permission"; return 1
  IO.println s!"server: permission installed; perms now = {a1.perms.map ipStr}"

  -- A becomes relayable with the verbatim payload; B (un-granted) still drops.
  let outA := relayOutbound s1 ft epPeerA payload 5
  let outB := relayOutbound s1 ft epPeerB payload 5
  IO.println s!"\n-- relay after permission (relay only to permitted) --"
  match outA with
  | some (dst, pl) =>
    IO.println s!"A permitted   -> relay to {ipStr dst.addr}:{dst.port}, payload={toHex pl} (verbatim={pl == payload})"
  | none => IO.println "A permitted   -> DROP (UNEXPECTED)"
  match outB with
  | some (dst, _) => IO.println s!"B un-granted  -> relay to {ipStr dst.addr} (LEAK — UNEXPECTED)"
  | none => IO.println "B un-granted  -> DROP (no leak, default-deny)"
  let aGranted := outA == some (epPeerA, payload)
  let bStillDrop := outB == none
  let aPermitted := hasPermission a1 epPeerA.addr
  let bUnpermitted := hasPermission a1 epPeerB.addr == false

  -- ── 3. CHANNEL-BIND peer B : the second grant path (§11, also permits B) ──
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
  IO.println s!"\n-- channel-bind (grant for B) --"
  IO.println s!"client -> CHANNEL-BIND ({bindBytes.length}B): ch=0x{Nat.toDigits 16 chNum |>.asString} valid={channelNumberValid chNum}, peer={ipStr bindPeer.addr}"
  let s2 := channelBind s1 ft chNum bindPeer
  let some a2 := s2.lookup ft
    | do IO.eprintln "server: allocation missing after channel-bind"; return 1
  IO.println s!"server: channel bound; perms now = {a2.perms.map ipStr}, channels = {a2.channels.length}"

  -- a ChannelData frame on the bound channel routes to exactly B
  let cdFrame := channelData chNum payload
  let cdOut := channelSend s2 ft cdFrame 5
  match cdOut with
  | some (dst, pl) =>
    IO.println s!"ChannelData on 0x{Nat.toDigits 16 chNum |>.asString} -> routes to {ipStr dst.addr}:{dst.port}, payload={toHex pl}"
  | none => IO.println "ChannelData -> DROP (UNEXPECTED)"
  let cdOk := cdOut == some (epPeerB, payload)
  let bBoundPermitted := hasPermission a2 epPeerB.addr
  -- B is now reachable inbound as ChannelData; A still via its permission
  let inBchan := relayInbound s2 ft epPeerB payload 5 == Inbound.channelData chNum payload
  let inAdata := relayInbound s2 ft epPeerA payload 5 == Inbound.dataInd epPeerA payload

  -- ── 4. faithfulness cross-check (realizes the two theorems) ──
  IO.println "\n-- cross-check (realizes turn_perm_faithful + turn_channel_bind_faithful) --"
  IO.println s!"fresh allocation drops A and B (default-deny)   : {freshDropA && freshDropB}"
  IO.println s!"create-permission decode == sent (peer A)       : {permDecodeOk}"
  IO.println s!"A permitted after grant                         : {aPermitted}"
  IO.println s!"B un-granted (create-permission was A only)      : {bUnpermitted}"
  IO.println s!"permitted A -> verbatim payload to exactly A     : {aGranted}"
  IO.println s!"un-granted B -> dropped (relay only to permitted): {bStillDrop}"
  IO.println s!"channel-bind installs permission for B           : {bBoundPermitted}"
  IO.println s!"ChannelData routes to exactly bound peer B       : {cdOk}"
  IO.println s!"inbound B (post-bind) = ChannelData              : {inBchan}"
  IO.println s!"inbound A (still permitted) = Data indication    : {inAdata}"

  if freshDropA && freshDropB && permDecodeOk && aPermitted && bUnpermitted && aGranted
      && bStillDrop && bBoundPermitted && cdOk && inBchan && inAdata then do
    IO.println "\nPASS — allocate default-deny; permit-A grants A only (B still dropped);"
    IO.println "       channel-bind-B grants+routes B; relay only to permitted peers."
    IO.println "TURN GRANT PIPELINE COMPLETE (drorb-native, byte-level, no leak)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the TURN grant pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do IO.eprintln "usage: turn-perm-live selftest"; return 1

end TurnPermLive

def main (args : List String) : IO UInt32 := TurnPermLive.main args
