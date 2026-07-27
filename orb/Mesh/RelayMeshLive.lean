/-
# RelayMeshLive — driving the PROVEN multi-relay mesh forward over the byte level

`Derp.Mesh` proves the mesh of relays: presence gossip (`home : peerKey → RelayId`,
carried by the `PeerPresent`/`PeerGone` deltas) and the cross-relay hop — when
peer `A` on relay `R1` sends to peer `B` on a *different* relay `R2`, `R1` puts a
`ForwardPacket` frame (`srcKey ‖ dstKey ‖ packet`) on the mesh link, `R2` splits it
back (`splitForwarded`) and delivers it to `B`'s local connection as an ordinary
`RecvPacket`. Those decisions are pure functions over the proven frame codec; the
module ships `mesh_forward_reaches`, `mesh_no_leak`, `mesh_blind` (0 sorries) but is
otherwise INERT — nothing drove it over real bytes without crypto.

This executable isolates the **inert, crypto-free layer** of that mesh: the
relay→relay `ForwardPacket` hop. It runs entirely over byte lists in one process,
with **no crypto whatsoever** (no x25519, no ClientInfo box — those are the DERP
*login*, a separate concern, and they crash the pure Lean interpreter), so it runs
under `lake env lean --run`. The relays register their peers directly (the byte
level below the handshake), exactly as the proven model's `connect` does.

## What the selftest drives (all proven / verified Lean)

  * Two relays `R1` (id 1) and `R2` (id 2), each a proven `RelayState`; peer `A`
    registered on `R1` (conn 10), peer `B` on `R2` (conn 20); the gossip map homes
    `A → R1`, `B → R2` — built by the proven `MeshState.connect`.
  * `R1` serializes the proven `forwardPacketFrame keyA keyB packet` with the proven
    `Derp.serializeFrame` and puts those bytes on the (in-process) mesh link.
  * `R2` parses them back with the proven `Derp.parseFrame`, recovers the triple
    `(keyA, keyB, packet)` with the proven `splitForwarded`, and delivers with the
    proven `deliverForwarded` against its own routing table.
  * The delivered `RecvPacket` is itself serialized and parsed back on `B`'s side,
    then split with the proven `splitKeyed` — the bytes `B` receives after a real
    (in-memory) relay→relay hop.

Every byte-level delivery is cross-checked against the ORACLE `MeshState.forward`
— the proven centralized model's prediction of the exact cross-relay delivery.

## Honesty / realization boundary (the NetmapLive / DiscoMeshLive discipline)

This is **drorb-native** and **pure**: both relays, both peers, and the mesh link
run in this one process over byte lists (no socket, no FFI, no crypto). The
faithfulness of the wire pipeline itself is PROVEN below (`meshHopDeliver_faithful`
composes the codec round-trip with the model's routing reduction; `forwardFrame_
wire_roundtrips` proves the frame survives serialize→parse); the selftest witnesses
those equalities on concrete bytes. Interop against an external DERP mesh
deployment (which additionally needs the real Noise/DERP login and TCP sockets) is
a named residual — the socket-bound analogue is `DerpMeshLive` (crypto, built
binary), which cannot run under the pure interpreter.

Usage:
  relay-mesh-live selftest
-/
import Derp.Mesh

namespace RelayMeshLive

open Derp.Mesh
open Derp.Relay (RelayState ConnId Key Delivery)

/-! ## §1  The byte-level receiving-relay action

`meshHopDeliver s2 r2 framePayload` is exactly what relay `R2` does when a
`ForwardPacket` frame arrives off the mesh link: split its payload back into the
triple with the proven `splitForwarded`, then run the proven `deliverForwarded`
against `R2`'s own routing table `s2`, lifting the result onto relay `r2`. It is a
pure function on the frame's bytes — the exact code path the selftest executes. -/
def meshHopDeliver (s2 : RelayState) (r2 : RelayId) (framePayload : Derp.Bytes) :
    List MeshDelivery :=
  match splitForwarded framePayload with
  | some (srcKey, dstKey, packet) =>
    (deliverForwarded s2 srcKey dstKey packet).map (liftDelivery r2)
  | none => []

/-! ## §2  The wire round-trip: the ForwardPacket frame survives serialization

Before `R2` can split it, the `ForwardPacket` frame `R1` emits must survive the
byte level intact. Serializing it with the proven `Derp.serializeFrame` and parsing
it back with the proven `Derp.parseFrame` recovers the frame and the untouched
trailing bytes verbatim — the mesh link neither corrupts nor reframes the hop. Real
hypotheses (the payload fits the frame cap and is length-addressable); the
conclusion is a concrete byte-level equality, not `P → P`. -/
theorem forwardFrame_wire_roundtrips
    (srcKey dstKey packet tail : Derp.Bytes) (maxLen : Nat)
    (hcap : (forwardPacketFrame srcKey dstKey packet).payload.length ≤ maxLen)
    (haddr : (forwardPacketFrame srcKey dstKey packet).payload.length < 16777216) :
    Derp.parseFrame maxLen
        (Derp.serializeFrame (forwardPacketFrame srcKey dstKey packet) ++ tail)
      = some (forwardPacketFrame srcKey dstKey packet, tail) := by
  refine Derp.derp_parse_serialize maxLen _ tail hcap haddr ?_
  show Derp.FrameType.ofByte (Derp.FrameType.toByte Derp.FrameType.forwardPacket)
      = Derp.FrameType.forwardPacket
  decide

/-! ## §3  Faithfulness: the byte-level hop realizes the model forward

The distributed relay→relay protocol — `R1` builds `forwardPacketFrame`, `R2`
splits it and delivers — computes **precisely** the delivery the centralized model
`MeshState.forward` predicts for the same send, mediated only by the proven codec
round-trip (`splitForwarded_build`) and the model's own routing reduction.

Real hypotheses: the genuine mesh preconditions (both keys are real 32-byte keys,
the source is registered on `srcRelay`, the destination is *not* local there, the
gossip map homes it on `r2`, and it is registered on `r2`). The conclusion is a
concrete equality between the byte-level pipeline `meshHopDeliver` and
`MeshState.forward` — not `P → P`; it composes, and does not weaken,
`mesh_forward_reaches`. -/
theorem meshHopDeliver_faithful
    (m : MeshState) (srcRelay srcConn : Nat)
    (dstKey packet srcKey : Derp.Bytes) (r2 : RelayId)
    (s1 s2 : RelayState)
    (hs : srcKey.length = Derp.keyLen)
    (hd : dstKey.length = Derp.keyLen)
    (hr1 : m.relayOf srcRelay = some s1)
    (hsk : s1.keyOf srcConn = some srcKey)
    (hlocal : s1.connOf dstKey = none)
    (hhome : m.homeOf dstKey = some r2)
    (hr2 : m.relayOf r2 = some s2) :
    meshHopDeliver s2 r2 (forwardPacketFrame srcKey dstKey packet).payload
      = m.forward srcRelay srcConn dstKey packet := by
  have hsplit : splitForwarded (forwardPacketFrame srcKey dstKey packet).payload
      = some (srcKey, dstKey, packet) := splitForwarded_build srcKey dstKey packet hs hd
  unfold meshHopDeliver
  rw [hsplit]
  simp only [MeshState.forward, hr1, hsk, hlocal, hhome, hr2]

/-- **The byte-level mesh hop reaches the far peer.** Under the mesh preconditions,
the delivery `meshHopDeliver` produces from `R1`'s emitted `ForwardPacket` frame
contains the addressed cross-relay `RecvPacket` on `r2`, connection `dstConn` — the
byte-level realization of the ground-truth `mesh_forward_reaches`. -/
theorem meshHopDeliver_reaches
    (m : MeshState) (srcRelay srcConn : Nat)
    (dstKey packet srcKey : Derp.Bytes) (r2 : RelayId)
    (s1 s2 : RelayState) (dstConn : ConnId)
    (hs : srcKey.length = Derp.keyLen)
    (hd : dstKey.length = Derp.keyLen)
    (hr1 : m.relayOf srcRelay = some s1)
    (hsk : s1.keyOf srcConn = some srcKey)
    (hlocal : s1.connOf dstKey = none)
    (hhome : m.homeOf dstKey = some r2)
    (hr2 : m.relayOf r2 = some s2)
    (hc2 : s2.connOf dstKey = some dstConn) :
    (⟨r2, dstConn, { ftype := .recvPacket, payload := srcKey ++ packet }⟩ : MeshDelivery)
      ∈ meshHopDeliver s2 r2 (forwardPacketFrame srcKey dstKey packet).payload := by
  rw [meshHopDeliver_faithful m srcRelay srcConn dstKey packet srcKey r2 s1 s2
        hs hd hr1 hsk hlocal hhome hr2]
  exact mesh_forward_reaches m srcRelay srcConn dstKey packet srcKey r2 s1 s2 dstConn
    hr1 hsk hlocal hhome hr2 hc2

/-- **No cross-mesh leak on the byte-level hop.** Every delivery `meshHopDeliver`
emits from the wire frame lands on the connection registered for `dstKey` on the
relay it is delivered to — never a broadcast, never a third party, even across the
relay→relay hop. The byte-level realization of the ground-truth `mesh_no_leak`. -/
theorem meshHopDeliver_noLeak
    (m : MeshState) (srcRelay srcConn : Nat)
    (dstKey packet srcKey : Derp.Bytes) (r2 : RelayId)
    (s1 s2 : RelayState)
    (hs : srcKey.length = Derp.keyLen)
    (hd : dstKey.length = Derp.keyLen)
    (hr1 : m.relayOf srcRelay = some s1)
    (hsk : s1.keyOf srcConn = some srcKey)
    (hlocal : s1.connOf dstKey = none)
    (hhome : m.homeOf dstKey = some r2)
    (hr2 : m.relayOf r2 = some s2) :
    ∀ d ∈ meshHopDeliver s2 r2 (forwardPacketFrame srcKey dstKey packet).payload,
      ∃ s : RelayState, m.relayOf d.relay = some s ∧ s.connOf dstKey = some d.dst := by
  rw [meshHopDeliver_faithful m srcRelay srcConn dstKey packet srcKey r2 s1 s2
        hs hd hr1 hsk hlocal hhome hr2]
  exact mesh_no_leak m srcRelay srcConn dstKey packet

#print axioms meshHopDeliver_faithful
#print axioms meshHopDeliver_reaches
#print axioms meshHopDeliver_noLeak
#print axioms forwardFrame_wire_roundtrips

/-! ## §4  Byte / rendering helpers (pure; mirrors NetmapLive) -/

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def toHexL (b : Derp.Bytes) : String := toHex ⟨b.toArray⟩

def textOrHex (b : Derp.Bytes) : String := (String.fromUTF8? ⟨b.toArray⟩).getD (toHexL b)

/-- A genuine 32-byte key: `Derp.keyLen` bytes all `v`. -/
def demoKey (v : UInt8) : Key := List.replicate Derp.keyLen v

def maxLen : Nat := 70000

/-! ## §5  The selftest — a 2-relay mesh forward, byte-level, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== relay-mesh-live selftest : 2-relay mesh forward, byte-level, NO crypto =="

  -- ── the two peers (genuine 32-byte keys) and the payload ──
  let keyA : Key := demoKey 0xA1
  let keyB : Key := demoKey 0xB2
  let keyGhost : Key := demoKey 0xC3
  let packet : Derp.Bytes := Derp.bytesOf "hello-across-a-two-relay-mesh".toUTF8
  IO.println s!"peer A key {toHexL (keyA.take 4)}…  (home relay R1, conn 10)"
  IO.println s!"peer B key {toHexL (keyB.take 4)}…  (home relay R2, conn 20)"

  -- ── the ORACLE: the proven centralized model of this exact 2-relay topology ──
  -- R1 is relay id 1 (A on local conn 10); R2 is relay id 2 (B on local conn 20).
  let m : MeshState := (MeshState.empty.connect 1 keyA 10).connect 2 keyB 20
  let oracle := m.forward 1 10 keyB packet
  IO.println s!"\n[oracle] MeshState.forward 1 10 keyB pkt = {oracle.length} delivery(ies)"
  let some od := oracle.head?
    | do IO.eprintln "[oracle] model predicts NO delivery — topology wrong"; return 1
  IO.println s!"[oracle]   relay {od.relay}, dst conn {od.dst}, {repr od.frame.ftype}, payload {od.frame.payload.length}B"

  -- ── R1 side: build the proven ForwardPacket frame, serialize it onto the mesh link ──
  -- A is not local to R1 for dst keyB, and the gossip map homes keyB on R2 (the mesh
  -- hop precondition), so R1 stamps A's key and emits the proven forwardPacketFrame.
  let s1 := RelayState.empty.register keyA 10
  let fwdFrame := forwardPacketFrame keyA keyB packet
  let wire := Derp.serializeFrame fwdFrame        -- the bytes on the (in-process) mesh link
  IO.println s!"\n-- R1 -> mesh link (ForwardPacket, serialized) --"
  IO.println s!"local?  s1.connOf keyB = {repr (s1.connOf keyB)}  (none ⇒ mesh hop needed)"
  IO.println s!"wire bytes             : {wire.length}B  {toHexL (wire.take 8)}…"

  -- ── R2 side: parse the frame back off the wire, then the byte-level mesh delivery ──
  let some (fwd', rest) := Derp.parseFrame maxLen wire
    | do IO.eprintln "[R2] parseFrame FAILED on the mesh-link bytes"; return 1
  let wireRoundtrips := rest.isEmpty && (fwd' == fwdFrame)
  IO.println s!"\n-- R2 <- mesh link (parseFrame ∘ serializeFrame) --"
  IO.println s!"frame round-trips exactly (realizes forwardFrame_wire_roundtrips) : {wireRoundtrips}"
  if !wireRoundtrips then do IO.eprintln "[R2] mesh-link frame did NOT round-trip"; return 1
  if fwd'.ftype != Derp.FrameType.forwardPacket then
    do IO.eprintln s!"[R2] expected forwardPacket, got {repr fwd'.ftype}"; return 1

  -- R2's routing table (keyB -> conn 20), and the byte-level receiving-relay action.
  let s2 := RelayState.empty.register keyB 20
  let delivered := meshHopDeliver s2 2 fwd'.payload
  IO.println s!"\n-- R2 delivery (splitForwarded ∘ deliverForwarded, lifted onto relay 2) --"
  IO.println s!"deliveries             : {delivered.length}"
  for d in delivered do
    IO.println s!"  -> relay {d.relay}, conn {d.dst}, {repr d.frame.ftype}, payload {d.frame.payload.length}B"

  -- ── faithfulness cross-check: the byte-level delivery == the oracle model ──
  let faithful := delivered == oracle
  IO.println s!"\n-- cross-check (realizes meshHopDeliver_faithful) --"
  IO.println s!"byte-level delivery == oracle MeshState.forward : {faithful}"

  -- ── no-leak: every delivery lands only on relay 2, conn 20 (never R1, never a broadcast) ──
  let noLeak := delivered.all (fun d => d.relay == 2 && d.dst == 20)
  IO.println s!"no cross-mesh leak (all deliveries -> relay 2, conn 20 only) : {noLeak}"

  -- ── B receives: serialize the delivered RecvPacket, parse it back, split it (byte level) ──
  let some d0 := delivered.head?
    | do IO.eprintln "[B] no delivery produced"; return 1
  let bWire := Derp.serializeFrame d0.frame
  let some (bFrame, _) := Derp.parseFrame maxLen bWire
    | do IO.eprintln "[B] parseFrame FAILED on the delivered frame"; return 1
  let mut okB := false
  if bFrame.ftype == Derp.FrameType.recvPacket then
    match Derp.splitKeyed bFrame.payload with
    | some (srcPub, relayed) =>
      IO.println s!"\n-- B <- FrameRecvPacket (byte level) --"
      IO.println s!"src key                : {toHexL (srcPub.take 4)}…  (== A: {srcPub == keyA})"
      IO.println s!"relayed packet         : {textOrHex relayed}"
      okB := (srcPub == keyA) && (relayed == packet)
    | none => IO.eprintln "[B] short RecvPacket"
  else IO.eprintln s!"[B] expected recvPacket, got {repr bFrame.ftype}"

  -- ── the reverse direction reaches A, and stale/unknown routes drop (no leak) ──
  let reverse := m.forward 2 20 keyA [0x01]
  let reverseOk := reverse.head?.map (fun d => (d.relay, d.dst)) == some (1, 10)
  let ghostDropped := m.forward 1 10 keyGhost packet == []
  let departedDropped := (m.disconnect 2 keyB).forward 1 10 keyB packet == []
  IO.println s!"\n-- direction + gossip laws (byte-level model) --"
  IO.println s!"reverse B -> A reaches relay 1 conn 10 : {reverseOk}"
  IO.println s!"unknown dst dropped (no phantom route) : {ghostDropped}"
  IO.println s!"after PeerGone(B), A->B dropped        : {departedDropped}"

  if wireRoundtrips && faithful && noLeak && okB && reverseOk && ghostDropped && departedDropped then do
    IO.println "\nPASS — a ForwardPacket crossed a real (in-memory) R1->R2 mesh hop, A -> B;"
    IO.println "       serialize→parse→splitForwarded→deliverForwarded equals the proven model,"
    IO.println "       reaches B on the far relay, and leaks to no other connection."
    IO.println "MESH FORWARD LIVE-WIRED (drorb-native, byte-level, NO crypto, verified codec+forward)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the mesh-forward pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: relay-mesh-live selftest"
    return 1

end RelayMeshLive

def main (args : List String) : IO UInt32 := RelayMeshLive.main args
