/-
# DerpMeshLive — driving the proven DERP *mesh* cross-relay forward over real sockets

`Derp.Mesh` proves the mesh of relays: presence gossip (`home : peerKey → RelayId`,
carried by `PeerPresent`/`PeerGone`) and the cross-relay hop — when peer `A` on
relay `R1` sends to peer `B` on a *different* relay `R2`, `R1` puts a
`ForwardPacket` (`srcKey ‖ dstKey ‖ packet`) on the mesh link, `R2` splits it back
(`splitForwarded`) and delivers it to `B`'s local connection as an ordinary
`RecvPacket`. Those decisions are pure functions on the proven `Derp` frame codec;
the module ships `mesh_forward_reaches`, `mesh_no_leak`, `mesh_blind` (0 sorries)
but is otherwise INERT — nothing drove it over the wire.

This executable wires that mesh to real TCP sockets. It runs **two** relay
servers, `R1` and `R2`, each a real listener, plus a real mesh link between them:

  * `R2` accepts client `B`, learns `B`'s key from its `FrameClientInfo`
    (the proven DERP login), and registers `keyB → connB` locally.
  * `R1` accepts client `A`, learns `keyA`, then opens a **mesh link** (a real TCP
    connection) to `R2`.
  * `A` sends a `FrameSendPacket` addressed to `keyB`. `B` is not local to `R1`
    (`s1.connOf keyB = none`) and the gossip map homes `keyB` on `R2`, so `R1`
    emits the proven `forwardPacketFrame keyA keyB packet` onto the mesh link.
  * `R2` reads that frame, recovers `(keyA, keyB, packet)` with the proven
    `splitForwarded`, runs the proven `deliverForwarded` against its own routing
    table, and delivers a `FrameRecvPacket` (`keyA ‖ packet`) to `B`'s socket.
  * `B` reads its `FrameRecvPacket` — a real packet that crossed a real
    relay→relay hop to a peer on the *other* relay.

The faithfulness cross-check the run realizes is proven below as
`meshLiveHopFaithful`: the wire codec R1/R2 execute (`forwardPacketFrame` then
`splitForwarded` then `deliverForwarded` lifted onto the far relay) reproduces
**exactly** the delivery the centralized model `MeshState.forward` predicts. The
selftest computes that model delivery as an oracle and checks the bytes `B`
actually receives against it.

Not part of the trusted core: this is a live cross-check, the mesh analogue of
`derp-relay`. DRORB-NATIVE (both relays + both clients + the mesh link run in
this one process over the loopback); interop against an external DERP mesh
deployment is a named residual. Everything cryptographic/structural/routing is
the proven/verified Lean; the sockets only move the bytes those functions decide.

Modes:
  derp-mesh selftest [portR1] [portR2]   two relays + two clients; A(R1) -> B(R2)
-/
import Derp.Mesh

open Crypto (x25519Base)
open Derp.Relay (RelayState ConnId Key Delivery)

namespace DerpMeshLive

/-! ## The Phase-0 mesh faithfulness theorem

The live mesh hop is two byte operations on two different relays: `R1` builds
`forwardPacketFrame srcKey dstKey packet` and puts it on the mesh link; `R2` reads
that payload, recovers the triple with `splitForwarded`, and delivers it locally
with `deliverForwarded`. This theorem proves that composite, lifted onto the far
relay `r2`, is **precisely** the delivery the centralized model `MeshState.forward`
computes for the same send — the distributed relay→relay protocol realizes the
model, mediated only by the proven codec round-trip (`splitForwarded_build`) and
the model's own routing reduction.

Not a `P → P`: the hypotheses are the genuine mesh preconditions (the source is
registered on `srcRelay`, the destination is *not* local there, the gossip map
homes it on `r2`, and it is registered on `r2` as `dstConn` — the very situation
the selftest sets up with two relays), and the conclusion is a concrete equality
between the wire pipeline and `MeshState.forward`, ending in the single addressed
cross-relay `RecvPacket`. It composes, and does not weaken, `mesh_forward_reaches`. -/
open Derp.Mesh in
theorem meshLiveHopFaithful
    (m : Derp.Mesh.MeshState) (srcRelay srcConn : Nat)
    (dstKey packet srcKey : Derp.Bytes) (r2 : Derp.Mesh.RelayId)
    (s1 s2 : RelayState) (dstConn : ConnId)
    (hs : srcKey.length = Derp.keyLen)
    (hd : dstKey.length = Derp.keyLen)
    (hr1 : m.relayOf srcRelay = some s1)
    (hsk : s1.keyOf srcConn = some srcKey)
    (hlocal : s1.connOf dstKey = none)
    (hhome : m.homeOf dstKey = some r2)
    (hr2 : m.relayOf r2 = some s2)
    (hc2 : s2.connOf dstKey = some dstConn) :
    -- (1) the mesh-link codec round-trips: R2 recovers the exact triple R1 emitted
    splitForwarded (forwardPacketFrame srcKey dstKey packet).payload
        = some (srcKey, dstKey, packet)
    -- (2) R2's local delivery of that triple, lifted onto r2, IS the model forward
    ∧ (deliverForwarded s2 srcKey dstKey packet).map (liftDelivery r2)
        = m.forward srcRelay srcConn dstKey packet
    -- (3) and that forward is exactly the single addressed cross-relay RecvPacket
    ∧ m.forward srcRelay srcConn dstKey packet
        = [⟨r2, dstConn, { ftype := .recvPacket, payload := srcKey ++ packet }⟩] := by
  refine ⟨?_, ?_, ?_⟩
  · -- the wire codec: forwardPacketFrame's payload split back is the exact triple
    show splitForwarded (forwardPacketPayload srcKey dstKey packet) = _
    exact splitForwarded_build srcKey dstKey packet hs hd
  · -- MeshState.forward, under the remote-hop hypotheses, IS deliverForwarded lifted
    simp only [MeshState.forward, hr1, hsk, hlocal, hhome, hr2]
  · -- and that delivery is the single addressed RecvPacket on r2
    simp only [MeshState.forward, hr1, hsk, hlocal, hhome, hr2, deliverForwarded, hc2,
      liftDelivery, List.map_cons, List.map_nil]

#print axioms meshLiveHopFaithful

/-! ## The socket seams (untrusted FFI — reused from the relay lane)

Client seam (`ffi/derp_net.c`): the mesh link R1 opens to R2 is an ordinary TCP
connection, so it uses the same client seam the DERP clients use. Server seam
(`ffi/derp_relay_net.c`): each relay listens/accepts/serves with it. No new C. -/

-- client seam (ffi/derp_net.c) — also used for the R1→R2 mesh link
@[extern "drorb_tcp_connect"]
opaque tcpConnect (host : String) (port : UInt16) : IO UInt32
@[extern "drorb_tcp_send"]
opaque tcpSend (fd : UInt32) (payload : ByteArray) : IO Unit
@[extern "drorb_tcp_recv_exact"]
opaque tcpRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)
@[extern "drorb_tcp_close"]
opaque tcpClose (fd : UInt32) : IO Unit

-- server seam (ffi/derp_relay_net.c)
@[extern "relay_tcp_listen"]
opaque tcpListen (port : UInt16) : IO UInt32
@[extern "relay_tcp_accept"]
opaque tcpAccept (lfd : UInt32) (timeoutMs : UInt32) : IO (Option UInt32)
@[extern "relay_tcp_send"]
opaque srvSend (fd : UInt32) (payload : ByteArray) : IO Unit
@[extern "relay_tcp_recv_exact"]
opaque srvRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)
@[extern "relay_tcp_recv_some"]
opaque srvRecvSome (fd : UInt32) (maxBytes : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)
@[extern "relay_tcp_close"]
opaque srvClose (fd : UInt32) : IO Unit

/-! ## Hex + rendering helpers -/

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

def utf8OrHex (b : ByteArray) : String := (String.fromUTF8? b).getD (toHex b)

def recvTimeout : UInt32 := 5000
def acceptTimeout : UInt32 := 8000
def maxLen : Nat := 70000

/-! ## Frame IO -/

/-- Read one complete DERP frame off a server-side connection (5-byte header then
the declared payload), reassembled and parsed by the proven `Derp.parseFrame`. -/
def srvReadFrame (fd : UInt32) : IO (Option Derp.Frame) := do
  match ← srvRecvExact fd 5 recvTimeout with
  | none => return none
  | some hb =>
    let len := Derp.be32 (hb.get! 1) (hb.get! 2) (hb.get! 3) (hb.get! 4)
    let payload ← if len == 0 then pure (some ByteArray.empty)
                  else srvRecvExact fd (UInt32.ofNat len) recvTimeout
    match payload with
    | none => return none
    | some pb =>
      match Derp.parseFrame maxLen (hb ++ pb).toList with
      | some (f, _) => return some f
      | none => return none

/-- Read one complete DERP frame off a client-side connection. -/
def cliReadFrame (fd : UInt32) : IO (Option Derp.Frame) := do
  match ← tcpRecvExact fd 5 recvTimeout with
  | none => return none
  | some hb =>
    let len := Derp.be32 (hb.get! 1) (hb.get! 2) (hb.get! 3) (hb.get! 4)
    let payload ← if len == 0 then pure (some ByteArray.empty)
                  else tcpRecvExact fd (UInt32.ofNat len) recvTimeout
    match payload with
    | none => return none
    | some pb =>
      match Derp.parseFrame maxLen (hb ++ pb).toList with
      | some (f, _) => return some f
      | none => return none

/-- Does `s` contain a CRLF CRLF (the end of an HTTP header block)? -/
def hasCrlfCrlf (s : List UInt8) : Bool :=
  (s.zip (s.drop 1) |>.zip ((s.drop 2).zip (s.drop 3))).any
    (fun ((a, b), (c, d)) => a == 13 ∧ b == 10 ∧ c == 13 ∧ d == 10)

/-- Drain the client's HTTP Upgrade preamble so the next bytes are frames. -/
partial def drainUpgrade (fd : UInt32) (acc : ByteArray) (fuel : Nat) : IO Bool := do
  if fuel == 0 then return false
  match ← srvRecvSome fd 2048 recvTimeout with
  | none => return false
  | some chunk =>
    let acc := acc ++ chunk
    if hasCrlfCrlf acc.toList then return true
    else drainUpgrade fd acc (fuel - 1)

/-! ## The relay server side (DERP login + the mesh) -/

/-- A fixed 24-byte nonce for a relay's ServerInfo box (one box per reply). -/
def serverNonce : ByteArray := ⟨Array.replicate 24 (0x5b : UInt8)⟩

/-- Run a relay's side of the DERP login on a freshly accepted client connection,
returning the peer's public key (learned by opening its `FrameClientInfo`). This
is the registration input: the key the relay routes to `fd`. -/
def relayHandshake (label : String) (serverSec serverPub : ByteArray) (fd : UInt32) :
    IO (Option Derp.Bytes) := do
  if !(← drainUpgrade fd ByteArray.empty 8) then IO.eprintln s!"[{label}] no HTTP upgrade"; return none
  let skFrame : Derp.Frame :=
    { ftype := .serverKey, payload := Derp.serverKeyPayload (Derp.bytesOf serverPub) }
  srvSend fd (Derp.baOf (Derp.serializeFrame skFrame))
  match ← srvReadFrame fd with
  | none => IO.eprintln s!"[{label}] no FrameClientInfo"; return none
  | some cif =>
    if cif.ftype != Derp.FrameType.clientInfo then
      IO.eprintln s!"[{label}] expected clientInfo, got {repr cif.ftype}"; return none
    match Derp.openClientInfo serverSec cif.payload with
    | none => IO.eprintln s!"[{label}] openClientInfo REJECTED"; return none
    | some (clientPubL, infoL) =>
      match Derp.buildServerInfo (Derp.baOf clientPubL) serverSec serverNonce (Derp.baOf infoL) with
      | none => IO.eprintln s!"[{label}] buildServerInfo failed"; return none
      | some sif =>
        srvSend fd (Derp.baOf (Derp.serializeFrame sif))
        IO.println s!"[{label}] registered peer {toHex (Derp.baOf clientPubL)}"
        return some clientPubL

/-- **Relay R2 (B's home relay).** Accept client `B`, register it, then accept the
mesh link from `R1`, read one `ForwardPacket`, recover the triple with the proven
`splitForwarded`, run the proven `deliverForwarded` against R2's own table, and
send the resulting `RecvPacket` to `B`'s socket. Returns `true` on delivery. -/
def runRelayR2 (port : UInt16) : IO Bool := do
  let serverSec := ofHex "2222222222222222222222222222222222222222222222222222222222222222"
  let some serverPub := (← pure (x25519Base serverSec)) | do
    IO.eprintln "[R2] x25519Base failed"; return false
  let lfd ← tcpListen port
  IO.println s!"[R2] listening on 127.0.0.1:{port}  pub {toHex serverPub}"
  -- accept + register client B on local conn 0
  let some fdB := (← tcpAccept lfd acceptTimeout) | do IO.eprintln "[R2] accept B timeout"; return false
  let some keyB := (← relayHandshake "R2" serverSec serverPub fdB) | do srvClose lfd; return false
  -- R2's local routing table: keyB -> conn 0 (the PROVEN register)
  let s2 := RelayState.empty.register keyB 0
  IO.println "[R2] client B registered on local conn 0; awaiting mesh link from R1"
  -- accept the mesh link from R1
  let some fdMesh := (← tcpAccept lfd acceptTimeout) | do IO.eprintln "[R2] accept mesh timeout"; srvClose fdB; srvClose lfd; return false
  IO.println "[R2] mesh link from R1 established; awaiting ForwardPacket"
  -- read one ForwardPacket off the mesh link
  match ← srvReadFrame fdMesh with
  | none => IO.eprintln "[R2] no ForwardPacket on mesh link"; srvClose fdB; srvClose fdMesh; srvClose lfd; return false
  | some ff =>
    if ff.ftype != Derp.FrameType.forwardPacket then
      IO.eprintln s!"[R2] expected forwardPacket, got {repr ff.ftype}"; srvClose fdB; srvClose fdMesh; srvClose lfd; return false
    -- THE PROVEN MESH SPLIT: recover (srcKey, dstKey, packet)
    match Derp.Mesh.splitForwarded ff.payload with
    | none => IO.eprintln "[R2] malformed ForwardPacket"; srvClose fdB; srvClose fdMesh; srvClose lfd; return false
    | some (srcKey, dstKey, pkt) =>
      IO.println s!"[R2] <- ForwardPacket  src {toHex (Derp.baOf srcKey)} -> dst {toHex (Derp.baOf dstKey)} ({pkt.length}B)"
      -- THE PROVEN LOCAL DELIVERY: deliverForwarded on R2's own table
      let ds := Derp.Mesh.deliverForwarded s2 srcKey dstKey pkt
      let mut ok := false
      for d in ds do
        if d.dst == 0 then
          srvSend fdB (Derp.baOf (Derp.serializeFrame d.frame))
          IO.println s!"[R2] delivered {repr d.frame.ftype} to B (local conn {d.dst}, {d.frame.payload.length}B)"
          ok := true
        else
          IO.eprintln s!"[R2] delivery to unknown local conn {d.dst}"
      srvClose fdB; srvClose fdMesh; srvClose lfd
      return ok

/-- **Relay R1 (A's home relay).** Accept client `A`, register it, open the mesh
link to `R2`, read one `FrameSendPacket` from `A`, and — since the destination is
not local and the gossip map homes it on `R2` — emit the proven
`forwardPacketFrame` (stamped with `A`'s learned key) onto the mesh link.
Returns `true` once the packet is forwarded. -/
def runRelayR1 (port meshPort : UInt16) : IO Bool := do
  let serverSec := ofHex "1111111111111111111111111111111111111111111111111111111111111111"
  let some serverPub := (← pure (x25519Base serverSec)) | do
    IO.eprintln "[R1] x25519Base failed"; return false
  let lfd ← tcpListen port
  IO.println s!"[R1] listening on 127.0.0.1:{port}  pub {toHex serverPub}"
  -- accept + register client A on local conn 0
  let some fdA := (← tcpAccept lfd acceptTimeout) | do IO.eprintln "[R1] accept A timeout"; return false
  let some keyA := (← relayHandshake "R1" serverSec serverPub fdA) | do srvClose lfd; return false
  -- R1's local routing table: keyA -> conn 0 (the PROVEN register)
  let s1 := RelayState.empty.register keyA 0
  IO.println "[R1] client A registered on local conn 0; opening mesh link to R2"
  -- open the mesh link to R2 (an ordinary TCP connection — client seam)
  let fdMesh ← tcpConnect "127.0.0.1" meshPort
  IO.println s!"[R1] mesh link to R2 open on 127.0.0.1:{meshPort}"
  -- read one SendPacket from A
  match ← srvReadFrame fdA with
  | none => IO.eprintln "[R1] no FrameSendPacket from A"; srvClose fdA; tcpClose fdMesh; srvClose lfd; return false
  | some sf =>
    if sf.ftype != Derp.FrameType.sendPacket then
      IO.eprintln s!"[R1] expected sendPacket, got {repr sf.ftype}"; srvClose fdA; tcpClose fdMesh; srvClose lfd; return false
    match Derp.splitKeyed sf.payload with
    | none => IO.eprintln "[R1] short SendPacket"; srvClose fdA; tcpClose fdMesh; srvClose lfd; return false
    | some (dstKey, pkt) =>
      -- The distributed decision: dst is NOT local to R1, gossip homes it on R2.
      match s1.connOf dstKey with
      | some _ =>
        IO.eprintln "[R1] unexpected: dst is local (mesh hop not exercised)"; srvClose fdA; tcpClose fdMesh; srvClose lfd; return false
      | none =>
        -- stamp A's learned key and put the PROVEN forwardPacketFrame on the mesh link
        let fwd := Derp.Mesh.forwardPacketFrame keyA dstKey pkt
        tcpSend fdMesh (Derp.baOf (Derp.serializeFrame fwd))
        IO.println s!"[R1] -> ForwardPacket to R2  src {toHex (Derp.baOf keyA)} -> dst {toHex (Derp.baOf dstKey)} ({pkt.length}B)"
        srvClose fdA; tcpClose fdMesh; srvClose lfd
        return true

/-! ## The client side -/

def clientNonce : ByteArray := ⟨Array.replicate 24 (0x2a : UInt8)⟩

def upgradeRequest : ByteArray :=
  "GET /derp HTTP/1.1\r\nHost: 127.0.0.1\r\nUpgrade: DERP\r\nConnection: Upgrade\r\nDerp-Fast-Start: 1\r\n\r\n".toUTF8

/-- One client's full DERP login against its home relay; returns its fd. -/
def clientLogin (label : String) (port : UInt16) (priv pub : ByteArray) :
    IO (Option UInt32) := do
  let fd ← tcpConnect "127.0.0.1" port
  tcpSend fd upgradeRequest
  match ← cliReadFrame fd with
  | none => IO.eprintln s!"[{label}] no FrameServerKey"; return none
  | some skf =>
    match Derp.parseServerKey skf.payload with
    | none => IO.eprintln s!"[{label}] bad ServerKey magic"; return none
    | some serverPubL =>
      let serverPub := Derp.baOf serverPubL
      let info := "{\"version\":2}".toUTF8
      match Derp.buildClientInfo pub serverPub priv clientNonce info with
      | none => IO.eprintln s!"[{label}] buildClientInfo failed"; return none
      | some cif =>
        tcpSend fd (Derp.baOf (Derp.serializeFrame cif))
        match ← cliReadFrame fd with
        | none => IO.eprintln s!"[{label}] no FrameServerInfo"; return none
        | some sif =>
          match Derp.openServerInfo serverPub priv sif.payload with
          | none => IO.eprintln s!"[{label}] openServerInfo REJECTED"; return none
          | some _ =>
            IO.println s!"[{label}] login complete (pub {toHex pub})"
            return some fd

/-! ## The self-contained 2-relay mesh end-to-end check -/

/-- Run two relays + two clients + a mesh link in one process: `A` (on `R1`) sends
to `B` (on `R2`), the packet crosses the R1→R2 mesh link, and `B` reads it back.
The bytes `B` receives are checked against the ORACLE `MeshState.forward` — the
proven model's prediction of the exact cross-relay delivery (realizing
`meshLiveHopFaithful` / `mesh_forward_reaches`). -/
def selftest (portR1 portR2 : UInt16) : IO UInt32 := do
  let privA := ofHex "a01111111111111111111111111111111111111111111111111111111111111a"
  let privB := ofHex "b02222222222222222222222222222222222222222222222222222222222222b"
  let some pubA := (← pure (x25519Base privA)) | do IO.eprintln "x25519Base(A) failed"; return 1
  let some pubB := (← pure (x25519Base privB)) | do IO.eprintln "x25519Base(B) failed"; return 1
  let keyA : Key := Derp.bytesOf pubA
  let keyB : Key := Derp.bytesOf pubB
  IO.println s!"client A pub {toHex pubA}  (home relay R1)"
  IO.println s!"client B pub {toHex pubB}  (home relay R2)\n"

  -- ── the ORACLE: the proven centralized model of this exact 2-relay topology ──
  -- R1 is relay id 1 (A on local conn 0); R2 is relay id 2 (B on local conn 0).
  let m : Derp.Mesh.MeshState :=
    (Derp.Mesh.MeshState.empty.connect 1 keyA 0).connect 2 keyB 0
  let packet := "hello-across-a-two-relay-DERP-mesh".toUTF8
  let pktL : Derp.Bytes := Derp.bytesOf packet
  let oracle := m.forward 1 0 keyB pktL
  IO.println s!"[oracle] MeshState.forward 1 0 keyB pkt  = {oracle.length} delivery(ies)"
  match oracle.head? with
  | none => IO.eprintln "[oracle] model predicts NO delivery — topology wrong"; return 1
  | some od =>
    IO.println s!"[oracle]   relay {od.relay}, dst conn {od.dst}, {repr od.frame.ftype}, payload {od.frame.payload.length}B"

    -- ── start both relays; give the listeners a moment to bind ──
    let r2Task ← IO.asTask (runRelayR2 portR2)
    IO.sleep 200
    let r1Task ← IO.asTask (runRelayR1 portR1 portR2)
    IO.sleep 200

    -- ── B logs into R2 first (so R2's accept #1 is B, accept #2 is the mesh link) ──
    IO.println "\n=== client B login (-> R2) ==="
    let some fdB := (← clientLogin "B" portR2 privB pubB) | do IO.eprintln "B login failed"; return 1
    IO.println "\n=== client A login (-> R1) ==="
    let some fdA := (← clientLogin "A" portR1 privA pubA) | do tcpClose fdB; IO.eprintln "A login failed"; return 1

    -- ── A sends to B's key; R1 forwards over the mesh link to R2; R2 delivers to B ──
    IO.println "\n=== mesh forward: A -> R1 =[mesh]=> R2 -> B ==="
    let sendFrame : Derp.Frame :=
      { ftype := .sendPacket, payload := Derp.bytesOf pubB ++ Derp.bytesOf packet }
    tcpSend fdA (Derp.baOf (Derp.serializeFrame sendFrame))
    IO.println s!"[A] -> FrameSendPacket to B ({(Derp.serializeFrame sendFrame).length}B)"

    let mut result : UInt32 := 1
    match ← cliReadFrame fdB with
    | none => IO.eprintln "[B] no frame arrived"
    | some rf =>
      if rf.ftype != Derp.FrameType.recvPacket then
        IO.eprintln s!"[B] expected recvPacket, got {repr rf.ftype}"
      else
        match Derp.splitKeyed rf.payload with
        | none => IO.eprintln "[B] short RecvPacket"
        | some (srcPub, relayed) =>
          IO.println s!"[B] <- FrameRecvPacket  src {toHex (Derp.baOf srcPub)}"
          IO.println s!"[B]    relayed packet   : {utf8OrHex (Derp.baOf relayed)}"
          let okSrc := srcPub == keyA
          let okPkt := relayed == pktL
          -- the faithfulness cross-check: the live delivered frame == the oracle's
          let okOracle := (rf.payload == od.frame.payload) && (rf.ftype == od.frame.ftype)
          IO.println s!"\n    src == A pubkey        : {okSrc}"
          IO.println s!"    packet verbatim        : {okPkt}"
          IO.println s!"    live == oracle delivery: {okOracle}  (realizes meshLiveHopFaithful)"
          if okSrc ∧ okPkt ∧ okOracle then
            IO.println "\nMESH RELAY COMPLETE — a real frame crossed a real R1->R2 mesh hop, A -> B."
            result := 0
          else IO.eprintln "\nrelayed frame did not match the model"
    tcpClose fdA; tcpClose fdB
    let _ ← IO.wait r1Task
    let r2ok ← IO.wait r2Task
    match r2ok with
    | .ok true => pure ()
    | _ => IO.eprintln "[R2] did not report a successful mesh delivery"
    return result

def main (args : List String) : IO UInt32 := do
  match args with
  | "selftest" :: rest =>
    let p1 := (rest.getD 0 "3391").toNat?.getD 3391 |>.toUInt16
    let p2 := (rest.getD 1 "3392").toNat?.getD 3392 |>.toUInt16
    selftest p1 p2
  | _ => selftest 3391 3392

end DerpMeshLive

def main (args : List String) : IO UInt32 := DerpMeshLive.main args
