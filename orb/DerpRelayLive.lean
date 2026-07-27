/-
# DerpRelayLive — driving the proven DERP relay-forwarding server over real sockets

The `Derp.Relay` model is sans-IO: `RelayState.step` / `RelayState.forward` compute
the routing decision (peer key → connection) and the exact forwarded frame bytes as
pure functions on the proven `Derp` frame codec and the verified `Crypto` crypto_box
login. This executable takes those decisions to real TCP sockets: it runs the relay
server (accept connections, learn each peer's key from its `FrameClientInfo`, and
forward `FrameSendPacket`s peer-to-peer as `FrameRecvPacket`s) and drives two clients
through it.

The forwarding is decided by the PROVEN `Derp.Relay.step`: the relay never chooses a
destination other than the one `RelayState.connOf` returns, and copies the payload
bytes verbatim (`relay_blind`). The relay opens the ClientInfo box only to LEARN the
sender's public key (the registration); it never reads the relayed packet payload.

Modes:
  derp-relay selftest [port]    run relay + two clients in one process; A -> B end to end
  derp-relay serve    [port]    run only the relay (drive it with the `derp-live` clients)
  derp-relay server   [port]    the PERSISTENT N-connection region a stock client homes on

## The verified-TLS front

A stock `tailscale` client dials its home DERP region over **HTTPS**
(`https://<host>:<DERPPort>/derp`), so a plaintext relay sees a TLS ClientHello where
it expected `GET /derp` and logs `no HTTP upgrade`. drorb does not need a second TLS
stack for this: `@[export drorb_tls_terminate]` (`Dataplane.Tls.drorbTlsTerminate`) is
the SAME verified TLS 1.3 server the HTTPS front door runs — the same `serverStep` /
`chooseCert` / `kexStep`, the same proven `appStep`/`sealAppData` record layer, the
same ALPN pin to `http/1.1` (`controlFront_negotiates_only_http11`, which is exactly
what an `Upgrade:`-based protocol needs) — with the decrypted duplex stream pumped
through a host file descriptor instead of into the served pipeline.

So the relay is fronted by the SAME crossing the ts2021 control front makes
(`crates/dataplane/src/control.rs::handle_tls`): the host accepts the TLS connection,
hands its fd to `drorb_tls_terminate` with one end of a loopback duplex pair, and the
UNMODIFIED relay runs over the other end. Everything below the crossing — the proven
`Derp.Upgrade` handshake, the proven `Derp` codec, the proven `Derp.Server.dispatch`
forwarding — runs on plaintext without knowing TLS exists.

That front lives in the `dataplane` host process (`crates/dataplane/src/derp_front.rs`,
`DRORB_DERP_TLS_LISTEN`), which already boots the Lean runtime and already owns the
terminator crossing, and it splices the decrypted stream to THIS relay's plaintext
listener. It is NOT in this process for one reason, worth naming: `Dataplane.lean`
cannot be imported by a Lean executable at all today, because its import closure reaches
`Route/StaticServe.lean`, which declares a ROOT-namespace `main` — so any `lean_exe`
importing it fails with "`main` has already been declared". The verified terminator is
also welded into the same namespace as the serve-crossing loops (`appLoop` / `h2Loop` /
`drorbServe`), which it does not need. Both are real structural debt; see the report.

`derp-relay certname` prints the `sha256-raw:` pin a served DERPMap must carry for the
leaf the front presents.

Not part of the trusted core: this is a live cross-check, the relay-server analogue of
`derp-live`. Everything cryptographic/structural/routing is the proven/verified Lean.
-/
import Derp.Relay
import Derp.Server
import Derp.Upgrade

open Crypto (x25519Base)

namespace DerpRelayLive

/-! ## The socket seams (untrusted FFI) -/

-- client seam (ffi/derp_net.c)
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
-- routable listen: bind a given host ("" / "0.0.0.0" -> INADDR_ANY). Host glue only;
-- the relay's proven forwarding is unchanged, just the LISTEN address.
@[extern "relay_tcp_listen_addr"]
opaque tcpListenAddr (host : String) (port : UInt16) : IO UInt32
@[extern "relay_tcp_accept"]
opaque tcpAccept (lfd : UInt32) (timeoutMs : UInt32) : IO (Option UInt32)
@[extern "relay_tcp_send"]
opaque srvSend (fd : UInt32) (payload : ByteArray) : IO Unit
@[extern "relay_tcp_recv_exact"]
opaque srvRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)
@[extern "relay_tcp_recv_some"]
opaque srvRecvSome (fd : UInt32) (maxBytes : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)
@[extern "relay_poll_readable"]
opaque pollReadable (fdA fdB : UInt32) (timeoutMs : UInt32) : IO UInt32
-- N-connection poll: readable index into `fds`, or 0xFFFFFFFF on timeout. A slot
-- holding the sentinel 0xFFFFFFFF (`deadFd`) is skipped (poll ignores fd=-1), so a
-- closed connection keeps its stable ConnId slot without being polled.
@[extern "relay_poll_many"]
opaque pollMany (fds : Array UInt32) (timeoutMs : UInt32) : IO UInt32
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
def maxLen : Nat := 70000

/-! ## The relay server -/

/-- The relay's fixed server static key (a live-harness constant; a real relay
would persist a generated key). The clients seal their ClientInfo to `serverPub`. -/
def serverSecHex : String :=
  "5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e"

/-- A fixed 24-byte nonce for the relay's ServerInfo box (one box per reply). -/
def serverNonce : ByteArray := ⟨Array.replicate 24 (0x5b : UInt8)⟩

/-- Read one complete DERP frame off a server-side connection, drawing FIRST from
`pend` — bytes already in hand, in particular the residue the proven upgrade parser
handed back — and only then from the socket. Returns the frame and the bytes still
unconsumed, so the next read starts exactly where this frame ended.

The old reader assumed every frame begins on a read boundary (`recv` exactly 5, then
exactly `len`), and the upgrade drain before it threw away everything past the header
terminator. Both are false on a TLS record stream: one record routinely carries the
end of the HTTP header block and the head of the first frame together.
`Derp.Upgrade.upgrade_no_loss` is why this signature carries the residue at all —
head ++ residue is exactly what arrived, so the residue must be PARSED, not dropped. -/
partial def readFrameBuf (fd : UInt32) (pend : ByteArray) :
    IO (Option (Derp.Frame × ByteArray)) := do
  match Derp.parseFrame maxLen pend.toList with
  | some (f, rest) => return some (f, Derp.baOf rest)
  | none =>
    match ← srvRecvSome fd 65536 recvTimeout with
    | none => return none
    | some chunk =>
      if chunk.size == 0 then return none
      else readFrameBuf fd (pend ++ chunk)

/-- Drive the PROVEN upgrade handshake (`Derp.Upgrade.serveUpgrade`) on a freshly
accepted connection: read until the model accepts a complete header block, send back
exactly the bytes it says to send — the `101 Switching Protocols` a stock
`derphttp.Client` blocks on (`serveUpgrade_stock_101`), and NOTHING AT ALL for a
`Derp-Fast-Start` client (`serveUpgrade_faststart_silent`), so drorb's own client is
byte-for-byte unaffected — and return the RESIDUE, which by `upgrade_no_loss` is the
frame stream verbatim. -/
partial def serveUpgradeLive (fd : UInt32) (acc : ByteArray) (fuel : Nat) :
    IO (Option ByteArray) := do
  if fuel == 0 then return none
  match Derp.Upgrade.serveUpgrade acc.toList with
  | some (out, rest) =>
    if !out.isEmpty then
      IO.println "[relay] stock client (no Derp-Fast-Start): sending HTTP 101 Switching Protocols"
      srvSend fd (Derp.baOf out)
    return some (Derp.baOf rest)
  | none =>
    match ← srvRecvSome fd 4096 recvTimeout with
    | none => return none
    | some chunk =>
      if chunk.size == 0 then return none
      else serveUpgradeLive fd (acc ++ chunk) (fuel - 1)

/-- Run the relay's side of the login handshake on a freshly accepted connection,
returning the peer's public key (learned by opening its ClientInfo) TOGETHER WITH the
bytes received but not yet consumed. This is the registration input: the key the relay
will route to `fd`. -/
def relayHandshake (serverSec serverPub : ByteArray) (fd : UInt32) :
    IO (Option (Derp.Bytes × ByteArray)) := do
  let some rest0 := (← serveUpgradeLive fd ByteArray.empty 16)
    | do IO.eprintln "[relay] no HTTP upgrade"; return none
  -- 1. send FrameServerKey greeting (magic ‖ serverPub)
  let skFrame : Derp.Frame :=
    { ftype := .serverKey, payload := Derp.serverKeyPayload (Derp.bytesOf serverPub) }
  srvSend fd (Derp.baOf (Derp.serializeFrame skFrame))
  -- 2. read FrameClientInfo, open it to LEARN the peer key (registration)
  match ← readFrameBuf fd rest0 with
  | none => IO.eprintln "[relay] no FrameClientInfo"; return none
  | some (cif, rest1) =>
    if cif.ftype != Derp.FrameType.clientInfo then
      IO.eprintln s!"[relay] expected clientInfo, got {repr cif.ftype}"; return none
    match Derp.openClientInfo serverSec cif.payload with
    | none => IO.eprintln "[relay] openClientInfo REJECTED"; return none
    | some (clientPubL, infoL) =>
      -- 3. reply FrameServerInfo, sealed back to the client (proven Derp.buildServerInfo)
      match Derp.buildServerInfo (Derp.baOf clientPubL) serverSec serverNonce (Derp.baOf infoL) with
      | none => IO.eprintln "[relay] buildServerInfo failed"; return none
      | some sif =>
        srvSend fd (Derp.baOf (Derp.serializeFrame sif))
        IO.println s!"[relay] registered peer {toHex (Derp.baOf clientPubL)}"
        return some (clientPubL, rest1)

/-- Deliver every `Delivery` the proven relay emits to its destination connection.
`fds` maps a `ConnId` to its socket. The frame bytes come straight from the proven
`Derp.serializeFrame`; the routing choice from the proven `Derp.Relay.step`. -/
def emitDeliveries (fds : Array UInt32) (ds : List Derp.Relay.Delivery) : IO Unit := do
  for d in ds do
    match fds[d.dst]? with
    | some dfd =>
      srvSend dfd (Derp.baOf (Derp.serializeFrame d.frame))
      IO.println s!"[relay] forwarded {repr d.frame.ftype} to conn {d.dst} ({d.frame.payload.length}B)"
    | none => IO.eprintln s!"[relay] delivery to unknown conn {d.dst}"

/-- The forward loop: whichever conn speaks, run the proven `Derp.Relay.step` and
emit its deliveries. Returns `true` once a frame is forwarded. Each connection carries
its own residue buffer (`pend0`/`pend1`) — the bytes the previous read pulled off the
socket past the end of the previous frame. -/
partial def forwardLoop (fd0 fd1 : UInt32) (fds : Array UInt32) (pend0 pend1 : ByteArray)
    (st : Derp.Relay.RelayState) (fuel : Nat) : IO Bool := do
  if fuel == 0 then return false
  let which ← pollReadable fd0 fd1 8000
  if which == 0xFFFFFFFF then IO.eprintln "[relay] poll timeout"; return false
  let (srcConn, srcFd, pend) :=
    if which == 0 then ((0 : Nat), fd0, pend0) else ((1 : Nat), fd1, pend1)
  match ← readFrameBuf srcFd pend with
  | none => IO.eprintln "[relay] read frame failed"; return false
  | some (f, rest) =>
    let (pend0', pend1') := if which == 0 then (rest, pend1) else (pend0, rest)
    -- THE PROVEN ROUTING DECISION: Derp.Server.dispatch (dispatch_addressed_only /
    -- dispatch_blind / dispatch_only_sendpacket). It matches the frame type, splits a
    -- SendPacket into (dstKey, pkt), and forwards through the proven RelayState.forward;
    -- every non-SendPacket and every short SendPacket yields no delivery.
    let ds := Derp.Server.dispatch st srcConn f
    if ds.isEmpty then forwardLoop fd0 fd1 fds pend0' pend1' st (fuel - 1)
    else emitDeliveries fds ds; return true

/-- The relay: accept two clients, register each (by opening its ClientInfo), then
forward one `SendPacket` through the proven `Derp.Relay.step`. Runs until a frame is
forwarded or the poll times out. Returns `true` on a successful forward. -/
def runRelay (port : UInt16) : IO Bool := do
  let serverSec := ofHex serverSecHex
  let some serverPub := (← pure (x25519Base serverSec)) | do
    IO.eprintln "[relay] x25519Base(serverSec) failed"; return false
  let lfd ← tcpListen port
  IO.println s!"[relay] listening on 127.0.0.1:{port}  pub {toHex serverPub}"
  -- accept + register conn 0
  let some fd0 := (← tcpAccept lfd 8000) | do IO.eprintln "[relay] accept 0 timeout"; return false
  let some (key0, pend0) := (← relayHandshake serverSec serverPub fd0) | return false
  -- accept + register conn 1
  let some fd1 := (← tcpAccept lfd 8000) | do IO.eprintln "[relay] accept 1 timeout"; return false
  let some (key1, pend1) := (← relayHandshake serverSec serverPub fd1) | return false
  let fds := #[fd0, fd1]
  -- build the proven routing table: conn 0 -> key0, conn 1 -> key1
  let s0 := (Derp.Relay.step Derp.Relay.RelayState.empty (.clientInfo 0 key0)).1
  let s1 := (Derp.Relay.step s0 (.clientInfo 1 key1)).1
  IO.println "[relay] both peers registered; entering forward loop"
  let ok ← forwardLoop fd0 fd1 fds pend0 pend1 s1 16
  srvClose fd0; srvClose fd1; srvClose lfd
  return ok

/-! ## The PERSISTENT N-connection relay (the real DERP region)

`runRelay` above is the single-shot two-client cross-check. A live DERP region a
stock tailscale client homes on must instead: accept connections dynamically, hold
each open indefinitely (magicsock keeps ONE persistent home-DERP connection per
node), and forward `SendPacket`s among ALL of them. This server does exactly that,
routing every inbound frame through the SAME proven `Derp.Server.dispatch` — the
routing decision stays the proven relay; only the connection multiplexing is new
(untrusted IO). Each accepted connection is registered by opening its `FrameClientInfo`
(the proven `Derp.openClientInfo`), gets a stable `ConnId` = its index, and a
`SendPacket` to a registered peer key is delivered as a `RecvPacket` on that peer's
connection (`forward_to_addressed_only` / `relay_blind`, unchanged). -/

/-- Sentinel fd for a closed connection whose `ConnId` slot must stay stable so the
proven `RelayState` routes keep pointing at the right index. `poll` ignores fd = -1. -/
def deadFd : UInt32 := 0xFFFFFFFF

/-! ### Plaintext, and the TLS front in front of it

The relay listener speaks plaintext. A STOCK tailscale client dials
`https://<host>:<DERPPort>/derp`, so in a deployment it is fronted by the verified TLS
1.3 terminator (`drorb_tls_terminate`) running in the host process, which decrypts and
splices the byte stream to this listener — see the module header. The relay itself is
unchanged by that: it reads a socket, and the proven upgrade + codec + dispatch run over
whatever bytes arrive. -/

/-- The `CertName` a served DERPMap must carry for a stock client to accept a
self-signed leaf: `sha256-raw:<hex sha256 of the leaf DER>`. `derphttp` pins the
certificate by that hash (`tlsdial.SetConfigExpectedCertHash`) instead of building a PKI
path, which is how a self-hosted DERP region is reachable at all without a public CA.
Derived from the DER the front actually presents, so the advertised value is never
typed twice. -/
def certNameOf (certDer : ByteArray) : String :=
  "sha256-raw:" ++ toHex (Crypto.sha256 certDer)

/-- A live relay connection: the socket the relay reads and writes (the PLAINTEXT side
of the TLS front, in a deployment) and the bytes received past the end of the last
frame — the residue the proven upgrade parser or the previous frame read left behind. -/
structure Conn where
  fd : UInt32
  pend : ByteArray := ByteArray.empty

/-- Deliver every proven `Delivery` to its destination connection, skipping closed
slots (a peer that hung up). The routing choice is the proven `Derp.Server.dispatch`;
this only moves the already-decided frame bytes to the already-decided socket. -/
def emitDeliveriesSrv (conns : Array Conn) (ds : List Derp.Relay.Delivery) : IO Unit := do
  for d in ds do
    match conns[d.dst]? with
    | some c =>
      if c.fd == deadFd then
        IO.eprintln s!"[relay] drop delivery to closed conn {d.dst}"
      else
        srvSend c.fd (Derp.baOf (Derp.serializeFrame d.frame))
        IO.println s!"[relay] forwarded {repr d.frame.ftype} to conn {d.dst} ({d.frame.payload.length}B)"
    | none => IO.eprintln s!"[relay] delivery to unknown conn {d.dst}"

/-- The persistent accept + forward loop. Polls the listen fd (slot 0) and every live
connection at once; on the listen fd it accepts + registers a new peer, on a
connection it reads one frame and either forwards it (proven dispatch), replies Pong
to a Ping, or reaps the slot on EOF. On idle it sends a KeepAlive to every live
connection so magicsock keeps the home-DERP connection up.

Every connection carries its own residue buffer, so a read that straddled a frame
boundary (what a TLS record stream does constantly) resumes exactly where it stopped. -/
partial def serverLoop (lfd : UInt32) (serverSec serverPub : ByteArray)
    (conns : Array Conn) (st : Derp.Relay.RelayState) : IO Unit := do
  let idx ← pollMany (#[lfd] ++ conns.map (·.fd)) 30000
  if idx == deadFd then
    let ka := Derp.baOf (Derp.serializeFrame { ftype := .keepAlive, payload := [] })
    for c in conns do
      if c.fd != deadFd then
        try srvSend c.fd ka catch _ => pure ()
    serverLoop lfd serverSec serverPub conns st
  else if idx == 0 then
    match ← tcpAccept lfd 2000 with
    | none => serverLoop lfd serverSec serverPub conns st
    | some fd =>
      match ← relayHandshake serverSec serverPub fd with
      | none =>
        srvClose fd
        serverLoop lfd serverSec serverPub conns st
      | some (key, pend) =>
        let connId := conns.size
        let st' := (Derp.Relay.step st (.clientInfo connId key)).1
        IO.println s!"[relay] conn {connId} REGISTERED and HELD OPEN ({connId + 1} live)"
        serverLoop lfd serverSec serverPub (conns.push { fd, pend }) st'
  else
    let connId := idx.toNat - 1
    match conns[connId]? with
    | none => serverLoop lfd serverSec serverPub conns st
    | some c =>
      if c.fd == deadFd then serverLoop lfd serverSec serverPub conns st
      else
        match ← readFrameBuf c.fd c.pend with
        | none =>
          IO.println s!"[relay] conn {connId} closed by peer"
          srvClose c.fd
          serverLoop lfd serverSec serverPub
            (conns.set! connId { c with fd := deadFd, pend := ByteArray.empty }) st
        | some (f, rest) =>
          let conns := conns.set! connId { c with pend := rest }
          if f.ftype == Derp.FrameType.ping then
            srvSend c.fd (Derp.baOf (Derp.serializeFrame { ftype := .pong, payload := f.payload }))
          let ds := Derp.Server.dispatch st connId f
          emitDeliveriesSrv conns ds
          serverLoop lfd serverSec serverPub conns st

/-- Bring up the persistent relay: bind, then serve DERP connections forever. This is
the mode the combined serve harness runs on `:3340` so a registered stock client's
home DERP region (drorb region 1) is genuinely REACHABLE.

A STOCK client dials `https://<host>:<DERPPort>/derp`, so a deployment binds this
listener on LOOPBACK and puts the verified TLS terminator in front of it
(`DRORB_DERP_TLS_LISTEN` in the host process); a plaintext listener exposed directly to
a stock client sees a TLS ClientHello where `GET /derp` should be and logs
`no HTTP upgrade`. -/
def runServer (port : UInt16) : IO UInt32 := do
  let serverSec := ofHex serverSecHex
  let some serverPub := (← pure (x25519Base serverSec)) | do
    IO.eprintln "[relay] x25519Base(serverSec) failed"; return 1
  -- DRORB_DERP_LISTEN picks the bind interface: 127.0.0.1 (default, loopback) or
  -- 0.0.0.0 / a host IP to make the verified relay REACHABLE from another host.
  let bindHost := (← IO.getEnv "DRORB_DERP_LISTEN").getD "127.0.0.1"
  let lfd ← tcpListenAddr bindHost port
  IO.println s!"[relay] PERSISTENT DERP server on {bindHost}:{port}  serverPub {toHex serverPub}"
  IO.println "[relay] N-conn accept + forward via proven Derp.Server.dispatch; Ctrl-C to stop"
  serverLoop lfd serverSec serverPub #[] Derp.Relay.RelayState.empty
  return 0

/-- `derp-relay certname [path]` — print the `CertName` a served DERPMap must carry for
this leaf, so the operator script derives it from the cert the relay actually presents. -/
def printCertName (path : String) : IO UInt32 := do
  try
    let der ← IO.FS.readBinFile path
    IO.println (certNameOf der)
    return 0
  catch e =>
    IO.eprintln s!"[relay] cannot read {path}: {e}"
    return 1

/-! ## The client side (drives the relay, for the self-contained check) -/

def clientNonce : ByteArray := ⟨Array.replicate 24 (0x2a : UInt8)⟩

def upgradeRequest : ByteArray :=
  "GET /derp HTTP/1.1\r\nHost: 127.0.0.1\r\nUpgrade: DERP\r\nConnection: Upgrade\r\nDerp-Fast-Start: 1\r\n\r\n".toUTF8

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

/-- One client's full login handshake against the relay; returns its fd. -/
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

/-- The self-contained end-to-end check: run the relay in a background task, log in
two clients B then A, have A send a packet addressed to B's key, and confirm B reads
it back as a RecvPacket carrying A's key and the verbatim packet. -/
def selftest (port : UInt16) : IO UInt32 := do
  let privA := ofHex "a01111111111111111111111111111111111111111111111111111111111111a"
  let privB := ofHex "b02222222222222222222222222222222222222222222222222222222222222b"
  let some pubA := (← pure (x25519Base privA)) | do IO.eprintln "x25519Base(A) failed"; return 1
  let some pubB := (← pure (x25519Base privB)) | do IO.eprintln "x25519Base(B) failed"; return 1
  IO.println s!"client A pub {toHex pubA}"
  IO.println s!"client B pub {toHex pubB}\n"
  -- start the relay in the background
  let relayTask ← IO.asTask (runRelay port)
  -- give the listener a moment to bind
  IO.sleep 300
  IO.println "=== client B login ==="
  let some fdB := (← clientLogin "B" port privB pubB) | do IO.eprintln "B login failed"; return 1
  IO.println "\n=== client A login ==="
  let some fdA := (← clientLogin "A" port privA pubA) | do tcpClose fdB; IO.eprintln "A login failed"; return 1
  IO.println "\n=== relay a real frame: A -> (relay) -> B ==="
  let packet := "hello-through-my-own-DERP-relay".toUTF8
  let sendFrame : Derp.Frame :=
    { ftype := .sendPacket, payload := Derp.bytesOf pubB ++ Derp.bytesOf packet }
  tcpSend fdA (Derp.baOf (Derp.serializeFrame sendFrame))
  IO.println s!"[A] -> FrameSendPacket to B ({(Derp.serializeFrame sendFrame).length}B)"
  -- B reads its RecvPacket
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
        let okSrc := srcPub == Derp.bytesOf pubA
        let okPkt := relayed == Derp.bytesOf packet
        IO.println s!"\n    src == A pubkey : {okSrc}"
        IO.println s!"    packet verbatim : {okPkt}"
        if okSrc ∧ okPkt then
          IO.println "\nRELAY COMPLETE — a real frame traversed MY OWN DERP relay, A -> B."
          result := 0
        else IO.eprintln "\nrelayed frame did not match"
  tcpClose fdA; tcpClose fdB
  let relayOk ← IO.wait relayTask
  match relayOk with
  | .ok true => pure ()
  | _ => IO.eprintln "[relay] did not report a successful forward"
  return result

def main (args : List String) : IO UInt32 := do
  match args with
  | "server" :: rest =>
    -- the PERSISTENT N-connection DERP region (what a stock client homes on)
    let port := (rest.getD 0 "3340").toNat?.getD 3340 |>.toUInt16
    runServer port
  | "serve" :: rest =>
    let port := (rest.getD 0 "3340").toNat?.getD 3340 |>.toUInt16
    let ok ← runRelay port
    return (if ok then 0 else 1)
  | "selftest" :: rest =>
    let port := (rest.getD 0 "3399").toNat?.getD 3399 |>.toUInt16
    selftest port
  | "certname" :: rest =>
    -- the `CertName` a served DERPMap must carry for this leaf (sha256-raw pin)
    printCertName (rest.getD 0 "conformance/tls/cert.der")
  | _ =>
    -- default: self-contained end-to-end check
    selftest 3399

end DerpRelayLive

def main (args : List String) : IO UInt32 := DerpRelayLive.main args
