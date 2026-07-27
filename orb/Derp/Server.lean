import Derp.Relay
import Derp.Frame
/-!
# DERP relay server — the frame-level dispatch, wired to the proven forwarding

`Derp.Relay` proves the *routing decision* (`step` / `forward`, with
`forward_to_addressed_only` / `relay_blind`) at the level of relay `Event`s. A live
relay, though, reads DERP **frames** off a socket. This module is the missing
adapter: the pure per-frame dispatch a relay runs — decode a `FrameSendPacket`,
split its `[dstKey 32B][packet]` payload, and forward through the *proven*
`Derp.Relay.step` — with the discipline lifted to the frame level. Every other frame
type produces no forward (the relay routes only `SendPacket`s peer-to-peer).

`DerpRelayLive.forwardLoop` runs exactly this function on real sockets, so the live
relay's routing choice IS `dispatch`, and `dispatch` IS the proven relay. Nothing here
re-implements the forwarding; it only names the frame → deliveries entry point and
carries the `forward_to_addressed_only` / `relay_blind` guarantees through it.
-/

namespace Derp.Server

open Derp Derp.Relay

/-- The relay's per-frame routing core. A `FrameSendPacket` on `srcConn` whose payload
splits into `[dstKey 32B][packet]` is forwarded through the proven `RelayState.forward`;
a malformed (short) SendPacket and every non-SendPacket frame yield no delivery. This is
the exact decision the socket loop takes on each inbound frame. -/
def dispatch (s : RelayState) (srcConn : ConnId) (f : Frame) : List Delivery :=
  match f.ftype with
  | .sendPacket =>
    match Derp.splitKeyed f.payload with
    | some (dstKey, pkt) => s.forward srcConn dstKey pkt
    | none => []
  | _ => []

/-- **Frame dispatch delivers to the addressed peer only.** Every delivery a
`FrameSendPacket` for `dstKey` produces targets the one connection registered for
`dstKey` — the frame-level lift of `forward_to_addressed_only`. -/
theorem dispatch_addressed_only (s : RelayState) (srcConn : ConnId) (f : Frame)
    (dstKey pkt : Bytes) (hf : f.ftype = .sendPacket)
    (hp : Derp.splitKeyed f.payload = some (dstKey, pkt)) :
    ∀ d ∈ dispatch s srcConn f, s.connOf dstKey = some d.dst := by
  intro d hd
  simp only [dispatch, hf, hp] at hd
  exact forward_to_addressed_only s srcConn dstKey pkt d hd

/-- **Frame dispatch is blind.** A forwarded frame is a `RecvPacket` carrying the
sender's key followed by the packet **unchanged** — the frame-level lift of
`relay_blind`. The relay never reads or rewrites the relayed packet. -/
theorem dispatch_blind (s : RelayState) (srcConn : ConnId) (f : Frame)
    (dstKey pkt srcKey : Bytes) (hf : f.ftype = .sendPacket)
    (hp : Derp.splitKeyed f.payload = some (dstKey, pkt))
    (hkey : s.keyOf srcConn = some srcKey) (hlen : srcKey.length = keyLen) :
    ∀ d ∈ dispatch s srcConn f,
      d.frame.ftype = .recvPacket ∧
      Derp.splitKeyed d.frame.payload = some (srcKey, pkt) := by
  intro d hd
  simp only [dispatch, hf, hp] at hd
  exact relay_blind s srcConn dstKey pkt srcKey hkey hlen d hd

/-- **Only SendPackets are forwarded.** A frame that is not a `FrameSendPacket`
produces no delivery — the relay never forwards handshake, keepalive, presence, or
mesh-admin frames as peer traffic. -/
theorem dispatch_only_sendpacket (s : RelayState) (srcConn : ConnId) (f : Frame)
    (h : f.ftype ≠ .sendPacket) : dispatch s srcConn f = [] := by
  unfold dispatch
  split
  · next hft => exact absurd hft h
  · rfl

/-- **A short SendPacket is dropped.** A `FrameSendPacket` whose payload is shorter
than a 32-byte destination key cannot be routed and yields no delivery — never a
mis-split, never a partial forward. -/
theorem dispatch_short_dropped (s : RelayState) (srcConn : ConnId) (f : Frame)
    (hf : f.ftype = .sendPacket) (hp : Derp.splitKeyed f.payload = none) :
    dispatch s srcConn f = [] := by
  simp only [dispatch, hf, hp]

/-! ## The registry fold — a whole frame stream through the proven relay

`serverStep` threads one `(srcConn, frame)` through the registry: a `FrameClientInfo`
registers the connection under its announced key (via the proven `RelayState.register`),
a `FrameSendPacket` forwards via `dispatch`, a `FramePeerGone` unregisters. The
registration key for a `ClientInfo` frame is supplied by the caller (the relay learns it
by opening the NaCl box — `Derp.openClientInfo`, proven in `Derp.lean`). -/

/-- One registry transition on an inbound frame. `keyHint` is the peer key the relay
learned from a `FrameClientInfo`'s opened box (used only for the registration frame). -/
def serverStep (s : RelayState) (srcConn : ConnId) (keyHint : Key) (f : Frame) :
    RelayState × List Delivery :=
  match f.ftype with
  | .clientInfo => (s.register keyHint srcConn, [])
  | .peerGone   => (s.unregister keyHint, [])
  | _           => (s, dispatch s srcConn f)

/-- **A registered ClientInfo binds the peer.** After a `FrameClientInfo` step for
`keyHint` on `srcConn`, the registry routes `keyHint` to `srcConn` — the registration
side of the relay, lifted to the frame level via the proven `register_binds`. -/
theorem serverStep_registers (s : RelayState) (srcConn : ConnId) (keyHint : Key)
    (f : Frame) (hf : f.ftype = .clientInfo) :
    (serverStep s srcConn keyHint f).1.connOf keyHint = some srcConn := by
  simp only [serverStep, hf]
  exact register_binds s keyHint srcConn

/-- **serverStep forwarding is addressed-only.** When the inbound frame is a
`SendPacket`, every delivery the registry step emits still targets the addressed peer —
the step forwards through `dispatch`, carrying `dispatch_addressed_only`. -/
theorem serverStep_addressed_only (s : RelayState) (srcConn : ConnId) (keyHint : Key)
    (f : Frame) (dstKey pkt : Bytes) (hf : f.ftype = .sendPacket)
    (hp : Derp.splitKeyed f.payload = some (dstKey, pkt)) :
    ∀ d ∈ (serverStep s srcConn keyHint f).2, s.connOf dstKey = some d.dst := by
  intro d hd
  have hstep : (serverStep s srcConn keyHint f).2 = dispatch s srcConn f := by
    simp only [serverStep, hf]
  rw [hstep] at hd
  exact dispatch_addressed_only s srcConn f dstKey pkt hf hp d hd

/-! ## Evaluation — the dispatch exercised on concrete frames (non-vacuous) -/

private def demoKey (n : UInt8) : Key := List.replicate Derp.keyLen n
private def kA : Key := demoKey 0xAA
private def kB : Key := demoKey 0xBB
private def relay2 : RelayState :=
  (RelayState.empty.register kA 1).register kB 2

-- A SendPacket frame from conn 1 to key B forwards exactly one RecvPacket to conn 2.
#guard (dispatch relay2 1 { ftype := .sendPacket, payload := kB ++ [0x68, 0x69] }).length = 1
#guard (dispatch relay2 1 { ftype := .sendPacket, payload := kB ++ [0x68, 0x69] }).head?.map (·.dst)
        = some 2
-- A KeepAlive frame forwards nothing.
#guard dispatch relay2 1 { ftype := .keepAlive, payload := [] } = []
-- A ClientInfo serverStep registers the peer.
#guard ((serverStep RelayState.empty 3 kA { ftype := .clientInfo, payload := [] }).1).connOf kA
        = some 3

end Derp.Server
