/-
Wireguard.Export — the C-ABI seam that wires the PROVEN transport data plane
(`Wire.sealPacket` / `Wire.openPacket`, `Wireguard.Window`) to the native
dataplane's UDP path.

Until now the deployed L4 UDP relay moved datagrams in PLAINTEXT: `forward_datagram`
sent the payload verbatim. The transport tunnel that would encrypt it — the type-4
transport-data seal/open on the verified `Crypto` ChaCha20-Poly1305, and the
RFC-6479 sliding-window anti-replay filter — was proven (`wg_transport_wire_roundtrip`,
`Window.replay_rejected`, `Window.too_old_rejected`) but governed nothing on the wire:
no host called it. This module lifts both across the C ABI so the tunnel ingress/egress
IS the proven codec: a datagram is sealed under a transport key and monotone counter,
and an inbound datagram is opened and admitted only by the proven anti-replay decision.

Two seams:

* `drorb_wg_seal` (`@[export]`) — seal one datagram. Input is
  `key(32) ‖ receiver(4, LE) ‖ counter(8, LE) ‖ payload`; output is `1 ‖ <wire>`
  where `<wire>` is the type-4 transport packet `Wire.sealPacket` produced, or `0`
  on an AEAD failure. The wire bytes are exactly the proven `sealPacket` output.

* `drorb_wg_open` (`@[export]`) — open one datagram AND take the anti-replay
  decision. Input is `key(32) ‖ win.next(8, LE) ‖ nSeen(4, LE) ‖ (nSeen × 8, LE) ‖ wire`;
  the middle carries the receive `Window` (high-water mark + the accepted counters
  still inside the window). Output is `0` on a bounded reject — the packet did not
  AEAD-open under the key, OR the proven `Window.willAccept` refused the counter
  (a replay, or too old) — and `1 ‖ win'.next(8, LE) ‖ nSeen'(4, LE) ‖
  (seen' 8, LE) ‖ plaintext` on accept, where `win'` is `Window.mark` of the
  accepted counter. The admission verdict is `Window.willAccept` and the state
  advance is `Window.mark` — both the proven anti-replay core.

Marshalling: counters ride little-endian via the proven `Wire.leList` / `Wire.leVal`.
Window counters are `Nat` in the model and `< 2^64` on the wire; the host prunes
`seen` to the window (a counter more than `windowSize` behind `next` is rejected by
`willAccept`'s too-old branch regardless of `seen` membership, so pruning it leaves
the proven decision unchanged), keeping the crossed state bounded.

SCOPE (honest): this deploys the transport DATA plane — the per-packet seal/open and
the anti-replay filter — over an ALREADY-ESTABLISHED transport key. It does NOT run
the Noise IK handshake in-band; the key is supplied by the host (config / a completed
handshake). The handshake FSM (`Peer.handleInitiation`, `Wire.mkInitiation` /
`consumeResponse`) is proven and cross-checked live (`WgLive`, `WgResponder`) but is
not part of THIS seam. The seam governs the tunnelled BYTES and their replay
admission, not the key agreement that precedes them.
-/
import Wireguard

namespace Wireguard
namespace Export

open Wireguard (Window)

/-- Little-endian `len`-byte encoding of `n`, via the proven `Wire.leList`. -/
def leBytes (n len : Nat) : List UInt8 := Wire.leList n len

/-- Numeric value of a little-endian byte list, via the proven `Wire.leVal`. -/
def leVal (bs : List UInt8) : Nat := Wire.leVal bs

/-- **`drorb_wg_seal`.** Seal one datagram into a type-4 transport packet.

Input `key(32) ‖ receiver(4, LE) ‖ counter(8, LE) ‖ payload`. Output `1 ‖ <wire>`
with `<wire>` the proven `Wire.sealPacket` output (header ‖ AEAD(key, ctr, payload)),
or the single octet `0` on an AEAD failure. -/
@[export drorb_wg_seal]
def sealExport (input : ByteArray) : ByteArray :=
  let bs := input.toList
  let key : ByteArray := ⟨(bs.take 32).toArray⟩
  let r1 := bs.drop 32
  let receiver := UInt32.ofNat (leVal (r1.take 4))
  let r2 := r1.drop 4
  let ctr := UInt64.ofNat (leVal (r2.take 8))
  let payload : ByteArray := ⟨(r2.drop 8).toArray⟩
  match Wire.sealPacket key receiver ctr payload with
  | some wire => ByteArray.mk (((1 : UInt8) :: wire).toArray)
  | none      => ByteArray.mk #[(0 : UInt8)]

/-- **`drorb_wg_open`.** Open one datagram and take the anti-replay decision.

Input `key(32) ‖ next(8, LE) ‖ nSeen(4, LE) ‖ (nSeen × 8, LE) ‖ wire`. The middle
carries the receive `Window`. Output `0` on a bounded reject (AEAD did not open, or
the proven `Window.willAccept` refused the counter — a replay or too old); on accept,
`1 ‖ next'(8, LE) ‖ nSeen'(4, LE) ‖ (seen' 8, LE) ‖ plaintext`, where the window
advanced by the proven `Window.mark`. -/
@[export drorb_wg_open]
def openExport (input : ByteArray) : ByteArray :=
  let bs := input.toList
  let key : ByteArray := ⟨(bs.take 32).toArray⟩
  let r1 := bs.drop 32
  let winNext := leVal (r1.take 8)
  let r2 := r1.drop 8
  let nSeen := leVal (r2.take 4)
  let r3 := r2.drop 4
  let seen := (List.range nSeen).map (fun i => leVal ((r3.drop (i * 8)).take 8))
  let wire := r3.drop (nSeen * 8)
  let w : Window := { next := winNext, seen := seen }
  match Wire.openPacket key wire with
  | some (_receiver, ctr, pt) =>
      let c := ctr.toNat
      if w.willAccept c then
        let w' := w.mark c
        let seenBytes := w'.seen.flatMap (fun s => leBytes s 8)
        let hdr := (1 : UInt8) :: (leBytes w'.next 8 ++ leBytes w'.seen.length 4 ++ seenBytes)
        ByteArray.mk ((hdr ++ pt.toList).toArray)
      else ByteArray.mk #[(0 : UInt8)]
  | none => ByteArray.mk #[(0 : UInt8)]

end Export
end Wireguard
