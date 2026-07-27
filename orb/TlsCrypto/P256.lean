/-
# TlsCrypto.P256 — secp256r1 (NIST P-256) ECDH over verified HACL*

RFC 8446 §9.1 makes `secp256r1` a MUST-support named group for TLS 1.3 key
exchange. This module binds HACL*'s `Hacl_P256` (F*-verified: memory-safe,
functionally correct against the P-256 group spec, secret-independent) through
the thin adapter in `ffi/tls_p256_shim.c` — the same trusted-crossing pattern
as `Crypto.lean` over `ffi/crypto_shim.c`.

The handshake core (`TlsHandshake`) does NOT import this module: it reaches
P-256 through the `ServerParams.p256Dh` function seam, which defaults to
"unsupported". Only executables that link `ffi/tls_p256_shim.o` (the TLS
conformance oracle and the handshake selftest) import this module and
instantiate the seam with `dhPair`; everything else keeps its link line.

Wire format (RFC 8446 §4.2.8.2): a secp256r1 KeyShareEntry carries the SEC1
uncompressed point `0x04 ‖ X(32) ‖ Y(32)`; the ECDH shared secret is the
32-byte X coordinate (§7.4.2). Invalid scalars and off-curve/infinity points
return `none` (Hacl_P256 validates the peer point before the scalar
multiplication).
-/
import TlsCrypto

namespace TlsCrypto.P256

/-- The server's secp256r1 key share (65-byte uncompressed point) for a
32-byte scalar; `none` if the scalar is not in `(0, order)`. -/
@[extern "drorb_p256_pub"]
opaque pub (priv : ByteArray) : Option ByteArray

/-- P-256 ECDH: the 32-byte X coordinate of `priv · peerPoint` (RFC 8446
§7.4.2), where `peer` is a 65-byte uncompressed point. `none` on a malformed
or invalid (off-curve, infinity) point or an invalid scalar. -/
@[extern "drorb_p256_ecdh"]
opaque ecdh (priv peer : ByteArray) : Option ByteArray

/-- The `ServerParams.p256Dh` seam instantiation: from the server's 32-byte
ephemeral scalar and the client's key-share bytes, produce the server's own
KeyShareEntry point and the shared secret. -/
def dhPair (priv : ByteArray) (peer : Tls.Bytes) : Option (ByteArray × ByteArray) :=
  match pub priv, ecdh priv (ByteArray.mk peer.toArray) with
  | some serverShare, some shared => some (serverShare, shared)
  | _, _ => none

end TlsCrypto.P256
