/-
Captp.Export — the C-ABI seam that wires the PROVEN capability-transport wire
codec (`Captp.decodeFrame` / `Captp.encodeFrame`, `Captp.Frame` / `Captp.Encode`)
to the native dataplane.

The frame layer proves a total, consumed-monotone decoder (`decodeFrame` — every
decode strictly advances the cursor, so a frame stream always terminates) and a
value-faithful round-trip against the encoder (`decodeFrame_encodeFrame` — on
anything the encoder produced, decoding recovers exactly the frame and leaves the
tail untouched). Until now those two theorems governed nothing on the wire: no
host called the codec. This module lifts them across the C ABI so the native
listener's frame/deframe path IS the proven codec — bounded and crash-safe by
construction, exactly as the HTTP/1.1 request framer and the WebSocket header
verdict already are.

`drorb_captp_frame` (`@[export]`) is the seam: an accumulated wire prefix in, the
encoded deframe/reframe verdict out (`[0]` = a bounded reject — the prefix is not
a decodable frame, decided totally, never a fault; `[1, kind, c₄, <encodeFrame f>]`
= the leading frame decoded to `f`, consuming `c` octets little-endian, with `f`'s
canonical re-encoding following). The re-encoding is `encodeFrame` itself, so both
halves of the proven codec ride the seam: the host DEFRAMES with `decodeFrame` and
REFRAMES its canonical response with `encodeFrame`.

Marshalling: the abstract octet type is `Byte := Nat`; wire octets arriving as
`UInt8` are lifted with `toNat` and lowered back with `ofNat`. On real wire bytes
(all ≤ 255) the lift/lower pair is the identity, and the encoder only ever emits
octets `< 256` (`toLE`'s `n % 256`), so the crossing is byte-exact — the round-trip
theorem's byte-identity survives the marshalling.

SCOPE (honest): this deploys the wire CODEC — the bounded, crash-safe framing of
capability-transport messages. It is NOT the full object-capability protocol:
descriptor resolution against the session tables (`Captp.Session`), promise
pipelining, third-party handoff, and import/export-table GC remain proven-core or
prose, un-wired. The seam governs the BYTES, not yet the objects they name.
-/
import Captp.Frame
import Captp.Encode

namespace Captp
namespace Export

/-- The frame's kind tag — the leading octet its encoding carries (§ the
reference TLV `frameTag.*`). Reported in the verdict so the host can classify a
decoded frame without re-parsing. -/
def frameKind : Frame → Byte
  | .Deliver ..     => frameTag.deliver
  | .DeliverOnly .. => frameTag.deliverOnly
  | .Listen ..      => frameTag.listen
  | .GcExport ..    => frameTag.gcExport
  | .GcAnswer ..    => frameTag.gcAnswer
  | .Abort ..       => frameTag.abort

/-- The deframe/reframe verdict on an accumulated wire prefix, as a byte list.

* `[0]` — the prefix is not a decodable frame: a bounded REJECT. `decodeFrame`
  is total, so this is a definite answer (unknown tag, or a field truncated past
  the end), never a crash.
* `1 :: kind :: (toLE 4 consumed ++ encodeFrame f)` — the leading frame decoded
  to `f`, consuming `consumed` octets (little-endian u32), with `f`'s canonical
  re-encoding following. Because `decodeFrame` and `encodeFrame` are the proven
  codec, on anything the encoder produced (`decodeFrame_encodeFrame`) the trailing
  `encodeFrame f` equals the original frame bytes, and the decoder always strictly
  advanced (`decodeFrame_consumes`). -/
def verdict (input : List Byte) : List Byte :=
  match decodeFrame input with
  | none => [0]
  | some (f, rest) =>
      let consumed := input.length - rest.length
      1 :: frameKind f :: (toLE 4 consumed ++ encodeFrame f)

/-- **`drorb_captp_frame`.** The C-ABI seam the native listener crosses to
DEFRAME an incoming capability-transport wire prefix and REFRAME the canonical
response: accumulated bytes in, the encoded verdict out. Total
`ByteArray → ByteArray` — the proven decoder is total, so a malformed prefix
yields the one-octet reject `[0]`, never a fault.

Octet marshalling is `UInt8.toNat` on the way in and `UInt8.ofNat` on the way
out; byte-exact on wire octets (≤ 255) and on all encoder output (`< 256`). -/
@[export drorb_captp_frame]
def frameExport (input : ByteArray) : ByteArray :=
  let bytes : List Byte := input.toList.map (·.toNat)
  ByteArray.mk ((verdict bytes).map (fun n => UInt8.ofNat n)).toArray

end Export
end Captp
