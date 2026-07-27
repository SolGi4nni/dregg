import Datapath.HtmlRewriteDense
import Gzip
import Deflate

/-!
# Datapath.GzipDense — the DENSE (index-native, `ByteArray`) gzip body transform,
proven byte-identical to the DEPLOYED `Gzip.gzipStored` (the body rewrite the
`Reactor.Stage.Gzip.gzipStage` runs when a request accepts `Accept-Encoding: gzip`).

The deployed gzip body transform is

    gzipStored x = mkHeader ++ deflateStored x ++ u32le (crc32 x).toNat
                            ++ u32le (x.length % 2³²)

with `deflateStored x = 0x01 :: u16le x.length ++ u16le (65535 - x.length) ++ x`.
On the deployed `List UInt8` body every one of those pieces is a cons-list: the
CRC-32 is a `List.foldl` over the body, and the DEFLATE **stored** block copies the
body as a cons-list (`… ++ x`). So the whole transform walks and re-conses the body.

★ HONEST NOTE ON DEFLATE. The RFC 1951 layer the deployed gzip uses is a *stored*
block (`BTYPE = 00`): a 5-byte framing header (`0x01`, `LEN`, `NLEN = ~LEN`) then a
**literal copy** of the body — there is NO LZ77 window and NO Huffman table here.
The whole `gzipStored` transform is therefore a clean fold + a literal copy + fixed
framing, all of which go dense. This file makes ALL of it dense; there is no genuine
compression loop to leave as a residual for THIS deployed transform. (An LZ77 +
Huffman `deflateFixed`/dynamic path exists in `Deflate.lean` but is NOT what the
deployed `gzipStored`-based stage runs; it is not on this path.)

This module re-expresses the SAME transform over `ByteArray`, index-native, reusing
the ONE generic stateful-fold combinator `byteArray_foldl_toList` from
`Datapath.HtmlRewriteDense` (the combinator that made htmlrewrite dense):

* `gzipCrc32Dense` — the CRC-32 checksum fold run over the `ByteArray` by index
  (`ByteArray.foldl`, the native bounded loop, NO `toList`); proven equal to the
  deployed `Gzip.crc32` on the byte denotation via `byteArray_foldl_toList`.
* `pushBytes` — copy a `ByteArray` body onto an accumulator by index (`ByteArray.foldl
  ByteArray.push`), the dense analogue of the stored block's literal `… ++ x`; proven
  to denote list append, again via `byteArray_foldl_toList`.
* `gzipBytesDense` — assemble the full RFC 1952 container into a `ByteArray` by `push`
  (fixed header/framing bytes ‖ dense body copy ‖ CRC-32 / ISIZE trailer);
  `gzipBytesDense_refines` proves it is byte-identical to the deployed
  `Gzip.gzipStored`. The `List UInt8` appears ONLY on the spec (RHS) side of the
  equality — the `ByteArray` compute path materialises NO body `List`.
-/

namespace Datapath.GzipDense

open Datapath.HtmlRewriteDense (byteArray_foldl_toList pushList pushList_toList empty_data_toList)

/-! ## 1. CRC-32 dense — the checksum fold over `ByteArray` by index -/

/-- **Dense gzip CRC-32.** Run the DEPLOYED per-byte reduction `Gzip.crc32Byte` over
the `ByteArray` by index (`ByteArray.foldl` — the native bounded loop, NO body
`toList`), pre-conditioned and inverted exactly as the deployed `Gzip.crc32`. -/
def gzipCrc32Dense (bs : ByteArray) : UInt32 :=
  (ByteArray.foldl Gzip.crc32Byte 0xFFFFFFFF bs) ^^^ 0xFFFFFFFF

/-- The dense CRC-32 is exactly the deployed `Gzip.crc32` on the byte denotation —
the index-native walk computes the identical checksum. The `toList` lives only on the
spec (RHS). Reuses the SAME `byteArray_foldl_toList` combinator as the tokenizer. -/
theorem gzipCrc32Dense_eq (bs : ByteArray) :
    gzipCrc32Dense bs = Gzip.crc32 bs.data.toList := by
  unfold gzipCrc32Dense Gzip.crc32
  rw [byteArray_foldl_toList]

/-! ## 2. Dense body copy — the stored block's literal `… ++ x`, index-native -/

/-- Copy every byte of a `ByteArray` onto an accumulator `ByteArray` by index
(`ByteArray.foldl ByteArray.push`) — the dense analogue of the stored block's literal
`… ++ x` (NO `toList`, NO cons-spine). -/
def pushBytes (acc bs : ByteArray) : ByteArray :=
  ByteArray.foldl ByteArray.push acc bs

/-- `pushBytes` denotes list append — proven from the SAME `byteArray_foldl_toList`
combinator, reusing `pushList_toList`. -/
theorem pushBytes_toList (acc bs : ByteArray) :
    (pushBytes acc bs).data.toList = acc.data.toList ++ bs.data.toList := by
  unfold pushBytes
  rw [byteArray_foldl_toList]
  show (pushList acc bs.data.toList).data.toList = acc.data.toList ++ bs.data.toList
  rw [pushList_toList]

/-! ## 3. The dense gzip container — proven byte-identical to `Gzip.gzipStored` -/

/-- **The dense gzip body transform.** Assemble the RFC 1952 container into a
`ByteArray` by `push`: the fixed header ‖ the stored-block framing (`0x01`, `LEN`,
`NLEN`) ‖ the dense body copy ‖ the CRC-32 / ISIZE trailer. NO body `List` on the
compute path — the body is read index-native by `pushBytes`, the CRC by
`gzipCrc32Dense`, and `bs.size` is the length. -/
def gzipBytesDense (bs : ByteArray) : ByteArray :=
  pushList
    (pushBytes
      (pushList ByteArray.empty
        (Gzip.mkHeader ++ 0x01 :: Deflate.u16le bs.size ++ Deflate.u16le (65535 - bs.size)))
      bs)
    (Gzip.u32le (gzipCrc32Dense bs).toNat ++ Gzip.u32le (bs.size % 4294967296))

/-- **THE REFINEMENT.** The dense `ByteArray` gzip container is byte-identical to the
DEPLOYED `Gzip.gzipStored` run on the byte denotation. The `List UInt8` appears ONLY
on the spec (RHS); the compute path is pure `ByteArray`. -/
theorem gzipBytesDense_refines (bs : ByteArray) :
    (gzipBytesDense bs).data.toList = Gzip.gzipStored bs.data.toList := by
  unfold gzipBytesDense
  rw [pushList_toList, pushBytes_toList, pushList_toList, empty_data_toList,
      List.nil_append, gzipCrc32Dense_eq, show bs.size = bs.data.toList.length from rfl]
  unfold Gzip.gzipStored Deflate.deflateStored
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-! ## 4. Non-vacuity — a concrete body, dense-gzipped, equals the deployed gzip -/

/-- `"hi"` as a `ByteArray` (bytes `0x68 0x69`). -/
def demoBody : ByteArray := ⟨#[0x68, 0x69]⟩

/-- The dense gzip of `"hi"` is the SAME bytes the deployed `Gzip.gzipStored` computes
on the list body — a direct instance of the refinement. -/
example : (gzipBytesDense demoBody).data.toList = Gzip.gzipStored demoBody.data.toList :=
  gzipBytesDense_refines demoBody

/-- Concrete: the dense gzip output equals the DEPLOYED gzip container of `[0x68,0x69]`
byte-for-byte. -/
theorem gzipBytesDense_demo_eq_deployed :
    (gzipBytesDense demoBody).data.toList = Gzip.gzipStored [0x68, 0x69] :=
  gzipBytesDense_refines demoBody

set_option maxRecDepth 100000 in
/-- The dense gzip genuinely changes the body: `"hi"` (2 bytes) becomes the full RFC
1952 container (25 bytes: 10 header + 5 stored-framing + 2 body + 8 trailer), NOT
the plaintext. -/
theorem gzipBytesDense_changes_demo :
    (gzipBytesDense demoBody).data.toList ≠ demoBody.data.toList := by decide

set_option maxRecDepth 100000 in
/-- **Round-trip: the dense gzip output is a valid gzip stream.** `Gzip.gunzip` of the
DENSE container recovers exactly `"hi"` with no error — the dense bytes ARE a real
gzip stream (via the refinement + the deployed `Gzip.gzip_accepts_valid`). -/
theorem gzipBytesDense_roundtrips :
    (Gzip.gunzip ⟨100⟩ (gzipBytesDense demoBody).data.toList).out = #[0x68, 0x69]
      ∧ (Gzip.gunzip ⟨100⟩ (gzipBytesDense demoBody).data.toList).err = none := by
  rw [gzipBytesDense_refines]
  exact Gzip.gzip_accepts_valid

#print axioms gzipCrc32Dense_eq
#print axioms pushBytes_toList
#print axioms gzipBytesDense_refines
#print axioms gzipBytesDense_demo_eq_deployed
#print axioms gzipBytesDense_changes_demo
#print axioms gzipBytesDense_roundtrips

end Datapath.GzipDense
