import Gzip
import Reactor.App

/-!
# Proto.GzipLargeProven — the size-agnostic gzip stored-block LAYOUT (the >64 KiB fix)
  AND an honest deployed-surface finding.

PROVE-WHAT-RUNS for the datapath row `h1.gzip.large` (`DRORB_RUST_GZIP=1`, the flate2
recompress seam), the FIX for the `Proto.GzipProven` finding (a >64 KiB stored block's
16-bit `LEN` field overflows, so the old flate2-*gunzip* handoff could not recover the
plaintext above 64 KiB).

## The fix (what the deployed seam now does)

`crates/dataplane/src/gzip.rs :: extract_stored_plaintext` no longer trusts the stored
block's 16-bit `LEN`. It reads the plaintext by FIXED OFFSET and the 32-bit `ISIZE`
trailer instead: the proven `Gzip.gzipStored` stream is `10-byte header · 5-byte stored
framing · BODY · CRC32(4) · ISIZE(4)`, so the plaintext is exactly `gz[15 .. len-8)` and
its length is recovered from `ISIZE = |body| mod 2³²` — SIZE-AGNOSTIC. It then re-deflates
that plaintext with `flate2` (TRUSTED, not verified) and checks CRC/ISIZE.

## What is proven here (pure-kernel, no `native_decide`, over `Gzip.gzipStored`)

* `gzipStored_body_at_15` — for ANY body `x` (incl. 1 MiB), the plaintext sits VERBATIM
  at fixed offset 15: `((gzipStored x).drop 15).take x.length = x`. This is exactly the
  window the fixed extractor reads; it does not depend on the 16-bit `LEN`.
* `gzipStored_isize` — the last 4 bytes are `u32le (x.length mod 2³²)`, the `ISIZE` the
  extractor uses to recover the body length (again size-agnostic).
* `gzipStored_length` — the stream is `x.length + 23` bytes (`10 + 5 + len + 8`).
* `bulk_fix_recovers_1MiB` — applied to the deployed 1 MiB `/bulk` body: the 16-bit `LEN`
  field is `[0,0]` (≠ the real length — WHY the old path failed), yet the fixed-offset +
  `ISIZE` recovery returns the full 1 MiB body and `ISIZE` decodes to exactly `1048576`.
  So the fix is correct at 1 MiB precisely where the old path broke — the contrast with
  `Proto.GzipProven.bulk_gzip_malformed` is the point.

## Deployed reality (curl-confirmed on hbox — one CONFIRMED, one FINDING)

CONFIRMED live: `DRORB_RUST_GZIP=1 ./dataplane --bind 127.0.0.1:8103 --io blocking`; the
recompress seam runs `extract_stored_plaintext` on every gzipped response and round-trips:

    $ curl -s -H 'Accept-Encoding: gzip' http://127.0.0.1:8103/ -o root.gz -D hdr
        Content-Encoding: gzip
    $ gunzip -c root.gz | cmp -s - <(curl -s http://127.0.0.1:8103/) && echo ROUND-TRIP-OK
        ROUND-TRIP-OK          # the extract+recompress path is LIVE and byte-exact

FINDING (a false-deployed premise, caught): the 1 MiB `/bulk` route the fix TARGETS is
NOT wired into the deployed serve. The deployed `drorbServe` runs
`Reactor.Deploy.deployStepFull2` over `demoAppConfig` (routes: `/health → 200`, default
`404`); `bulkRoute` (1 MiB) lives only in `Reactor.App.demoApp`/`demoVhBlocks`, used in
proofs, NOT in `demoAppConfig`. On the running binary:

    $ curl -s -o /dev/null -w '%{http_code} %{size_download}\n' http://127.0.0.1:8103/bulk
        404 162
    $ curl -s -o /dev/null -w '%{http_code}\n' http://127.0.0.1:8103/static/app.js
        404
    # only `/` (small HTML) and `/health` (2 bytes) are served; NO route emits a >64 KiB
    # body through the gzip pipeline, so the >64 KiB round-trip cannot be exercised
    # end-to-end on this binary's app surface. The fix's CORRECTNESS at 1 MiB is proven
    # (below); its DEPLOYMENT needs `bulkRoute` wired into `demoAppConfig` (out of lane).

Axioms ⊆ {propext, Quot.sound}; `decide`/`rfl`/`simp` only.
-/

namespace Proto.GzipLargeProven

open Reactor.App (bulkBody bulkSize bulkBody_length)

/-! ## The stored-block byte layout, factored as `pre15 · body · suf8` -/

/-- The 15-byte prefix of `gzipStored x`: the 10-byte gzip header, the stored-block
header byte `0x01`, and the two 16-bit `LEN`/`NLEN` fields. Its LENGTH is 15 for every
`x` (`pre15_length`), so the body always begins at offset 15. -/
def pre15 (x : List UInt8) : List UInt8 :=
  Gzip.mkHeader ++ [0x01] ++ Deflate.u16le x.length ++ Deflate.u16le (65535 - x.length)

/-- The 8-byte trailer of `gzipStored x`: `CRC32(x)` then `ISIZE = |x| mod 2³²`. -/
def suf8 (x : List UInt8) : List UInt8 :=
  Gzip.u32le (Gzip.crc32 x).toNat ++ Gzip.u32le (x.length % 4294967296)

theorem pre15_length (x : List UInt8) : (pre15 x).length = 15 := by
  simp [pre15, Gzip.mkHeader, Deflate.u16le]

/-- **The layout factorization.** `gzipStored x = pre15 x ++ (x ++ suf8 x)` — the body
`x` sits between a 15-byte prefix and an 8-byte trailer, VERBATIM. -/
theorem gzipStored_split (x : List UInt8) :
    Gzip.gzipStored x = pre15 x ++ (x ++ suf8 x) := by
  simp only [Gzip.gzipStored, Deflate.deflateStored, pre15, suf8,
    List.append_assoc, List.cons_append, List.nil_append]

/-! ## The size-agnostic recovery invariants the fixed extractor relies on -/

/-- **`gzipStored_body_at_15`.** For ANY body `x`, the plaintext sits verbatim at fixed
offset 15: reading `x.length` bytes from offset 15 returns `x`. This is exactly the
window `extract_stored_plaintext` reads (`gz[15 .. 15+len)`); it does NOT depend on the
16-bit `LEN` — so it is correct for a 1 MiB body where `LEN` overflows. -/
theorem gzipStored_body_at_15 (x : List UInt8) :
    ((Gzip.gzipStored x).drop 15).take x.length = x := by
  rw [gzipStored_split x, ← pre15_length x, List.drop_left, List.take_left]

/-- **`gzipStored_isize`.** The last 4 bytes are `u32le (x.length mod 2³²)` — the `ISIZE`
trailer the extractor uses to recover the body length (size-agnostic). The offset
`x.length + 19` is `15 (prefix) + x.length (body) + 4 (CRC)`. -/
theorem gzipStored_isize (x : List UInt8) :
    (Gzip.gzipStored x).drop (x.length + 19) = Gzip.u32le (x.length % 4294967296) := by
  have hsplit : Gzip.gzipStored x
      = (pre15 x ++ x ++ Gzip.u32le (Gzip.crc32 x).toNat) ++ Gzip.u32le (x.length % 4294967296) := by
    simp only [Gzip.gzipStored, Deflate.deflateStored, pre15,
      List.append_assoc, List.cons_append, List.nil_append]
  have hlen : (pre15 x ++ x ++ Gzip.u32le (Gzip.crc32 x).toNat).length = x.length + 19 := by
    simp only [List.length_append, pre15_length, Gzip.u32le, List.length_cons, List.length_nil]
    omega
  rw [hsplit, ← hlen, List.drop_left]

/-- **`gzipStored_length`.** The stored-block gzip stream is `x.length + 23` bytes
(`10 header + 5 framing + len + 4 CRC + 4 ISIZE`), for every `x`. -/
theorem gzipStored_length (x : List UInt8) :
    (Gzip.gzipStored x).length = x.length + 23 := by
  rw [gzipStored_split x]
  simp only [List.length_append, pre15_length, suf8, Gzip.u32le, List.length_cons, List.length_nil]
  omega

/-! ## Applied to the deployed 1 MiB `/bulk` body — the fix works where the old path broke -/

/-- **`bulk_fix_recovers_1MiB`.** For the deployed 1 MiB `/bulk` body:
1. the 16-bit stored `LEN` field is `[0,0]` — it does NOT encode the real length
   (`1048576 mod 65536 = 0`); this is exactly why the OLD flate2-gunzip handoff failed
   (`Proto.GzipProven.bulk_gzip_malformed`);
2. yet the FIXED fixed-offset recovery returns the FULL 1 MiB body; and
3. the `ISIZE` trailer decodes to exactly `1048576`, so the extractor's `ISIZE` check
   passes and it recovers the exact body length WITHOUT reading `LEN`.
The fix is proven correct at 1 MiB — precisely the regime the old path could not handle. -/
theorem bulk_fix_recovers_1MiB :
    Deflate.u16le bulkBody.length = [0, 0]
  ∧ ((Gzip.gzipStored bulkBody).drop 15).take bulkBody.length = bulkBody
  ∧ bulkBody.length % 4294967296 = 1048576
  ∧ (Gzip.gzipStored bulkBody).drop (bulkBody.length + 19)
      = Gzip.u32le (bulkBody.length % 4294967296) := by
  have hlen : bulkBody.length = 1048576 := bulkBody_length.trans (by rfl)
  refine ⟨?_, gzipStored_body_at_15 bulkBody, ?_, gzipStored_isize bulkBody⟩
  · rw [hlen]; decide
  · rw [hlen]

end Proto.GzipLargeProven

#print axioms Proto.GzipLargeProven.gzipStored_body_at_15
#print axioms Proto.GzipLargeProven.gzipStored_isize
#print axioms Proto.GzipLargeProven.gzipStored_length
#print axioms Proto.GzipLargeProven.bulk_fix_recovers_1MiB
