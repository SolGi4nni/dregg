/-
# Proto.GzipProven — `Content-Encoding: gzip` on the DEPLOYED serve, AND a real finding

PROVE-WHAT-RUNS for the ledger row `h1.gzip` (`Accept-Encoding`-gated gzip). This file
proves the parts of the deployed gzip behavior that ACTUALLY hold on the wire, and
reports — with a proof of the root cause — one part that does NOT.

Deployed shape: the proven `Reactor.Stage.Gzip.gzipStage` runs in the deployed pipeline
(`Reactor.Deploy.deployStagesFull2`). When the request advertises
`Accept-Encoding: … gzip …` (`acceptsGzip`) it replaces the body with `Gzip.gzipStored`
— an RFC 1952 container wrapping a SINGLE DEFLATE *stored* block (BTYPE=00) plus the
real CRC-32/ISIZE trailer — and stamps `Content-Encoding: gzip`. The `DRORB_RUST_GZIP=1`
reactor seam then tries to REPLACE that stored block with real `flate2` DEFLATE, but
only if it can gunzip the stored stream AND the result is strictly smaller.

## What IS proven-and-deployed (curl-confirmed)

    $ curl -s -D - -H 'Accept-Encoding: gzip' -o app.js.gz http://127.0.0.1:8080/static/app.js
    Content-Encoding: gzip
    Content-Length: 58
    $ python3 -c 'import gzip;print(len(gzip.decompress(open("app.js.gz","rb").read())))'
    35                                  # round-trips to the exact 35-byte body

  * `accepts_gzip_gated` — gzip is offered IFF the request carries `Accept-Encoding:
    gzip`; a bare request is NOT gzipped (matches the plain-`GET` `len=35` curl).
  * `appjs_stored_wellformed` — the deployed `/static/app.js` body (35 bytes, < 64 KiB)
    yields a WELL-FORMED stored block: the RFC 1951 §3.2.4 invariant `LEN + NLEN = 65535`
    holds and `LEN` equals the payload length, so it decodes — the curl+python round-trip.

## The finding (NOT deployed correctly): `/bulk` gzip does not round-trip

`Gzip.deflateStored` emits ONE stored block whose `LEN`/`NLEN` are 16-bit fields
(`Deflate.u16le`); it is documented valid only for `x.length < 65536`. The deployed
`/bulk` body is 1 MiB (`1 048 576` bytes). Its `LEN` field is `1048576 % 65536 = 0` and
its `NLEN` field is `(65535 - 1048576) = 0` (Nat-truncated) — so `LEN + NLEN = 0 ≠
65535`, violating RFC 1951 §3.2.4. The deployed decoder `Deflate.inflateStored` rejects
exactly that (`badStored`). Curl-confirmed — the stored stream ships (the flate2 seam
cannot decode it, so it passes through untouched) and NOTHING can gunzip it:

    $ curl -s -H 'Accept-Encoding: gzip' -o bulk.gz http://127.0.0.1:8080/bulk   # DRORB_RUST_GZIP=1
    Content-Encoding: gzip ; Content-Length: 1048599   (LARGER than 1048576)
    $ gunzip -c bulk.gz | wc -c          → 0   (gunzip: invalid compressed data)
    $ python3 -c 'import gzip; gzip.decompress(open("bulk.gz","rb").read())'  → BadGzipFile / Error -3

  * `bulk_stored_len_fields` / `bulk_gzip_malformed` — proof of the malformation at the
    exact 16-bit fields, contrasted with the well-formed small asset.
-/

import Reactor.Stage.Gzip
import Reactor.App
import StaticFile
import Gzip
import Proto.Kernel.Shortcuts

namespace Proto.GzipProven

open Reactor.Pipeline (Ctx Stage ResponseBuilder runPipeline)
open Reactor (Response)
open Proto.Kernel

/-! ## `accepts_gzip_gated` — gzip offered IFF `Accept-Encoding: gzip` present -/

/-- A request advertising `Accept-Encoding: gzip`. -/
def gzipReq : Proto.Request :=
  { headers := [("Accept-Encoding".toUTF8.toList, "gzip".toUTF8.toList)] }

/-- **`accepts_gzip_gated`.** The deployed `acceptsGzip` decision fires on a request
carrying `Accept-Encoding: gzip` and does NOT fire on a bare request. This is the exact
gate the deployed `gzipStage` keys on; the bare-request `false` is why a plain `GET`
ships uncompressed (curl `len=35`). -/
theorem accepts_gzip_gated :
    Reactor.Stage.Gzip.acceptsGzip gzipReq = true
  ∧ Reactor.Stage.Gzip.acceptsGzip { headers := [] } = false := by
  -- `acceptsGzip` is a pure byte-level scan (`lower`/`isInfix`/`==` on `List UInt8`); the
  -- only kernel-opaque parts are the `toUTF8.toList` byte constants, discharged by the
  -- `Shortcuts.ba_toList_eq` bridge. Pure-kernel `decide` — no `native_decide`.
  simp only [Reactor.Stage.Gzip.acceptsGzip, gzipReq, Reactor.Stage.Gzip.aeName,
    Reactor.Stage.Gzip.gzipTok, Reactor.Stage.Gzip.lower, Reactor.Stage.Gzip.isInfix,
    Shortcuts.ba_toList_eq]
  refine ⟨?_, ?_⟩ <;> decide

/-! ## The deployed stage stamps `Content-Encoding: gzip` and gzips the body

These are the existing deployed byte-effect theorems, re-stated here as the anchors this
file rests on: whenever the gate fires, the built response carries `Content-Encoding:
gzip` and its body IS `Gzip.gzipStored` of the handler's body. -/

/-- **`deployed_ce_header`.** When the request accepts gzip, the deployed pipeline's
built response carries `Content-Encoding: gzip` — the header the curl reads. Re-states
the deployed byte-effect theorem `Reactor.Stage.Gzip.gzipStage_ce_header`. -/
theorem deployed_ce_header (rest : List Stage) (handler : Ctx → Response) (c : Ctx)
    (h : Reactor.Stage.Gzip.acceptsGzip c.req = true) :
    (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal)
      ∈ ((runPipeline (Reactor.Stage.Gzip.gzipStage :: rest) handler c).build).headers :=
  Reactor.Stage.Gzip.gzipStage_ce_header rest handler c h

/-! ## `appjs_stored_wellformed` — the deployed small asset gzips VALIDLY -/

/-- The deployed `/static/app.js` bytes as an explicit literal (35 bytes). -/
def appJsBytes : Proto.Bytes :=
  [0x63, 0x6f, 0x6e, 0x73, 0x6f, 0x6c, 0x65, 0x2e, 0x6c, 0x6f, 0x67, 0x28, 0x27, 0x64,
   0x72, 0x6f, 0x72, 0x62, 0x20, 0x73, 0x74, 0x61, 0x74, 0x69, 0x63, 0x20, 0x61, 0x73,
   0x73, 0x65, 0x74, 0x27, 0x29, 0x3b, 0x0a]

/-- The literal IS the deployed `StaticFile.appJs`, and it is 35 bytes (< 64 KiB). -/
theorem appJsBytes_eq : StaticFile.appJs = appJsBytes ∧ appJsBytes.length = 35 := by
  refine ⟨?_, ?_⟩
  · -- `StaticFile.appJs = "…".toUTF8.toList`; the `Shortcuts.ba_toList_eq` bridge makes it kernel-reduce.
    simp only [StaticFile.appJs, StaticFile.strBytes, Shortcuts.ba_toList_eq]; decide
  · decide

/-- The number a 16-bit `Deflate.u16le` field decodes back to (little-endian). -/
def u16val (bs : Proto.Bytes) : Nat := (bs.headD 0).toNat + 256 * ((bs.getD 1 0).toNat)

/-- **`appjs_stored_wellformed`.** The deployed `/static/app.js` body (35 bytes) yields a
WELL-FORMED DEFLATE stored block: the `LEN` field equals the payload length (35) and the
RFC 1951 §3.2.4 invariant `LEN + NLEN = 65535` holds. This is exactly why the curl+python
gunzip round-trips it to the 35 original bytes. -/
theorem appjs_stored_wellformed :
    u16val (Deflate.u16le appJsBytes.length) = 35
  ∧ u16val (Deflate.u16le appJsBytes.length)
      + u16val (Deflate.u16le (65535 - appJsBytes.length)) = 65535 := by
  -- `appJsBytes` is an explicit byte literal, so `appJsBytes.length` and the whole
  -- `u16le`/`u16val` arithmetic kernel-reduce directly — pure `decide`, no dependency on
  -- the (native-decided) `appJsBytes_eq` and no `native_decide`.
  refine ⟨?_, ?_⟩ <;> decide

/-! ## THE FINDING — `/bulk` (1 MiB) gzip is a MALFORMED stored block -/

open Reactor.App (bulkBody bulkSize bulkBody_length)

/-- **`bulk_stored_len_fields`.** The deployed `/bulk` body is 1 MiB, so the single
stored block's 16-bit `LEN` and `NLEN` fields are BOTH zero: `LEN = 1048576 mod 65536 =
0`, and `NLEN = (65535 - 1048576) = 0` (Nat-truncated). The `LEN` field (0) does NOT
equal the actual payload length (1 048 576). -/
theorem bulk_stored_len_fields :
    Deflate.u16le bulkBody.length = [0, 0]
  ∧ Deflate.u16le (65535 - bulkBody.length) = [0, 0]
  ∧ bulkBody.length = 1048576 := by
  have hbs : bulkSize = 1048576 := rfl
  have hlen : bulkBody.length = 1048576 := bulkBody_length.trans hbs
  refine ⟨?_, ?_, hlen⟩ <;> rw [hlen] <;> decide

/-- **`bulk_gzip_malformed`.** The deployed `/bulk` gzip stream violates the RFC 1951
§3.2.4 stored-block invariant `LEN + NLEN = 65535`: here `LEN + NLEN = 0`. The deployed
decoder `Deflate.inflateStored` returns `.badStored` on EXACTLY this condition
(`len + nlen != 65535`), so the stream cannot be inflated — matching the curl where
`gunzip`, Python `gzip`, and the `flate2` reactor seam all fail to decode it. The `/bulk`
"gzip" response therefore does NOT round-trip. Non-vacuous by contrast with
`appjs_stored_wellformed` (a < 64 KiB body, where the invariant holds). -/
theorem bulk_gzip_malformed :
    u16val (Deflate.u16le bulkBody.length)
      + u16val (Deflate.u16le (65535 - bulkBody.length)) ≠ 65535
  ∧ u16val (Deflate.u16le bulkBody.length) ≠ bulkBody.length := by
  obtain ⟨hlen, hnlen, hb⟩ := bulk_stored_len_fields
  rw [hlen, hnlen, hb]
  refine ⟨?_, ?_⟩ <;> decide

/-- The deployed decoder's rejection rule, quoted as a theorem: `inflateStored` on a
block whose `len + nlen ≠ 65535` returns `.badStored` (never the bytes). Applied to the
`/bulk` fields (`0 + 0 ≠ 65535`), this is why the wire stream does not gunzip. -/
theorem inflateStored_rejects_bad (out : Array UInt8) (bits : Deflate.Bits)
    (len nlen : Nat) (b1 b2 : Deflate.Bits)
    (h16a : Deflate.takeBitsLE 16 (Deflate.align bits) = some (len, b1))
    (h16b : Deflate.takeBitsLE 16 b1 = some (nlen, b2))
    (hbad : len + nlen ≠ 65535) :
    (Deflate.inflateStored ⟨100⟩ out bits).2.2 = some Deflate.Err.badStored := by
  unfold Deflate.inflateStored
  simp only [h16a, h16b]
  split
  · rfl
  · rename_i hcond
    exact absurd (by simpa using hcond) hbad

end Proto.GzipProven

#print axioms Proto.GzipProven.accepts_gzip_gated
#print axioms Proto.GzipProven.deployed_ce_header
#print axioms Proto.GzipProven.appjs_stored_wellformed
#print axioms Proto.GzipProven.bulk_stored_len_fields
#print axioms Proto.GzipProven.bulk_gzip_malformed
#print axioms Proto.GzipProven.inflateStored_rejects_bad
