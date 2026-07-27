import Reactor.Stage.Gzip

/-!
# O11y.CompressProven — the deployed gzip response-compression behaviour

PROVE-WHAT-RUNS for ledger row `ob.compress` (response compression). The deployed
serve threads `Reactor.Stage.Gzip.gzipStage` verbatim inside `deployStagesFull2`
(slot 11), so the theorems below — stated over an ARBITRARY tail / handler / ctx —
are exactly the deployed stage's semantics; the tail instantiates to the
`deployStagesFull2` suffix `[htmlrewrite, security, header]` on the real path. The
`--io uring` curl (see the lane return) re-confirms the wire.

Three angles, matched to what the engine ACTUALLY emits:

* `compress_when_accepted` — `Accept-Encoding: gzip` ⇒ the finalized response
  carries `Content-Encoding: gzip` AND its body is a well-formed RFC 1952 gzip
  container: `Gzip.parseHeader` of the emitted body succeeds with the magic
  (`ID1=0x1f`, `ID2=0x8b`) and DEFLATE method (`CM=0x08`), exposing the DEFLATE
  payload ‖ CRC-32/ISIZE trailer. A real client's `gunzip` parses it.
* `compress_stream_decodes` — a CONCRETE deployed body (the default `404` body
  `"not found"`) gzipped by the stage decodes back to the exact bytes with no
  error, through the real `Gzip.gunzip` (header parse → inflate → CRC-32 + ISIZE
  check). Kernel-computed, not asserted.
* `compress_skips_unaccepted` — no `Accept-Encoding` (`acceptsGzip = false`) ⇒ the
  stage is the IDENTITY on the builder: it adds no header and rewrites no byte.

## REAL FINDING (`compress_small_not_skipped`)

The reference (a gzip middleware with a `minSize: 1024` threshold) leaves
responses below a size threshold uncompressed ("response below minSize is NOT
compressed"). The DEPLOYED `gzipStage` has NO such threshold: `acceptsGzip = true`
compresses EVERY body regardless of size. `compress_small_not_skipped` proves it —
a 1-byte body still gets `Content-Encoding: gzip` and a `gzipStored` body strictly
different from (and, via the stored-block framing, larger than) the plaintext. So a
`compress_skips_small` theorem would be FALSE of what runs; the deviation is proven
instead of papered over. (The reference also stamps `Vary: Accept-Encoding`; the
deployed stage does not — a second, secondary divergence.)
-/

namespace O11y.CompressProven.Deployed

open Reactor.Pipeline
open Reactor.Stage.Gzip

/-! ## `gzipStored` is a well-formed gzip container (header parses to the magic) -/

/-- Every `Gzip.gzipStored x` stream parses as a valid RFC 1952 header: the parser
consumes exactly the 10 fixed header bytes and returns the DEFLATE payload ‖ trailer
untouched, with the magic (`0x1f 0x8b`) and DEFLATE method (`0x08`) recovered. -/
theorem gzipStored_header_valid (x : List UInt8) :
    _root_.Gzip.parseHeader (_root_.Gzip.gzipStored x)
      = some (⟨0x1f, 0x8b, 0x08, 0x00⟩,
              Deflate.deflateStored x
                ++ _root_.Gzip.u32le (_root_.Gzip.crc32 x).toNat
                ++ _root_.Gzip.u32le (x.length % 4294967296)) := by
  have hwf := (_root_.Gzip.gzip_header_wellformed
    (Deflate.deflateStored x
      ++ _root_.Gzip.u32le (_root_.Gzip.crc32 x).toNat
      ++ _root_.Gzip.u32le (x.length % 4294967296))).1
  simp only [_root_.Gzip.gzipStored, List.append_assoc] at hwf ⊢
  exact hwf

/-! ## 1. `Accept-Encoding: gzip` ⇒ header + valid gzip body -/

/-- **The deployed compress behaviour.** For ANY tail / handler / ctx, when the
request accepts gzip the finalized (serialized) response both (a) carries
`Content-Encoding: gzip` and (b) has a body that is a genuine RFC 1952 gzip
container — its header parses to the magic + DEFLATE method, exposing the payload
and CRC-32/ISIZE trailer. This is the exact stage `deployStagesFull2` runs. -/
theorem compress_when_accepted (rest : List Stage) (handler : Ctx → Reactor.Response)
    (c : Ctx) (h : acceptsGzip c.req = true) :
    (ceName, gzipVal) ∈ ((runPipeline (gzipStage :: rest) handler c).build).headers
    ∧ _root_.Gzip.parseHeader ((runPipeline (gzipStage :: rest) handler c).build).body
        = some (⟨0x1f, 0x8b, 0x08, 0x00⟩,
                Deflate.deflateStored ((runPipeline rest handler c).build).body
                  ++ _root_.Gzip.u32le
                       (_root_.Gzip.crc32 ((runPipeline rest handler c).build).body).toNat
                  ++ _root_.Gzip.u32le
                       (((runPipeline rest handler c).build).body.length % 4294967296)) := by
  refine ⟨gzipStage_ce_header rest handler c h, ?_⟩
  rw [gzipStage_body_gzipped rest handler c h]
  exact gzipStored_header_valid _

/-! ## 2. A concrete deployed body round-trips through a real `gunzip` -/

/-- The exact bytes the deployed default handler emits on a `404` — `"not found"`
(`Reactor.demoVhBlocks` catch-all), given as explicit ASCII so the kernel reduces
the whole `gunzip` computation. -/
def notFoundBody : List UInt8 :=
  [0x6e, 0x6f, 0x74, 0x20, 0x66, 0x6f, 0x75, 0x6e, 0x64]

set_option maxRecDepth 100000 in
/-- **The gzip stream a real client decodes.** The deployed `404` body, gzipped by
the stage (`gzipStored`), decodes back to exactly `"not found"` with NO error —
through the real `Gzip.gunzip`: header parse, DEFLATE inflate, and both the CRC-32
and ISIZE trailer checks pass. This is `curl --compressed` succeeding, as a kernel
computation. -/
theorem compress_stream_decodes :
    (_root_.Gzip.gunzip ⟨100⟩ (_root_.Gzip.gzipStored notFoundBody)).out
        = notFoundBody.toArray
    ∧ (_root_.Gzip.gunzip ⟨100⟩ (_root_.Gzip.gzipStored notFoundBody)).err = none := by
  refine ⟨?_, ?_⟩ <;> rfl

/-! ## 3. No `Accept-Encoding` ⇒ the stage is the identity -/

/-- **Unaccepted requests are untouched.** When the request does NOT accept gzip,
the whole gzip stage collapses to the identity on the response builder: it adds no
header, rewrites no byte — `runPipeline (gzipStage :: rest)` equals `runPipeline
rest`. So an identity-encoded client's bytes are handed back verbatim. -/
theorem compress_skips_unaccepted (rest : List Stage) (handler : Ctx → Reactor.Response)
    (c : Ctx) (h : acceptsGzip c.req = false) :
    runPipeline (gzipStage :: rest) handler c = runPipeline rest handler c := by
  rw [pipeline_stage_effect gzipStage rest handler c c rfl]
  show (match acceptsGzip c.req with
        | true => ((runPipeline rest handler c).mapResp gzipBody).addHeader (ceName, gzipVal)
        | false => runPipeline rest handler c) = runPipeline rest handler c
  rw [h]

/-! ## REAL FINDING: small bodies are NOT skipped (no `minSize` threshold) -/

/-- **REAL FINDING.** The deployed stage has no size threshold: for ANY accepting
request and ANY handler whose response body is a single byte, the stage still (a)
stamps `Content-Encoding: gzip` and (b) replaces the body with its `gzipStored`
container — strictly different from the plaintext (the stored-block framing is
larger). The stage never inspects the body length, so the reference's `minSize`
guard ("response below minSize is NOT compressed") is absent. A
`compress_skips_small` theorem would therefore be FALSE of what runs; this proves
the divergence. -/
theorem compress_small_not_skipped (handler : Ctx → Reactor.Response) (c : Ctx)
    (h : acceptsGzip c.req = true) (hb : (handler c).body = [0x41]) :
    (ceName, gzipVal) ∈ ((runPipeline [gzipStage] handler c).build).headers
    ∧ ((runPipeline [gzipStage] handler c).build).body = _root_.Gzip.gzipStored [0x41]
    ∧ ((runPipeline [gzipStage] handler c).build).body ≠ [0x41] := by
  have hbody : ((runPipeline ([] : List Stage) handler c).build).body = [0x41] := hb
  refine ⟨gzipStage_ce_header [] handler c h, ?_, ?_⟩
  · rw [gzipStage_body_gzipped [] handler c h, hbody]
  · rw [gzipStage_body_gzipped [] handler c h, hbody]; decide

#print axioms O11y.CompressProven.Deployed.compress_when_accepted
#print axioms O11y.CompressProven.Deployed.compress_stream_decodes
#print axioms O11y.CompressProven.Deployed.compress_skips_unaccepted
#print axioms O11y.CompressProven.Deployed.compress_small_not_skipped

end O11y.CompressProven.Deployed
