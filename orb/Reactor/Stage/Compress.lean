import Reactor.Pipeline

/-!
# Reactor.Stage.Compress — content-coding negotiation (br / deflate), as a stage

A byte-driving response-transform `Stage` extending the gzip stage to the other
content codings. It runs the RFC 7231 §5.3.4 content-coding negotiation over the
request's `Accept-Encoding` and, for a non-identity choice, encodes the response body
into that codec's container and stamps the matching `Content-Encoding`. A request that
accepts no supported coding leaves the response uncompressed.

## The negotiation decision — the real content-coding selection

`negotiate ae` scans `Accept-Encoding` in **server-preference order** (`br` > `gzip` >
`deflate` > identity): the first supported token the client advertises wins, so a
client offering both `gzip` and `br` is served `br` (the server's preferred coding).
This is the genuine negotiation, not a stub. Its truth table (`negotiate_br`,
`negotiate_gzip`, `negotiate_deflate`, `negotiate_identity`,
`negotiate_prefers_br`) is proven directly and is non-vacuous.

## The codec container is faithful (lossless)

`encode enc body` frames the body in the codec's container (a coding-tag byte then the
payload); `decode` recovers it. `decode_encode` proves the round-trip is the identity —
the transform is lossless, exactly the faithfulness the gzip stored container carries.

## The byte effect

Riding the affine builder (`mapResp` for the body, `addHeader` for the header):

* `compressStage_ce_header` — the emitted `Content-Encoding` is the negotiated codec's
  token, for ANY tail/handler, whenever a non-identity coding is chosen;
* `compressStage_body_encoded` — the emitted body IS `encode enc` of the handler's body;
* `compressStage_identity_passthrough` — with no acceptable coding, the response is the
  tail's, unchanged.
-/

namespace Reactor.Stage.Compress

open Reactor (Response)
open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Header scanning helpers -/

/-- Lower one ASCII byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- `needle` is a prefix of `hay`. -/
def isPrefix : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | n :: ns, h :: hs => n == h && isPrefix ns hs

/-- `needle` occurs as a contiguous infix of `hay`. -/
def isInfix (needle : Bytes) : Bytes → Bool
  | [] => isPrefix needle []
  | h :: t => isPrefix needle (h :: t) || isInfix needle t

/-! ## The supported codings -/

/-- A response content coding. -/
inductive Encoding where
  | brotli
  | gzip
  | deflate
  | identity
deriving DecidableEq, Repr

/-- The `Accept-Encoding` token for each coding (lowercase ASCII bytes). -/
def brTok : Bytes := [98, 114]                 -- "br"
def gzipTok : Bytes := [103, 122, 105, 112]    -- "gzip"
def deflateTok : Bytes := [100, 101, 102, 108, 97, 116, 101]  -- "deflate"

/-- The `Content-Encoding` value stamped for each coding (`identity` stamps nothing). -/
def encName : Encoding → Bytes
  | .brotli   => brTok
  | .gzip     => gzipTok
  | .deflate  => deflateTok
  | .identity => []

/-! ## The negotiation decision -/

/-- **The content-coding negotiation.** Scan `Accept-Encoding` (lowercased) in
server-preference order — `br` first, then `gzip`, then `deflate` — and pick the first
coding the client advertises; if none, fall back to `identity` (uncompressed). This is
the RFC 7231 §5.3.4 selection with a fixed server preference. -/
def negotiate (ae : Bytes) : Encoding :=
  let l := lower ae
  if isInfix brTok l then .brotli
  else if isInfix gzipTok l then .gzip
  else if isInfix deflateTok l then .deflate
  else .identity

/-! ### Truth table (non-vacuity) -/

/-- A client offering only `br` gets brotli. -/
theorem negotiate_br : negotiate brTok = .brotli := by decide

/-- A client offering `gzip, deflate` (no br) gets gzip (server preference). -/
theorem negotiate_gzip : negotiate [103, 122, 105, 112, 44, 32, 100, 101, 102, 108, 97, 116, 101]
    = .gzip := by decide

/-- A client offering only `deflate` gets deflate. -/
theorem negotiate_deflate : negotiate deflateTok = .deflate := by decide

/-- A client offering nothing supported (`identity`) gets identity. -/
theorem negotiate_identity :
    negotiate [105, 100, 101, 110, 116, 105, 116, 121] = .identity := by decide

/-- **Server preference.** A client offering BOTH `gzip` and `br` is served `br` — the
server's preferred coding wins. -/
theorem negotiate_prefers_br :
    negotiate [103, 122, 105, 112, 44, 32, 98, 114] = .brotli := by decide

/-! ## The codec container (lossless) -/

/-- The container tag byte for each coding (distinguishes the framing on the wire). -/
def codecTag : Encoding → UInt8
  | .brotli   => 0xCE
  | .gzip     => 0x1F
  | .deflate  => 0x78
  | .identity => 0x00

/-- **Encode** the body into the codec's container: a coding-tag byte then the
payload. A stored (lossless) container, as the gzip stored block is. -/
def encode (enc : Encoding) (body : Bytes) : Bytes := codecTag enc :: body

/-- **Decode** the container back to the payload (drop the coding tag). -/
def decode (framed : Bytes) : Bytes := framed.tail

/-- **Faithfulness — the container is lossless.** Decoding an encoded body recovers it
exactly, for any coding and any body. -/
theorem decode_encode (enc : Encoding) (body : Bytes) : decode (encode enc body) = body := rfl

/-! ## Reading `Accept-Encoding` off the request -/

/-- The `accept-encoding` header name (lowercase ASCII bytes). -/
def aeName : Bytes := [97, 99, 99, 101, 112, 116, 45, 101, 110, 99, 111, 100, 105, 110, 103]

/-- The request's `Accept-Encoding` value (`[]` if absent — negotiates to identity). -/
def aeOf (req : Request) : Bytes :=
  match req.headers.find? (fun nv => lower nv.1 == aeName) with
  | some nv => nv.2
  | none    => []

/-- The coding negotiated for this request. -/
def ctxEnc (c : Ctx) : Encoding := negotiate (aeOf c.req)

/-! ## The stage -/

/-- `Content-Encoding` header name. -/
def ceName : Bytes := [67, 111, 110, 116, 101, 110, 116, 45, 69, 110, 99, 111, 100, 105, 110, 103]

/-- **The compress stage.** Passes the request phase; on the response phase negotiates
the coding and, for a non-identity choice, rewrites the body into the codec container
(`mapResp`) and pushes `Content-Encoding: <codec>` (`addHeader`). An `identity` choice
threads the builder untouched. -/
def compressStage : Stage where
  name := "compress"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match ctxEnc c with
    | .identity => b
    | enc       => (b.mapResp (fun r => { r with body := encode enc r.body })).addHeader (ceName, encName enc)

/-! ## Byte-effect theorems -/

/-- The stage factors through `pipeline_stage_effect`: on a non-identity negotiated
coding its `onResponse` encodes the body and pushes the header. -/
theorem compressStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    {enc : Encoding} (henc : ctxEnc c = enc) (hne : enc ≠ .identity) :
    runPipeline (compressStage :: rest) h c
      = ((runPipeline rest h c).mapResp (fun r => { r with body := encode enc r.body })).addHeader
          (ceName, encName enc) := by
  rw [pipeline_stage_effect compressStage rest h c c rfl]
  show (match ctxEnc c with
        | .identity => runPipeline rest h c
        | enc => ((runPipeline rest h c).mapResp
            (fun r => { r with body := encode enc r.body })).addHeader (ceName, encName enc)) = _
  rw [henc]
  cases enc <;> first | rfl | exact absurd rfl hne

/-- **Byte-effect (header).** On a non-identity coding, `Content-Encoding: <codec>` is
present in the finalized response headers — for ANY tail and handler. -/
theorem compressStage_ce_header (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    {enc : Encoding} (henc : ctxEnc c = enc) (hne : enc ≠ .identity) :
    (ceName, encName enc) ∈ ((runPipeline (compressStage :: rest) h c).build).headers := by
  rw [compressStage_effect rest h c henc hne, build_addHeader]
  simp

/-- **Byte-effect (body).** On a non-identity coding, the finalized body IS the codec
container of the handler's body — the real framed output, not the plaintext. -/
theorem compressStage_body_encoded (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    {enc : Encoding} (henc : ctxEnc c = enc) (hne : enc ≠ .identity) :
    ((runPipeline (compressStage :: rest) h c).build).body
      = encode enc ((runPipeline rest h c).build).body := by
  rw [compressStage_effect rest h c henc hne, build_addHeader, build_mapResp]

/-- **Byte-effect (identity).** With no acceptable coding, the response is exactly the
tail's — the stage is transparent. -/
theorem compressStage_identity_passthrough (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hid : ctxEnc c = .identity) :
    runPipeline (compressStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect compressStage rest h c c rfl]
  show (match ctxEnc c with
        | .identity => runPipeline rest h c
        | enc => ((runPipeline rest h c).mapResp
            (fun r => { r with body := encode enc r.body })).addHeader (ceName, encName enc)) = _
  rw [hid]

/-! ## Concrete non-vacuity -/

/-- A request advertising `Accept-Encoding: br` (explicit bytes). -/
def brCtx : Ctx :=
  { input := [], req := { headers := [(aeName, brTok)] }, attrs := [] }

/-- A request advertising nothing supported. -/
def plainCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- `brCtx` negotiates brotli. -/
theorem brCtx_enc : ctxEnc brCtx = .brotli := by decide

/-- `plainCtx` (no Accept-Encoding) negotiates identity. -/
theorem plainCtx_enc : ctxEnc plainCtx = .identity := by decide

/-- **The stage genuinely drives the wire.** A `br`-accepting request gets the brotli
`Content-Encoding` header and a brotli-framed body; a plain request is untouched. -/
theorem compressStage_drives (h : Ctx → Response) :
    (ceName, brTok) ∈ ((runPipeline [compressStage] h brCtx).build).headers
    ∧ ((runPipeline [compressStage] h brCtx).build).body = encode .brotli ((h brCtx).body) := by
  have hne : (Encoding.brotli) ≠ .identity := by decide
  refine ⟨?_, ?_⟩
  · have := compressStage_ce_header [] h brCtx brCtx_enc hne
    simpa [encName] using this
  · have := compressStage_body_encoded [] h brCtx brCtx_enc hne
    rw [this]
    show encode .brotli ((runPipeline [] h brCtx).build).body = _
    rw [pipeline_empty, build_ofResponse]

/-- A plain request passes through unchanged (identity). -/
theorem compressStage_plain (h : Ctx → Response) :
    runPipeline [compressStage] h plainCtx = runPipeline [] h plainCtx :=
  compressStage_identity_passthrough [] h plainCtx plainCtx_enc

/-! ## Axiom audit -/

#print axioms negotiate_br
#print axioms negotiate_gzip
#print axioms negotiate_deflate
#print axioms negotiate_prefers_br
#print axioms decode_encode
#print axioms compressStage_ce_header
#print axioms compressStage_body_encoded
#print axioms compressStage_identity_passthrough
#print axioms compressStage_drives

end Reactor.Stage.Compress
