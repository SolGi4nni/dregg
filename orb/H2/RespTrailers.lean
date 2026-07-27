import H2.Ext
import H2.FrameEncode
import H2.PseudoHeader

/-!
# HTTP/2 response trailers — gRPC `grpc-status` delivery (RFC 9113 §8.1)

`H2/Ext.lean` proves the trailer *detection* rule (`detectTrailers`): a HEADERS
block that carries `END_STREAM` after the initial HEADERS and ≥ 1 DATA frame is a
**trailer** section, not a second header block. This module closes the *emission*
side — the shape of the frame stream a server lays down when it finishes a
response with trailers, exactly the pattern gRPC uses to deliver `grpc-status` /
`grpc-message` after the response body:

```text
HEADERS(:status, END_HEADERS)        -- response head, stream stays open
DATA … DATA                          -- the body (END_STREAM NOT set here)
HEADERS(grpc-status, …, END_STREAM)  -- the TRAILER block closes the stream
```

Three machine-checked properties (RFC 9113 §8.1):

* **`response_trailers_after_data`** — the emitted frame list is `pre ++ [trailer]`
  where `pre` starts with the response HEADERS and contains ≥ 1 DATA frame, so the
  trailer detector (`H2.Ext.detectTrailers`) fires `true` at the trailer boundary;
  the trailer is the `END_STREAM` HEADERS frame carrying the `grpc-status` /
  `grpc-message` block, whose fields are pseudo-header-free.
* **`trailers_no_pseudo`** — a trailer section is well-formed iff it contains no
  pseudo-header field (a `:`-prefixed name); the full both-directions rule
  (RFC 9113 §8.1: "Trailers MUST NOT include pseudo-header fields").
* **`trailers_end_stream`** — the encoded trailer HEADERS frame decodes back (via
  the existing `H2.FrameEncode` round-trip) with its `END_STREAM` flag set — the
  trailer closes the stream on the wire.

Ground truth: `H2/Ext.lean` (`detectTrailers`), `H2/FrameEncode.lean`
(`encodeFrame` + `decode_encode_headers`), `H2/PseudoHeader.lean` (`isPseudoName`),
and RFC 9113 §8.1. All theorems are grounded on concrete octets (`#guard` /
`decide`) so none is vacuous.
-/

namespace H2
namespace RespTrailers

open H2 (Frame FrameResult decode)
open H2.Ext (detectTrailers be16)
open H2.FrameEncode (encodeFrame)
open H2.PseudoHeader (isPseudoName)

/-! ## Trailer fields and the gRPC trailer section -/

/-- One trailer field: a regular (non-pseudo) name/value byte-string pair. -/
abbrev Field := Bytes × Bytes

/-- `grpc-status` field name, spelled as explicit octets so the codec reduces in
the kernel. -/
def bGrpcStatus : Bytes :=
  [0x67, 0x72, 0x70, 0x63, 0x2d, 0x73, 0x74, 0x61, 0x74, 0x75, 0x73]  -- "grpc-status"

/-- `grpc-message` field name, as explicit octets. -/
def bGrpcMessage : Bytes :=
  [0x67, 0x72, 0x70, 0x63, 0x2d, 0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65]  -- "grpc-message"

/-- The gRPC trailer section: `grpc-status` then `grpc-message` (RFC 9113 §8.1 as
gRPC uses it). Both are regular header fields — never pseudo-headers. -/
def grpcTrailers (status message : Bytes) : List Field :=
  [(bGrpcStatus, status), (bGrpcMessage, message)]

/-! ## Trailer-block serialization (the HEADERS payload)

A concrete length-prefixed serialization of the trailer field list, used as the
opaque HEADERS payload the frame carries. (The wire block a full server lays is
HPACK; this module reasons about the *frame stream shape* and the *field
constraints*, so any faithful field serialization suffices.) -/

/-- Encode one trailer field: `name-len ‖ name ‖ value-len ‖ value`. -/
def encodeField (f : Field) : Bytes :=
  be16 f.1.length ++ f.1 ++ be16 f.2.length ++ f.2

/-- Encode a trailer field list into the HEADERS payload. -/
def encodeBlock : List Field → Bytes
  | [] => []
  | f :: rest => encodeField f ++ encodeBlock rest

/-! ## The no-pseudo-header rule (RFC 9113 §8.1) -/

/-- A trailer section is well-formed iff no field name is a pseudo-header (i.e.
begins with `:`). RFC 9113 §8.1: "Trailers MUST NOT include pseudo-header
fields." -/
def noPseudo (fs : List Field) : Bool := fs.all (fun f => ! isPseudoName f.1)

/-- **Trailers carry no pseudo-headers (RFC 9113 §8.1).** A trailer section
passes validation exactly when every one of its field names is a regular
(non-`:`-prefixed) name — the full both-directions rule. -/
theorem trailers_no_pseudo (fs : List Field) :
    noPseudo fs = true ↔ ∀ f ∈ fs, isPseudoName f.1 = false := by
  unfold noPseudo
  induction fs with
  | nil => simp
  | cons f rest ih =>
    rw [List.all_cons, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hf, hrest⟩ g hg
      rcases List.mem_cons.mp hg with rfl | hg'
      · simpa using hf
      · exact hrest g hg'
    · intro h
      refine ⟨?_, fun g hg => h g (List.mem_cons_of_mem _ hg)⟩
      simpa using h f (List.mem_cons_self)

/-- The gRPC trailer section is always pseudo-header-free — `grpc-status` and
`grpc-message` are regular field names. -/
theorem grpcTrailers_no_pseudo (status message : Bytes) :
    noPseudo (grpcTrailers status message) = true := rfl

/-- A trailer section carrying a pseudo-header (here a `:status`, a response
pseudo-header) is rejected — witnessing that `noPseudo` is not vacuously true. -/
theorem trailers_reject_status :
    noPseudo [([0x3a, 0x73, 0x74, 0x61, 0x74, 0x75, 0x73], [0x32, 0x30, 0x30])] = false := by
  decide

/-! ## Stream progress and the emitted frame stream -/

/-- Progress of a response stream, as the peer's trailer detector tracks it:
whether the initial HEADERS and ≥ 1 DATA frame have been seen. -/
structure Progress where
  initialHeaders : Bool := false
  dataSeen : Bool := false
deriving Repr, DecidableEq

/-- Fold one emitted frame into the progress. A HEADERS latches `initialHeaders`;
a DATA latches `dataSeen`; every other frame is transparent to the detector. -/
def step (p : Progress) : Frame → Progress
  | .headers .. => { p with initialHeaders := true }
  | .data ..    => { p with dataSeen := true }
  | _           => p

/-- The progress accumulated over a frame prefix. -/
def run (fs : List Frame) : Progress := fs.foldl step {}

/-- The trailer HEADERS frame (RFC 9113 §8.1): `END_STREAM` and `END_HEADERS`
both set, carrying the trailer block. -/
def trailerFrame (sid : Nat) (block : Bytes) : Frame := Frame.headers sid true true block

/-- The frames a server emits to finish a response with trailers: the response
HEADERS (stream stays open), the body DATA frames, then the trailer HEADERS with
`END_STREAM`. -/
def response (sid : Nat) (statusBlock : Bytes) (body : List Bytes)
    (status message : Bytes) : List Frame :=
  Frame.headers sid false true statusBlock
    :: (body.map (fun c => Frame.data sid false c)
        ++ [trailerFrame sid (encodeBlock (grpcTrailers status message))])

/-! ### Monotonicity of progress -/

/-- `initialHeaders`, once set, stays set across one step. -/
theorem step_ih_mono (p : Progress) (f : Frame) (h : p.initialHeaders = true) :
    (step p f).initialHeaders = true := by
  cases f <;> simp_all [step]

/-- `dataSeen`, once set, stays set across one step. -/
theorem step_ds_mono (p : Progress) (f : Frame) (h : p.dataSeen = true) :
    (step p f).dataSeen = true := by
  cases f <;> simp_all [step]

/-- A fold preserves a set `initialHeaders`. -/
theorem foldl_ih (fs : List Frame) (p : Progress) (h : p.initialHeaders = true) :
    (fs.foldl step p).initialHeaders = true := by
  induction fs generalizing p with
  | nil => exact h
  | cons g t ih => exact ih _ (step_ih_mono p g h)

/-- A fold preserves a set `dataSeen`. -/
theorem foldl_ds (fs : List Frame) (p : Progress) (h : p.dataSeen = true) :
    (fs.foldl step p).dataSeen = true := by
  induction fs generalizing p with
  | nil => exact h
  | cons g t ih => exact ih _ (step_ds_mono p g h)

/-- Stepping a HEADERS frame always latches `initialHeaders`. -/
theorem step_headers_ih (p : Progress) (sid : Nat) (es eh : Bool) (pl : Bytes) :
    (step p (Frame.headers sid es eh pl)).initialHeaders = true := rfl

/-- Stepping a DATA frame always latches `dataSeen`. -/
theorem step_data_ds (p : Progress) (sid : Nat) (es : Bool) (pl : Bytes) :
    (step p (Frame.data sid es pl)).dataSeen = true := rfl

/-- Any fold over a frame list containing a DATA frame ends with `dataSeen` set. -/
theorem foldl_ds_mem (fs : List Frame) (p : Progress)
    (h : ∃ sid es pl, Frame.data sid es pl ∈ fs) :
    (fs.foldl step p).dataSeen = true := by
  induction fs generalizing p with
  | nil => obtain ⟨_, _, _, hmem⟩ := h; simp at hmem
  | cons g t ih =>
    obtain ⟨sid, es, pl, hmem⟩ := h
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hmem with heq | htail
    · subst heq; exact foldl_ds t _ (step_data_ds p sid es pl)
    · exact ih _ ⟨sid, es, pl, htail⟩

/-! ### The headline emission theorem -/

/-- **Response trailers after data (RFC 9113 §8.1).** For any response with a
non-empty body, the emitted frame stream is `pre ++ [trailer]` where:

* `pre` begins with the response HEADERS and contains ≥ 1 DATA frame, so the peer
  has both `initialHeaders` and `dataSeen` set — `detectTrailers` fires `true` at
  the trailer boundary (it *is* a trailer section, not a second header block);
* `trailer` is the `END_STREAM` HEADERS frame carrying the `grpc-status` /
  `grpc-message` trailer block; and
* that trailer block is pseudo-header-free.

This is exactly the DATA-then-`END_STREAM`-HEADERS shape gRPC uses to deliver
`grpc-status`. -/
theorem response_trailers_after_data
    (sid : Nat) (statusBlock : Bytes) (body : List Bytes) (status message : Bytes)
    (hbody : body ≠ []) :
    ∃ pre : List Frame,
      response sid statusBlock body status message
        = pre ++ [trailerFrame sid (encodeBlock (grpcTrailers status message))] ∧
      (∃ f ∈ pre, ∃ es pl, f = Frame.data sid es pl) ∧
      detectTrailers (run pre).initialHeaders (run pre).dataSeen = true ∧
      noPseudo (grpcTrailers status message) = true := by
  -- The response body is non-empty: peel off its head DATA chunk.
  obtain ⟨c, rest, rfl⟩ : ∃ c rest, body = c :: rest := by
    cases body with
    | nil => exact absurd rfl hbody
    | cons c rest => exact ⟨c, rest, rfl⟩
  -- `pre` = the response HEADERS followed by the body DATA frames.
  refine ⟨Frame.headers sid false true statusBlock
            :: (c :: rest).map (fun c => Frame.data sid false c), ?_, ?_, ?_, ?_⟩
  · -- response = pre ++ [trailer]  (cons distributes over the ++)
    simp [response, List.cons_append]
  · -- a DATA frame lives in `pre`: the first body chunk.
    exact ⟨Frame.data sid false c, by simp, false, c, rfl⟩
  · -- both progress flags are set over `pre`, so the trailer detector fires.
    have hih : (run (Frame.headers sid false true statusBlock
        :: (c :: rest).map (fun c => Frame.data sid false c))).initialHeaders = true := by
      unfold run
      rw [List.foldl_cons]
      exact foldl_ih _ _ (step_headers_ih _ sid false true statusBlock)
    have hds : (run (Frame.headers sid false true statusBlock
        :: (c :: rest).map (fun c => Frame.data sid false c))).dataSeen = true := by
      unfold run
      rw [List.foldl_cons]
      exact foldl_ds_mem _ _ ⟨sid, false, c, by simp⟩
    rw [hih, hds]; rfl
  · exact grpcTrailers_no_pseudo status message

/-! ### The trailer frame carries END_STREAM on the wire -/

/-- **Trailer HEADERS carries END_STREAM (RFC 9113 §8.1).** Encoding the trailer
frame and decoding it back (via the existing `H2.FrameEncode` round-trip) recovers
a HEADERS frame with its `END_STREAM` flag set — the trailer closes the stream on
the wire. -/
theorem trailers_end_stream (sid : Nat) (block : Bytes) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : block.length < 2 ^ 24) (hmfs : block.length ≤ mfs) :
    decode (encodeFrame (trailerFrame sid block)) mfs
      = FrameResult.complete (Frame.headers sid true true block) (9 + block.length) := by
  unfold trailerFrame
  exact FrameEncode.decode_encode_headers sid true true block mfs hsid hlen hmfs

/-! ## Non-vacuity — concrete wire vectors

The emission and END_STREAM theorems exercised on real octets. -/

/- A concrete response: HEADERS on stream 3 (open), one DATA chunk, then the
gRPC trailer HEADERS with `END_STREAM`. The last frame is the `END_STREAM`
trailer carrying `grpc-status: 0`. -/
#guard (response 3 [0x88] [[0x68, 0x69]] [0x30] [0x4f, 0x4b]).getLast?
  = some (Frame.headers 3 true true
      (encodeBlock (grpcTrailers [0x30] [0x4f, 0x4b])))

/- The response is `pre ++ [trailer]` with the trailer last. -/
#guard (response 3 [0x88] [[0x68, 0x69]] [0x30] [0x4f, 0x4b]).length = 3

/- The trailer detector fires over the concrete prefix (headers + one data). -/
#guard detectTrailers
    (run [Frame.headers 3 false true [0x88], Frame.data 3 false [0x68, 0x69]]).initialHeaders
    (run [Frame.headers 3 false true [0x88], Frame.data 3 false [0x68, 0x69]]).dataSeen = true

/-- The concrete trailer frame decodes back with END_STREAM set. -/
example :
    decode (encodeFrame (trailerFrame 3 [0x88])) 16384
      = FrameResult.complete (Frame.headers 3 true true [0x88]) 10 := rfl

/- gRPC trailer names are regular fields (never pseudo). -/
#guard noPseudo (grpcTrailers [0x30] [0x4f, 0x4b]) = true
/- A `:status` trailer is rejected. -/
#guard noPseudo [([0x3a, 0x73], [0x32])] = false

end RespTrailers
end H2
