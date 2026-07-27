import ChunkedCorrect
import Proto.ChunkedFraming

/-!
# PROVE-WHAT-RUNS: chunked Transfer-Encoding, the deployed wire (RFC 7230 §4.1)

Ledger row **h1.chunked**. The running dataplane, on the reverse-proxy path
(`crates/dataplane/src/proxy_dial.rs :: forward_streaming` /
`uring.rs :: ReplyFraming::Chunked`), forwards a `Transfer-Encoding: chunked`
upstream response to the client STREAMED VERBATIM — the chunk framing bytes on
the client wire are exactly the upstream's, copied block-by-block up to the
terminating zero-chunk. So the wire the curl below observes IS the chunked
framing this file proves.

RFC 7230 §4.1:

    chunked-body = *chunk last-chunk trailer-part CRLF
    chunk        = chunk-size [ chunk-ext ] CRLF chunk-data CRLF
    chunk-size   = 1*HEXDIG
    last-chunk   = 1*("0") [ chunk-ext ] CRLF

This file states the two headline results **as the deployed wire sees them** and
grounds them on the machine-checked framing/decoder theory in
`Body/Chunked.lean`, `ChunkedCorrect.lean`, and `Proto/ChunkedFraming.lean`:

* **`chunked_frames`** — the wire of a chunked body is exactly the per-chunk
  frames `chunk-size(hex) CRLF chunk-data CRLF` concatenated in order, followed
  by the terminator `0 CRLF CRLF` — the RFC §4.1 structure, byte-for-byte.
* **`chunked_decode_roundtrip`** — decoding that wire recovers exactly the
  in-order concatenation of the chunk payloads (no framing octet leaks into the
  body), consuming the whole input; the payload-extractor `dechunk` returns it;
  and the deployed incremental terminator parser (`ChunkedParser`, ported as
  `run`) reaches `Done`.

The two are exercised on the exact bytes the curl carries (`helloWire`,
`"5\r\nHello\r\n6\r\n World\r\n0\r\n\r\n"` ⇒ payload `"Hello World"`).
-/

namespace Proto.ChunkedProven

open Body Body.Hex Body.Chunked Proto.ChunkedFraming

/-! ## The terminator is exactly `0 CRLF CRLF` -/

/-- RFC §4.1 `last-chunk` (no trailers): the terminating zero-size chunk is
exactly the five octets `'0' CR LF CR LF`. -/
theorem chunked_terminator : encodeTerminal = [0x30, CR, LF, CR, LF] := by decide

/-! ## `chunked_frames`: the wire is size-CRLF-data-CRLF frames + terminator -/

/-- **`chunked_frames`.** The chunked wire of a message list is exactly:
* the per-chunk frames — each `chunk-size(hex) CRLF chunk-data CRLF` — in order,
* followed by the `0 CRLF CRLF` terminator.
This is the RFC 7230 §4.1 `chunked-body` structure, byte-for-byte: no octet
precedes the first size line, the frames abut, and the terminator closes it. -/
theorem chunked_frames (chunks : List Bytes) :
    encodeStream chunks = (chunks.map encodeChunk).flatten ++ encodeTerminal
    ∧ (∀ d ∈ chunks, encodeChunk d = toHex d.length ++ CR :: LF :: (d ++ CR :: LF :: []))
    ∧ encodeTerminal = [0x30, CR, LF, CR, LF] := by
  refine ⟨?_, ?_, chunked_terminator⟩
  · induction chunks with
    | nil => simp [encodeStream]
    | cons d ds ih =>
      simp only [encodeStream, List.map_cons, List.flatten_cons, ih, List.append_assoc]
  · intro d _
    simp [encodeChunk, List.append_assoc]

/-! ## `chunked_decode_roundtrip`: decode ∘ encode = payload, and the parser terminates -/

/-- **`chunked_decode_roundtrip`.** For a list of non-empty, in-range messages:
* the streaming decoder recovers exactly `chunks.flatten` (the in-order payload
  concatenation) consuming the whole wire — no framing octet (size digits,
  CRLFs, terminator) leaks into the delivered body;
* the payload extractor `dechunk` returns that same body;
* the deployed incremental terminator parser (`run`, the port of `ChunkedParser`)
  reaches its absorbing `Done` state on the same wire.
Reuses the machine-checked byte-conservation (`decodeStream_encodeStream`), the
decoder⇔grammar refinement (`dechunk_iff_spec`/`isChunking_encodeStream`), and
the parser-termination (`chunked_roundtrip`) theorems. -/
theorem chunked_decode_roundtrip (chunks : List Bytes)
    (hne : ∀ d ∈ chunks, d ≠ []) (hle : ∀ d ∈ chunks, d.length ≤ maxChunkSize) :
    decodeStream (encodeStream chunks)
        = .complete chunks.flatten (encodeStream chunks).length
    ∧ dechunk (encodeStream chunks) = some chunks.flatten
    ∧ run .Size 0 (encodeStream chunks) = (.Done, 0) := by
  refine ⟨decodeStream_encodeStream chunks hne hle, ?_, (chunked_roundtrip chunks hne hle).2⟩
  exact (dechunk_iff_spec (encodeStream chunks) chunks.flatten).mpr
    (isChunking_encodeStream chunks hne hle)

/-! ## The exact deployed-wire vector the curl carries

`helloWire` is the chunked body bytes the reverse-proxied client observes for the
two-chunk response `"Hello"` + `" World"`. These theorems bind the general
results above to those concrete octets, so nothing is vacuous. -/

/-- The two payload messages `"Hello"` and `" World"`. -/
def helloChunks : List Bytes :=
  [[0x48, 0x65, 0x6c, 0x6c, 0x6f], [0x20, 0x57, 0x6f, 0x72, 0x6c, 0x64]]

/-- The chunked body bytes on the wire: `encodeStream helloChunks`. -/
def helloWire : Bytes := encodeStream helloChunks

/-- The wire is exactly `"5\r\nHello\r\n6\r\n World\r\n0\r\n\r\n"` — the bytes the
deployed proxy streams to the client, verified octet-for-octet. -/
theorem helloWire_bytes :
    helloWire =
      [0x35, CR, LF, 0x48, 0x65, 0x6c, 0x6c, 0x6f, CR, LF,
       0x36, CR, LF, 0x20, 0x57, 0x6f, 0x72, 0x6c, 0x64, CR, LF,
       0x30, CR, LF, CR, LF] := by decide

/-- The two messages are non-empty and in range (the `chunked_decode_roundtrip`
hypotheses, discharged for the concrete vector). -/
theorem helloChunks_ne : ∀ d ∈ helloChunks, d ≠ [] := by decide
theorem helloChunks_le : ∀ d ∈ helloChunks, d.length ≤ maxChunkSize := by decide

/-- Decoding the deployed wire recovers exactly `"Hello World"` — the eleven
payload octets, with every framing octet stripped. -/
theorem helloWire_decodes :
    dechunk helloWire
      = some [0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x57, 0x6f, 0x72, 0x6c, 0x64] := by
  have h := (chunked_decode_roundtrip helloChunks helloChunks_ne helloChunks_le).2.1
  have hflat : helloChunks.flatten
      = [0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x57, 0x6f, 0x72, 0x6c, 0x64] := by decide
  rw [helloWire, h, hflat]

/-- The deployed incremental terminator parser reaches `Done` on the wire — the
same `Done` the running `ChunkedParser` reports to close the streamed forward. -/
theorem helloWire_done : run .Size 0 helloWire = (.Done, 0) := by decide

end Proto.ChunkedProven
