import Body.Hex

/-!
# Chunked transfer-encoding (RFC 7230 §4.1)

A chunked body is a sequence of chunks

    chunk-size [ chunk-ext ] CRLF chunk-data CRLF

terminated by a zero-size chunk (`0 CRLF CRLF`). This file models the decode as
a header parse plus a single-frame decoder plus a streaming fold, and proves the
byte accounting.

Layered as:

* `findCrlf` — the chunk-size line terminator scan, with a bound
  (`findCrlf_some_bound`) that a found CRLF fits in the buffer.
* `parseHeader` — parse one chunk header to `(size, headerLen)`. **Theorem 3**:
  `parseHeader_total` (defined on every input) and `parseHeader_consumed`
  (`0 < headerLen ≤ buffer length` — consumed-monotone). **Theorem 5**:
  `parseHeader_overflow` (a size over `maxChunkSize` is a total error) and
  `parseHeader_bad_hex` (a non-hex / empty size token is a total error).
* `decodeFrame` — decode one frame to `incomplete | error | chunk data c |
  terminal c`. `decodeFrame_chunk_bound` gives `0 < c ≤ buffer length` (this is
  what makes the streaming fold terminate).
* `decodeStream` — fold frames to a terminal `complete`. **Theorem 2**:
  `decodeStream_encodeStream` — decoding the encoding of a chunk list recovers
  exactly the in-order concatenation of the payloads (`chunks.flatten`), so the
  delivered byte count is `Σ chunk sizes` and no framing octet (size digits,
  CRLFs, terminal) leaks into the body. **Theorem 4**:
  `decodeStream_encodeChunks_incomplete` — a stream missing its terminal chunk
  stays `incomplete`, never falsely `complete`.

Deliberately out of scope for the *payload-correctness* decoder above (and for
the `ChunkedCorrect.lean` spec stated over it): chunk extensions (`chunk-ext`)
and trailer header fields; there the terminal is modeled as the bare
`0 CRLF CRLF`. The **request-framing** decision, however, must accept the full
RFC 7230 §4.1 wire — a recipient MUST parse and ignore chunk extensions
(§4.1.1) and MUST accept a trailer section after the last-chunk (§4.1.2) — so
the final section of this file extends the decoder, for the boundary decision
only, to `decodeStreamExt`: `chunk-ext` tolerated on any size line, a
`trailer-part` consumed after the zero-size chunk.
-/

namespace Body
namespace Chunked

open Body.Hex

/-- The largest `chunk-size` the parser admits. A size octet-run denoting more
than this is rejected as a total error — the model of the reference decoder's
`usize`/`checked_add` overflow guard. -/
def maxChunkSize : Nat := 2 ^ 63

/-! ## Chunk-size line scan -/

/-- Offset of the first `CRLF` in the buffer, if any. -/
def findCrlf : Bytes → Option Nat
  | a :: b :: rest => if a = CR ∧ b = LF then some 0 else (findCrlf (b :: rest)).map (· + 1)
  | _ => none

/-! ### Bounded-stack `findCrlf`

`findCrlf` recurses *inside* `Option.map`, so the compiled code pushes one stack
frame per size-line octet until the CRLF (or the buffer end) — recursion depth =
size-line length, and a long chunk-size/extension line exhausts the thread stack
before the size gate can refuse it. `findCrlfGo` is the same single pass in
accumulator-passing (tail-recursive) form: the compiler emits a loop, so the
stack cost is `O(1)` regardless of input length. `findCrlf_eq_tail` proves the
two agree and installs the loop as the compiled implementation (`@[csimp]`);
every theorem about `findCrlf` keeps referring to the unchanged spec. -/

/-- Tail-recursive `findCrlf` carrying the running offset: the recursive call is
the whole `else` branch, so the compiler emits a loop (constant stack). -/
def findCrlfGo : Nat → Bytes → Option Nat
  | _, [] => none
  | _, [_] => none
  | i, a :: b :: rest =>
    if a = CR ∧ b = LF then some i else findCrlfGo (i + 1) (b :: rest)

/-- The loop equals the spec up to the running-offset shift. -/
theorem findCrlfGo_eq (bs : Bytes) :
    ∀ i, findCrlfGo i bs = (findCrlf bs).map (· + i) := by
  induction bs with
  | nil => intro i; simp [findCrlfGo, findCrlf]
  | cons a xs ih =>
    intro i
    match xs, ih with
    | [], _ => simp [findCrlfGo, findCrlf]
    | b :: rest, ih =>
      rw [findCrlfGo, findCrlf]
      by_cases h : a = CR ∧ b = LF
      · simp [h]
      · rw [if_neg h, if_neg h, ih (i + 1), Option.map_map]
        cases findCrlf (b :: rest) with
        | none => simp
        | some q =>
          simp only [Option.map_some', Function.comp_apply, Option.some.injEq]
          omega

/-- The bounded-stack `findCrlf`: the loop from offset `0`. -/
def findCrlfTail (bs : Bytes) : Option Nat := findCrlfGo 0 bs

/-- **The loop/spec agreement.** `findCrlfTail` computes the same offset as
`findCrlf`, in constant stack. -/
@[csimp] theorem findCrlf_eq_tail : @findCrlf = @findCrlfTail := by
  funext bs
  rw [findCrlfTail, findCrlfGo_eq bs 0]
  simp

/-- If the size line has no CR octet, the first CRLF is exactly at its end — the
line terminator is unambiguous. -/
theorem findCrlf_append_no_cr : ∀ (pre rest : Bytes), (∀ b ∈ pre, b ≠ CR) →
    findCrlf (pre ++ CR :: LF :: rest) = some pre.length := by
  intro pre
  induction pre with
  | nil => intro rest _; simp [findCrlf]
  | cons a pre' ih =>
    intro rest h
    have ha : a ≠ CR := h a (List.mem_cons_self a pre')
    have hpre' : ∀ b ∈ pre', b ≠ CR := fun b hb => h b (List.mem_cons_of_mem a hb)
    obtain ⟨c, t', ht⟩ : ∃ c t', pre' ++ CR :: LF :: rest = c :: t' := by
      cases pre' with
      | nil => exact ⟨CR, LF :: rest, rfl⟩
      | cons x xs => exact ⟨x, xs ++ CR :: LF :: rest, rfl⟩
    rw [List.cons_append, ht]
    simp only [findCrlf]
    rw [if_neg (by rintro ⟨rfl, _⟩; exact ha rfl), ← ht, ih rest hpre']
    simp

/-- A found CRLF (plus its two octets) fits inside the buffer: the consumed
prefix length `p + 2` is bounded by the buffer length. -/
theorem findCrlf_some_bound : ∀ (buf : Bytes) (p : Nat),
    findCrlf buf = some p → p + 2 ≤ buf.length := by
  intro buf
  induction buf using findCrlf.induct with
  | case1 a b rest hcond =>
    intro p hp
    simp only [findCrlf, if_pos hcond, Option.some.injEq] at hp
    subst hp
    simp only [List.length_cons]; omega
  | case2 a b rest hcond ih =>
    intro p hp
    simp only [findCrlf, if_neg hcond] at hp
    cases hfc : findCrlf (b :: rest) with
    | none => rw [hfc] at hp; simp at hp
    | some q =>
      rw [hfc] at hp; simp at hp
      have hq := ih q hfc
      simp only [List.length_cons] at hq ⊢; omega
  | case3 t hlt =>
    intro p hp
    cases t with
    | nil => simp [findCrlf] at hp
    | cons x xs =>
      cases xs with
      | nil => simp [findCrlf] at hp
      | cons y ys => exact absurd rfl (hlt x y ys)

/-! ## Chunk-header parse -/

/-- Outcome of parsing one chunk header. -/
inductive Hdr where
  /-- No CRLF yet — need more bytes. -/
  | incomplete
  /-- Malformed size token, or a size beyond `maxChunkSize`. -/
  | error
  /-- Parsed a chunk of `size` bytes; the header consumed `headerLen` octets
  (the size digits and their CRLF). -/
  | ok (size : Nat) (headerLen : Nat)
deriving Repr, DecidableEq

/-- Parse one chunk header from the front of the buffer. Total. -/
def parseHeader (buf : Bytes) : Hdr :=
  match findCrlf buf with
  | none => .incomplete
  | some p =>
    match parseHex (buf.take p) with
    | none => .error
    | some size => if maxChunkSize < size then .error else .ok size (p + 2)

/-- **Theorem 3 (totality).** `parseHeader` is defined on every input: it is
`incomplete`, `error`, or a genuine `ok`. -/
theorem parseHeader_total (buf : Bytes) :
    parseHeader buf = .incomplete ∨ parseHeader buf = .error ∨
      ∃ s c, parseHeader buf = .ok s c := by
  unfold parseHeader
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- **Theorem 3 (consumed-monotonicity).** When the header parses, it consumes a
positive number of octets, bounded by the buffer length. This is what makes the
streaming decode strictly shrink the buffer. -/
theorem parseHeader_consumed (buf : Bytes) (s c : Nat) (h : parseHeader buf = .ok s c) :
    0 < c ∧ c ≤ buf.length := by
  unfold parseHeader at h
  split at h
  · simp at h
  · next p hfc =>
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i size hpx
        have hb := findCrlf_some_bound buf p hfc
        simp only [Hdr.ok.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨by omega, by omega⟩

/-- The header parse of a size line `pre` (no CR) followed by CRLF and `rest`,
factored through `parseHex pre`. -/
theorem parseHeader_line (pre rest : Bytes) (hpre : ∀ b ∈ pre, b ≠ CR) :
    parseHeader (pre ++ CR :: LF :: rest)
      = match parseHex pre with
        | none => .error
        | some size => if maxChunkSize < size then .error else .ok size (pre.length + 2) := by
  have hcr := findCrlf_append_no_cr pre rest hpre
  have htake : (pre ++ CR :: LF :: rest).take pre.length = pre := List.take_left _ _
  simp only [parseHeader, hcr, htake]

/-- **Theorem 5 (overflow → error).** A size octet-run denoting a value beyond
`maxChunkSize` is a total error. -/
theorem parseHeader_overflow (n : Nat) (rest : Bytes) (h : maxChunkSize < n) :
    parseHeader (toHex n ++ CR :: LF :: rest) = .error := by
  rw [parseHeader_line (toHex n) rest (toHex_no_cr n)]
  simp only [parseHex_toHex]
  rw [if_pos h]

/-- **Theorem 5 (malformed → error).** A size token that is empty or contains a
non-hex octet (`parseHex pre = none`) is a total error. -/
theorem parseHeader_bad_hex (pre rest : Bytes) (hpre : ∀ b ∈ pre, b ≠ CR)
    (hbad : parseHex pre = none) :
    parseHeader (pre ++ CR :: LF :: rest) = .error := by
  rw [parseHeader_line pre rest hpre]; simp only [hbad]

/-- A bare `CRLF` (empty size line) is a malformed header. -/
theorem parseHeader_empty_line (rest : Bytes) :
    parseHeader (CR :: LF :: rest) = .error :=
  parseHeader_bad_hex [] rest (by simp) rfl

/-! ## Single-frame decode -/

/-- Result of decoding one chunk frame. -/
inductive Frame where
  /-- Not enough bytes to complete a frame yet. -/
  | incomplete
  /-- Malformed framing. -/
  | error
  /-- A data chunk of payload `data`, consuming `consumed` octets. -/
  | chunk (data : Bytes) (consumed : Nat)
  /-- The terminal zero-size chunk, consuming `consumed` octets. -/
  | terminal (consumed : Nat)
deriving Repr, DecidableEq

/-- Decode one chunk frame from the front of the buffer. Total. Mirrors the
reference `decode_chunked_frame`, with the trailing CRLF after chunk data
checked (RFC-required) rather than blindly consumed. -/
def decodeFrame (buf : Bytes) : Frame :=
  match parseHeader buf with
  | .incomplete => .incomplete
  | .error => .error
  | .ok size headerLen =>
    if size = 0 then
      if (buf.drop headerLen).take 2 = [CR, LF] then .terminal (headerLen + 2)
      else .incomplete
    else
      if buf.length < headerLen + size + 2 then .incomplete
      else if (buf.drop (headerLen + size)).take 2 = [CR, LF] then
        .chunk ((buf.drop headerLen).take size) (headerLen + size + 2)
      else .error

/-- **A decoded data chunk consumes a positive, in-bounds number of octets.**
This is the consumed-monotonicity that makes `decodeStream` terminate. -/
theorem decodeFrame_chunk_bound (buf data : Bytes) (c : Nat)
    (h : decodeFrame buf = .chunk data c) : 0 < c ∧ c ≤ buf.length := by
  unfold decodeFrame at h
  split at h
  · simp at h
  · simp at h
  · next size headerLen hph =>
    split at h
    · split at h <;> simp at h
    · split at h
      · simp at h
      · next hge =>
        split at h
        · simp only [Frame.chunk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact ⟨by omega, by omega⟩
        · simp at h

/-- The empty buffer needs more data. -/
theorem decodeFrame_nil : decodeFrame [] = .incomplete := rfl

/-! ## Encoding (the wire form we decode against) -/

/-- Encode one data chunk: `chunk-size CRLF chunk-data CRLF`. -/
def encodeChunk (d : Bytes) : Bytes := toHex d.length ++ [CR, LF] ++ d ++ [CR, LF]

/-- The terminal zero-size chunk: `0 CRLF CRLF`. -/
def encodeTerminal : Bytes := toHex 0 ++ [CR, LF] ++ [CR, LF]

/-- Encode a whole chunked body: the chunks in order, then the terminal. -/
def encodeStream : List Bytes → Bytes
  | [] => encodeTerminal
  | d :: ds => encodeChunk d ++ encodeStream ds

/-- Encode the chunks with **no** terminal (a truncated / still-open stream). -/
def encodeChunks : List Bytes → Bytes
  | [] => []
  | d :: ds => encodeChunk d ++ encodeChunks ds

/-- Length of one encoded chunk: size digits + CRLF + data + CRLF. -/
theorem encodeChunk_length (d : Bytes) :
    (encodeChunk d).length = (toHex d.length).length + 2 + d.length + 2 := by
  simp only [encodeChunk, List.length_append, List.length_cons, List.length_nil]

/-- Decoding one encoded data chunk (followed by any tail) recovers the payload
exactly, consuming exactly the encoded-chunk octets — no framing leaks. -/
theorem decodeFrame_encodeChunk (d tail : Bytes) (hne : d ≠ [])
    (hle : d.length ≤ maxChunkSize) :
    decodeFrame (encodeChunk d ++ tail) = .chunk d (encodeChunk d).length := by
  -- Two prefix groupings of the buffer.
  have gA : encodeChunk d ++ tail
      = (toHex d.length ++ [CR, LF]) ++ (d ++ CR :: LF :: tail) := by
    simp [encodeChunk, List.append_assoc]
  have gB : encodeChunk d ++ tail
      = (toHex d.length ++ [CR, LF] ++ d) ++ (CR :: LF :: tail) := by
    simp [encodeChunk, List.append_assoc]
  have gShape : encodeChunk d ++ tail
      = toHex d.length ++ CR :: LF :: (d ++ CR :: LF :: tail) := by
    simp [encodeChunk, List.append_assoc]
  have lenA : (toHex d.length ++ [CR, LF]).length = (toHex d.length).length + 2 := by
    simp [List.length_append]
  have lenB : (toHex d.length ++ [CR, LF] ++ d).length
      = (toHex d.length).length + 2 + d.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  -- Header parse.
  have hph : parseHeader (encodeChunk d ++ tail)
      = .ok d.length ((toHex d.length).length + 2) := by
    rw [gShape, parseHeader_line _ _ (toHex_no_cr d.length)]
    simp only [parseHex_toHex]
    rw [if_neg (Nat.not_lt.mpr hle)]
  -- Data and trailing-CRLF extractions.
  have hTakeHead :
      ((encodeChunk d ++ tail).drop ((toHex d.length).length + 2)).take d.length = d := by
    rw [gA, List.drop_left' lenA]; exact List.take_left' rfl
  have hTakeData :
      ((encodeChunk d ++ tail).drop ((toHex d.length).length + 2 + d.length)).take 2 = [CR, LF] := by
    rw [gB, List.drop_left' lenB]; rfl
  -- Non-zero size, and the whole frame is present.
  have hne0 : ¬ d.length = 0 := by
    have := List.length_pos.mpr hne; omega
  have hnotlt : ¬ (encodeChunk d ++ tail).length
      < (toHex d.length).length + 2 + d.length + 2 := by
    simp only [List.length_append, encodeChunk, List.length_cons, List.length_nil]; omega
  -- Assemble.
  rw [encodeChunk_length]
  simp only [decodeFrame, hph]
  rw [if_neg hne0, if_neg hnotlt, if_pos hTakeData, hTakeHead]

/-- Decoding the terminal chunk yields `terminal`, consuming exactly its octets. -/
theorem decodeFrame_encodeTerminal :
    decodeFrame encodeTerminal = .terminal encodeTerminal.length := by
  have gShape : encodeTerminal = toHex 0 ++ CR :: LF :: [CR, LF] := by
    simp [encodeTerminal, List.append_assoc]
  have hph : parseHeader encodeTerminal = .ok 0 ((toHex 0).length + 2) := by
    rw [gShape, parseHeader_line _ _ (toHex_no_cr 0)]
    simp only [parseHex_toHex]
    rw [if_neg (by omega)]
  have hlen1 : (toHex 0).length = 1 := rfl
  have hdrop : (encodeTerminal.drop ((toHex 0).length + 2)).take 2 = [CR, LF] := by
    rw [hlen1]; rfl
  have hTermLen : (toHex 0).length + 2 + 2 = encodeTerminal.length := by
    simp only [encodeTerminal, List.length_append, List.length_cons, List.length_nil]
  simp only [decodeFrame, hph]
  rw [if_pos True.intro, if_pos hdrop, hTermLen]

/-! ## Streaming decode -/

/-- Result of a streaming decode. -/
inductive Decoded where
  /-- Buffer exhausted before the terminal chunk. -/
  | incomplete
  /-- Malformed framing somewhere in the stream. -/
  | error
  /-- The whole body decoded: `body` is the in-order concatenation of the chunk
  payloads, consuming `consumed` octets. -/
  | complete (body : Bytes) (consumed : Nat)
deriving Repr, DecidableEq

set_option linter.unusedVariables false in
/-- Fold `decodeFrame` across the buffer, accumulating the delivered body and
consumed octets, until the terminal chunk. Terminates because each data chunk
strictly shrinks the buffer (`decodeFrame_chunk_bound`). The `h :` binding names
the frame equation for the termination proof. -/
def decodeStream (buf : Bytes) : Decoded :=
  match h : decodeFrame buf with
  | .incomplete => .incomplete
  | .error => .error
  | .terminal c => .complete [] c
  | .chunk data c =>
    match decodeStream (buf.drop c) with
    | .complete body c' => .complete (data ++ body) (c + c')
    | .incomplete => .incomplete
    | .error => .error
  termination_by buf.length
  decreasing_by
    have hb := decodeFrame_chunk_bound buf data c h
    simp only [List.length_drop]; omega

/-- One-step unfolding of `decodeStream` at a data chunk. -/
theorem decodeStream_chunk (buf data : Bytes) (c : Nat) (h : decodeFrame buf = .chunk data c) :
    decodeStream buf =
      match decodeStream (buf.drop c) with
      | .complete body c' => .complete (data ++ body) (c + c')
      | .incomplete => .incomplete
      | .error => .error := by
  rw [decodeStream, h]

/-- One-step unfolding of `decodeStream` at the terminal chunk. -/
theorem decodeStream_terminal (buf : Bytes) (c : Nat) (h : decodeFrame buf = .terminal c) :
    decodeStream buf = .complete [] c := by
  rw [decodeStream, h]

/-- One-step unfolding of `decodeStream` at an incomplete frame. -/
theorem decodeStream_incomplete (buf : Bytes) (h : decodeFrame buf = .incomplete) :
    decodeStream buf = .incomplete := by
  rw [decodeStream, h]

/-- **Theorem 2 (bytes conserved).** Decoding the encoding of a chunk list
recovers exactly the in-order concatenation of the chunk payloads
(`chunks.flatten`) and consumes exactly the whole encoded stream. The delivered
byte count is therefore the sum of the chunk sizes, and nothing from the framing
octets (size digits, CRLFs, the terminal chunk) leaks into the body. -/
theorem decodeStream_encodeStream (chunks : List Bytes)
    (hne : ∀ d ∈ chunks, d ≠ []) (hle : ∀ d ∈ chunks, d.length ≤ maxChunkSize) :
    decodeStream (encodeStream chunks)
      = .complete chunks.flatten (encodeStream chunks).length := by
  induction chunks with
  | nil =>
    show decodeStream encodeTerminal = Decoded.complete [] encodeTerminal.length
    exact decodeStream_terminal encodeTerminal encodeTerminal.length decodeFrame_encodeTerminal
  | cons d ds ih =>
    have hne_d : d ≠ [] := hne d (by simp)
    have hle_d : d.length ≤ maxChunkSize := hle d (by simp)
    have hne_ds : ∀ x ∈ ds, x ≠ [] := fun x hx => hne x (by simp [hx])
    have hle_ds : ∀ x ∈ ds, x.length ≤ maxChunkSize := fun x hx => hle x (by simp [hx])
    have hdf : decodeFrame (encodeChunk d ++ encodeStream ds) = .chunk d (encodeChunk d).length :=
      decodeFrame_encodeChunk d (encodeStream ds) hne_d hle_d
    rw [show encodeStream (d :: ds) = encodeChunk d ++ encodeStream ds from rfl,
        decodeStream_chunk _ d (encodeChunk d).length hdf,
        show (encodeChunk d ++ encodeStream ds).drop (encodeChunk d).length = encodeStream ds
          from List.drop_left _ _,
        ih hne_ds hle_ds]
    simp only [List.flatten_cons, List.length_append]

/-- **Theorem 4 (incomplete stays non-terminal).** A stream that carries all its
data chunks but is missing the terminal zero-size chunk never decodes to
`complete`: after the last data chunk the buffer is empty, so the decode reports
`incomplete`. The reader never falsely reports completion. -/
theorem decodeStream_encodeChunks_incomplete (chunks : List Bytes)
    (hne : ∀ d ∈ chunks, d ≠ []) (hle : ∀ d ∈ chunks, d.length ≤ maxChunkSize) :
    decodeStream (encodeChunks chunks) = .incomplete := by
  induction chunks with
  | nil =>
    show decodeStream [] = Decoded.incomplete
    exact decodeStream_incomplete [] decodeFrame_nil
  | cons d ds ih =>
    have hne_d : d ≠ [] := hne d (by simp)
    have hle_d : d.length ≤ maxChunkSize := hle d (by simp)
    have hne_ds : ∀ x ∈ ds, x ≠ [] := fun x hx => hne x (by simp [hx])
    have hle_ds : ∀ x ∈ ds, x.length ≤ maxChunkSize := fun x hx => hle x (by simp [hx])
    have hdf : decodeFrame (encodeChunk d ++ encodeChunks ds) = .chunk d (encodeChunk d).length :=
      decodeFrame_encodeChunk d (encodeChunks ds) hne_d hle_d
    rw [show encodeChunks (d :: ds) = encodeChunk d ++ encodeChunks ds from rfl,
        decodeStream_chunk _ d (encodeChunk d).length hdf,
        show (encodeChunk d ++ encodeChunks ds).drop (encodeChunk d).length = encodeChunks ds
          from List.drop_left _ _]
    simp only [ih hne_ds hle_ds]

/-! ## Framing-grade decode: chunk extensions and trailer sections (RFC 7230 §4.1)

`decodeStream` above deliberately models the no-`chunk-ext`, no-trailer subset —
the payload-correctness spec (`ChunkedCorrect.lean`) is stated over exactly that
grammar, and it stays that way. But the request-**framing** decision must accept
the full §4.1 wire: a recipient MUST parse and ignore chunk extensions
(`chunk-size [ chunk-ext ] CRLF`, §4.1.1) and MUST accept a trailer section
after the last-chunk (`last-chunk trailer-part CRLF`, §4.1.2). Rejecting them at
the boundary turns RFC-valid requests into closed connections.

This section extends the decoder for the boundary decision only:

* `sizeToken` — the `chunk-size` octets of a size line: everything before the
  first `;` (where the `chunk-ext` begins), without trailing `BWS` (§3.2.3: a
  recipient MUST be able to parse and ignore `BWS`).
* `parseHeaderExt` — `parseHeader` with the size read from `sizeToken`; the
  extension octets are parsed and ignored. A malformed size token is still a
  total error (`ZZ` stays rejected).
* `trailerEnd` — consume the trailer section after the zero-size chunk: zero or
  more non-empty lines each ended by CRLF, then the terminating bare CRLF.
* `decodeFrameExt` / `decodeStreamExt` — the frame/stream decode over those.

Safety facts proven below: a decoded data chunk consumes a positive, in-bounds
count (`decodeFrameExt_chunk_bound` — termination), a terminal never overreads
(`decodeFrameExt_terminal_bound`), the extended decoder agrees with the strict
one on every canonical ext-free stream (`decodeStreamExt_encodeStream`), it
never falsely completes a stream missing its terminal
(`decodeStreamExt_encodeChunks_incomplete`), and the two concrete RFC shapes the
strict decoder refused — a chunk extension, a trailer section — are decoded to
their exact boundaries (`wireExt_complete`, `wireTrailerSection_complete`). -/

/-- ASCII `;` — the chunk-extension separator (RFC 7230 §4.1.1). -/
def SEMI : UInt8 := 59
/-- ASCII space. -/
def SP : UInt8 := 32
/-- ASCII horizontal tab. -/
def HT : UInt8 := 9

/-- A `BWS` octet (RFC 7230 §3.2.3 bad whitespace): space or horizontal tab. -/
def isBws (b : UInt8) : Bool := b == SP || b == HT

/-- The size-line octets before the first `;` (the `chunk-ext`, if any, starts
there). Identity on `;`-free lines. -/
def dropExt : Bytes → Bytes
  | [] => []
  | b :: bs => if b = SEMI then [] else b :: dropExt bs

/-! ### Bounded-stack `dropExt`

`dropExt` conses *after* the recursive call, so the compiled code pushes one
stack frame per size-line octet before the `;` — recursion depth = chunk-size
token length, the same blow-up class as the naive `findCrlf`. `dropExtRevGo` is
the same pass with the kept octets accumulated in reverse (tail-recursive: a
loop, constant stack); `dropExt_eq_tail` installs it as the compiled
implementation (`@[csimp]`), with every theorem still stated over the spec. -/

/-- Tail-recursive `dropExt`: kept octets accumulate in reverse, one loop
frame total. -/
def dropExtRevGo : Bytes → Bytes → Bytes
  | acc, [] => acc.reverse
  | acc, b :: bs => if b = SEMI then acc.reverse else dropExtRevGo (b :: acc) bs

/-- The reverse-accumulator loop computes the spec behind the flushed
accumulator. -/
theorem dropExtRevGo_eq (bs : Bytes) :
    ∀ acc, dropExtRevGo acc bs = acc.reverse ++ dropExt bs := by
  induction bs with
  | nil => intro acc; simp [dropExtRevGo, dropExt]
  | cons b t ih =>
    intro acc
    rw [dropExtRevGo, dropExt]
    by_cases h : b = SEMI
    · simp [h]
    · rw [if_neg h, if_neg h, ih (b :: acc)]
      simp

/-- The bounded-stack `dropExt`: the loop from the empty accumulator. -/
def dropExtTail (bs : Bytes) : Bytes := dropExtRevGo [] bs

/-- **The loop/spec agreement.** `dropExtTail` computes the same token as
`dropExt`, in constant stack. -/
@[csimp] theorem dropExt_eq_tail : @dropExt = @dropExtTail := by
  funext bs
  rw [dropExtTail, dropExtRevGo_eq bs []]
  simp

/-- Drop trailing `BWS` octets (the grammar allows `chunk-size BWS ";"`). -/
def dropTrailingBws (bs : Bytes) : Bytes := (bs.reverse.dropWhile isBws).reverse

/-- The `chunk-size` token of a size line: everything before the first `;`,
without trailing optional whitespace. -/
def sizeToken (line : Bytes) : Bytes := dropTrailingBws (dropExt line)

/-- `dropExt` is the identity on `;`-free runs. -/
theorem dropExt_eq_self : ∀ (bs : Bytes), (∀ b ∈ bs, b ≠ SEMI) → dropExt bs = bs := by
  intro bs
  induction bs with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    have ha : a ≠ SEMI := h a (List.mem_cons_self _ _)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [dropExt, if_neg ha, ht]

/-- `dropTrailingBws` is the identity on whitespace-free runs. `dropWhile` only
inspects the head, so one case split suffices. -/
theorem dropTrailingBws_eq_self (bs : Bytes) (h : ∀ b ∈ bs, isBws b = false) :
    dropTrailingBws bs = bs := by
  have hrev : bs.reverse.dropWhile isBws = bs.reverse := by
    cases hr : bs.reverse with
    | nil => rfl
    | cons a t =>
      have ha : isBws a = false := by
        refine h a (List.mem_reverse.mp ?_)
        rw [hr]
        exact List.mem_cons_self _ _
      simp [List.dropWhile, ha]
  simp [dropTrailingBws, hrev]

/-- `sizeToken` is the identity on `;`-free, whitespace-free runs. -/
theorem sizeToken_eq_self (bs : Bytes)
    (hsemi : ∀ b ∈ bs, b ≠ SEMI) (hws : ∀ b ∈ bs, isBws b = false) :
    sizeToken bs = bs := by
  unfold sizeToken
  rw [dropExt_eq_self bs hsemi, dropTrailingBws_eq_self bs hws]

/-- A hex-digit byte is neither the extension separator nor whitespace. -/
theorem hexDigit_not_ext (d : Nat) (h : d < 16) :
    hexDigit d ≠ SEMI ∧ isBws (hexDigit d) = false := by
  rcases lt_sixteen_cases d h with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- A fueled hex encoding contains no `;` and no whitespace octet. -/
theorem toHexFuel_not_ext :
    ∀ (fuel n : Nat), ∀ b ∈ toHexFuel fuel n, b ≠ SEMI ∧ isBws b = false := by
  intro fuel
  induction fuel with
  | zero => intro n b hb; simp [toHexFuel] at hb
  | succ f ih =>
    intro n b hb
    simp only [toHexFuel] at hb
    split at hb
    · rename_i hlt
      simp only [List.mem_singleton] at hb
      subst hb
      exact hexDigit_not_ext n hlt
    · rw [List.mem_append] at hb
      rcases hb with hb | hb
      · exact ih (n / 16) b hb
      · simp only [List.mem_singleton] at hb
        subst hb
        exact hexDigit_not_ext (n % 16) (Nat.mod_lt _ (by omega))

/-- The size token of a canonical hex size line is the whole line. -/
theorem sizeToken_toHex (n : Nat) : sizeToken (toHex n) = toHex n :=
  sizeToken_eq_self _ (fun b hb => (toHexFuel_not_ext (n + 1) n b hb).1)
    (fun b hb => (toHexFuel_not_ext (n + 1) n b hb).2)

/-- Parse one chunk header, tolerating a `chunk-ext`: the size is read from the
`chunk-size` token only; the extension octets are parsed and ignored
(RFC 7230 §4.1.1). A malformed size token stays a total error. -/
def parseHeaderExt (buf : Bytes) : Hdr :=
  match findCrlf buf with
  | none => .incomplete
  | some p =>
    match parseHex (sizeToken (buf.take p)) with
    | none => .error
    | some size => if maxChunkSize < size then .error else .ok size (p + 2)

/-- A parsed extended header consumes a positive, in-bounds octet count. -/
theorem parseHeaderExt_consumed (buf : Bytes) (s c : Nat)
    (h : parseHeaderExt buf = .ok s c) : 0 < c ∧ c ≤ buf.length := by
  unfold parseHeaderExt at h
  split at h
  · simp at h
  · next p hfc =>
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i size hpx
        have hb := findCrlf_some_bound buf p hfc
        simp only [Hdr.ok.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨by omega, by omega⟩

/-- The extended header parse of a size line `pre` (no CR) followed by CRLF,
factored through `parseHex (sizeToken pre)`. -/
theorem parseHeaderExt_line (pre rest : Bytes) (hpre : ∀ b ∈ pre, b ≠ CR) :
    parseHeaderExt (pre ++ CR :: LF :: rest)
      = match parseHex (sizeToken pre) with
        | none => .error
        | some size => if maxChunkSize < size then .error else .ok size (pre.length + 2) := by
  have hcr := findCrlf_append_no_cr pre rest hpre
  have htake : (pre ++ CR :: LF :: rest).take pre.length = pre := List.take_left _ _
  simp only [parseHeaderExt, hcr, htake]

/-- Consume the trailer section and its terminating CRLF (RFC 7230 §4.1.2):
zero or more non-empty lines each ended by CRLF, then the bare CRLF. Returns
the octet count consumed, or `none` while the terminator is not yet in the
buffer. Fuel-bounded structural recursion (`length + 1` always suffices: each
step consumes at least three octets). -/
def trailerEndFuel : Nat → Bytes → Option Nat
  | 0, _ => none
  | fuel + 1, bs =>
    match findCrlf bs with
    | none => none
    | some p =>
      if p = 0 then some 2
      else (trailerEndFuel fuel (bs.drop (p + 2))).map (· + (p + 2))

/-! ### Bounded-stack `trailerEndFuel`

`trailerEndFuel` maps over the recursive result, so the compiled code pushes one
stack frame per trailer *line* — recursion depth = trailer-line count, and a
long run of tiny trailer lines is the same blow-up class as the naive line
scanners above. `trailerEndFuelGo` carries the running consumed count instead
(tail-recursive: a loop, constant stack); `trailerEndFuel_eq_tail` installs it
as the compiled implementation (`@[csimp]`) — `trailerEnd` and every theorem
stay on the spec. -/

/-- Tail-recursive `trailerEndFuel` carrying the running consumed count: the
recursive call is the whole `else` branch, so the compiler emits a loop
(constant stack). -/
def trailerEndFuelGo : Nat → Nat → Bytes → Option Nat
  | 0, _, _ => none
  | fuel + 1, acc, bs =>
    match findCrlf bs with
    | none => none
    | some p =>
      if p = 0 then some (acc + 2)
      else trailerEndFuelGo fuel (acc + (p + 2)) (bs.drop (p + 2))

/-- The loop equals the spec up to the running consumed-count shift. -/
theorem trailerEndFuelGo_eq : ∀ (fuel : Nat) (bs : Bytes) (acc : Nat),
    trailerEndFuelGo fuel acc bs = (trailerEndFuel fuel bs).map (· + acc) := by
  intro fuel
  induction fuel with
  | zero => intro bs acc; simp [trailerEndFuelGo, trailerEndFuel]
  | succ f ih =>
    intro bs acc
    cases hfc : findCrlf bs with
    | none => simp [trailerEndFuelGo, trailerEndFuel, hfc]
    | some p =>
      simp only [trailerEndFuelGo, trailerEndFuel, hfc]
      by_cases hp : p = 0
      · simp [hp, Nat.add_comm]
      · rw [if_neg hp, if_neg hp, ih (bs.drop (p + 2)) (acc + (p + 2)), Option.map_map]
        cases trailerEndFuel f (bs.drop (p + 2)) with
        | none => simp
        | some u =>
          simp only [Option.map_some', Function.comp_apply, Option.some.injEq]
          omega

/-- The bounded-stack `trailerEndFuel`: the loop from a zero consumed count. -/
def trailerEndFuelTail (fuel : Nat) (bs : Bytes) : Option Nat :=
  trailerEndFuelGo fuel 0 bs

/-- **The loop/spec agreement.** `trailerEndFuelTail` computes the same consumed
count as `trailerEndFuel`, in constant stack. -/
@[csimp] theorem trailerEndFuel_eq_tail : @trailerEndFuel = @trailerEndFuelTail := by
  funext fuel bs
  rw [trailerEndFuelTail, trailerEndFuelGo_eq fuel bs 0]
  simp

/-- Locate the end of the trailer section (octets consumed), or `none` if the
terminating bare CRLF is not yet in the buffer. Defined AFTER `trailerEndFuel_eq_tail`
so its compiled body picks up the `@[csimp]` tail-loop replacement (csimp rewrites
only call sites compiled after the attribute is registered). -/
def trailerEnd (bs : Bytes) : Option Nat := trailerEndFuel (bs.length + 1) bs

/-- A located trailer end is in bounds: the consumed count never overreads. -/
theorem trailerEndFuel_bound : ∀ (fuel : Nat) (bs : Bytes) (t : Nat),
    trailerEndFuel fuel bs = some t → t ≤ bs.length := by
  intro fuel
  induction fuel with
  | zero => intro bs t h; simp [trailerEndFuel] at h
  | succ f ih =>
    intro bs t h
    unfold trailerEndFuel at h
    split at h
    · simp at h
    · next p hfc =>
      have hb := findCrlf_some_bound bs p hfc
      split at h
      · simp only [Option.some.injEq] at h
        omega
      · cases hin : trailerEndFuel f (bs.drop (p + 2)) with
        | none => rw [hin] at h; simp at h
        | some u =>
          rw [hin] at h
          simp only [Option.map_some', Option.some.injEq] at h
          have hu := ih (bs.drop (p + 2)) u hin
          simp only [List.length_drop] at hu
          omega

/-- In-bounds form for `trailerEnd`. -/
theorem trailerEnd_bound (bs : Bytes) (t : Nat) (h : trailerEnd bs = some t) :
    t ≤ bs.length := trailerEndFuel_bound (bs.length + 1) bs t h

/-- Decode one chunk frame with framing-grade RFC 7230 §4.1 tolerance: a
`chunk-ext` on any size line is parsed and ignored; the zero-size last-chunk is
followed by a (possibly empty) trailer section and its terminating CRLF. The
data-chunk arms are those of `decodeFrame` verbatim. -/
def decodeFrameExt (buf : Bytes) : Frame :=
  match parseHeaderExt buf with
  | .incomplete => .incomplete
  | .error => .error
  | .ok size headerLen =>
    if size = 0 then
      match trailerEnd (buf.drop headerLen) with
      | none => .incomplete
      | some t => .terminal (headerLen + t)
    else
      if buf.length < headerLen + size + 2 then .incomplete
      else if (buf.drop (headerLen + size)).take 2 = [CR, LF] then
        .chunk ((buf.drop headerLen).take size) (headerLen + size + 2)
      else .error

/-- A decoded data chunk consumes a positive, in-bounds octet count — the
consumed-monotonicity that makes `decodeStreamExt` terminate. -/
theorem decodeFrameExt_chunk_bound (buf data : Bytes) (c : Nat)
    (h : decodeFrameExt buf = .chunk data c) : 0 < c ∧ c ≤ buf.length := by
  unfold decodeFrameExt at h
  split at h
  · simp at h
  · simp at h
  · next size headerLen hph =>
    split at h
    · split at h <;> simp at h
    · split at h
      · simp at h
      · next hge =>
        split at h
        · simp only [Frame.chunk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact ⟨by omega, by omega⟩
        · simp at h

/-- A decoded terminal (last-chunk plus trailer section) never overreads. -/
theorem decodeFrameExt_terminal_bound (buf : Bytes) (c : Nat)
    (h : decodeFrameExt buf = .terminal c) : c ≤ buf.length := by
  unfold decodeFrameExt at h
  split at h
  · simp at h
  · simp at h
  · next size headerLen hph =>
    have hhdr := parseHeaderExt_consumed buf size headerLen hph
    split at h
    · split at h
      · simp at h
      · next t hte =>
        simp only [Frame.terminal.injEq] at h
        have hb := trailerEnd_bound (buf.drop headerLen) t hte
        simp only [List.length_drop] at hb
        omega
    · split at h
      · simp at h
      · split at h <;> simp at h

/-- The empty buffer needs more data. -/
theorem decodeFrameExt_nil : decodeFrameExt [] = .incomplete := rfl

set_option linter.unusedVariables false in
/-- Fold `decodeFrameExt` across the buffer until the terminal — the
request-framing decode of the full RFC 7230 §4.1 wire. Terminates because each
data chunk strictly shrinks the buffer (`decodeFrameExt_chunk_bound`). -/
def decodeStreamExt (buf : Bytes) : Decoded :=
  match h : decodeFrameExt buf with
  | .incomplete => .incomplete
  | .error => .error
  | .terminal c => .complete [] c
  | .chunk data c =>
    match decodeStreamExt (buf.drop c) with
    | .complete body c' => .complete (data ++ body) (c + c')
    | .incomplete => .incomplete
    | .error => .error
  termination_by buf.length
  decreasing_by
    have hb := decodeFrameExt_chunk_bound buf data c h
    simp only [List.length_drop]; omega

/-- One-step unfolding of `decodeStreamExt` at a data chunk. -/
theorem decodeStreamExt_chunk (buf data : Bytes) (c : Nat)
    (h : decodeFrameExt buf = .chunk data c) :
    decodeStreamExt buf =
      match decodeStreamExt (buf.drop c) with
      | .complete body c' => .complete (data ++ body) (c + c')
      | .incomplete => .incomplete
      | .error => .error := by
  rw [decodeStreamExt, h]

/-- One-step unfolding of `decodeStreamExt` at the terminal. -/
theorem decodeStreamExt_terminal (buf : Bytes) (c : Nat)
    (h : decodeFrameExt buf = .terminal c) :
    decodeStreamExt buf = .complete [] c := by
  rw [decodeStreamExt, h]

/-- One-step unfolding of `decodeStreamExt` at an incomplete frame. -/
theorem decodeStreamExt_incomplete (buf : Bytes) (h : decodeFrameExt buf = .incomplete) :
    decodeStreamExt buf = .incomplete := by
  rw [decodeStreamExt, h]

/-! ### Conservativity: on the canonical ext-free wire the two decoders agree -/

/-- Decoding one encoded data chunk with the extended decoder: same payload,
same consumed count as `decodeFrame_encodeChunk`. -/
theorem decodeFrameExt_encodeChunk (d tail : Bytes) (hne : d ≠ [])
    (hle : d.length ≤ maxChunkSize) :
    decodeFrameExt (encodeChunk d ++ tail) = .chunk d (encodeChunk d).length := by
  have gA : encodeChunk d ++ tail
      = (toHex d.length ++ [CR, LF]) ++ (d ++ CR :: LF :: tail) := by
    simp [encodeChunk, List.append_assoc]
  have gB : encodeChunk d ++ tail
      = (toHex d.length ++ [CR, LF] ++ d) ++ (CR :: LF :: tail) := by
    simp [encodeChunk, List.append_assoc]
  have gShape : encodeChunk d ++ tail
      = toHex d.length ++ CR :: LF :: (d ++ CR :: LF :: tail) := by
    simp [encodeChunk, List.append_assoc]
  have lenA : (toHex d.length ++ [CR, LF]).length = (toHex d.length).length + 2 := by
    simp [List.length_append]
  have lenB : (toHex d.length ++ [CR, LF] ++ d).length
      = (toHex d.length).length + 2 + d.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hph : parseHeaderExt (encodeChunk d ++ tail)
      = .ok d.length ((toHex d.length).length + 2) := by
    rw [gShape, parseHeaderExt_line _ _ (toHex_no_cr d.length)]
    simp only [sizeToken_toHex, parseHex_toHex]
    rw [if_neg (Nat.not_lt.mpr hle)]
  have hTakeHead :
      ((encodeChunk d ++ tail).drop ((toHex d.length).length + 2)).take d.length = d := by
    rw [gA, List.drop_left' lenA]; exact List.take_left' rfl
  have hTakeData :
      ((encodeChunk d ++ tail).drop ((toHex d.length).length + 2 + d.length)).take 2 = [CR, LF] := by
    rw [gB, List.drop_left' lenB]; rfl
  have hne0 : ¬ d.length = 0 := by
    have := List.length_pos.mpr hne; omega
  have hnotlt : ¬ (encodeChunk d ++ tail).length
      < (toHex d.length).length + 2 + d.length + 2 := by
    simp only [List.length_append, encodeChunk, List.length_cons, List.length_nil]; omega
  rw [encodeChunk_length]
  simp only [decodeFrameExt, hph]
  rw [if_neg hne0, if_neg hnotlt, if_pos hTakeData, hTakeHead]

/-- The extended decoder consumes the bare terminal exactly as the strict one:
`0 CRLF CRLF` is the last-chunk with an empty trailer section. -/
theorem decodeFrameExt_encodeTerminal :
    decodeFrameExt encodeTerminal = .terminal encodeTerminal.length := by decide

/-- **Conservativity.** On every canonical ext-free, trailer-free stream the
extended decoder returns exactly the strict decoder's verdict: the in-order
payload concatenation, consuming the whole encoded stream
(`decodeStream_encodeStream`'s statement, verbatim). -/
theorem decodeStreamExt_encodeStream (chunks : List Bytes)
    (hne : ∀ d ∈ chunks, d ≠ []) (hle : ∀ d ∈ chunks, d.length ≤ maxChunkSize) :
    decodeStreamExt (encodeStream chunks)
      = .complete chunks.flatten (encodeStream chunks).length := by
  induction chunks with
  | nil =>
    show decodeStreamExt encodeTerminal = Decoded.complete [] encodeTerminal.length
    exact decodeStreamExt_terminal encodeTerminal encodeTerminal.length
      decodeFrameExt_encodeTerminal
  | cons d ds ih =>
    have hne_d : d ≠ [] := hne d (by simp)
    have hle_d : d.length ≤ maxChunkSize := hle d (by simp)
    have hne_ds : ∀ x ∈ ds, x ≠ [] := fun x hx => hne x (by simp [hx])
    have hle_ds : ∀ x ∈ ds, x.length ≤ maxChunkSize := fun x hx => hle x (by simp [hx])
    have hdf : decodeFrameExt (encodeChunk d ++ encodeStream ds)
        = .chunk d (encodeChunk d).length :=
      decodeFrameExt_encodeChunk d (encodeStream ds) hne_d hle_d
    rw [show encodeStream (d :: ds) = encodeChunk d ++ encodeStream ds from rfl,
        decodeStreamExt_chunk _ d (encodeChunk d).length hdf,
        show (encodeChunk d ++ encodeStream ds).drop (encodeChunk d).length = encodeStream ds
          from List.drop_left _ _,
        ih hne_ds hle_ds]
    simp only [List.flatten_cons, List.length_append]

/-- **No false completion.** A stream carrying its data chunks but missing the
terminal never decodes `complete` under the extended decoder either. -/
theorem decodeStreamExt_encodeChunks_incomplete (chunks : List Bytes)
    (hne : ∀ d ∈ chunks, d ≠ []) (hle : ∀ d ∈ chunks, d.length ≤ maxChunkSize) :
    decodeStreamExt (encodeChunks chunks) = .incomplete := by
  induction chunks with
  | nil =>
    show decodeStreamExt [] = Decoded.incomplete
    exact decodeStreamExt_incomplete [] decodeFrameExt_nil
  | cons d ds ih =>
    have hne_d : d ≠ [] := hne d (by simp)
    have hle_d : d.length ≤ maxChunkSize := hle d (by simp)
    have hne_ds : ∀ x ∈ ds, x ≠ [] := fun x hx => hne x (by simp [hx])
    have hle_ds : ∀ x ∈ ds, x.length ≤ maxChunkSize := fun x hx => hle x (by simp [hx])
    have hdf : decodeFrameExt (encodeChunk d ++ encodeChunks ds)
        = .chunk d (encodeChunk d).length :=
      decodeFrameExt_encodeChunk d (encodeChunks ds) hne_d hle_d
    rw [show encodeChunks (d :: ds) = encodeChunk d ++ encodeChunks ds from rfl,
        decodeStreamExt_chunk _ d (encodeChunk d).length hdf,
        show (encodeChunk d ++ encodeChunks ds).drop (encodeChunk d).length = encodeChunks ds
          from List.drop_left _ _]
    simp only [ih hne_ds hle_ds]

/-! ### Concrete non-vacuity: the two RFC shapes the strict decoder refused -/

/-- The chunk-extension wire `5;name=value CRLF hello CRLF 0 CRLF CRLF`
(RFC 7230 §4.1.1: the extension MUST be parsed and ignored). -/
def wireExt : Bytes :=
  [0x35, 0x3b, 0x6e, 0x61, 0x6d, 0x65, 0x3d, 0x76, 0x61, 0x6c, 0x75, 0x65, CR, LF,
   0x68, 0x65, 0x6c, 0x6c, 0x6f, CR, LF,
   0x30, CR, LF, CR, LF]

/-- The chunk with an extension decodes to its exact payload and boundary. -/
theorem wireExt_frame :
    decodeFrameExt wireExt = .chunk [0x68, 0x65, 0x6c, 0x6c, 0x6f] 21 := by decide

/-- **The extension wire decodes complete** — payload `hello`, the whole 26
octets consumed. The strict `decodeStream` errors on this buffer (the size line
is not a bare hex run), which is exactly the K-class conformance failure the
extended decoder repairs. -/
theorem wireExt_complete :
    decodeStreamExt wireExt = .complete [0x68, 0x65, 0x6c, 0x6c, 0x6f] 26 := by
  have h2 : decodeFrameExt (wireExt.drop 21) = .terminal 5 := by decide
  rw [decodeStreamExt_chunk wireExt _ 21 wireExt_frame,
      decodeStreamExt_terminal _ 5 h2]
  decide

/-- The trailer wire `5 CRLF hello CRLF 0 CRLF X-Trailer: v CRLF CRLF`
(RFC 7230 §4.1.2: the trailer section is accepted). -/
def wireTrailerSection : Bytes :=
  [0x35, CR, LF, 0x68, 0x65, 0x6c, 0x6c, 0x6f, CR, LF,
   0x30, CR, LF,
   0x58, 0x2d, 0x54, 0x72, 0x61, 0x69, 0x6c, 0x65, 0x72, 0x3a, 0x20, 0x76, CR, LF,
   CR, LF]

/-- **The trailer wire decodes complete** — payload `hello`, the whole 29 octets
(including the trailer section) consumed. The strict `decodeStream` never
completes on this buffer (its terminal is the bare `0 CRLF CRLF`), which is the
other K-class conformance failure the extended decoder repairs. -/
theorem wireTrailerSection_complete :
    decodeStreamExt wireTrailerSection = .complete [0x68, 0x65, 0x6c, 0x6c, 0x6f] 29 := by
  have h1 : decodeFrameExt wireTrailerSection = .chunk [0x68, 0x65, 0x6c, 0x6c, 0x6f] 10 := by
    decide
  have h2 : decodeFrameExt (wireTrailerSection.drop 10) = .terminal 19 := by decide
  rw [decodeStreamExt_chunk wireTrailerSection _ 10 h1,
      decodeStreamExt_terminal _ 19 h2]
  decide

end Chunked
end Body
