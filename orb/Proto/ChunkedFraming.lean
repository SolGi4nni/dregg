import Body.Chunked

/-!
# Chunked transfer framing: wire format + the deployed terminator parser

This file proves the HTTP/1.1 chunked transfer coding (RFC 7230 §4.1) for the
row the running dataplane deploys but had left unproven:

    chunk-size(hex) CRLF chunk-data CRLF …  0 CRLF  trailer-line*  CRLF

Two complementary results:

* **`chunked_roundtrip`** — encoding a list of (non-empty) messages as chunks
  and decoding the wire recovers exactly the in-order concatenation of the
  messages (`chunks.flatten`), with no framing octet leaking into the body; and
  the same wire is detected complete by the deployed parser. The body-recovery
  half reuses the proven byte-conservation theorem in `Body/Chunked.lean`.

* **`chunked_trailers`** — a faithful port of the deployed incremental parser
  (`crates/dataplane/src/proxy_dial.rs :: ChunkedParser`, whose job is to detect
  the terminating zero-chunk while streaming a body verbatim) is proven to reach
  its terminal `Done` state on `chunks ++ 0 CRLF trailer-lines CRLF` — i.e. the
  trailer header block after the zero-chunk is consumed, exactly as the running
  engine does. The dual `chunked_no_false_terminator` proves it never reports
  completion on a body that is missing its terminating zero-chunk.

The parser model (`PSt`, `step`, `run`) is a byte-for-byte transcription of the
Rust state machine: the `TrailerStart`/`TrailerLine`/`TrailerLineCr`/
`TrailerFinalCr` states, the size-line hex accumulation, and the data-length
countdown all mirror `ChunkedParser::advance`. Chunk data content is opaque to
the framing (the `Data` countdown consumes it by length), which is why the
theorems quantify over arbitrary payload bytes.
-/

namespace Proto.ChunkedFraming

open Body Body.Hex Body.Chunked

/-! ## The deployed parser, ported

`step`/`run` transcribe `ChunkedParser` (proxy_dial.rs). `run s sz bs` folds the
byte stream `bs` from state `s` with accumulator `sz`; `Done` is absorbing. -/

/-- Parser state — the `ChunkSt` enum of the deployed `ChunkedParser`. -/
inductive PSt where
  | Size | SizeExt | SizeCr | Data | DataCr | DataLf
  | TrailerStart | TrailerLine | TrailerLineCr | TrailerFinalCr | Done
  deriving DecidableEq, Repr

/-- ASCII `;` (chunk-extension separator). -/
def semi : UInt8 := 59
/-- ASCII `:` (trailer header field separator). -/
def COLON : UInt8 := 58
/-- ASCII space. -/
def SP : UInt8 := 32

/-- One byte of the parser. The accumulator `sz` holds the running chunk-size on
the size line and the remaining data-byte count inside a chunk — exactly the
`size` field of the deployed struct. -/
def step : PSt → Nat → UInt8 → PSt × Nat
  | .Size, sz, b =>
    match hexVal b with
    | some d => (.Size, sz * 16 + d)
    | none => if b = CR then (.SizeCr, sz) else if b = semi then (.SizeExt, sz) else (.Size, sz)
  | .SizeExt, sz, b => if b = CR then (.SizeCr, sz) else (.SizeExt, sz)
  | .SizeCr, sz, _ => if sz = 0 then (.TrailerStart, 0) else (.Data, sz)
  | .Data, sz, _ => if sz ≤ 1 then (.DataCr, 0) else (.Data, sz - 1)
  | .DataCr, sz, _ => (.DataLf, sz)
  | .DataLf, _, _ => (.Size, 0)
  | .TrailerStart, sz, b => if b = CR then (.TrailerFinalCr, sz) else (.TrailerLine, sz)
  | .TrailerLine, sz, b => if b = CR then (.TrailerLineCr, sz) else (.TrailerLine, sz)
  | .TrailerLineCr, sz, _ => (.TrailerStart, sz)
  | .TrailerFinalCr, sz, _ => (.Done, sz)
  | .Done, sz, _ => (.Done, sz)

/-- Fold `step` across a byte stream. -/
def run : PSt → Nat → Bytes → PSt × Nat
  | s, sz, [] => (s, sz)
  | s, sz, b :: bs => run (step s sz b).1 (step s sz b).2 bs

@[simp] theorem run_nil (s : PSt) (sz : Nat) : run s sz [] = (s, sz) := rfl

theorem run_cons (s : PSt) (sz : Nat) (b : UInt8) (bs : Bytes) :
    run s sz (b :: bs) = run (step s sz b).1 (step s sz b).2 bs := rfl

/-- Fold splits over an append (`run` threads its state through). -/
theorem run_append (xs ys : Bytes) : ∀ (s : PSt) (sz : Nat),
    run s sz (xs ++ ys) = run (run s sz xs).1 (run s sz xs).2 ys := by
  induction xs with
  | nil => intro s sz; rfl
  | cons b bs ih => intro s sz; simp only [List.cons_append, run_cons]; exact ih _ _

/-! ## Per-state transition lemmas (each a byte of the deployed machine) -/

theorem step_size_digit (sz : Nat) (b : UInt8) (d : Nat) (h : hexVal b = some d) :
    step .Size sz b = (.Size, sz * 16 + d) := by simp [step, h]

theorem run_Size_CR (sz : Nat) (bs : Bytes) :
    run .Size sz (CR :: bs) = run .SizeCr sz bs := by rw [run_cons]; rfl

theorem run_SizeCr_pos (sz : Nat) (b : UInt8) (bs : Bytes) (h : sz ≠ 0) :
    run .SizeCr sz (b :: bs) = run .Data sz bs := by
  rw [run_cons]; simp [step, if_neg h]

theorem run_SizeCr_zero (b : UInt8) (bs : Bytes) :
    run .SizeCr 0 (b :: bs) = run .TrailerStart 0 bs := by rw [run_cons]; simp [step]

theorem run_Data_last (a : UInt8) (bs : Bytes) :
    run .Data 1 (a :: bs) = run .DataCr 0 bs := by rw [run_cons]; simp [step]

theorem run_Data_more (sz : Nat) (a : UInt8) (bs : Bytes) (h : ¬ sz ≤ 1) :
    run .Data sz (a :: bs) = run .Data (sz - 1) bs := by rw [run_cons]; simp [step, if_neg h]

theorem run_DataCr (sz : Nat) (b : UInt8) (bs : Bytes) :
    run .DataCr sz (b :: bs) = run .DataLf sz bs := by rw [run_cons]; rfl

theorem run_DataLf (sz : Nat) (b : UInt8) (bs : Bytes) :
    run .DataLf sz (b :: bs) = run .Size 0 bs := by rw [run_cons]; rfl

theorem run_TrailerStart_CR (sz : Nat) (bs : Bytes) :
    run .TrailerStart sz (CR :: bs) = run .TrailerFinalCr sz bs := by rw [run_cons]; rfl

theorem run_TrailerStart_ne (sz : Nat) (b : UInt8) (bs : Bytes) (h : b ≠ CR) :
    run .TrailerStart sz (b :: bs) = run .TrailerLine sz bs := by
  rw [run_cons]; simp [step, if_neg h]

theorem run_TrailerLine_CR (sz : Nat) (bs : Bytes) :
    run .TrailerLine sz (CR :: bs) = run .TrailerLineCr sz bs := by rw [run_cons]; rfl

theorem run_TrailerLine_ne (sz : Nat) (b : UInt8) (bs : Bytes) (h : b ≠ CR) :
    run .TrailerLine sz (b :: bs) = run .TrailerLine sz bs := by
  rw [run_cons]; simp [step, if_neg h]

theorem run_TrailerLineCr (sz : Nat) (b : UInt8) (bs : Bytes) :
    run .TrailerLineCr sz (b :: bs) = run .TrailerStart sz bs := by rw [run_cons]; rfl

theorem run_TrailerFinalCr (sz : Nat) (b : UInt8) (bs : Bytes) :
    run .TrailerFinalCr sz (b :: bs) = run .Done sz bs := by rw [run_cons]; rfl

/-! ## Size-line hex accumulation matches `parseHexAux` -/

theorem len_pos {α} (l : List α) (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => simp

/-- Folding the `Size` state over a hex-digit run reproduces the Horner decode
`parseHexAux` — the deployed `size = size*16 + digit` accumulation. -/
theorem run_size_digits (hs : Bytes) : ∀ (acc v : Nat), parseHexAux acc hs = some v →
    run .Size acc hs = (.Size, v) := by
  induction hs with
  | nil => intro acc v h; simp only [parseHexAux, Option.some.injEq] at h; subst h; rfl
  | cons b bs ih =>
    intro acc v h
    simp only [parseHexAux] at h
    cases hb : hexVal b with
    | none => rw [hb] at h; simp at h
    | some d =>
      rw [hb] at h; simp only [Option.bind_some] at h
      rw [run_cons, step_size_digit acc b d hb]
      exact ih (acc * 16 + d) v h

/-- `parseHexAux 0 (toHex m) = some m` (the non-empty specialisation of
`parseHex_toHex`). -/
theorem parseHexAux_toHex (m : Nat) : parseHexAux 0 (toHex m) = some m := by
  have h := parseHex_toHex m
  unfold parseHex at h
  rw [if_neg (by simp [List.isEmpty_iff, toHex_ne_nil])] at h
  exact h

/-- The whole size line: `run .Size 0 (toHex m ++ tail) = run .Size m tail`. -/
theorem run_size_toHex (m : Nat) (tail : Bytes) :
    run .Size 0 (toHex m ++ tail) = run .Size m tail := by
  rw [run_append, run_size_digits (toHex m) 0 m (parseHexAux_toHex m)]

/-! ## Consuming one data chunk / one trailer line -/

/-- Inside `Data`, the machine consumes exactly `xs.length` payload bytes (content
irrelevant) and lands on `DataCr`. -/
theorem run_data_consume : ∀ (xs tail : Bytes), xs ≠ [] →
    run .Data xs.length (xs ++ tail) = run .DataCr 0 tail := by
  intro xs
  induction xs with
  | nil => intro tail h; exact absurd rfl h
  | cons a t ih =>
    intro tail _
    rw [List.cons_append, List.length_cons]
    by_cases ht : t = []
    · subst ht; simp only [List.length_nil, Nat.zero_add, List.nil_append]
      exact run_Data_last a tail
    · have hpos : 0 < t.length := len_pos t ht
      have hle : ¬ (t.length + 1 ≤ 1) := by omega
      rw [run_Data_more (t.length + 1) a (t ++ tail) hle, Nat.add_sub_cancel]
      exact ih tail ht

/-- Inside `TrailerLine`, the machine consumes a header line up to its terminating
CRLF (no CR in the field octets), returning to `TrailerStart`. -/
theorem run_trailerLine_body (ys tail : Bytes) (h : ∀ b ∈ ys, b ≠ CR) :
    run .TrailerLine 0 (ys ++ CR :: LF :: tail) = run .TrailerStart 0 tail := by
  induction ys with
  | nil =>
    simp only [List.nil_append]
    rw [run_TrailerLine_CR, run_TrailerLineCr]
  | cons a t ih =>
    have ha : a ≠ CR := h a (List.mem_cons_self)
    have ht : ∀ b ∈ t, b ≠ CR := fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [List.cons_append, run_TrailerLine_ne 0 a (t ++ CR :: LF :: tail) ha]
    exact ih ht

/-! ## Encoding a trailer block -/

/-- One trailer header line: `name: value CRLF`. -/
def trailerLine (name value : Bytes) : Bytes := name ++ COLON :: SP :: value ++ [CR, LF]

/-- The trailer header block: the lines in order (the empty terminating line is
supplied by the terminal chunk). -/
def trailerBlock (ts : List (Bytes × Bytes)) : Bytes :=
  (ts.map (fun p => trailerLine p.1 p.2)).flatten

/-- The terminating zero-chunk with a trailer block: `0 CRLF trailer-lines CRLF`. -/
def terminalT (ts : List (Bytes × Bytes)) : Bytes :=
  toHex 0 ++ [CR, LF] ++ trailerBlock ts ++ [CR, LF]

/-- COLON and SP are not CR. -/
theorem colon_sp_ne_cr : COLON ≠ CR ∧ SP ≠ CR := by decide

/-- One whole trailer line is consumed, returning to `TrailerStart`. -/
theorem run_trailerLine (n v tail : Bytes)
    (hn : ∀ b ∈ n, b ≠ CR) (hv : ∀ b ∈ v, b ≠ CR) :
    run .TrailerStart 0 (trailerLine n v ++ tail) = run .TrailerStart 0 tail := by
  have hbody : trailerLine n v ++ tail
      = (n ++ COLON :: SP :: v) ++ CR :: LF :: tail := by
    simp [trailerLine, List.append_assoc]
  rw [hbody]
  -- The body `n ++ COLON :: SP :: v` is non-empty: peel its first byte in
  -- TrailerStart, then scan the rest in TrailerLine.
  cases n with
  | nil =>
    simp only [List.nil_append, List.cons_append]
    rw [run_TrailerStart_ne 0 COLON (SP :: (v ++ CR :: LF :: tail)) colon_sp_ne_cr.1,
        run_TrailerLine_ne 0 SP (v ++ CR :: LF :: tail) colon_sp_ne_cr.2]
    exact run_trailerLine_body v tail hv
  | cons a n' =>
    have ha : a ≠ CR := hn a (List.mem_cons_self)
    have hrest : ∀ b ∈ n' ++ COLON :: SP :: v, b ≠ CR := by
      intro b hb
      rcases List.mem_append.mp hb with h | h
      · exact hn b (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with rfl | h2
        · exact colon_sp_ne_cr.1
        · rcases List.mem_cons.mp h2 with rfl | h3
          · exact colon_sp_ne_cr.2
          · exact hv b h3
    simp only [List.cons_append]
    rw [run_TrailerStart_ne 0 a ((n' ++ COLON :: SP :: v) ++ CR :: LF :: tail) ha]
    exact run_trailerLine_body (n' ++ COLON :: SP :: v) tail hrest

/-- The whole trailer block is consumed, returning to `TrailerStart`. -/
theorem run_trailerBlock : ∀ (ts : List (Bytes × Bytes)) (tail : Bytes),
    (∀ p ∈ ts, ∀ b ∈ p.1, b ≠ CR) → (∀ p ∈ ts, ∀ b ∈ p.2, b ≠ CR) →
    run .TrailerStart 0 (trailerBlock ts ++ tail) = run .TrailerStart 0 tail := by
  intro ts
  induction ts with
  | nil => intro tail _ _; simp [trailerBlock]
  | cons p ps ih =>
    intro tail hn hv
    have hnp : ∀ b ∈ p.1, b ≠ CR := hn p (List.mem_cons_self)
    have hvp : ∀ b ∈ p.2, b ≠ CR := hv p (List.mem_cons_self)
    have hnps : ∀ q ∈ ps, ∀ b ∈ q.1, b ≠ CR := fun q hq => hn q (List.mem_cons_of_mem _ hq)
    have hvps : ∀ q ∈ ps, ∀ b ∈ q.2, b ≠ CR := fun q hq => hv q (List.mem_cons_of_mem _ hq)
    have hblk : trailerBlock (p :: ps) = trailerLine p.1 p.2 ++ trailerBlock ps := by
      simp [trailerBlock, List.map_cons, List.flatten_cons]
    rw [hblk, List.append_assoc, run_trailerLine p.1 p.2 _ hnp hvp]
    exact ih tail hnps hvps

/-! ## Data chunks: `encodeChunk`/`encodeChunks` returns the machine to `Size` -/

/-- One encoded data chunk (non-empty payload) is fully consumed, returning the
machine to a fresh `Size` state. -/
theorem run_encodeChunk (d rest : Bytes) (hd : d ≠ []) :
    run .Size 0 (encodeChunk d ++ rest) = run .Size 0 rest := by
  have hne0 : d.length ≠ 0 := by have := len_pos d hd; omega
  have hbuf : encodeChunk d ++ rest
      = toHex d.length ++ (CR :: LF :: (d ++ CR :: LF :: rest)) := by
    simp [encodeChunk, List.append_assoc]
  rw [hbuf, run_size_toHex, run_Size_CR,
      run_SizeCr_pos d.length LF (d ++ CR :: LF :: rest) hne0,
      run_data_consume d (CR :: LF :: rest) hd, run_DataCr, run_DataLf]

/-- A whole list of non-empty data chunks is consumed, returning to `Size`. -/
theorem run_encodeChunks : ∀ (chunks : List Bytes) (rest : Bytes),
    (∀ d ∈ chunks, d ≠ []) → run .Size 0 (encodeChunks chunks ++ rest) = run .Size 0 rest := by
  intro chunks
  induction chunks with
  | nil => intro rest _; simp [encodeChunks]
  | cons d ds ih =>
    intro rest h
    have hd : d ≠ [] := h d (List.mem_cons_self)
    have hds : ∀ x ∈ ds, x ≠ [] := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [show encodeChunks (d :: ds) = encodeChunk d ++ encodeChunks ds from rfl,
        List.append_assoc, run_encodeChunk d _ hd]
    exact ih rest hds

/-- The terminal-with-trailers is consumed and reaches `Done`. -/
theorem run_terminalT (ts : List (Bytes × Bytes))
    (hn : ∀ p ∈ ts, ∀ b ∈ p.1, b ≠ CR) (hv : ∀ p ∈ ts, ∀ b ∈ p.2, b ≠ CR) :
    run .Size 0 (terminalT ts) = (.Done, 0) := by
  have hbuf : terminalT ts = toHex 0 ++ (CR :: LF :: (trailerBlock ts ++ [CR, LF])) := by
    simp [terminalT, List.append_assoc]
  rw [hbuf, run_size_toHex, run_Size_CR, run_SizeCr_zero,
      run_trailerBlock ts [CR, LF] hn hv,
      run_TrailerStart_CR, run_TrailerFinalCr]
  rfl

/-- `encodeStream` (Body's) is the data chunks followed by the empty-trailer
terminal. -/
theorem encodeStream_eq (chunks : List Bytes) :
    encodeStream chunks = encodeChunks chunks ++ terminalT [] := by
  induction chunks with
  | nil =>
    simp [encodeStream, encodeChunks, terminalT, encodeTerminal, trailerBlock,
          List.append_assoc, List.nil_append, List.append_nil]
  | cons d ds ih => simp [encodeStream, encodeChunks, ih, List.append_assoc]

/-! ## Main results -/

/-- **The deployed chunked-body format, byte-conservation + trailer termination.**
Encoding non-empty messages as chunks and decoding the wire recovers exactly the
in-order message concatenation (`chunks.flatten`) with no framing leakage
(reusing `Body.Chunked.decodeStream_encodeStream`), and the same wire is detected
complete by the deployed terminator parser. -/
theorem chunked_roundtrip (chunks : List Bytes)
    (hne : ∀ d ∈ chunks, d ≠ [])
    (hle : ∀ d ∈ chunks, d.length ≤ maxChunkSize) :
    decodeStream (encodeStream chunks)
        = .complete chunks.flatten (encodeStream chunks).length
    ∧ run .Size 0 (encodeStream chunks) = (.Done, 0) := by
  refine ⟨decodeStream_encodeStream chunks hne hle, ?_⟩
  rw [encodeStream_eq, run_encodeChunks chunks (terminalT []) hne,
      run_terminalT [] (by simp) (by simp)]

/-- **Trailer termination.** The deployed parser, fed a chunked body followed by
`0 CRLF trailer-lines CRLF`, consumes the trailer header block after the
zero-chunk and reaches its terminal `Done` state — exactly the behaviour of
`ChunkedParser::advance`. The trailer field octets must not contain a bare CR
(as real header fields do not). -/
theorem chunked_trailers (chunks : List Bytes) (ts : List (Bytes × Bytes))
    (hchunks : ∀ d ∈ chunks, d ≠ [])
    (hn : ∀ p ∈ ts, ∀ b ∈ p.1, b ≠ CR)
    (hv : ∀ p ∈ ts, ∀ b ∈ p.2, b ≠ CR) :
    run .Size 0 (encodeChunks chunks ++ terminalT ts) = (.Done, 0) := by
  rw [run_encodeChunks chunks (terminalT ts) hchunks, run_terminalT ts hn hv]

/-- **No false completion.** A body carrying all its data chunks but missing the
terminating zero-chunk is never reported `Done` — the reader keeps waiting. -/
theorem chunked_no_false_terminator (chunks : List Bytes) (hchunks : ∀ d ∈ chunks, d ≠ []) :
    (run .Size 0 (encodeChunks chunks)).1 ≠ .Done := by
  have h : run .Size 0 (encodeChunks chunks) = run .Size 0 [] := by
    have := run_encodeChunks chunks [] hchunks
    simpa using this
  rw [h]; decide

/-! ## Concrete deployed-wire vectors (the `ChunkedParser` unit-test bytes)

These are the exact byte streams the deployed Rust unit test / the curl wire
carry, proven complete by the ported parser via kernel computation. -/

/-- `"5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n"` — two data chunks, no trailers. -/
def wireHello : Bytes :=
  [0x35, CR, LF, 0x68, 0x65, 0x6c, 0x6c, 0x6f, CR, LF,
   0x36, CR, LF, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, CR, LF,
   0x30, CR, LF, CR, LF]

theorem wireHello_done : run .Size 0 wireHello = (.Done, 0) := by decide

/-- `"0\r\nX-Trailer: v\r\n\r\n"` — the terminal zero-chunk with a trailer line. -/
def wireTrailer : Bytes :=
  [0x30, CR, LF, 0x58, 0x2d, 0x54, 0x72, 0x61, 0x69, 0x6c, 0x65, 0x72,
   0x3a, 0x20, 0x76, CR, LF, CR, LF]

theorem wireTrailer_done : run .Size 0 wireTrailer = (.Done, 0) := by decide

end Proto.ChunkedFraming
