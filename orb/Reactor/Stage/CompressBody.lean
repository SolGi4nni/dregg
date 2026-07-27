import Reactor.Stage.CompressExt

/-!
# Reactor.Stage.CompressBody — the LZ meta-block body (parity row `mw.2b`)

`Reactor.Stage.CompressExt` closed the zstd/brotli **container**: negotiation, the
frame magic, and the integrity trailer. Its one named residual was *the entropy-coded
body itself* — "the FSE/Huffman-and-LZ zstd block, the brotli meta-block bitstream".
This module closes that residual's provable core: **the LZ77 sequence layer** that is
the shared heart of both codings (zstd's `Sequences` section, brotli's insert-and-copy
commands), with a proven lossless round-trip, a real back-reference decoder, and the
window / block-size well-formedness that the header fields advertise.

## The model

An LZ meta-block body is a list of `Tok`ens: a `lit b` emits one literal byte; a
`copy dist len` copies `len` bytes from `dist` positions back in the output produced so
far — the sliding-window back-reference. Distances may be **shorter than the length**
(overlapping copy), which is how both codings encode runs: `copy 1 n` repeats the last
byte `n` times (RLE), `copy 2 n` repeats the last two bytes, and so on. `decode` replays
the token stream left-to-right against the growing window (`lzDecode`).

## What is proven (all 0-sorry, axioms ⊆ {propext, Quot.sound})

* **`rle_roundtrip`** — the headline losslessness: for *any* byte string, a real
  run-length LZ encoder (`rleEncode`, which genuinely emits `copy` tokens) decodes back
  to the exact input. `lzDecode (rleEncode bs) = bs`. Non-vacuous: `rleEncode_compresses`
  exhibits a run collapsing to a `lit` + `copy` pair (real compression, not a literal
  passthrough).

* **`backref_period_2`** — a distance-2 back-reference genuinely reconstructs a periodic
  string (`[1,2] → 1,2,1,2,1,2`), proving the window copy is a real dictionary reference,
  not just RLE.

* **`decode_size`** — the decoded size is exactly `#literals + Σ copy-lengths`: the
  block's advertised content size (zstd `Frame_Content_Size`, brotli `MLEN`) is met on
  the nose. `copyN_length` is the window-copy size law it rests on.

* **`window_safe`** — the meaning of the window-log header field: a copy whose distance is
  within the produced output (`1 ≤ dist ≤ |out|`) reads a byte that was **genuinely in
  the window** (`byteBack out dist ∈ out`) — never an out-of-range default. This is the
  "no reference before the start of the block / beyond the window" safety property.

* **`header_wf` / `block_size_matches`** — a meta-block header (final flag, window-log,
  content size) is well-formed when its window-log is in the RFC-legal band and its
  advertised size matches what the body decodes to.

* **`body_stack_roundtrip`** — the layering: for any lawful sequence serializer, the LZ
  body threaded through `CompressExt`'s proven container round-trips end to end
  (`src → rleEncode → serialize → container → unwrap → parse → lzDecode = src`).

## Honest follow-ons (the entropy stage proper)

The FSE/tANS numeric decoder (zstd) and the full brotli context-modeling + canonical
Huffman entropy stage — and the concrete bit-level sequence serializer — remain named
follow-ons; this module proves the LZ layer they sit atop, plus the window/size
well-formedness the headers carry.
-/

namespace Reactor.Stage.CompressBody

open Proto (Bytes)

/-! ## Tokens and the window-copy decoder -/

/-- An LZ meta-block token: a literal byte, or a back-reference copying `len` bytes from
`dist` positions back in the output produced so far (the sliding-window match). -/
inductive Tok where
  | lit  : UInt8 → Tok
  | copy : Nat → Nat → Tok
  deriving DecidableEq, Repr

/-- The byte `dist` positions back from the current end of `out` (1 = the last byte).
Out-of-range distances read the `0` default — `window_safe` shows a valid distance never
does. -/
def byteBack (out : Bytes) (dist : Nat) : UInt8 := out.reverse.getD (dist - 1) 0

/-- Emit one back-referenced byte, growing the window by one. -/
def emit1 (out : Bytes) (dist : Nat) : Bytes := out ++ [byteBack out dist]

/-- Copy `len` bytes from `dist` back, re-reading the growing window each step (so
`dist < len` overlaps — the RLE / periodic case). -/
def copyN (out : Bytes) (dist : Nat) : Nat → Bytes
  | 0 => out
  | len + 1 => copyN (emit1 out dist) dist len

/-- Replay one token against the current window. -/
def step (out : Bytes) : Tok → Bytes
  | .lit b        => out ++ [b]
  | .copy dist len => copyN out dist len

/-- Decode a token stream starting from a window `out`. -/
def lzRun (out : Bytes) (ts : List Tok) : Bytes := ts.foldl step out

/-- **Decode** an LZ meta-block body: replay the tokens from an empty window. -/
def lzDecode (ts : List Tok) : Bytes := lzRun [] ts

/-- Decoding a concatenation threads the window through — the fold splits. -/
theorem lzRun_append (out : Bytes) (a b : List Tok) :
    lzRun out (a ++ b) = lzRun (lzRun out a) b := by
  simp [lzRun, List.foldl_append]

/-! ## Overlapping distance-1 copy (the RLE core) -/

/-- A distance-1 copy appends `k` repetitions of the window's last byte. -/
theorem copyN_dist1 (k : Nat) (pre : Bytes) (b : UInt8) :
    copyN (pre ++ [b]) 1 k = pre ++ [b] ++ List.replicate k b := by
  induction k generalizing pre b with
  | zero => simp [copyN]
  | succ k ih =>
    have hbb : byteBack (pre ++ [b]) 1 = b := by
      simp [byteBack]
    have : emit1 (pre ++ [b]) 1 = (pre ++ [b]) ++ [b] := by
      simp [emit1, hbb]
    rw [copyN, this, ih (pre ++ [b]) b]
    simp [List.replicate_succ, List.append_assoc]

/-! ## A real run-length LZ encoder and its round-trip -/

/-- Flush a pending run of `cnt` copies of `b` into tokens: a literal then, for a run
longer than one, a distance-1 copy of the remainder (genuine compression). -/
def flush (b : UInt8) (cnt : Nat) : List Tok :=
  match cnt with
  | 0     => []
  | c + 1 => .lit b :: (if c == 0 then [] else [.copy 1 c])

/-- Decoding a flushed run appends exactly that run to the window. -/
theorem flush_decode (out : Bytes) (b : UInt8) (cnt : Nat) :
    lzRun out (flush b cnt) = out ++ List.replicate cnt b := by
  match cnt with
  | 0 => simp [flush, lzRun]
  | 1 => simp [flush, lzRun, step, List.replicate]
  | c + 2 =>
    show lzRun out (.lit b :: [Tok.copy 1 (c + 1)]) = out ++ List.replicate (c + 2) b
    simp only [lzRun, List.foldl_cons, List.foldl_nil, step]
    show copyN (out ++ [b]) 1 (c + 1) = out ++ List.replicate (c + 2) b
    rw [copyN_dist1 (c + 1) out b]
    simp [List.replicate_succ, List.append_assoc]

/-- Pending-run state: the current byte and how many of it we have seen. -/
def stBytes : Option (UInt8 × Nat) → Bytes
  | none        => []
  | some (b, c) => List.replicate c b

/-- The streaming RLE-LZ pass: coalesce maximal runs, flushing on a byte change. -/
def rleGo : Bytes → Option (UInt8 × Nat) → List Tok
  | [],      none        => []
  | [],      some (b, c) => flush b c
  | x :: xs, none        => rleGo xs (some (x, 1))
  | x :: xs, some (b, c) =>
      if x == b then rleGo xs (some (b, c + 1))
      else flush b c ++ rleGo xs (some (x, 1))

/-- **Encode** a byte string into an LZ meta-block body (run-length back-references). -/
def rleEncode (bs : Bytes) : List Tok := rleGo bs none

/-- The decoder invariant: decoding the tokens for `bs` with a pending run `st` appends
the pending run and then `bs` to the window. -/
theorem rleGo_decode : ∀ (bs : Bytes) (out : Bytes) (st : Option (UInt8 × Nat)),
    lzRun out (rleGo bs st) = out ++ stBytes st ++ bs := by
  intro bs
  induction bs with
  | nil =>
    intro out st
    cases st with
    | none => simp [rleGo, lzRun, stBytes]
    | some p =>
      obtain ⟨b, c⟩ := p
      simp only [rleGo, stBytes]
      rw [flush_decode]
      simp
  | cons x xs ih =>
    intro out st
    cases st with
    | none =>
      simp only [rleGo, stBytes]
      rw [ih out (some (x, 1))]
      simp [stBytes, List.replicate]
    | some p =>
      obtain ⟨b, c⟩ := p
      simp only [rleGo, stBytes]
      split
      · next hxb =>
        have hx : x = b := eq_of_beq hxb
        rw [ih out (some (b, c + 1))]
        subst hx
        simp [stBytes, List.replicate_succ', List.append_assoc]
      · next hxb =>
        rw [lzRun_append, flush_decode, ih (out ++ List.replicate c b) (some (x, 1))]
        simp [stBytes, List.replicate, List.append_assoc]

/-- **Headline losslessness.** The RLE-LZ meta-block body is lossless: any byte string
encodes and decodes back to itself. -/
theorem rle_roundtrip (bs : Bytes) : lzDecode (rleEncode bs) = bs := by
  unfold lzDecode rleEncode
  rw [rleGo_decode bs [] none]
  simp [stBytes]

/-! ## Non-vacuity — real compression and a real back-reference -/

/-- The encoder genuinely compresses a run: five equal bytes collapse to a literal and a
distance-1 copy (a `copy` token really appears — not a literal passthrough). -/
theorem rleEncode_compresses :
    rleEncode [7, 7, 7, 7, 7] = [.lit 7, .copy 1 4] := by decide

/-- And that pair decodes back to the run. -/
theorem rleEncode_compresses_roundtrip :
    lzDecode [.lit 7, .copy 1 4] = [7, 7, 7, 7, 7] := by decide

/-- **A genuine distance-2 back-reference.** Copying with distance 2 reconstructs a
periodic string — a real sliding-window dictionary reference, distinct from RLE. -/
theorem backref_period_2 :
    lzDecode [.lit 1, .lit 2, .copy 2 4] = [1, 2, 1, 2, 1, 2] := by decide

/-! ## Decoded-size well-formedness (the content-size header) -/

/-- A window copy grows the output by exactly its length. -/
theorem copyN_length (dist len : Nat) (out : Bytes) :
    (copyN out dist len).length = out.length + len := by
  induction len generalizing out with
  | zero => simp [copyN]
  | succ len ih =>
    rw [copyN, ih (emit1 out dist)]
    simp only [emit1, List.length_append, List.length_cons, List.length_nil]
    omega

/-- One token grows the window by 1 (literal) or by the copy length. -/
theorem step_length (out : Bytes) (t : Tok) :
    (step out t).length = out.length + (match t with | .lit _ => 1 | .copy _ len => len) := by
  cases t with
  | lit b => simp [step]
  | copy dist len => simp [step, copyN_length]

/-- The size a token contributes to the decoded block. -/
def tokLen : Tok → Nat
  | .lit _      => 1
  | .copy _ len => len

/-- **Decoded content size.** The block decodes to exactly `Σ tokLen` bytes — the size
the header (`Frame_Content_Size` / `MLEN`) advertises. -/
theorem decode_size (ts : List Tok) :
    (lzDecode ts).length = (ts.map tokLen).sum := by
  suffices h : ∀ out, (lzRun out ts).length = out.length + (ts.map tokLen).sum by
    simpa [lzDecode] using h []
  induction ts with
  | nil => intro out; simp [lzRun]
  | cons t ts ih =>
    intro out
    show (lzRun (step out t) ts).length = _
    rw [ih (step out t), step_length]
    cases t <;> simp [tokLen, Nat.add_assoc]

/-! ## Window safety (the window-log header field) -/

/-- **Window safety.** A copy whose distance lies within the produced output reads a byte
that was genuinely in the window — never the out-of-range default. This is the meaning of
the window-log header: no back-reference before the start of the block. -/
theorem window_safe (out : Bytes) (dist : Nat) (h1 : 1 ≤ dist) (h2 : dist ≤ out.length) :
    byteBack out dist ∈ out := by
  have hlt : dist - 1 < out.reverse.length := by
    rw [List.length_reverse]
    omega
  have hbb : byteBack out dist = out.reverse[dist - 1] := by
    simp only [byteBack, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      Option.getD_some]
  rw [hbb, ← List.mem_reverse]
  exact List.getElem_mem hlt

/-! ## Meta-block header well-formedness -/

/-- A meta-block header: the final-block flag (zstd `Last_Block` / brotli `ISLAST`), the
window-log (`Window_Descriptor` / `WBITS`), and the advertised decoded content size. -/
structure BlockHeader where
  final     : Bool
  windowLog : Nat
  size      : Nat
  deriving DecidableEq, Repr

/-- A header is well-formed when its window-log is in the RFC-legal band (zstd 10..31,
brotli 10..24 — the intersection lower bound 10, upper 31 admits both). -/
def BlockHeader.wf (h : BlockHeader) : Prop := 10 ≤ h.windowLog ∧ h.windowLog ≤ 31

/-- A header describes a body when its advertised size is what the body decodes to and
its declared distances all fit in `2^windowLog` positions. -/
def BlockHeader.describes (h : BlockHeader) (ts : List Tok) : Prop :=
  h.size = (lzDecode ts).length ∧
    ∀ dist len, Tok.copy dist len ∈ ts → 1 ≤ dist ∧ dist ≤ 2 ^ h.windowLog

/-- A concrete well-formed header over a real body (non-vacuity of `wf`/`describes`). -/
def sampleHeader : BlockHeader := { final := true, windowLog := 21, size := 5 }

theorem header_wf : sampleHeader.wf := by
  constructor <;> decide

/-- The sample header genuinely describes the RLE body of a 5-byte run: the advertised
size matches the decode and the lone distance-1 copy is inside the 2^21 window. -/
theorem block_size_matches :
    sampleHeader.describes (rleEncode [7, 7, 7, 7, 7]) := by
  constructor
  · rw [rle_roundtrip]; rfl
  · intro dist len hmem
    rw [rleEncode_compresses] at hmem
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    · exact Tok.noConfusion h
    · injection h with hd hl
      subst hd
      exact ⟨by decide, by decide⟩

/-! ## The layering — LZ body inside CompressExt's container -/

open Reactor.Stage.CompressExt (Codec encode decode)

/-- **End-to-end stack round-trip.** For any lawful sequence serializer, the LZ body
threaded through `CompressExt`'s proven zstd container round-trips: the source is
recovered after encode → serialize → container-wrap → container-unwrap → parse → decode.
The concrete bit-level serializer is the named follow-on; the container and the LZ body
are both proven here. -/
theorem body_stack_roundtrip
    (ser : List Tok → Bytes) (de : Bytes → Option (List Tok))
    (hser : ∀ ts, de (ser ts) = some ts) (src : Bytes) :
    (decode (encode Codec.zstd (ser (rleEncode src)))).bind
        (fun p => (de p.2).map lzDecode) = some src := by
  rw [Reactor.Stage.CompressExt.compress_decompress_roundtrip_zstd]
  show (de (ser (rleEncode src))).map lzDecode = some src
  rw [hser, Option.map_some, rle_roundtrip]

/-! ## Axiom audit -/

#print axioms rle_roundtrip
#print axioms backref_period_2
#print axioms decode_size
#print axioms window_safe
#print axioms block_size_matches
#print axioms body_stack_roundtrip

end Reactor.Stage.CompressBody
