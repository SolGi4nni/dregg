import Arena.Parse

/-!
# Datapath.Span — a borrowed byte-window (the zero-copy concrete representation)

The deployed serve is typed on `Proto.Bytes = List UInt8`: every received request
is materialized as a per-byte cons-list before it is parsed, and the same
representation flows through the whole pipeline. That cons-list is the dominant
datapath cost — one heap cell per received byte, plus a `ByteArray → List`
marshal at the FFI boundary.

This module introduces the concrete representation a zero-copy datapath uses
instead: a **borrowed window** into a buffer — an `(off, len)` span over a shared
`ByteArray`, exactly the reference engine's arena+offset request view. No bytes
are copied to name a window; a single received buffer can back many spans
(pipelined requests: `⟨buf, off₁, len₁⟩`, `⟨buf, off₂, len₂⟩`, …) with no
per-request allocation.

The bridge back to the abstract model is `denote`: the `List UInt8` a span
*represents*. Every refinement theorem in `Datapath.Refine` is stated as an
equation between a span-native computation and the abstract list computation on
`denote`, so the model's meaning is preserved exactly while the representation
becomes a borrowed offset view.

`read` is the second, index-native reading of the same bytes: it reads the window
byte-by-byte through `buf[off + i]` (no whole-buffer `toList`). `read_eq_denote`
proves the two agree on a well-formed span — the load-bearing bridge that lets a
span-native parser (which reads by index) be proven equal to the abstract
list-parser (which consumes `denote`).

## CODEGEN OBLIGATION (the request half's analogue of Pipeline's obligation #2)

`read`/`denote` are `List`-valued in the *model* (Lean is pure). The obligation
the specializing backend discharges is that a span-native scan lowers to direct
indexed loads `buf[off + i]` with **no** materialized intermediate list — exactly
as the affine `ResponseBuilder` lowers to in-place writes. The model proves the
scan computes the right bytes; the codegen removes the allocation. The two are
separable, and this file closes the model half.
-/

namespace Datapath

/-- A borrowed byte-window: an `(off, len)` view into a shared buffer. This is the
zero-copy concrete request representation — no copy is made to name the window,
and one `buf` backs many spans. Mirrors the reference engine's arena+offset
request view (`ParsedRequest`: one arena `Bytes` + `(offset, length)` pairs). -/
structure SpanBytes where
  /-- The shared underlying buffer (borrowed, not owned by the span). -/
  buf : ByteArray
  /-- Window start offset into `buf`. -/
  off : Nat
  /-- Window length. -/
  len : Nat

namespace SpanBytes

/-- Well-formedness: the window lies inside the buffer. -/
def Wf (s : SpanBytes) : Prop := s.off + s.len ≤ s.buf.size

/-- **The abstract bytes a span represents** — the `List UInt8` window
`buf[off .. off+len)`. This is the denotation into the model's `Bytes` type; the
refinement theorems equate span-native computations with the abstract list
computations applied to `denote`. -/
def denote (s : SpanBytes) : List UInt8 :=
  (s.buf.data.toList.drop s.off).take s.len

/-- **The index-native reading** of the same window: byte `i` is read directly
through `buf[off + i]`, never materializing a whole-buffer list. `read_eq_denote`
proves this equals `denote` on a well-formed span — so a parser that scans by
index computes the same bytes as the abstract list-parser. -/
def read (s : SpanBytes) : List UInt8 :=
  List.ofFn (n := s.len) (fun i => s.buf.get! (s.off + i.val))

/-- A single byte of the window, read by index (`buf[off + i]`). -/
def getByte (s : SpanBytes) (i : Nat) : UInt8 := s.buf.get! (s.off + i)

@[simp] theorem length_read (s : SpanBytes) : s.read.length = s.len := by
  simp [read]

/-- `denote` has the window length on a well-formed span. -/
theorem length_denote (s : SpanBytes) (h : s.Wf) : s.denote.length = s.len := by
  unfold denote Wf at *
  rw [List.length_take, List.length_drop, Array.length_toList]
  have : s.buf.data.size = s.buf.size := rfl
  omega

/-- `getByte` reads the underlying array element in bounds. -/
theorem getByte_eq (s : SpanBytes) (i : Nat) (h : s.off + i < s.buf.size) :
    s.getByte i = s.buf.data[s.off + i]'(h) := by
  unfold getByte
  show s.buf.data.get! (s.off + i) = _
  have h' : s.off + i < s.buf.data.size := h
  simp only [Array.get!, Array.getD, dif_pos h']
  rfl

/-- **The load-bearing bridge.** On a well-formed span, the index-native `read`
equals the abstract `denote`: reading the window byte-by-byte through
`buf[off + i]` reconstructs exactly the `List UInt8` the span represents. This is
what lets a span-native (index-reading) parser be proven equal to the abstract
list-parser on `denote`. -/
theorem read_eq_denote (s : SpanBytes) (h : s.Wf) : s.read = s.denote := by
  apply List.ext_getElem
  · rw [length_read, length_denote s h]
  · intro i h₁ h₂
    rw [length_read] at h₁
    have hb : s.off + i < s.buf.size := by unfold Wf at h; omega
    -- LHS: read[i] = buf.get! (off + i) = buf.data[off+i]
    have hlhs : s.read[i] = s.buf.data[s.off + i]'hb := by
      simp only [read, List.getElem_ofFn]
      show s.buf.get! (s.off + i) = _
      have hb' : s.off + i < s.buf.data.size := hb
      simp only [ByteArray.get!, Array.get!, Array.getD, dif_pos hb']
      rfl
    -- RHS: denote[i] = buf.data.toList[off+i] = buf.data[off+i]
    have hdroplen : i < (s.buf.data.toList.drop s.off).length := by
      rw [List.length_drop, Array.length_toList]
      have : s.buf.data.size = s.buf.size := rfl
      unfold Wf at h; omega
    have hrhs : s.denote[i] = s.buf.data[s.off + i]'hb := by
      unfold denote
      rw [List.getElem_take, List.getElem_drop, Array.getElem_toList]
    rw [hlhs, hrhs]

/-! ## The full-buffer span (the trivial window) -/

/-- The whole buffer as one span. -/
def full (buf : ByteArray) : SpanBytes := ⟨buf, 0, buf.size⟩

@[simp] theorem full_wf (buf : ByteArray) : (full buf).Wf := by
  simp [full, Wf]

/-- The whole-buffer span denotes to the buffer's underlying byte list. -/
theorem denote_full (buf : ByteArray) : (full buf).denote = buf.data.toList := by
  unfold denote full
  rw [List.drop_zero, show buf.size = buf.data.toList.length from Array.length_toList.symm,
    List.take_length]

end SpanBytes
end Datapath
