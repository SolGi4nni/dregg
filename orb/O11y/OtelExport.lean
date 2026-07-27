/-
# O11y.OtelExport — the OTLP/JSON span exporter (ob.5)

Ledger row ob.5 (distributed tracing / OTel export) was PARTIAL: the W3C trace-context and
the span model + batch processor (`O11y.OtelTrace`) were proven, but the *exporter* — the
step that serializes a span to the OTLP wire an OpenTelemetry collector ingests — was
MISSING. This module is that exporter: `Span → OTLP/JSON`.

It renders each span to the OTLP/JSON span object shape
(`{"traceId":"…","spanId":"…","parentSpanId":"…","name":"…"}`) with the 128/64-bit ids as
lowercase hex, and a batch of spans to a JSON array. Reuses the proven order-preserving
batcher (`O11y.batches` / `otel_export_batches`).

What is proved:
  * `readTraceId_spanJson` — the OPERATIONAL emit=readback theorem: a real field parser
    (`readTraceId`: skip the `{"traceId":"` prefix, read to the closing quote) applied to the
    emitted `spanJson name s` recovers exactly the span's rendered traceId
    (`s.traceId.map nibHex`), `∀ name s`. This is `parse (emit s) = spec`, not a definitional
    identity — the parser genuinely walks the emitted bytes.
  * `readTraceId_discriminates` — the NON-VACUITY witness: two spans with distinct traceIds
    parse back to distinct values, so the readback is not a vacuous constant map (a "pre-state
    where the conclusion is false" is inhabited — `readTraceId (spanJson name s₂)` does NOT
    equal `s₁`'s id when the ids differ).

Structural support lemmas (injectivity / length / count / order — NOT end-to-end on their own):
  * `hexOf_inj` — the hex rendering of an id is injective: distinct trace and span ids render
    to distinct strings, so no two spans can collide on the exported id (no cross-attribution).
  * `hexOf_len` — a `k`-nibble id renders to exactly `k` hex chars (128-bit → 32 chars).
  * `span_traceId_hex_len` and `span_spanId_hex_len` — a well-formed span exports a
    32 or 16 hex-char traceId or spanId (RFC-mandated widths).
  * `exportSpans_count` — the exported batch has exactly one JSON object per span (none
    dropped/duplicated), and `exportSpans_order` (via `otel_export_batches`) preserves order.

Honest residual: the readback is proved for the traceId FIELD. The full OTLP/JSON grammar
roundtrip (all four fields + the batch array, via a total JSON parser) is NOT yet proved —
`readTraceId_spanJson` is the first field-level operational stone, not the whole-object parser.
The driver `O11y.OtelDrive` prints the exported OTLP/JSON for a concrete sampled span.
-/
import O11y.OtelTrace

namespace O11y.OtelExport

open O11y
open Trace

/-! ## Hex rendering of an id -/

/-- A hex nibble as its lowercase ASCII char (`0-9a-f`). -/
def nibHex (n : Nibble) : Char :=
  if n.val < 10 then Char.ofNat (48 + n.val) else Char.ofNat (97 + n.val - 10)

/-- Render an id (nibble list) to its hex string. -/
def hexOf (ns : List Nibble) : String := String.ofList (ns.map nibHex)

theorem nibHex_inj : ∀ (a b : Nibble), nibHex a = nibHex b → a = b := by decide

theorem map_nibHex_inj : ∀ {a b : List Nibble}, a.map nibHex = b.map nibHex → a = b
  | [], [], _ => rfl
  | [], _::_, h => by simp at h
  | _::_, [], h => by simp at h
  | x::xs, y::ys, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      have hx := nibHex_inj x y h.1
      have ht := map_nibHex_inj h.2
      rw [hx, ht]

/-- **`hexOf_inj`.** Hex rendering is injective: distinct ids render distinct — no two
spans collide on the exported trace or span id. -/
theorem hexOf_inj : ∀ (a b : List Nibble), hexOf a = hexOf b → a = b := by
  intro a b h; exact map_nibHex_inj (String.ofList_injective h)

/-- The rendered id's char list is exactly one hex char per nibble. -/
theorem hexOf_toList (ns : List Nibble) : (hexOf ns).toList = ns.map nibHex := by
  unfold hexOf; exact String.toList_ofList

theorem hexOf_len (ns : List Nibble) : (hexOf ns).toList.length = ns.length := by
  rw [hexOf_toList, List.length_map]

/-! ## The span → OTLP/JSON exporter -/

/-- One OTLP/JSON span object. -/
def spanJson (name : String) (s : Span) : String :=
  "{\"traceId\":\"" ++ hexOf s.traceId ++
  "\",\"spanId\":\"" ++ hexOf s.spanId ++
  "\",\"parentSpanId\":\"" ++ hexOf s.parentId ++
  "\",\"name\":\"" ++ name ++ "\"}"

/-- A batch of spans as a JSON array of span objects. -/
def exportSpans (name : String) (spans : List Span) : String :=
  "[" ++ String.intercalate "," (spans.map (spanJson name)) ++ "]"

/-- **`span_traceId_hex_len`.** A well-formed span exports a 32-hex-char (128-bit) traceId. -/
theorem span_traceId_hex_len (s : Span) (h : s.Wf) : (hexOf s.traceId).toList.length = 32 := by
  rw [hexOf_len]; exact h.1

/-- **`span_spanId_hex_len`.** A well-formed span exports a 16-hex-char (64-bit) spanId. -/
theorem span_spanId_hex_len (s : Span) (h : s.Wf) : (hexOf s.spanId).toList.length = 16 := by
  rw [hexOf_len]; exact h.2.1

/-- **`exportSpans_count`.** The exporter emits exactly one span object per span. -/
theorem exportSpans_count (name : String) (spans : List Span) :
    (spans.map (spanJson name)).length = spans.length := by simp

/-- **`exportSpans_order`.** Chunking a span queue into export batches and flattening
recovers the queue in order (reuses the proven batcher) — no span dropped/reordered. -/
theorem exportSpans_order (cap : Nat) (spans : List Span) :
    (batches cap spans).flatten = spans := otel_export_batches cap spans

/-! ## Operational: the emitted traceId field parses back to the span's id

`readTraceId` is a real parser — skip the fixed `{"traceId":"` prefix (12 chars), then read
characters up to the closing `"`. `readTraceId_spanJson` proves it recovers exactly the
rendered traceId from the emitted object, `∀ name s` — `parse (emit s) = spec`. -/

/-- ASCII double-quote, the OTLP/JSON field delimiter. -/
def quoteC : Char := Char.ofNat 34

/-- Parse the traceId value out of an OTLP/JSON span object: skip the 12-char `{"traceId":"`
prefix, then read up to the closing quote. -/
def readTraceId (js : String) : List Char :=
  (js.toList.drop 12).takeWhile (fun c => c != quoteC)

/-- No hex nibble renders to the `"` delimiter, so a hex run never terminates the field early. -/
theorem nibHex_ne_quote : ∀ (n : Nibble), nibHex n != quoteC := by decide

/-- `takeWhile (≠ ") ` over a quote-free run followed by the delimiter returns exactly the run. -/
theorem takeWhile_append_quote (l r : List Char) (hl : ∀ x ∈ l, x != quoteC) :
    (l ++ quoteC :: r).takeWhile (fun c => c != quoteC) = l := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have ha : a != quoteC := hl a (List.mem_cons_self ..)
      have has : ∀ x ∈ as, x != quoteC := fun x hx => hl x (List.mem_cons_of_mem _ hx)
      simp [ha, ih has]

/-- **`readTraceId_spanJson`** (OPERATIONAL emit=readback). The traceId field parsed out of
the emitted span object is exactly the span's rendered traceId, `∀ name s`. -/
theorem readTraceId_spanJson (name : String) (s : Span) :
    readTraceId (spanJson name s) = s.traceId.map nibHex := by
  rw [← hexOf_toList]
  have hmem : ∀ x ∈ (hexOf s.traceId).toList, x != quoteC := by
    rw [hexOf_toList]; intro x hx
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hx
    exact nibHex_ne_quote n
  have e : "\",\"spanId\":\"".toList = quoteC :: "\",\"spanId\":\"".toList.tail := by decide
  unfold readTraceId spanJson
  rw [show (12 : Nat) = "{\"traceId\":\"".toList.length from by decide]
  simp only [String.toList_append, List.append_assoc]
  rw [List.drop_append_length, e, List.cons_append]
  exact takeWhile_append_quote _ _ hmem

/-- **`readTraceId_discriminates`** (NON-VACUITY). Distinct traceIds parse back to distinct
values: the readback genuinely recovers the id, it is not a vacuous constant. In particular
`readTraceId (spanJson name s₂)` does NOT equal `s₁`'s rendered id when the ids differ — the
required pre-state where the readback conclusion is false is inhabited. -/
theorem readTraceId_discriminates (name : String) (s₁ s₂ : Span) (h : s₁.traceId ≠ s₂.traceId) :
    readTraceId (spanJson name s₁) ≠ readTraceId (spanJson name s₂) := by
  rw [readTraceId_spanJson, readTraceId_spanJson]
  exact fun hEq => h (map_nibHex_inj hEq)

/-! ## Non-vacuity: a concrete span renders to real OTLP/JSON hex

These `#guard`s evaluate the rendered char list (`hexOf x` has `.toList = x.map nibHex`,
`hexOf_toList`), so they are the exact exported hex without forcing kernel reduction through
the opaque UTF-8-backed `String`. -/

#guard hexOf [(0 : Nibble), 1] = "01"
#guard hexOf [(10 : Nibble), 15] = "af"
#guard (exampleSpan.traceId.map nibHex).length = 32
#guard (exampleSpan.spanId.map nibHex).length = 16
#guard (exampleSpan.spanId.map nibHex).getLast? = some '2'

#print axioms readTraceId_spanJson
#print axioms readTraceId_discriminates
#print axioms hexOf_inj
#print axioms hexOf_len
#print axioms span_traceId_hex_len
#print axioms span_spanId_hex_len
#print axioms exportSpans_count
#print axioms exportSpans_order

end O11y.OtelExport
