import Trace.W3C
import Trace.Correlation

/-!
# O11y.OtelTrace — verified OpenTelemetry span export over W3C Trace Context

An OpenTelemetry-style span carries a 128-bit trace id, a 64-bit span id, its
parent span id and trace flags — exactly the material of a W3C `traceparent`
value

```
version(00) '-' trace-id(32 hex) '-' parent-id(16 hex) '-' flags(2 hex)
```

plus a *correlation id* linking the span to the request that produced it. This
file sits on top of `Trace.W3C` (the token-level `traceparent` parser) and
`Trace.Correlation` (the corr-id assignment), and proves the export layer:

* `traceparent_roundtrip` — a well-formed `traceparent` (right field widths, a
  non-zero trace-id and parent-id) **renders** to a token stream that `parse`
  consumes back to exactly that structure with no leftover — the header is a
  genuine round-trip, not merely a projection.
* `otel_span_wellformed` — an OTel span emits a `traceparent` that round-trips
  (so the receiver recovers the span's trace-id, span-id and flags), and the
  span's correlation id survives injection into an upstream request and readback
  (`Trace.inject_faithful`). One theorem witnessing "carries trace-id / span-id /
  parent + corr-id, in W3C format".
* `otel_export_batches` — chunking a span queue into export batches of a bounded
  size **preserves order**: flattening the batches recovers the original span
  sequence. Companions bound each batch size and forbid empty batches.

The proofs are core-Lean only (no Mathlib); the axiom footprint on the headline
theorems is empty (checked with `#print axioms`).
-/

namespace O11y

open Trace

/-! ## Rendering a `traceparent` to its token stream

The inverse of `Trace.parse`: lay each fixed-width nibble field down as `nib`
tokens, separated by `dash`. The nesting is right-associated (`a ++ (dash :: b)`)
so it matches the shape `parse` consumes field by field. -/

/-- Render a parsed `traceparent` to the token stream `parse` accepts:
`version - traceId - parentId - flags`. -/
def renderToks (tp : TraceParent) : List Tok :=
  tp.version.map Tok.nib ++ Tok.dash ::
    (tp.traceId.map Tok.nib ++ Tok.dash ::
      (tp.parentId.map Tok.nib ++ Tok.dash ::
        tp.flags.map Tok.nib))

/-- `takeNibs` on a rendered nibble run: it consumes exactly the run and returns
the untouched tail. This is the field-level inverse used by `traceparent_roundtrip`. -/
theorem takeNibs_map (xs : List Nibble) (rest : List Tok) :
    takeNibs xs.length (xs.map Tok.nib ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.length_cons, List.map_cons, List.cons_append, takeNibs, ih]

/-! ## Theorem A — the W3C `traceparent` header parses+renders (round-trip)

`renderToks` followed by `parse` is the identity on any well-formed structure:
the field widths (`2 / 32 / 16 / 2` nibbles) let each `takeNibs` succeed, and the
non-zero trace-id / parent-id clear the two spec rejections. -/

/-- **traceparent_roundtrip.** A well-formed `traceparent` renders to a token
stream that `parse` reads back to exactly that structure, consuming all of it. -/
theorem traceparent_roundtrip (tp : TraceParent)
    (hv : tp.version.length = 2) (ht : tp.traceId.length = 32)
    (hp : tp.parentId.length = 16) (hf : tp.flags.length = 2)
    (htz : allZero tp.traceId = false) (hpz : allZero tp.parentId = false) :
    parse (renderToks tp) = .ok (tp, []) := by
  have k1 := takeNibs_map tp.version
      (Tok.dash :: (tp.traceId.map Tok.nib ++ Tok.dash ::
        (tp.parentId.map Tok.nib ++ Tok.dash :: tp.flags.map Tok.nib)))
  have k2 := takeNibs_map tp.traceId
      (Tok.dash :: (tp.parentId.map Tok.nib ++ Tok.dash :: tp.flags.map Tok.nib))
  have k3 := takeNibs_map tp.parentId (Tok.dash :: tp.flags.map Tok.nib)
  have k4 := takeNibs_map tp.flags []
  rw [hv] at k1; rw [ht] at k2; rw [hp] at k3; rw [hf, List.append_nil] at k4
  simp only [parse, renderToks, k1, expectDash, k2, k3, k4, htz, hpz]

/-! ## The OTel span model

A span bundles the W3C fields with the request's correlation id. Its *emitted*
`traceparent` (the one a downstream hop receives) uses the current spec version
`00`, keeps the trace-id, installs this span's id as the parent-id, and carries
the flags — matching the reference `format_traceparent(trace_id, span_id, flags)`. -/

/-- An OpenTelemetry span: a 128-bit trace id (32 nibbles), a 64-bit span id (16
nibbles), the parent span id, trace flags (2 nibbles), and the correlation id
linking it to the originating request. -/
structure Span where
  /-- 128-bit trace id — 32 hex nibbles. -/
  traceId : List Nibble
  /-- 64-bit span id (this span) — 16 hex nibbles. -/
  spanId : List Nibble
  /-- Parent span id (all-zero at a trace root). -/
  parentId : List Nibble
  /-- Trace flags — 2 hex nibbles (bit 0 = sampled). -/
  flags : List Nibble
  /-- Correlation id linking the span to its request. -/
  corr : CorrId

/-- The `traceparent` this span emits to a downstream hop: version `00`, the
trace-id, this span's id as the parent-id, and the flags. -/
def Span.traceparent (s : Span) : TraceParent :=
  { version := [0, 0], traceId := s.traceId, parentId := s.spanId, flags := s.flags }

/-- A span is well-formed when its ids have the mandated widths and its trace-id
and span-id are non-zero (both rejections the spec — and `parse` — enforce). -/
def Span.Wf (s : Span) : Prop :=
  s.traceId.length = 32 ∧ s.spanId.length = 16 ∧ s.flags.length = 2
    ∧ allZero s.traceId = false ∧ allZero s.spanId = false

/-- **otel_span_wellformed.** A well-formed span emits a `traceparent` that
round-trips — the receiver recovers the span's trace-id, span-id (as parent-id)
and flags — and the span's correlation id survives injection into an upstream
request and readback. This is the "carries trace-id / span-id / parent + corr-id,
in W3C format" guarantee. -/
theorem otel_span_wellformed (s : Span) (h : s.Wf) :
    parse (renderToks s.traceparent) = .ok (s.traceparent, [])
      ∧ s.traceparent.traceId = s.traceId
      ∧ s.traceparent.parentId = s.spanId
      ∧ s.traceparent.flags = s.flags
      ∧ upstreamCorr (inject ⟨s.corr⟩) = some s.corr := by
  obtain ⟨ht, hs, hf, htz, hsz⟩ := h
  refine ⟨?_, rfl, rfl, rfl, inject_faithful _⟩
  exact traceparent_roundtrip s.traceparent rfl ht hs hf htz hsz

/-! ## Batch export

The OTLP batch-span-processor accumulates spans and flushes them in bounded
chunks. `batches cap` splits a span queue into consecutive chunks of at most
`cap + 1` spans (so every chunk is non-empty). Order preservation is the safety
property: flattening the batches recovers the queue. -/

/-- Split a list into consecutive chunks of at most `cap + 1` elements. Each
chunk is non-empty; the chunking is order-preserving (`batches_flatten`). -/
def batches (cap : Nat) : List α → List (List α)
  | [] => []
  | x :: xs =>
      (x :: xs).take (cap + 1) :: batches cap ((x :: xs).drop (cap + 1))
  termination_by l => l.length
  decreasing_by simp_wf; omega

/-- **otel_export_batches.** Batch export preserves order: flattening the export
batches recovers the original span queue exactly (no span dropped, duplicated, or
reordered). -/
theorem otel_export_batches (cap : Nat) (l : List α) : (batches cap l).flatten = l := by
  induction l using batches.induct (cap := cap) with
  | case1 => simp [batches]
  | case2 x xs ih =>
      unfold batches
      rw [List.flatten_cons, ih, List.take_append_drop]

/-- Every export batch fits the cap: no batch exceeds `cap + 1` spans. -/
theorem batches_size_le (cap : Nat) (l : List α) :
    ∀ b ∈ batches cap l, b.length ≤ cap + 1 := by
  induction l using batches.induct (cap := cap) with
  | case1 => intro b hb; simp [batches] at hb
  | case2 x xs ih =>
      intro b hb
      rw [batches] at hb
      rcases List.mem_cons.mp hb with h | h
      · subst h; rw [List.length_take]; exact Nat.min_le_left _ _
      · exact ih b h

/-- No empty export batch: every batch carries at least one span. -/
theorem batches_nonempty (cap : Nat) (l : List α) :
    ∀ b ∈ batches cap l, b ≠ [] := by
  induction l using batches.induct (cap := cap) with
  | case1 => intro b hb; simp [batches] at hb
  | case2 x xs ih =>
      intro b hb
      rw [batches] at hb
      rcases List.mem_cons.mp hb with h | h
      · subst h; simp [List.take]
      · exact ih b h

/-! ## Non-vacuous concrete instances

A concrete sampled span with a real 128-bit trace-id and 64-bit span-id emits a
`traceparent` that round-trips, and a nine-span queue batches into chunks of ≤ 4
whose flattening recovers the queue. The `#guard`s check the exact structure. -/

/-- A concrete sampled span (trace-id `0…01`, span-id `0…02`, flags `01`). -/
def exampleSpan : Span :=
  { traceId := (List.replicate 31 (0 : Nibble)) ++ [1]
    spanId := (List.replicate 15 (0 : Nibble)) ++ [2]
    parentId := List.replicate 16 (0 : Nibble)
    flags := [0, 1]
    corr := [7, 7, 7] }

theorem exampleSpan_wf : exampleSpan.Wf := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;> decide

-- The example span emits a round-tripping W3C traceparent (instance of the theorem).
example : parse (renderToks exampleSpan.traceparent) = .ok (exampleSpan.traceparent, []) :=
  (otel_span_wellformed exampleSpan exampleSpan_wf).1

-- Nine spans, cap 3 → chunks of 4,4,1; flattening recovers the queue.
#guard batches 3 [0,1,2,3,4,5,6,7,8] == [[0,1,2,3], [4,5,6,7], [8]]
#guard (batches 3 [0,1,2,3,4,5,6,7,8]).flatten == [0,1,2,3,4,5,6,7,8]

-- A single batch never exceeds the cap and is never empty.
#guard (batches 3 [0,1,2,3,4,5,6,7,8]).all (fun b => b.length ≤ 4 && !b.isEmpty)

def version : String := "otel-1.0"

end O11y
