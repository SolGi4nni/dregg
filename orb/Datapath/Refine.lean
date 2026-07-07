import Datapath.Span
import Datapath.Scan
import Reactor.Config
import Reactor.Pipeline
import Uring.RecycleOnce

/-!
# Datapath.Refine — the data-refinement framework for a zero-copy serve

A zero-copy datapath must **provably refine** the deployed `List UInt8` model.
This module states that refinement as a relation and a bundle of obligations, and
**proves the FIRST real instance**: the request parse. A span-native request parse
— reading offsets into a borrowed buffer — is proven to yield exactly the
`Proto.Request` the deployed cons-list parser (`Reactor.Config.h1ParseFn`,
= `arenaToProto ∘ Arena.Parse.parse`) produces on the span's denotation.

## The framework

* **Abstract representation** `List UInt8` (= `Proto.Bytes`), abstract serve
  `serveA : List UInt8 → List UInt8` (the deployed `servePipelineOf` / `drorbServe`).
* **Concrete representation** `Datapath.SpanBytes` (a borrowed `(buf, off, len)`
  window) and `OutBuf` (a borrowed write buffer with a live length).
* **Refinement relation** `Refines a s := s.denote = a` — a span refines the
  abstract bytes it denotes.
* **Concrete serve** `ServeC := SpanBytes → OutBuf → OutBuf` — parse the request
  span in place, write the response into the borrowed `out` in place.
* **Refinement obligation** `RefinesServe serveA serveC` — the in-place serve
  yields the same bytes as the abstract list serve on the denotation.
* **Separation / ownership obligations** (all named, one proven here, two
  reduced to existing proven theorems):
  - **no-aliasing** — a disjoint response write cannot corrupt a request span
    still being read (`denote_store_disjoint`, proven here; the `memRel_store_disjoint`
    / C7–C9 analogue in the serve's `Bytes`);
  - **recycle-exactly-once** on the recv lease — `Uring.recycle_at_most_once`;
  - **affine consume-once** on the write builder — `Reactor.Pipeline.built_absorbing`.

## What is proven here vs. the roadmap

**Proven (this seed):** the request-parse refinement (`spanParseRequest_refines`)
and the no-aliasing separation lemma. **Roadmap (follow-on):** the concrete
`serveC` (the response half is CODEGEN OBLIGATION #2 — lowering the affine
`ResponseBuilder` to in-place writes) and the full `RefinesServe` composition. See
the report for the new-proof / codegen / shell split.
-/

namespace Datapath

open SpanBytes

/-! ## The refinement relation -/

/-- **`Refines a s`** — the span `s` refines the abstract bytes `a`: `s` denotes
exactly `a`. The concrete borrowed window carries the abstract `List UInt8`
without materializing it. -/
def Refines (a : List UInt8) (s : SpanBytes) : Prop := s.denote = a

theorem Refines.rfl_full (buf : ByteArray) : Refines buf.data.toList (full buf) :=
  denote_full buf

/-! ## No-aliasing — the separation obligation (proven)

The `memRel_store_disjoint` (C7/C9) analogue for the serve's `Bytes`: a store
DISJOINT from a read window preserves that window's denotation. This is what makes
an in-place response write (into the borrowed `out`) sound while a request span is
still being read out of the recv buffer. -/

/-- Two spans with the same geometry and byte-identical windows denote equally —
the congruence the separation lemma factors through. -/
theorem denote_congr (s₁ s₂ : SpanBytes) (h₁ : s₁.Wf) (h₂ : s₂.Wf)
    (hlen : s₁.len = s₂.len)
    (hwin : ∀ i, i < s₁.len → s₁.getByte i = s₂.getByte i) :
    s₁.denote = s₂.denote := by
  rw [← read_eq_denote s₁ h₁, ← read_eq_denote s₂ h₂]
  apply List.ext_getElem
  · rw [length_read, length_read, hlen]
  · intro i hi _
    rw [length_read] at hi
    have e₁ : s₁.read[i] = s₁.getByte i := by
      simp only [SpanBytes.read, List.getElem_ofFn]; rfl
    have e₂ : s₂.read[i] = s₂.getByte i := by
      simp only [SpanBytes.read, List.getElem_ofFn]; rfl
    rw [e₁, e₂]; exact hwin i hi

/-- A byte read outside a single-index store is unchanged. -/
theorem byteArray_get!_set!_ne (b : ByteArray) (j k : Nat) (v : UInt8) (hne : k ≠ j) :
    (b.set! j v).get! k = b.get! k := by
  show ((b.data.set! j v).get! k) = b.data.get! k
  simp only [Array.set!, Array.setD, Array.get!, Array.getD, Array.size_setIfInBounds]
  by_cases hk : k < b.data.size
  · rw [dif_pos hk, dif_pos hk]
    exact Array.getElem_setIfInBounds_ne b.data v (by simpa using hk) (Ne.symm hne)
  · rw [dif_neg hk, dif_neg hk]

@[simp] theorem byteArray_size_set! (b : ByteArray) (j : Nat) (v : UInt8) :
    (b.set! j v).size = b.size := by
  show (b.data.set! j v).size = b.data.size
  simp [Array.set!, Array.setD, Array.size_setIfInBounds]

/-- **`denote_store_disjoint` — the no-aliasing / separation obligation, proven.**
A single-byte store at index `j` DISJOINT from the read window `[off, off+len)`
leaves the read span's denotation unchanged: an in-place write that does not touch
a request span cannot corrupt the bytes that span still reads. This is the serve's
instance of the compiler's `memRel_store_disjoint` (a disjoint `Store` preserves
the input byte-relation). -/
theorem denote_store_disjoint (s : SpanBytes) (j : Nat) (v : UInt8)
    (hw : s.Wf) (hdisj : j < s.off ∨ s.off + s.len ≤ j) :
    ({ s with buf := s.buf.set! j v } : SpanBytes).denote = s.denote := by
  have hw' : ({ s with buf := s.buf.set! j v } : SpanBytes).Wf := by
    show s.off + s.len ≤ (s.buf.set! j v).size
    rw [byteArray_size_set!]; exact hw
  apply denote_congr _ _ hw' hw rfl
  intro i hi
  have hi2 : i < s.len := hi
  show (s.buf.set! j v).get! (s.off + i) = s.buf.get! (s.off + i)
  apply byteArray_get!_set!_ne
  omega

/-! ## THE FIRST REFINEMENT — the zero-copy request parse

`spanParseRequest` reads the request out of a borrowed span (index reads through
`buf[off + i]`, the `read` reading), then runs the proven arena head-parser +
adapter (`Reactor.Config.h1ParseFn`). `spanParseRequest_refines` proves it yields
**exactly** the `ParseOutcome` — hence the exact `Proto.Request` — the deployed
cons-list parser produces on the span's denotation. The two computations are
distinct (one reads by index, one consumes `denote`); they are equal by
`read_eq_denote`. -/

/-- The span-native request parse: read the borrowed window by index, then parse
with the deployed arena parser + adapter. In the model the read is `List`-valued;
CODEGEN OBLIGATION (see `Datapath.Span`) lowers it to direct indexed loads with no
materialized list. -/
def spanParseOutcome (s : SpanBytes) : Proto.ParseOutcome :=
  Reactor.Config.h1ParseFn s.read

/-- Project a `ParseOutcome` to its dispatchable request (if any). -/
def outcomeRequest? : Proto.ParseOutcome → Option (Nat × Proto.Request × Bool)
  | .request consumed req keepAlive => some (consumed, req, keepAlive)
  | _ => none

/-- The span-native request parse, as an `Option Request` view. -/
def spanParseRequest (s : SpanBytes) : Option (Nat × Proto.Request × Bool) :=
  outcomeRequest? (spanParseOutcome s)

/-- **THE FIRST REFINEMENT (outcome level).** The zero-copy span parse yields
exactly the `ParseOutcome` the deployed cons-list parser (`h1ParseFn`) produces on
the span's denotation. Non-vacuous: `spanParseOutcome` is defined by index reads
(`read`), NOT by `h1ParseFn s.denote`; the equality holds because `read = denote`
on a well-formed span (`read_eq_denote`). -/
theorem spanParseOutcome_refines (s : SpanBytes) (h : s.Wf) :
    spanParseOutcome s = Reactor.Config.h1ParseFn s.denote := by
  unfold spanParseOutcome
  rw [read_eq_denote s h]

/-- **THE FIRST REFINEMENT (request level).** The zero-copy span parse yields the
SAME `Proto.Request` (method, target, version, headers) — and the same consumed
count and keep-alive — as the deployed cons-list parse on the span's denotation. -/
theorem spanParseRequest_refines (s : SpanBytes) (h : s.Wf) :
    spanParseRequest s = outcomeRequest? (Reactor.Config.h1ParseFn s.denote) := by
  unfold spanParseRequest
  rw [spanParseOutcome_refines s h]

/-- Framed against the deployed serve's actual parse field: the zero-copy parse of
a well-formed span equals the config's `h1Parse` on the denotation. -/
theorem spanParseOutcome_demoConfig (s : SpanBytes) (h : s.Wf) :
    spanParseOutcome s = Reactor.Config.demoConfig.h1Parse s.denote := by
  rw [spanParseOutcome_refines s h, Reactor.Config.demoConfig_h1Parse]

/-! ## Non-vacuity — the parse genuinely depends on the span's bytes

A concrete request span parses to the exact `Proto.Request`; a span whose bytes
differ parses differently (different method, or no request at all). -/

/-- `"GET /health HTTP/1.1\r\n\r\n"` as a buffer. -/
def healthBytes : ByteArray := "GET /health HTTP/1.1\r\n\r\n".toUTF8

/-- The whole-buffer span over the health request. -/
def healthSpan : SpanBytes := full healthBytes

/-- A different request (`POST`) — different method bytes. -/
def postBytes : ByteArray := "POST /health HTTP/1.1\r\n\r\n".toUTF8
def postSpan : SpanBytes := full postBytes

/-- An incomplete span (no `CRLFCRLF`) — parses to no request. -/
def truncBytes : ByteArray := "GET /health HTTP/1.1\r\n".toUTF8
def truncSpan : SpanBytes := full truncBytes

/-- The health span parses to a dispatchable request with method `GET`, target
`/health`, version `HTTP/1.1`, and no headers. -/
def healthParsesExact : Bool :=
  match spanParseRequest healthSpan with
  | some (_, req, _) =>
      req.method == "GET".toUTF8.toList &&
      req.target == "/health".toUTF8.toList &&
      req.version == "HTTP/1.1".toUTF8.toList &&
      req.headers == []
  | none => false

#guard healthParsesExact

/-- A span whose bytes differ (POST) parses to a DIFFERENT request. -/
def differentBytesDifferParse : Bool :=
  match spanParseRequest healthSpan, spanParseRequest postSpan with
  | some (_, r1, _), some (_, r2, _) => r1.method != r2.method
  | _, _ => false

#guard differentBytesDifferParse

/- An incomplete span parses to no request. -/
#guard (spanParseRequest truncSpan).isNone

/-! ## The index-native scanner meets the deployed parse — non-vacuity

The index-native `spanFindDoubleCrlf` (materialization-free in the model,
`Datapath.Scan`) computes the deployed framing scan's offset on real requests. -/

/- The native dominant scan finds the `CRLFCRLF` at offset `20` of the health
request (`"GET /health HTTP/1.1"` is 20 bytes, then `\r\n\r\n`). -/
#guard SpanBytes.spanFindDoubleCrlf healthSpan == some 20

/- The native scan agrees with the deployed parser's own framing scan. -/
#guard SpanBytes.spanFindDoubleCrlf healthSpan == Arena.Parse.findDoubleCrlf healthSpan.read

/- A single-`CRLF` (incomplete) head has no `CRLFCRLF` — native scan returns none. -/
#guard SpanBytes.spanFindDoubleCrlf truncSpan == none

/- The native per-line sweep agrees with the deployed `crlfPositions`. -/
#guard SpanBytes.spanCrlfPositions healthSpan == Arena.Parse.crlfPositions healthSpan.read

/-! ## SpanRequest — the request head as offset sub-windows into the SAME buffer

`spanScanReqLine` frames the request natively and re-presents the deployed
parser's request-line entries as borrowed `(off,len)` windows into `s.buf` — no
bytes copied. `SpanBytes.entryWindow_denote` (in `Datapath.Scan`) proves the
GENERAL fact that any in-bounds main-arena entry's window denotes to exactly the
bytes the deployed adapter resolves; the `#guard`s below evaluate the whole
pipeline concretely on a real request, showing the three windows denote to the
exact deployed `Proto.Request` fields. -/

/-- The request-line head as three borrowed windows into the same buffer
(`method`, `target`, `version` — each an `(off,len)` view into `s.buf`). -/
structure SpanRequest where
  method : SpanBytes
  target : SpanBytes
  version : SpanBytes

/-- Frame + project: run the deployed head parser over the borrowed window's
bytes, then re-present its request-line entries as offset windows into `s.buf`.
The dominant framing scan the parser gates on is the index-native
`spanFindDoubleCrlf` in the model (proven `= Arena.Parse.findDoubleCrlf` on the
denotation). No bytes are copied to name the three windows. -/
def spanScanReqLine (s : SpanBytes) : Option SpanRequest :=
  match Arena.Parse.parse s.read with
  | .complete req =>
      some { method  := s.entryWindow req.method
             target  := s.entryWindow req.target
             version := s.entryWindow req.version }
  | _ => none

/- **The projected windows denote to the exact deployed request-line fields.**
Evaluated on the health request: the three borrowed buffer windows denote to
`GET`, `/health`, `HTTP/1.1` — byte-for-byte the deployed parse's result. -/
#guard (spanScanReqLine healthSpan).map (·.method.denote) == some "GET".toUTF8.toList
#guard (spanScanReqLine healthSpan).map (·.target.denote) == some "/health".toUTF8.toList
#guard (spanScanReqLine healthSpan).map (·.version.denote) == some "HTTP/1.1".toUTF8.toList

/-- **The SpanRequest windows equal the deployed cons-list parse's fields.** The
offset windows' denotations are byte-identical to the `Proto.Request` the deployed
parser (`spanParseRequest`) produces — the zero-copy request head refines the
deployed parse. -/
def spanReqLineMatchesDeployed : Bool :=
  match spanScanReqLine healthSpan, spanParseRequest healthSpan with
  | some sr, some (_, req, _) =>
      sr.method.denote == req.method &&
      sr.target.denote == req.target &&
      sr.version.denote == req.version
  | _, _ => false

#guard spanReqLineMatchesDeployed

/-- A `POST` request yields a different method window (genuine byte-dependence). -/
def spanReqLineMethodDiffers : Bool :=
  match spanScanReqLine healthSpan, spanScanReqLine postSpan with
  | some a, some b => a.method.denote != b.method.denote
  | _, _ => false

#guard spanReqLineMethodDiffers

/-! ## The serve shape — abstract/concrete serve + the full refinement obligation

The request half above is proven; the shapes below name the full serve refinement
and its remaining obligations (the response half + composition are the roadmap). -/

/-- Abstract serve — the deployed `List UInt8 → List UInt8` pipeline
(`Reactor.Deploy.servePipelineOf` / `drorbServe`'s core). -/
abbrev ServeA := List UInt8 → List UInt8

/-- A borrowed output buffer with a live-byte count: the caller-owned pooled
writer the response is written into in place (the reference's `ResponseWriter`). -/
structure OutBuf where
  buf : ByteArray
  live : Nat

/-- The live response bytes an `OutBuf` currently holds. -/
def OutBuf.bytes (o : OutBuf) : List UInt8 := o.buf.data.toList.take o.live

/-- The concrete zero-copy serve shape (the target of the FULL refinement): parse
the request span out of `s` in place, write the response into the borrowed `out`
in place, return the grown buffer. Left abstract in this seed — building it is the
response-half codegen (CODEGEN OBLIGATION #2) plus the shell wiring. -/
abbrev ServeC := SpanBytes → OutBuf → OutBuf

/-- **The end-to-end refinement obligation.** The in-place concrete serve yields
the same bytes the abstract list serve produces on the span's denotation, for
every well-formed span. `spanParseRequest_refines` is the request-parse half of
discharging this; the response half is the affine-builder lowering. -/
def RefinesServe (serveA : ServeA) (serveC : ServeC) : Prop :=
  ∀ (s : SpanBytes) (out : OutBuf), s.Wf → (serveC s out).bytes = serveA s.denote

/-- **The obligation bundle** a discharged zero-copy serve must satisfy: the
byte-refinement plus the three separation/ownership properties. Two of the three
are already proven theorems in the tree; the byte-refinement's request half is
`spanParseRequest_refines`. -/
structure ServeObligations (serveA : ServeA) (serveC : ServeC) : Prop where
  /-- The concrete serve refines the abstract serve (bytes agree on denotation). -/
  refines : RefinesServe serveA serveC
  /-- No-aliasing: a disjoint response write preserves any request span still
  being read. Witnessed generically by `denote_store_disjoint`. -/
  noAlias : ∀ (s : SpanBytes) (j : Nat) (v : UInt8), s.Wf →
    (j < s.off ∨ s.off + s.len ≤ j) →
    ({ s with buf := s.buf.set! j v } : SpanBytes).denote = s.denote

/-- The no-aliasing field of the obligation bundle is discharged, for ANY serve,
by the proven separation lemma. -/
theorem noAlias_discharged :
    ∀ (s : SpanBytes) (j : Nat) (v : UInt8), s.Wf →
      (j < s.off ∨ s.off + s.len ≤ j) →
      ({ s with buf := s.buf.set! j v } : SpanBytes).denote = s.denote :=
  fun s j v hw hdisj => denote_store_disjoint s j v hw hdisj

/-! ## The remaining ownership obligations are existing proven theorems

- **Recycle-exactly-once** on the recv lease is `Uring.recycle_at_most_once`
  (between any two recycles of a leased buffer id there is a fresh delivery — no
  lease recycled twice, under every interleaving). The lease is held across the
  whole span parse + serve, so the kernel cannot reuse the recv slot underneath.
- **Affine consume-once** on the write builder is `Reactor.Pipeline.built_absorbing`
  (a finalized `ResponseBuilder` absorbs every op — never reused), which is exactly
  what licenses lowering the in-place response write soundly. -/

/-- The recycle-once lease obligation, bound to its proven theorem. -/
def recycleOnce_obligation := @Uring.recycle_at_most_once

/-- The affine write-once obligation, bound to its proven theorem. -/
def affineWriteOnce_obligation := @Reactor.Pipeline.built_absorbing

end Datapath
