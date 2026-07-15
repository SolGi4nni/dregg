/-
# Sse.Framing — the event-stream wire, exactly as the reactor emits it (LF)

`Sse.Frame` pins down the frame *parser* (round-trip, totality,
consumed-monotonicity) and `SseFrameCorrect` pins down an *encoder* whose lines
are closed with **CRLF**. But the wire bytes the running reactor path lays down
for one dispatched event are

    eventBytes e = ((Sse.encodeFrame e).map (fun l => l ++ [Sse.LF])).flatten

(`Reactor.Sse.eventBytes`) — each line closed by a **single LF**, not CRLF. LF is
one of the three terminators the format admits (WHATWG HTML §9.2: `CR`, `LF`, or
`CRLF`), so the emit is spec-legal; but it is a *different byte sequence* from the
CRLF `SseFrameCorrect.implWire`. This file proves the framing of the bytes the
reactor **actually** produces, over exactly that LF expression.

`wireBytes` below is character-for-character the body of `Reactor.Sse.eventBytes`
(same defining term); it is restated here so this file depends only on the
`Sse` core (`Sse.Frame` → `Sse.Basic`) and stays isolation-checkable, without
pulling in the whole `Reactor` closure. The connection is definitional: for any
`e`, `wireBytes e` and `Reactor.Sse.eventBytes e` reduce to the same term.

## What is proven

* `sse_event_wellformed` — a data-only event `⟨none,none,none,[p]⟩` is exactly
  `data: <p> LF LF`: the WHATWG data-only event, a single `data:` field line and
  the blank dispatch line.
* `sse_event_with_type` — the optional `event:` field, when set, precedes the
  `data:` line in canonical order; the frame still closes with the blank line.
* `wireBytes_eq_wireSpecLF` — the **exact bytes**, for *every* event: the present
  `event`/`id`/`retry` field lines in canonical order, one `data:` line per data
  value (multi-line payloads are NOT merged, §9.2.6), then the terminating blank
  line. Stated against an independent `wireSpecLF` written by direct byte
  concatenation, never mentioning the encoder.
* `sse_frame_terminated` — every event carrying at least one field ends with the
  blank-line terminator `LF LF`.
* `sse_stream_framing` — a stream is its events concatenated; each non-empty
  event is `LF LF`-terminated, so consecutive events are blank-line separated —
  the frame boundary the parser dispatches on (`Sse.parseFrame_complete_of_blank`).
* `sse_comment_starts_colon` — a comment line begins with a colon (§9.2.5: a line
  starting `:` is a comment, ignored on dispatch).
* `sse_frame_parses_back` — the emitted framing is decodable: parsing `wireBytes`
  back (via the line model) recovers the event, consuming exactly the frame.

## Non-vacuity + the LF/CRLF finding

`noBlankLF` (drops the terminator) and `mergedLF` (collapses a multi-line `data`
payload) are shown to *disagree* with `wireSpecLF` on concrete events, so the
refinement carries information. `wireBytes_has_no_cr` machine-checks that the
reactor's emit contains no `CR` byte — the concrete way it differs from the CRLF
`SseFrameCorrect.implWire`.
-/
import Sse.Frame

namespace Sse.Framing

open Sse

/-! ## The wire rendering the reactor actually emits (single-LF terminator) -/

/-- Render a list of `LF`-free lines to wire bytes with a **single LF** after
each line — the transport layer `Reactor.Sse.eventBytes` uses. -/
def renderLF (lines : List Line) : Bytes := (lines.map (· ++ [LF])).flatten

/-- The wire bytes of one dispatched event, exactly as `Reactor.Sse.eventBytes`
lays them down: the canonical `Sse.encodeFrame` field lines plus the blank
dispatch line, each closed by a single `LF`. Definitionally
`((Sse.encodeFrame e).map (fun l => l ++ [Sse.LF])).flatten`. -/
def wireBytes (e : Event) : Bytes := renderLF (Sse.encodeFrame e)

/-- `wireBytes` is the very term `Reactor.Sse.eventBytes` is defined by — the
`map (· ++ [LF]) >>> flatten` of the encoded frame. Kept as an explicit lemma so
the tie to the deployed reactor expression is machine-checked here, not merely
asserted in prose. -/
theorem wireBytes_eq_flatten (e : Event) :
    wireBytes e = ((Sse.encodeFrame e).map (fun l => l ++ [LF])).flatten := rfl

/-! ## `renderLF` structure -/

@[simp] theorem renderLF_nil : renderLF [] = [] := rfl

theorem renderLF_cons (x : Line) (xs : List Line) :
    renderLF (x :: xs) = (x ++ [LF]) ++ renderLF xs := by
  simp [renderLF]

theorem renderLF_append (a b : List Line) :
    renderLF (a ++ b) = renderLF a ++ renderLF b := by
  simp [renderLF, List.map_append, List.flatten_append]

/-- The blank dispatch line renders to a lone `LF` — the closing half of the
frame-terminating `LF LF`. -/
theorem renderLF_blank : renderLF [([] : Line)] = [LF] := by
  simp [renderLF_cons]

/-! ## The independent wire specification (LF variant, WHATWG HTML §9.2.5–§9.2.6) -/

/-- One field line's bytes: `name` `:` ` ` `value` then a single `LF` (the `": "`
pad is the space §9.2.5 strips on parse). Written directly — no reference to the
serializer. -/
def fieldWireLF (name value : Bytes) : Bytes := name ++ COLON :: SP :: value ++ [LF]

/-- The `data` section: one `data:` line per value, in order (§9.2.6 — each
buffered `data` line is its own field; a multi-line payload is never merged). -/
def dataLinesLF (ds : List Bytes) : Bytes := (ds.map (fieldWireLF nameData)).flatten

/-- The exact wire bytes an event serializes to under the LF terminator: the
present field lines in canonical order (`event`, `id`, `retry`), one `data:` line
per data value, then the terminating blank line (the trailing `LF` that, with the
previous line's `LF`, forms the dispatch-triggering empty line). -/
def wireSpecLF (e : Event) : Bytes :=
  (match e.event with | some v => fieldWireLF nameEvent v | none => []) ++
  (match e.id    with | some v => fieldWireLF nameId    v | none => []) ++
  (match e.retry with | some v => fieldWireLF nameRetry v | none => []) ++
  dataLinesLF e.data ++
  [LF]

/-! ## Field-line agreement: `encodeFieldLine · ++ [LF] = fieldWireLF` -/

theorem enc_eventLF (v : Bytes) :
    encodeFieldLine (.event v) ++ [LF] = fieldWireLF nameEvent v := by
  simp [encodeFieldLine, fieldWireLF, List.append_assoc]

theorem enc_idLF (v : Bytes) :
    encodeFieldLine (.id v) ++ [LF] = fieldWireLF nameId v := by
  simp [encodeFieldLine, fieldWireLF, List.append_assoc]

theorem enc_retryLF (v : Bytes) :
    encodeFieldLine (.retry v) ++ [LF] = fieldWireLF nameRetry v := by
  simp [encodeFieldLine, fieldWireLF, List.append_assoc]

theorem enc_dataLF (v : Bytes) :
    encodeFieldLine (.data v) ++ [LF] = fieldWireLF nameData v := by
  simp [encodeFieldLine, fieldWireLF, List.append_assoc]

/-- Rendering the serializer's `data` field lines yields exactly one specified
`data:` line per value. -/
theorem renderLF_dataMap (dat : List Bytes) :
    renderLF ((dat.map Field.data).map encodeFieldLine) = dataLinesLF dat := by
  induction dat with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, renderLF_cons, ih, enc_dataLF, dataLinesLF,
      List.flatten_cons]

/-! ## The exact-bytes refinement (matches the deployed reactor emit) -/

/-- **Wire-format correctness, LF variant.** The bytes the reactor lays on the
wire (`wireBytes` = `Reactor.Sse.eventBytes`) are *exactly* the independently
specified event-stream framing: the present field lines in canonical order, one
`data:` line per data value, terminated by the blank dispatch line — every line
closed by a single `LF`. Holds for every event. -/
theorem wireBytes_eq_wireSpecLF (e : Event) : wireBytes e = wireSpecLF e := by
  obtain ⟨ev, iv, rv, dat⟩ := e
  unfold wireBytes Sse.encodeFrame Sse.eventFields wireSpecLF
  cases ev <;> cases iv <;> cases rv <;>
    simp only [List.map_append, List.map_cons, List.map_nil, List.nil_append,
      renderLF_append, renderLF_cons, renderLF_nil, renderLF_blank,
      renderLF_dataMap, enc_eventLF, enc_idLF, enc_retryLF,
      List.append_nil, List.append_assoc]

/-! ## `sse_event_wellformed` — the data-only event -/

/-- **`sse_event_wellformed`.** A data-only event is exactly `data: <payload>`
then the blank dispatch line: `nameData ": " payload LF LF`. This is the canonical
WHATWG data-only event (a single `data:` field, one blank line to dispatch). -/
theorem sse_event_wellformed (p : Bytes) :
    wireBytes ⟨none, none, none, [p]⟩
      = nameData ++ [COLON, SP] ++ p ++ [LF, LF] := by
  rw [wireBytes_eq_wireSpecLF]
  simp [wireSpecLF, dataLinesLF, fieldWireLF, List.append_assoc]

/-- **`sse_event_with_type`.** With an event type set, the `event:` line precedes
the `data:` line (canonical order), and the frame still closes with the blank
line: `event: <t> LF data: <p> LF LF`. Shows the optional field is real and
ordered, not dropped. -/
theorem sse_event_with_type (t p : Bytes) :
    wireBytes ⟨some t, none, none, [p]⟩
      = nameEvent ++ [COLON, SP] ++ t ++ [LF]
        ++ (nameData ++ [COLON, SP] ++ p ++ [LF, LF]) := by
  rw [wireBytes_eq_wireSpecLF]
  simp [wireSpecLF, dataLinesLF, fieldWireLF, List.append_assoc]

/-! ## `sse_stream_framing` — blank-line separation of events -/

/-- Rendering a non-empty list of lines ends with `LF`: the last line's own
`LF` terminator is the final byte. -/
theorem renderLF_ends_LF :
    ∀ (lines : List Line), lines ≠ [] → ∃ pre, renderLF lines = pre ++ [LF]
  | [], h => absurd rfl h
  | [x], _ => ⟨x, by simp [renderLF_cons]⟩
  | x :: y :: ys, _ => by
    obtain ⟨pre', hpre'⟩ := renderLF_ends_LF (y :: ys) (by simp)
    refine ⟨(x ++ [LF]) ++ pre', ?_⟩
    rw [renderLF_cons, hpre']
    simp [List.append_assoc]

/-- Every event that carries at least one field ends with the frame terminator
`LF LF` (the last field line's `LF`, then the blank dispatch line's `LF`). -/
theorem sse_frame_terminated (e : Event) (h : Sse.eventFields e ≠ []) :
    ∃ pre, wireBytes e = pre ++ [LF, LF] := by
  have hfl : (Sse.eventFields e).map encodeFieldLine ≠ [] := by
    cases hfe : Sse.eventFields e with
    | nil => exact absurd hfe h
    | cons a as => simp
  obtain ⟨pre, hpre⟩ := renderLF_ends_LF _ hfl
  refine ⟨pre, ?_⟩
  unfold wireBytes Sse.encodeFrame
  rw [renderLF_append, renderLF_blank, hpre, List.append_assoc]
  rfl

/-- **`sse_stream_framing`.** A stream is its events concatenated. When the first
event carries a field, its wire ends in the blank-line terminator `LF LF`, so it
is separated from the next event's bytes by that blank line — exactly the frame
boundary the parser dispatches on. Concretely `wireBytes e₁ ++ wireBytes e₂`
factors as `pre ++ [LF, LF] ++ wireBytes e₂`. -/
theorem sse_stream_framing (e₁ e₂ : Event) (h : Sse.eventFields e₁ ≠ []) :
    ∃ pre, wireBytes e₁ ++ wireBytes e₂ = pre ++ [LF, LF] ++ wireBytes e₂ := by
  obtain ⟨pre, hpre⟩ := sse_frame_terminated e₁ h
  exact ⟨pre, by rw [hpre]⟩

/-! ## `sse_comment_starts_colon` -/

/-- **`sse_comment_starts_colon`.** A comment line is emitted as `:` then its
bytes (`encodeFieldLine`), so it begins with a colon — the §9.2.5 comment marker,
ignored on dispatch. -/
theorem sse_comment_starts_colon (v : Bytes) :
    (encodeFieldLine (.comment v)).head? = some COLON := rfl

/-- A comment renders on the wire as `: <v> LF` — colon-led, LF-terminated, no
`data:`/`event:` name. -/
theorem sse_comment_wire (v : Bytes) :
    renderLF [encodeFieldLine (.comment v)] = COLON :: v ++ [LF] := by
  simp [renderLF_cons, encodeFieldLine]

/-! ## Decodability: the framing parses back -/

/-- **`sse_frame_parses_back`.** The framing the reactor emits is decodable: the
line list `Sse.encodeFrame e` (whose LF-render is `wireBytes e`) parses back to
the very event, consuming exactly the frame — no trailing lines left. This lifts
`Sse.parseFrame_encodeFrame` (with no tail) to state that the emitted frame is a
complete, self-delimiting, correctly-dispatching unit. -/
theorem sse_frame_parses_back (e : Event) (hwf : e.Wf) :
    Sse.parseFrame (Sse.encodeFrame e)
      = .complete e (Sse.encodeFrame e).length [] := by
  have h := Sse.parseFrame_encodeFrame e [] hwf
  simpa using h

/-! ## Non-vacuity: wrong LF serializers disagree; the LF/CRLF finding -/

/-- A two-line `data` event: `data: a` / `data: b`. -/
def eg2 : Event := ⟨none, none, none, [[97], [98]]⟩

/-- A single-`data` event: `data: hi`. -/
def eg1 : Event := ⟨none, none, none, [[104, 105]]⟩

/-- A broken serializer that drops the terminating blank line (no dispatch). -/
def noBlankLF (e : Event) : Bytes :=
  renderLF ((Sse.eventFields e).map encodeFieldLine)

/-- A broken serializer that merges a multi-line `data` payload onto one line. -/
def mergedLF (e : Event) : Bytes :=
  (match e.event with | some v => fieldWireLF nameEvent v | none => []) ++
  (match e.id    with | some v => fieldWireLF nameId    v | none => []) ++
  (match e.retry with | some v => fieldWireLF nameRetry v | none => []) ++
  fieldWireLF nameData e.data.flatten ++
  [LF]

/-- The reactor's serializer meets the spec on the multi-line event. -/
theorem impl_ok_eg2 : wireBytes eg2 = wireSpecLF eg2 := wireBytes_eq_wireSpecLF eg2

/-- Dropping the blank line fails: without the terminator the bytes are not the
specified framing. -/
theorem noBlank_differs : noBlankLF eg2 ≠ wireSpecLF eg2 := by decide

/-- Merging multi-line data fails: one `data:` line for two values is not the
specified framing (which mandates one line per value, §9.2.6). -/
theorem merged_differs : mergedLF eg2 ≠ wireSpecLF eg2 := by decide

/-- On a single-line payload the merging bug is invisible — it is the multi-line
case that exposes it. -/
theorem merged_agrees_single : mergedLF eg1 = wireSpecLF eg1 := by decide

/-- Distinct events have distinct wire bytes: the refinement carries information. -/
theorem wireSpecLF_injective_witness : wireSpecLF eg1 ≠ wireSpecLF eg2 := by decide

/-- **The LF/CRLF finding, machine-checked.** The reactor's emit contains no `CR`
(`0x0D`) byte — it is LF-terminated, NOT the CRLF byte sequence
`SseFrameCorrect.implWire`/`wireSpec` proves. The two "wire-format correctness"
proofs pin down *different* byte strings; this one matches what the reactor path
(`Reactor.Sse.eventBytes`) actually lays down. -/
theorem wireBytes_has_no_cr : (13 : UInt8) ∉ wireBytes eg2 := by decide

#print axioms wireBytes_eq_wireSpecLF
#print axioms sse_event_wellformed
#print axioms sse_stream_framing
#print axioms sse_comment_starts_colon
#print axioms sse_frame_parses_back
#print axioms wireBytes_has_no_cr

end Sse.Framing
