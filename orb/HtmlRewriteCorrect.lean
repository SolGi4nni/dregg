import Reactor.Stage.HtmlRewrite

/-!
# HtmlRewriteCorrect — correctness of the streaming HTML markup-strip rewrite

This upgrades the streaming HTML rewriter from *safety* to *correctness by proof*.

## What the deployed rewriter does

`Reactor.Stage.HtmlRewrite.htmlrewriteStage` transforms a response body by running
the per-byte streaming tokenizer `HtmlRewrite.feed` (folded by `feedBytes`) and
rendering the result with markup dropped (`rewriteState`), i.e. it applies
`rewriteBytes` to the body (`htmlrewriteStage_body`). The transform keeps the text
runs and drops every `<…>` tag span; a trailing unclosed `<…` (no closing `>`) is
dropped. This is a *tag-stripping* rewrite.

## The independent specification (from the standard)

The reference is the WHATWG HTML Standard, §13.2.5 *Tokenization*. In the **data
state** (§13.2.5.1) a `<` (U+003C LESS-THAN SIGN) switches to the **tag open
state** (§13.2.5.6); markup runs until the `>` (U+003E GREATER-THAN SIGN) of the
end-tag/tag close, at which point the tokenizer returns to the data state. A
markup *stripper* emits the character data and discards the tag tokens.

`stripData` / `stripInTag` below is a direct, first-principles transcription of
that two-state machine as a function of the *whole* concatenated input — it never
mentions chunks, folds, or the tokenizer's internal `TState`. It is independent of
the implementation: it is a plain structural recursion over the byte list.

Deviation from the standard, reported as a FINDING (see the module return): the
deployed `feed` treats **every** `<` as the start of a tag, whereas §13.2.5.6
tag-open-state "anything else" re-emits `<` as a character when it is not followed
by an ASCII alpha / `!` / `/` / `?`. So input like `5 < 10 > 3` is over-stripped
to `5  3` by the deployed rewriter. For a security-oriented stripper this is
fail-safe (it over-strips rather than under-strips), but it is a genuine
divergence from HTML parsing. The spec here transcribes the deployed *simplified*
tag recognition so the refinement is exact; the divergence is a policy fact about
the deployed tokenizer, not a gap in this proof.

## The theorems

* `rewriteBytes_eq_spec`         — the DEPLOYED whole-input rewrite equals the
  independent spec on every input (the exact-substitution property).
* `streamRewrite_eq_spec`        — the DEPLOYED streaming fold over ANY list of
  chunks equals the spec applied to the concatenation: streaming decode of the
  body, split however the transport happens to deliver it, is a function of the
  concatenated bytes alone.
* `stream_chunk_independent`     — two chunkings with the same concatenation yield
  the same output: the chunk boundaries are invisible.
* `htmlrewriteStage_body_spec`   — the BUILT pipeline response body (what the
  serializer renders) is exactly `stripData` of the tail body — binding the spec
  to the real deployed stage, not a wrapper.
* Non-vacuity: `split_inside_tag_ok` (a tag split across a chunk boundary strips
  correctly) and `naive_wrong_on_split` (a boundary-dependent per-chunk stripper
  gives a DIFFERENT, wrong answer on that same split — so the theorem is not
  vacuous and a chunk-boundary bug would fail it).
-/

namespace HtmlRewriteCorrect

open HtmlRewrite
  (Byte lt gt Token Mode TState init feed feedBytes tokenize flush feedBytes_append)
open Reactor.Stage.HtmlRewrite
  (renderTok rewriteState rewriteBytes htmlrewriteStage htmlrewriteStage_body)
open Reactor.Pipeline (Stage Ctx runPipeline)
open Reactor (Response)
open Proto (Bytes)

/-! ## The independent whole-input specification (WHATWG §13.2.5) -/

/-- The two-state markup stripper as a single structural recursion over the whole
input (`inTag` is the WHATWG data/tag-open state bit). In the data state
(`inTag = false`) characters are copied and a `<` enters the tag state (the `<` is
dropped). In the tag state a `>` returns to the data state (the `>` is dropped);
all other bytes — and an unclosed tag at end-of-input — are dropped. No chunk or
fold notion appears: it is a function of the concatenated input alone. -/
def strip (inTag : Bool) : List Byte → List Byte
  | [] => []
  | b :: rest =>
    if inTag then
      if b = gt then strip false rest else strip true rest
    else
      if b = lt then strip true rest else b :: strip false rest

/-- The whole-input spec: strip from the data state. -/
def stripData (bs : List Byte) : List Byte := strip false bs

/-- The spec continued from inside a tag. -/
def stripInTag (bs : List Byte) : List Byte := strip true bs

/-! ## The refinement: deployed streaming engine = spec -/

/-- One step of the streaming fold. -/
theorem feedBytes_cons (s : TState) (b : Byte) (rest : List Byte) :
    feedBytes s (b :: rest) = feedBytes (feed s b) rest := by
  simp [feedBytes, List.foldl_cons]

/-- **Core refinement lemma.** From any tokenizer state, rendering the streamed
result appends the spec's strip of the fed bytes to the already-emitted output —
where "already emitted" is exactly `rewriteState s`. Proved by induction on the
fed bytes, simultaneously for both tokenizer modes (mutual with the spec's two
states). This is the fold-vs-recursion equivalence that makes streaming = whole. -/
theorem rewriteState_feedBytes (bs : List Byte) : ∀ s : TState,
    (s.mode = Mode.text → rewriteState (feedBytes s bs) = rewriteState s ++ stripData bs) ∧
    (s.mode = Mode.tag  → rewriteState (feedBytes s bs) = rewriteState s ++ stripInTag bs) := by
  induction bs with
  | nil =>
    intro s
    refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
      simp [feedBytes, stripData, stripInTag, strip]
  | cons b rest ih =>
    intro s
    refine ⟨fun hmode => ?_, fun hmode => ?_⟩
    · -- s.mode = text
      rw [feedBytes_cons]
      by_cases hb : b = lt
      · -- `<`: flush text, enter tag mode. Emitted output is unchanged.
        subst hb
        have hns : (feed s lt).mode = Mode.tag := by simp [feed, hmode]
        have hstep := (ih (feed s lt)).2 hns
        have hstate : rewriteState (feed s lt) = rewriteState s := by
          simp only [feed, hmode, flush, rewriteState, renderTok]
          by_cases hc : s.cur = [] <;>
            simp [hc, List.flatMap_append, renderTok]
        rw [hstep, hstate]
        simp [stripData, stripInTag, strip]
      · -- ordinary text byte: extends the current run.
        have hns : (feed s b).mode = Mode.text := by simp [feed, hmode, hb]
        have hstep := (ih (feed s b)).1 hns
        have hstate : rewriteState (feed s b) = rewriteState s ++ [b] := by
          simp only [feed, hmode, hb, if_neg hb, rewriteState]
          simp [List.append_assoc]
        rw [hstep, hstate]
        simp [stripData, stripInTag, strip, hb, List.append_assoc]
    · -- s.mode = tag
      rw [feedBytes_cons]
      by_cases hb : b = gt
      · -- `>`: close the tag (rendered to nothing), return to text mode.
        subst hb
        have hns : (feed s gt).mode = Mode.text := by simp [feed, hmode]
        have hstep := (ih (feed s gt)).1 hns
        have hstate : rewriteState (feed s gt) = rewriteState s := by
          simp [feed, hmode, rewriteState, renderTok, List.flatMap_append]
        rw [hstep, hstate]
        simp [stripData, stripInTag, strip]
      · -- ordinary tag byte: extends the (to-be-dropped) tag buffer.
        have hns : (feed s b).mode = Mode.tag := by simp [feed, hmode, hb]
        have hstep := (ih (feed s b)).2 hns
        have hstate : rewriteState (feed s b) = rewriteState s := by
          simp [feed, hmode, hb, rewriteState]
        rw [hstep, hstate]
        simp [stripData, stripInTag, strip, hb]

/-- **Exact substitution.** The DEPLOYED whole-input rewrite `rewriteBytes` equals
the independent spec `stripData` on every input. -/
theorem rewriteBytes_eq_spec (bs : List Byte) : rewriteBytes bs = stripData bs := by
  have h := (rewriteState_feedBytes bs init).1 rfl
  simpa [rewriteBytes, tokenize, rewriteState, init, renderTok] using h

/-! ## Chunk-independence of the deployed streaming rewrite -/

/-- The DEPLOYED streaming rewrite: fold the real per-byte tokenizer over an
arbitrary list of chunks (the body as the transport delivers it), then render. -/
def streamRewrite (chunks : List Bytes) : Bytes :=
  rewriteState (chunks.foldl feedBytes init)

/-- Folding the streaming engine over chunks equals feeding the concatenation:
the deployed fold is chunk-associative (`feedBytes_append`). -/
theorem foldl_feedBytes (chunks : List Bytes) (s : TState) :
    chunks.foldl feedBytes s = feedBytes s chunks.flatten := by
  induction chunks generalizing s with
  | nil => simp [feedBytes]
  | cons c cs ih =>
    simp [List.foldl_cons, List.flatten_cons, ih, feedBytes_append]

/-- **Chunk-independence (streaming = whole).** The DEPLOYED streaming rewrite over
ANY chunking equals the spec applied to the concatenated input — the output is a
function of the concatenation, not the chunk boundaries. -/
theorem streamRewrite_eq_spec (chunks : List Bytes) :
    streamRewrite chunks = stripData chunks.flatten := by
  unfold streamRewrite
  rw [foldl_feedBytes]
  have h := (rewriteState_feedBytes chunks.flatten init).1 rfl
  simpa [rewriteState, init, renderTok] using h

/-- The streaming rewrite over any chunking equals the deployed whole-input
`rewriteBytes` of the concatenation. -/
theorem streamRewrite_eq_rewriteBytes (chunks : List Bytes) :
    streamRewrite chunks = rewriteBytes chunks.flatten := by
  rw [streamRewrite_eq_spec, rewriteBytes_eq_spec]

/-- **Chunk boundaries are invisible.** Any two chunkings of the same bytes give
the same streamed output. -/
theorem stream_chunk_independent (c1 c2 : List Bytes) (h : c1.flatten = c2.flatten) :
    streamRewrite c1 = streamRewrite c2 := by
  rw [streamRewrite_eq_spec, streamRewrite_eq_spec, h]

/-! ## Binding to the real deployed stage (not a wrapper) -/

/-- **Deployed stage body = spec.** The BUILT pipeline response body the serializer
renders, for the html-rewrite stage on ANY tail/handler/context, is exactly
`stripData` of the tail body. Rides the deployed `htmlrewriteStage_body`. -/
theorem htmlrewriteStage_body_spec (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (htmlrewriteStage :: rest) h c).build).body
      = stripData ((runPipeline rest h c).build).body := by
  rw [htmlrewriteStage_body, rewriteBytes_eq_spec]

/-! ## Non-vacuity -/

/-- The transform genuinely strips: `"<b>hi"` (`60,98,62,104,105`) becomes
`"hi"` (`104,105`). Output ≠ input, so the spec is not the identity. -/
theorem spec_strips_tag : stripData [lt, 98, gt, 104, 105] = [104, 105] := by decide

/-- **Tag split across a chunk boundary strips correctly.** The body `"<b>hi"`
delivered as chunks `["<b", ">hi"]` — the split falls INSIDE the `<b>` tag — still
yields the whole-input rewrite. A boundary-splitting bug would break this. -/
theorem split_inside_tag_ok :
    streamRewrite [[lt, 98], [gt, 104, 105]] = rewriteBytes [lt, 98, gt, 104, 105] := by
  rw [streamRewrite_eq_rewriteBytes]; rfl

/-- A boundary-DEPENDENT stripper: rewrite each chunk independently, concatenate.
This is the bug the chunk-safety property rules out. -/
def naivePerChunk (chunks : List Bytes) : Bytes := (chunks.map rewriteBytes).flatten

/-- **The theorem is non-vacuous.** On the tag-split delivery `["<b", ">hi"]` the
naive per-chunk stripper emits `">hi"`'s `>` as text (`62,104,105`) — a WRONG,
boundary-dependent answer — whereas the deployed streaming rewrite emits `"hi"`
(`104,105`). An impl whose output depended on chunk boundaries would match the
naive result and fail `streamRewrite_eq_spec`. -/
theorem naive_wrong_on_split :
    naivePerChunk [[lt, 98], [gt, 104, 105]] ≠ streamRewrite [[lt, 98], [gt, 104, 105]] := by
  decide

end HtmlRewriteCorrect
