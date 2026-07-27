import Reactor.Pipeline
import HtmlRewrite.Basic
import Proto.Http10

/-!
# Reactor.Stage.HtmlRewrite — a body-rewriting response-transform stage

A response-transform pipeline stage that runs the REAL streaming HTML tokenizer
(`HtmlRewrite.tokenize` / the per-byte `feed` fold from `HtmlRewrite/Basic.lean`)
over the response body and emits the rewritten bytes. The rewrite is a genuine,
lossy transform — it **strips markup**: every `<…>` tag span the tokenizer
recognises is dropped, and the text runs between them are kept, in order.

**The rewrite is CONTENT-TYPE-GATED.** The markup strip is only correct on
`text/html` bodies — running it on a JSON / binary / octet-stream body silently
deletes any `<`/`>` in the payload (a latent corruption bug). So `htmlrewriteStage`
applies the strip via `gatedHtmlTransformResp`: it fires **iff** the response
declares `Content-Type: text/html`, and on anything else the body is a pure
passthrough, returned untouched and never tokenized. This is the same gate proven
correct additively in `Datapath.BodyGate` (`gatedHtmlrewrite`, tied to this stage by
`Datapath.BodyGate.gatedHtmlrewrite_eq_stage`).

The engine is the real streaming tokenizer, so the rewrite inherits its
chunk-boundary safety: feeding the body split at *any* boundary and streaming the
chunks yields the same stripped output as feeding it whole
(`rewrite_stream_eq_whole`, riding on `HtmlRewrite.stream_eq_whole`). A
chunk-at-a-time markup stripper that splits inside a `<…>` span is exactly what
this gets right.

The stage's `onResponse` threads the affine `ResponseBuilder` and applies the
transform via the sanctioned `mapResp` escape hatch (a body rewrite is not a
single append, so `appendBody` cannot express it; `mapResp` is the affine op the
builder provides for a whole-`Response` in-place transform). `build_mapResp`
carries the transform into the finalized `Response` the serializer renders.

Byte-effect theorems:
* `htmlrewriteStage_effect`      — the stage rides `pipeline_stage_effect`.
* `htmlrewriteStage_body`        — the BUILT pipeline body is `rewriteBytes` of the
  tail's body IFF the tail declares `text/html`, and the untouched tail body
  otherwise (the content-type gate), for ANY tail/handler/ctx.
* `htmlrewriteStage_demo_passthrough` — an UNLABELLED `"<b>hi"` body is PRESERVED
  (the correctness fix: the gate no longer corrupts non-HTML bodies).
* `htmlrewriteStage_body_html` — for any `text/html` tail the built body IS the
  stripped `rewriteBytes` (the gate fires); a concrete `#guard` witnesses it natively.
-/

namespace Reactor.Stage.HtmlRewrite

open Reactor (Response)
open Reactor.Pipeline
open Proto (Bytes)
open Proto.Http10 (lowerBytes)
open _root_.HtmlRewrite (Token TState Mode tokenize tokenizeFast tokenizeFast_eq feedBytes stream_eq_whole)

/-- Render one token in the stripped output: keep a text run's bytes verbatim,
drop a tag span entirely. This is the whole rewrite decision, per token. -/
def renderTok : Token → List UInt8
  | Token.text b => b
  | Token.tag _  => []

/-- The rewrite output of a final tokenizer state: the completed tokens rendered
in chronological order, then the in-progress buffer — kept if it is a trailing
text run (`Mode.text`), dropped if it is an unclosed tag (`Mode.tag`). -/
def rewriteState (s : TState) : List UInt8 :=
  (s.toks.reverse.flatMap renderTok) ++
    (match s.mode with
      | Mode.text => s.cur
      | Mode.tag  => [])

/-- The real streaming HTML rewrite: tokenize the body with the REAL tokenizer,
then render the tokens with markup stripped. Uses the linear-time `tokenizeFast`
(proven byte-for-byte equal to the abstract `tokenize` by `tokenizeFast_eq`), so
the deployed body rewrite is O(N), not the O(N²) of the per-byte `cur ++ [b]`
append — while computing the identical bytes. -/
def rewriteBytes (bs : Bytes) : Bytes := rewriteState (tokenizeFast bs)

/-- `rewriteBytes` computes exactly the abstract `rewriteState (tokenize …)` — the
linear tokenizer changed HOW the body is rewritten, never WHAT. -/
@[simp] theorem rewriteBytes_eq (bs : Bytes) : rewriteBytes bs = rewriteState (tokenize bs) := by
  unfold rewriteBytes; rw [tokenizeFast_eq]

/-- The whole-`Response` transform the stage applies in place via `mapResp`:
the body becomes the rewrite output; every other field is untouched. -/
def htmlTransformResp (r : Response) : Response :=
  { r with body := rewriteBytes r.body }

/-! ## The content-type gate — rewrite HTML only, pass everything else through

The markup strip is only correct on `text/html` bodies: `renderTok (Token.tag _) = []`
deletes every `<…>` span, so running it UNCONDITIONALLY on every response body
corrupts non-HTML payloads (a `<` in a JSON string or a binary body is silently
dropped). The gate below keys the rewrite on the response's declared `Content-Type`:
the strip fires iff the body is `text/html`; on anything else the response is a pure
passthrough, returned untouched (and never tokenized). This is the same predicate
proven correct additively in `Datapath.BodyGate` (`gatedHtmlrewrite`); the deployed
stage now applies it (`Datapath.BodyGate.gatedHtmlrewrite_eq_stage` ties them). -/

/-- ASCII bytes of the (lowercase) `content-type` header name. -/
def ctName : Bytes := "content-type".toUTF8.toList

/-- ASCII bytes of the `text/html` media-type prefix. -/
def htmlPrefix : Bytes := "text/html".toUTF8.toList

/-- A `Content-Type` value names HTML iff — case-folded — it BEGINS with `text/html`.
So `text/html`, `text/html; charset=utf-8`, and `TEXT/HTML` all count; `application/
json`, `application/octet-stream`, `image/png` do not. -/
def isHtmlValue (v : Bytes) : Bool := htmlPrefix.isPrefixOf (lowerBytes v)

/-- **The gate predicate.** The response's declared media type is HTML: the first
header whose case-folded name is `content-type` carries an HTML value. A response
with no `Content-Type` is NOT html (so a header-less body is a passthrough). -/
def isHtmlCT (headers : List (Bytes × Bytes)) : Bool :=
  match headers.find? (fun h => lowerBytes h.1 == ctName) with
  | some h => isHtmlValue h.2
  | none   => false

/-- **The content-type-GATED whole-`Response` transform the stage applies.** If the
response declares `text/html`, run the real body rewrite (`htmlTransformResp`);
otherwise return the response UNTOUCHED — the body is a pure passthrough, never
tokenized. This is the conditional the deployed stage previously lacked. -/
def gatedHtmlTransformResp (r : Response) : Response :=
  if isHtmlCT r.headers then htmlTransformResp r else r

/-- The gated transform's body: the tag-stripped `rewriteBytes r.body` iff the content
is HTML, the untouched `r.body` otherwise. The correct behaviour — strips markup
exactly when it should and never otherwise. -/
theorem gatedHtmlTransformResp_body (r : Response) :
    (gatedHtmlTransformResp r).body
      = if isHtmlCT r.headers then rewriteBytes r.body else r.body := by
  unfold gatedHtmlTransformResp htmlTransformResp
  cases isHtmlCT r.headers <;> simp

/-- The gated transform never changes the status (both branches keep `r.status`). -/
theorem gatedHtmlTransformResp_status (r : Response) :
    (gatedHtmlTransformResp r).status = r.status := by
  unfold gatedHtmlTransformResp htmlTransformResp
  cases isHtmlCT r.headers <;> rfl

/-- **The stage.** Always passes the request phase, then runs the CONTENT-TYPE-GATED
body rewrite in place on the affine builder (`mapResp` — the sanctioned whole-
`Response` op): the markup strip fires only on `text/html`, and every other body is a
passthrough (correctness fix + the non-HTML zero-transform fast path). -/
def htmlrewriteStage : Stage where
  name := "htmlrewrite"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp gatedHtmlTransformResp

/-! ## Chunk-boundary safety of the rewrite -/

/-- **Chunk-boundary safety.** Streaming the body split at any single boundary
`a ++ b` and rewriting the streamed final state yields exactly the rewrite of the
whole input — the boundary is invisible. Rides on the real tokenizer's
`HtmlRewrite.stream_eq_whole`. -/
theorem rewrite_stream_eq_whole (a b : Bytes) :
    rewriteState (feedBytes (tokenize a) b) = rewriteBytes (a ++ b) := by
  rw [rewriteBytes_eq, stream_eq_whole]

/-! ## Byte-effect -/

/-- The stage factors through `pipeline_stage_effect`: its `onResponse` applies the
CONTENT-TYPE-GATED `gatedHtmlTransformResp` to the tail builder. -/
theorem htmlrewriteStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (htmlrewriteStage :: rest) h c
      = (runPipeline rest h c).mapResp gatedHtmlTransformResp :=
  pipeline_stage_effect htmlrewriteStage rest h c c rfl

/-- **The byte-effect.** The BUILT pipeline body is exactly the CONTENT-TYPE-GATED
rewrite applied to the tail's `Response` — for ANY tail, handler, and context. The
body is `rewriteBytes` of the tail body iff the tail declares `text/html`, and the
untouched tail body otherwise. `build_mapResp` carries the in-place transform into the
finalized `Response` the serializer renders. -/
theorem htmlrewriteStage_body (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (htmlrewriteStage :: rest) h c).build).body
      = if isHtmlCT ((runPipeline rest h c).build).headers
        then rewriteBytes ((runPipeline rest h c).build).body
        else ((runPipeline rest h c).build).body := by
  rw [htmlrewriteStage_effect, build_mapResp, gatedHtmlTransformResp_body]

/-! ## The gate is real (concrete witnesses: passthrough on non-HTML, strip on HTML) -/

/-- A concrete markup body: `"<b>hi"` (bytes `<`, `b`, `>`, `h`, `i`). -/
def demoBody : Bytes := [60, 98, 62, 104, 105]

/-- The demo handler answers with the markup body and NO `Content-Type` header — the
non-HTML (unlabelled) case, so the gate treats it as a passthrough. -/
def demoHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [], body := demoBody }

/-- An HTML demo handler: the SAME markup body, now labelled `Content-Type: text/html`
— so the gate FIRES and the markup is stripped. -/
def demoHtmlHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [(ctName, htmlPrefix)], body := demoBody }

/-- A concrete context. -/
def demoCtx : Ctx := { input := [], req := {} }

/-- The rewrite genuinely changes the markup body: stripping the `<b>` tag leaves
`"hi"`, which is not `"<b>hi"`. -/
theorem rewrite_changes_demo : rewriteBytes demoBody ≠ demoBody := by decide

/-- **The gate PRESERVES a non-HTML body (the correctness fix).** Run through the real
`runPipeline`, the built response body for the UNLABELLED markup handler is EXACTLY the
handler's body — the stage no longer strips it. The deployed unconditional stage would
have corrupted it (dropped the `<b>`); the gated stage passes it through verbatim. -/
theorem htmlrewriteStage_demo_passthrough :
    ((runPipeline [htmlrewriteStage] demoHandler demoCtx).build).body = demoBody := by
  rw [htmlrewriteStage_body]
  rfl

/-- **The gate FIRES on a `text/html` body (non-vacuity).** For ANY tail whose built
response declares `text/html`, the built body IS the stripped `rewriteBytes` of the
tail body — the stage is a genuine byte-driver on HTML. (Instantiated concretely by
the native `#guard` below, which the kernel cannot check because the `text/html`
`Content-Type` bytes go through `String.toUTF8`, opaque to kernel reduction — the same
reason `Datapath.BodyGate` witnesses gate-firing with `#guard`.) -/
theorem htmlrewriteStage_body_html (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hct : isHtmlCT ((runPipeline rest h c).build).headers = true) :
    ((runPipeline (htmlrewriteStage :: rest) h c).build).body
      = rewriteBytes ((runPipeline rest h c).build).body := by
  rw [htmlrewriteStage_body, if_pos hct]

-- ★ NON-VACUITY (native): the `text/html`-labelled `"<b>hi"` body IS stripped to `"hi"`
-- — the gate genuinely fires, the built body differs from the handler's body.
#guard ((runPipeline [htmlrewriteStage] demoHtmlHandler demoCtx).build).body != demoBody
#guard ((runPipeline [htmlrewriteStage] demoHtmlHandler demoCtx).build).body == [104, 105]
-- And the UNLABELLED body is preserved verbatim (the correctness fix, native check).
#guard ((runPipeline [htmlrewriteStage] demoHandler demoCtx).build).body == demoBody

end Reactor.Stage.HtmlRewrite
