import Datapath.FlatHeaders
import Reactor.Stage.HtmlRewrite

/-!
# Datapath.FlatStage_htmlrw — the deployed `htmlrewrite` stage (position 11 of
`Reactor.Deploy.deployStagesFull2`) proven flat, byte-identical to its deployed
`List` form, via the BODY path of the refinement calculus.

Unlike the header-transform stage `securityheaders` (`Datapath.FlatStage`) and
unlike `gzip` (which also pushes a `Content-Encoding` header), the deployed
`htmlrewrite` stage's whole-response effect is a PURE BODY rewrite — no header
touch:

* the BODY becomes `Reactor.Stage.HtmlRewrite.rewriteBytes r.body` — the real
  streaming markup-stripping rewrite (tokenize with the linear `tokenizeFast`,
  then render the tokens with every `<…>` tag span dropped and the text runs
  kept), read off the deployed `htmlTransformResp` / `htmlrewriteStage.onResponse`;
* the HEADER block, status, and reason are untouched.

So this stage exercises ONLY the BODY grain of `Datapath.ByteRefine` (the
`Array UInt8` FOLD combinator) — the body path the scope named, with no header
half.

## The body transform's OUTPUT ASSEMBLY IS a `refine_fold` — grounded, not re-specified

`rewriteState s` (the output of a final tokenizer state `s`) is definitionally the
`List.++` chain `(s.toks.reverse.flatMap renderTok) ++ trailing` — the completed
tokens rendered in order (each `renderTok`: keep text bytes, drop a tag), then the
trailing in-progress buffer (kept as a text run, dropped as an unclosed tag).
`rewriteState_eq_flatten` re-presents that chain as the `flatten` of a fragment
list `htmlFragments s` (`renderHeaders_eq_flatten`'s sibling on the body). The flat
body assembly is then `foldAppend List.toArray #[] (htmlFragments s)` — the byte
FOLD combinator applied to those fragments — and `flatRewriteBody_refines` proves
it computes byte-identical bytes to `rewriteState s` **for free** from
`foldAppend_toArray_refines` (the calculus's `refine_fold`). No new byte reasoning;
the per-token `flatMap`-concat of the stripped output is discharged by the shared
fold lemma.

## What is proven here (equality-transfer, BYTE-IDENTICAL, non-vacuous)

* `stageResp_eq_gate` — the DEPLOYED stage's built response is exactly the
  content-type gate `gatedHtmlTransformResp b.build`, read off
  `htmlrewriteStage.onResponse`'s `mapResp gatedHtmlTransformResp` via the deployed
  faithfulness lemma `build_mapResp`; `rewrittenResp_eq_stage` specialises it to the
  FIRING (`text/html`) branch where the built response is exactly `rewrittenResp`
  (body ⟶ `rewriteBytes`). Grounds the flat form in the ACTUAL deployed function; we
  do NOT re-specify the stage.
* `rewriteState_eq_flatten` — `rewriteState` is the `flatten` of `htmlFragments`
  (the stripped body's framing decomposition, read off `rewriteState`'s definition).
* `flatRewriteBody` + `flatRewriteBody_refines` — the flat body assembly (the byte
  FOLD) computes byte-identical bytes to `rewriteState`. Non-vacuous: it folds real
  `Array.++`s over the real per-token stripped fragments; the bytes are proven
  equal, not assumed.
* `flatRewrittenResp` + `flatRewrittenResp_eq` — the flat whole-response transform
  (flat body FOLD over the tokenizer state) equals the deployed built response
  `rewrittenResp` — PROVEN via the body refinement, not by definition.
* `flatHtml_serialize_refines` — the flat htmlrewrite stage's whole serialized
  response is byte-identical to `Reactor.serialize` of the DEPLOYED stage's
  response `rewrittenResp`, chaining `flatRewrittenResp_eq` into
  `flatSerialize_refines` (the byte-grain serialize equality). The whole
  computation is flat but for the named `List` seams.

## The honest residual (`RESIDUAL`, at the bottom)

The OUTPUT ASSEMBLY (the per-token stripped-fragment concatenation + trailing
buffer) is proven flat and byte-identical here. The TOKENIZER itself
(`HtmlRewrite.tokenizeFast`, which builds the `s.toks : List Token` spine, and
`s.toks.reverse`, a cons reverse) remains a `List`/`Token`-cons computation
producing the fragment list. The tokenizer is a genuine stateful per-byte loop (the
`feedF` fold) with an intermediate token cons-list — that is the `refine_fold`
residual for this stage (analogous to `FlatStage_gzip`'s named DEFLATE/CRC
fragment-content residual); it is NOT faked here.
-/

namespace Datapath.FlatStage_htmlrw

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx ResponseBuilder build_mapResp)
open Reactor.Stage.HtmlRewrite (htmlrewriteStage htmlTransformResp gatedHtmlTransformResp isHtmlCT rewriteBytes rewriteState renderTok)
open _root_.HtmlRewrite (TState Mode tokenizeFast)
open Datapath.Refinement

/-! ## 1. The deployed stage's whole-response effect, read off the REAL stage -/

/-- **The deployed `htmlrewrite` stage's built response — grounded, not
re-specified.** The finalized (`build`) response of the real
`htmlrewriteStage.onResponse` rewrites the body to the markup-stripped
`rewriteBytes r.body`; the status, reason, and header block are untouched. This is
the function the flat form must compute. -/
def rewrittenResp (r : Response) : Response :=
  { r with body := rewriteBytes r.body }

/-- **The deployed stage's built response IS the content-type gate.** The finalized
(`build`) response of the real `htmlrewriteStage.onResponse` is exactly
`gatedHtmlTransformResp b.build` — read off the stage's `mapResp gatedHtmlTransformResp`
via `build_mapResp`. Grounds the flat form in the ACTUAL deployed function. -/
theorem stageResp_eq_gate (c : Ctx) (b : ResponseBuilder) :
    (htmlrewriteStage.onResponse c b).build = gatedHtmlTransformResp b.build := by
  show (b.mapResp gatedHtmlTransformResp).build = gatedHtmlTransformResp b.build
  rw [build_mapResp]

/-- **On a `text/html` response the deployed stage's built response is exactly the
body rewrite `rewrittenResp`** (the FIRING branch of the content-type gate). This is
the branch the flat body work below computes; on a non-`text/html` response the stage
is a passthrough (`gatedHtmlTransformResp` returns `b.build` untouched), so there is no
body assembly to flatten. -/
theorem rewrittenResp_eq_stage (c : Ctx) (b : ResponseBuilder)
    (hct : isHtmlCT b.build.headers = true) :
    (htmlrewriteStage.onResponse c b).build = rewrittenResp b.build := by
  rw [stageResp_eq_gate]
  show (if isHtmlCT b.build.headers then htmlTransformResp b.build else b.build)
      = rewrittenResp b.build
  rw [hct]; rfl

/-! ## 2. The body output assembly IS a `refine_fold` (byte grain) -/

/-- The trailing in-progress buffer of a final tokenizer state: kept as a text run
(`Mode.text`), dropped as an unclosed tag (`Mode.tag`) — exactly the trailing
`match` arm of `rewriteState`. -/
def htmlTrailing (s : TState) : Bytes :=
  match s.mode with
  | Mode.text => s.cur
  | Mode.tag  => []

/-- The stripped body as a FIXED list of byte fragments: each completed token
rendered (`renderTok`, in chronological order via `toks.reverse`), then the trailing
buffer — mirroring `rewriteState`'s `flatMap`-`++`-chain structure.
`rewriteState_eq_flatten` proves its `flatten` is exactly `rewriteState`. -/
def htmlFragments (s : TState) : List Bytes :=
  s.toks.reverse.map renderTok ++ [htmlTrailing s]

/-- **The stripped body's framing decomposition (spec side).** `rewriteState s` is
the `flatten` of its fragment list — the body-grain sibling of
`Datapath.ByteRefine.serializeWire_eq`. Read straight off `rewriteState`'s
definition (the per-token `flatMap` is the `flatten` of the mapped fragments, plus
the trailing buffer); the flatness is the fold calculus's doing. -/
theorem rewriteState_eq_flatten (s : TState) :
    rewriteState s = (htmlFragments s).flatten := by
  show (s.toks.reverse.flatMap renderTok)
        ++ (match s.mode with | Mode.text => s.cur | Mode.tag => [])
      = (htmlFragments s).flatten
  simp [htmlFragments, htmlTrailing, List.flatMap_def, List.flatten_append]

/-- **The flat body assembly.** Assemble the stripped body flat: `foldAppend` over
the per-token fragments (one flat `Array.++` per fragment, no per-join cons-spine) —
the byte FOLD combinator (`refine_fold`) applied. This is the flat sibling of
`rewriteState`'s `List.++`/`flatMap`-chain. -/
def flatRewriteBody (s : TState) : Array UInt8 :=
  foldAppend List.toArray #[] (htmlFragments s)

/-- **The flat body assembly is byte-identical to `rewriteState` — reused, not
re-proven.** `flatRewriteBody s` refines `rewriteState s`: the FOLD combinator
(`foldAppend_toArray_refines`) reads back the flatten of the fragments, and
`rewriteState_eq_flatten` collapses that to `rewriteState`. Non-vacuous: the flat
op folds real appends over the real per-token stripped fragments; the bytes are
proven equal, not assumed. -/
theorem flatRewriteBody_refines (s : TState) :
    Datapath.Refinement.Refines (rewriteState s) (flatRewriteBody s) := by
  show (flatRewriteBody s).toList = rewriteState s
  unfold flatRewriteBody
  have hfold := foldAppend_toArray_refines (htmlFragments s)
  rw [show (foldAppend List.toArray #[] (htmlFragments s)).toList
        = (htmlFragments s).flatten from hfold, rewriteState_eq_flatten]

/-! ## 3. The flat whole-response transform = the deployed built response -/

/-- The flat computation of the htmlrewrite-stage response: the body assembled flat
by the byte FOLD (`flatRewriteBody`) over the tokenizer's final state. The single
`.toList` boundary (`Response.body` is `List`-typed) is the named residual seam; the
body output assembly is flat. -/
def flatRewrittenResp (r : Response) : Response :=
  { r with body := (flatRewriteBody (tokenizeFast r.body)).toList }

/-- **The flat htmlrewrite response equals the deployed one — PROVEN via the body
refinement, not by definition.** The body half is `flatRewriteBody_refines` (flat
fold = `rewriteState (tokenizeFast …)` = `rewriteBytes`); no other field changes. -/
theorem flatRewrittenResp_eq (r : Response) : flatRewrittenResp r = rewrittenResp r := by
  have hbody : (flatRewriteBody (tokenizeFast r.body)).toList = rewriteBytes r.body :=
    flatRewriteBody_refines (tokenizeFast r.body)
  unfold flatRewrittenResp rewrittenResp
  rw [hbody]

/-! ## 4. Full serialize: the flat htmlrewrite stage's whole response is byte-identical -/

/-- **THE FULL BYTE-IDENTITY.** The flat htmlrewrite stage's whole serialized
response (flat body FOLD ⟶ `Datapath.ByteRefine.flatSerialize`, the derived flat
serializer) is byte-identical to `Reactor.serialize` of the DEPLOYED stage's
response `rewrittenResp`. Chains the whole-response refinement
(`flatRewrittenResp_eq`) into the byte-grain serialize equality
(`flatSerialize_refines`). No deployed byte changes; the whole computation is flat
but for the named `List` seams. -/
theorem flatHtml_serialize_refines (r : Response) :
    Datapath.Refinement.Refines (Reactor.serialize (rewrittenResp r))
      (flatSerialize (flatRewrittenResp r)) := by
  rw [flatRewrittenResp_eq]
  exact flatSerialize_refines (rewrittenResp r)

/-! ## Non-vacuity — the flat ops genuinely compute the REAL stripped body -/

-- The flat body assembly over the real `"<b>hi"` body produces the REAL stripped
-- bytes `rewriteBytes "<b>hi"` — evaluated by the kernel (not just proven).
#guard (flatRewriteBody (tokenizeFast [60, 98, 62, 104, 105])).toList
        == rewriteBytes ([60, 98, 62, 104, 105] : Bytes)

-- The stripped bytes are genuinely `"hi"` (the `<b>` tag dropped) — the flat op
-- computes the REAL lossy transform, not the identity.
#guard (flatRewriteBody (tokenizeFast [60, 98, 62, 104, 105])).toList
        == ([104, 105] : List UInt8)

-- The flat op genuinely changes the wire: the stripped body is NOT the input body.
#guard (flatRewriteBody (tokenizeFast "<b>hi".toUTF8.toList)).toList
        != "<b>hi".toUTF8.toList

-- The full flat serialized response is byte-identical to the deployed serialize —
-- evaluated on a real `200 OK` carrying an html body.
#guard (flatSerialize (flatRewrittenResp (Reactor.ok200 "<b>hi".toUTF8.toList))).data.toList
        == Reactor.serialize (rewrittenResp (Reactor.ok200 "<b>hi".toUTF8.toList))

/-! ## RESIDUAL — the honest open piece for THIS stage

Proven flat + byte-identical here: the body OUTPUT ASSEMBLY (`rewriteState`'s
per-token stripped-fragment `flatMap`-concat + trailing buffer ⟶ the byte FOLD),
and the whole serialize on top of it.

Still a `List`/`Token`-cons computation (named, NOT faked):

* **The tokenizer.** `HtmlRewrite.tokenizeFast` is a genuine stateful per-byte loop
  (`feedF` fold) that builds the intermediate `s.toks : List Token` spine; the
  fragment list rides `s.toks.reverse` (a cons reverse) and `renderTok` per token.
  Flattening the token spine into the byte FOLD directly (so the tokenizer never
  materializes a `Token` cons-list) is the follow-on, analogous to
  `FlatStage_gzip`'s DEFLATE/CRC fragment-content residual — a per-stage streaming
  refinement, not covered by the fixed-fragment fold this file discharges.

* **The `Response.body` `List` seam.** `flatRewrittenResp` still `.toList`s the flat
  body `Array` at the `Reactor.Response.body` field boundary (the deployed
  `Response.body` is `List UInt8`-typed). `flatRewriteBody` shows the body assembles
  flat with NO such materialization; closing it fully is the same additive flat
  `Response`/serialize variant named in `Datapath.FlatStage`'s REMAINING (b).
-/

end Datapath.FlatStage_htmlrw
