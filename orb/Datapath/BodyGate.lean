import Reactor.Stage.HtmlRewrite
import Proto.Http10

/-!
# Datapath.BodyGate — the CONTENT-TYPE-GATED body transform (the correct engine shape)

The deployed `Reactor.Stage.HtmlRewrite.htmlrewriteStage.onResponse` runs
`rewriteBytes r.body` **UNCONDITIONALLY** on EVERY response body (there is no
content-type check), and `renderTok (Token.tag _) = []` strips every `<…>` span.
So the deployed pipeline TAG-STRIPS every body it serves — a latent CORRUPTION bug
for any non-HTML body (JSON, images, `application/octet-stream`): a `<` in a JSON
string or a binary body is silently deleted. It is latent only because the demo
`/health` body is tagless (`rewriteBytes` of a tagless body is the identity).

This module builds the CORRECT shape a real engine has: the html-rewrite is
**CONDITIONAL on the response's `Content-Type`**. `gatedHtmlrewrite` rewrites the
body iff the response declares `text/html`; on anything else the body is a pure
PASSTHROUGH — returned UNTOUCHED, never tokenized. This is BOTH a correctness fix
(non-HTML bodies are no longer corrupted) AND the enabler of the common-case
zero-copy body path (`Datapath.ServeGated`): a non-HTML body never enters the
tokenizer at all.

This is ADDITIVE — the deployed `Reactor.Stage.HtmlRewrite` spec is untouched; the
gated variant is a new def proven against the deployed `htmlTransformResp`.

Proven:
* `gatedHtmlrewrite_html`        — when `Content-Type` is `text/html`, the gate is
  byte-identical to the DEPLOYED `htmlTransformResp` (it fires exactly as deployed).
* `gatedHtmlrewrite_passthrough` — when it is NOT `text/html`, the WHOLE response is
  returned untouched (`= r`), so the body is a zero-transform passthrough.
* `gatedHtmlrewrite_correct`     — the body is `rewriteBytes r.body` IFF the content
  is HTML: the gate strips markup exactly when it should, and never otherwise — the
  correct behaviour, strictly better than the deployed corrupt-everything.
-/

namespace Datapath.BodyGate

open Proto (Bytes)
open Reactor (Response)
open Reactor.Stage.HtmlRewrite (rewriteBytes htmlTransformResp)
open Proto.Http10 (lowerBytes)

/-! ## Reading the response's declared media type -/

/-- ASCII bytes of the (lowercase) `content-type` header name. -/
def ctName : Bytes := "content-type".toUTF8.toList

/-- ASCII bytes of the `text/html` media-type prefix. -/
def htmlPrefix : Bytes := "text/html".toUTF8.toList

/-- A `Content-Type` value names HTML iff — case-folded — it BEGINS with
`text/html`. So `text/html`, `text/html; charset=utf-8`, and `TEXT/HTML` all count;
`application/json`, `application/octet-stream`, `image/png` do not. -/
def isHtmlValue (v : Bytes) : Bool := htmlPrefix.isPrefixOf (lowerBytes v)

/-- **The gate predicate.** The response's declared media type is HTML: the first
header whose case-folded name is `content-type` carries an HTML value. A response
with no `Content-Type` is NOT html (so a header-less body is a passthrough). -/
def isHtmlCT (headers : List (Bytes × Bytes)) : Bool :=
  match headers.find? (fun h => lowerBytes h.1 == ctName) with
  | some h => isHtmlValue h.2
  | none   => false

/-! ## The content-type-gated body transform -/

/-- **THE CONTENT-TYPE-GATED HTML-REWRITE.** If the response declares `text/html`,
run the REAL deployed body rewrite (`{ r with body := rewriteBytes r.body }`, i.e.
`htmlTransformResp`); otherwise return the response UNTOUCHED — the body is a pure
passthrough, never tokenized. This is the conditional the deployed stage lacks. -/
def gatedHtmlrewrite (r : Response) : Response :=
  if isHtmlCT r.headers then { r with body := rewriteBytes r.body } else r

/-- **(a) On `text/html`, the gate IS the deployed transform.** When the response
declares HTML, `gatedHtmlrewrite` is byte-identical to the deployed
`Reactor.Stage.HtmlRewrite.htmlTransformResp` — the gate fires exactly as the
deployed stage does, so no HTML response changes behaviour. -/
theorem gatedHtmlrewrite_html (r : Response) (h : isHtmlCT r.headers = true) :
    gatedHtmlrewrite r = htmlTransformResp r := by
  unfold gatedHtmlrewrite htmlTransformResp
  simp only [h, if_true]

/-- **(b) On non-`text/html`, the WHOLE response is untouched.** When the response
is not HTML, `gatedHtmlrewrite r = r` — the body (and every other field) is a pure
zero-transform passthrough. The deployed stage would have tokenized and stripped it;
the gate does not touch it. -/
theorem gatedHtmlrewrite_passthrough (r : Response) (h : isHtmlCT r.headers = false) :
    gatedHtmlrewrite r = r := by
  unfold gatedHtmlrewrite
  simp only [h, Bool.false_eq_true, if_false]

/-- The body of a non-HTML response is returned VERBATIM (`= r.body`) — the
zero-transform passthrough at the body grain. -/
theorem gatedHtmlrewrite_body_passthrough (r : Response) (h : isHtmlCT r.headers = false) :
    (gatedHtmlrewrite r).body = r.body := by
  rw [gatedHtmlrewrite_passthrough r h]

/-- **(c) The gate is CORRECT: strips markup IFF the content is HTML.** The served
body is the tag-stripping `rewriteBytes r.body` exactly when the response declares
HTML, and the untouched `r.body` otherwise. This is the correct behaviour — strictly
better than the deployed stage, which strips unconditionally (corrupting non-HTML
bodies). -/
theorem gatedHtmlrewrite_correct (r : Response) :
    (gatedHtmlrewrite r).body
      = if isHtmlCT r.headers then rewriteBytes r.body else r.body := by
  unfold gatedHtmlrewrite
  cases h : isHtmlCT r.headers with
  | true  => simp only [h, if_true]
  | false => simp only [h, Bool.false_eq_true, if_false]

/-! ## The deployed stage APPLIES this proven gate (single source of truth) -/

/-- `isHtmlCT` is definitionally the predicate the deployed stage inlines. -/
theorem isHtmlCT_eq_stage (h : List (Bytes × Bytes)) :
    isHtmlCT h = Reactor.Stage.HtmlRewrite.isHtmlCT h := rfl

/-- **The deployed stage's gated transform IS this proven gate.** The transform
`Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp` that the deployed `htmlrewriteStage`
now applies is byte-identical to `gatedHtmlrewrite` on every response — so all three
correctness facts above (`_html`, `_passthrough`, `_correct`) transfer verbatim to the
deployed stage. No drift between the proof and the deployed pipeline. -/
theorem gatedHtmlrewrite_eq_stage (r : Response) :
    gatedHtmlrewrite r = Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp r := by
  unfold gatedHtmlrewrite Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp
    Reactor.Stage.HtmlRewrite.htmlTransformResp
  rw [isHtmlCT_eq_stage]

/-! ## Non-vacuity — the gate genuinely fires on HTML and passes non-HTML through -/

/-- A `text/html` response whose body is the tag `"<b>hi"`. -/
def htmlResp : Response :=
  { status := 200, reason := [], headers := [(ctName, "text/html".toUTF8.toList)],
    body := [60, 98, 62, 104, 105] }

/-- An `application/json` response with the SAME `"<b>hi"` body. -/
def jsonResp : Response :=
  { status := 200, reason := [], headers := [(ctName, "application/json".toUTF8.toList)],
    body := [60, 98, 62, 104, 105] }

-- The gate predicate genuinely distinguishes the two.
#guard isHtmlCT htmlResp.headers == true
#guard isHtmlCT jsonResp.headers == false
-- A `charset` parameter is still recognised as HTML.
#guard isHtmlCT [(ctName, "text/html; charset=utf-8".toUTF8.toList)] == true
-- An UPPERCASE header name / value is still recognised (case-insensitive).
#guard isHtmlCT [("Content-Type".toUTF8.toList, "TEXT/HTML".toUTF8.toList)] == true

-- On HTML: the gate FIRES — `<b>` stripped, body becomes `"hi"` (bytes 104,105).
#guard (gatedHtmlrewrite htmlResp).body == [104, 105]
-- On JSON: the gate PASSES THROUGH — body UNTOUCHED, `<` (60) and `>` (62) preserved.
#guard (gatedHtmlrewrite jsonResp).body == [60, 98, 62, 104, 105]
#guard (gatedHtmlrewrite jsonResp).body.contains 60
#guard (gatedHtmlrewrite jsonResp).body.contains 62
-- ★ THE CORRECTNESS IMPROVEMENT: the DEPLOYED unconditional rewrite would CORRUPT
-- the JSON body (strip the `<b>`), but the gate preserves it — they DIFFER, and the
-- gate is the correct one.
#guard rewriteBytes jsonResp.body == [104, 105]
#guard (gatedHtmlrewrite jsonResp).body != rewriteBytes jsonResp.body
-- On a TAGLESS body the gate is byte-identical to the deployed rewrite EITHER way
-- (`rewriteBytes` of a tagless body is the identity) — the demo `/health` case.
#guard (gatedHtmlrewrite { jsonResp with body := "hello".toUTF8.toList }).body
        == rewriteBytes "hello".toUTF8.toList

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms gatedHtmlrewrite_html
#print axioms gatedHtmlrewrite_passthrough
#print axioms gatedHtmlrewrite_correct

end Datapath.BodyGate
