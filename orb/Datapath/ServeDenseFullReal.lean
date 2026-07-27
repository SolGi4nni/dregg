import HtmlRewriteCorrect
import Reactor.App

/-!
# Datapath.ServeDenseFullReal — the `/bulk` BODY, proven densely reproducible

This module proves the **body half** of "the full 14-stage dense serve = `drorbServe`
on `/bulk`": on the deployed `/bulk` (1 MiB) route the served response body is
`Reactor.App.bulkBody = List.replicate 1048576 0x61`, the two body-touching transform
stages leave it UNCHANGED, and it is reproducible as a genuine `ByteArray` with NO
per-byte `cons`.

## Why the `/bulk` body is left untouched by the fold (ground truth)

Evaluated on hbox, `Reactor.ServeArr.respOf ("GET /bulk HTTP/1.1…")` produces
`status 200`, a 7-header set, and a body of `1048576` copies of `0x61`. The two
stages that could rewrite a response body in `deployStagesFull2` are BOTH gated OFF
for `/bulk`:

* `Reactor.Stage.Gzip.gzipStage` compresses only when the REQUEST advertises
  `Accept-Encoding: … gzip …` (`Gzip.acceptsGzip`); a plain `GET /bulk` does not, so
  the stage is the identity on the body.
* `Reactor.Stage.HtmlRewrite.htmlrewriteStage` rewrites only when the RESPONSE
  declares `Content-Type: text/html` (`isHtmlCT`, `htmlrewriteStage_body`); the
  `/bulk` response carries no `Content-Type`, so it is the identity on the body — and
  EVEN IF it fired, `rewriteBytes bulkBody = bulkBody` (`rewriteBytes_bulkBody` below,
  the tagless body has nothing to strip).

The remaining response stages (`securityheaders`, `header`, `cors`, the deploy
`headerRewrite`) touch only headers. So the served `/bulk` body is exactly
`bulkBody`, reproducible densely.

## What is proven here vs. the named residual

* PROVEN (this file): `rewriteBytes_bulkBody` (the K2 whole-body html-rewrite is the
  identity on `/bulk`) and `bulkBodyDense_toList` (the dense `ByteArray` body denotes
  to `bulkBody`) — axioms ⊆ {propext, Quot.sound}.

* RESIDUAL (named, NOT attempted here): the full byte-identity
  `serveDenseFullReal input = Dataplane.drorbServe input` for `/bulk`. Its blocker is
  NOT the body but the **input-dependent response HEAD**: the deployed `/bulk` headers
  include `x-corr` (the whole request rendered as dotted-decimal) and `x-upstream`
  (a hash of the request), stamped by the deploy `headerRewrite` (`deployProg`). Any
  RUNTIME-dense serve must reproduce that head WITHOUT calling `respOf` (which, being
  strict, would materialise the 1 MiB body it is trying to avoid), i.e. re-express the
  response-phase header fold over `deployStagesFull2` densely and prove it equal to the
  deployed fold. That is the "still-open multi-file `runPipeline` re-proof"
  (`Datapath.ServePolyFull` honest-scope, `Reactor.ServeArr` L37-46): byte-identity to
  `servePipelineFull2 input.toList` pins any total serve to FEEDING it `input.toList`,
  so the head cannot be produced densely without that re-proof.
-/

namespace Datapath.ServeDenseFullReal

open HtmlRewriteCorrect (strip stripData rewriteBytes_eq_spec)
open Reactor.Stage.HtmlRewrite (rewriteBytes)

/-! ## `strip` is the identity on a byte list with no `<` (0x3C) -/

/-- In the data state, `strip` copies every byte that is not `<` (`lt`). So on a list
containing no `<` it is the identity. -/
theorem strip_false_no_lt : ∀ bs : List HtmlRewrite.Byte,
    (∀ b ∈ bs, b ≠ HtmlRewrite.lt) → strip false bs = bs := by
  intro bs
  induction bs with
  | nil => intro _; rfl
  | cons b rest ih =>
    intro h
    have hb : b ≠ HtmlRewrite.lt := h b (List.mem_cons_self)
    have hrest : strip false rest = rest := ih (fun x hx => h x (List.mem_cons_of_mem b hx))
    show (if b = HtmlRewrite.lt then strip true rest else b :: strip false rest) = b :: rest
    rw [if_neg hb, hrest]

/-! ## The `/bulk` body is untouched by the deployed html-rewrite -/

/-- Every byte of `bulkBody` is `0x61` (`'a'`), which is not `<` (`0x3C`). -/
theorem bulkBody_no_lt : ∀ b ∈ Reactor.App.bulkBody, b ≠ HtmlRewrite.lt := by
  intro b hb
  have : b = (0x61 : UInt8) := List.eq_of_mem_replicate hb
  subst this
  decide

/-- **THE HTML-REWRITE IDENTITY ON `/bulk`.** The deployed whole-body html-rewrite
(`rewriteBytes`, the K2 whole-body loop that fires on every response) is the IDENTITY
on the 1 MiB `/bulk` body — it has no markup, so nothing is stripped. This is the
body transform whose per-byte `List` walk the dense serve avoids. -/
theorem rewriteBytes_bulkBody : rewriteBytes Reactor.App.bulkBody = Reactor.App.bulkBody := by
  rw [rewriteBytes_eq_spec]
  show strip false Reactor.App.bulkBody = Reactor.App.bulkBody
  exact strip_false_no_lt Reactor.App.bulkBody bulkBody_no_lt

/-! ## The `/bulk` body reproduced DENSELY as a `ByteArray` (no per-byte cons) -/

/-- The 1 MiB `/bulk` body as a genuine `ByteArray`, built by `ByteArray.mk` of a bulk
`Array` — no `List` spine, no per-byte `cons`. -/
def bulkBodyDense : ByteArray := ByteArray.mk (Array.replicate Reactor.App.bulkSize (0x61 : UInt8))

/-- **The dense body denotes to the deployed `/bulk` body.** Reading the dense
`ByteArray` back as a byte list yields exactly `bulkBody` — so the dense serve's body
is byte-identical to the deployed one while never consing a 1 MiB `List`. -/
theorem bulkBodyDense_toList : bulkBodyDense.data.toList = Reactor.App.bulkBody := by
  have h : ∀ n, (Array.replicate n (0x61 : UInt8)).toList = List.replicate n (0x61 : UInt8) :=
    fun _ => rfl
  show (Array.replicate Reactor.App.bulkSize (0x61 : UInt8)).toList = Reactor.App.bulkBody
  rw [h Reactor.App.bulkSize]
  rfl

/-! ## Non-vacuity — the html-rewrite is genuinely NOT the identity in general -/

-- The dense body is genuinely 1 MiB, not a placeholder.
#guard bulkBodyDense.size == Reactor.App.bulkSize
-- The identity `rewriteBytes_bulkBody` is NOT vacuous: on a MARKUP body the deployed
-- rewrite genuinely strips the tag (`"<b>hi"` → `"hi"`), so it is not the identity map.
#guard rewriteBytes [60, 98, 62, 104, 105] == [104, 105]
#guard rewriteBytes [60, 98, 62, 104, 105] != [60, 98, 62, 104, 105]

/-! ## Axiom audit -/

#print axioms rewriteBytes_bulkBody
#print axioms bulkBodyDense_toList

end Datapath.ServeDenseFullReal
