import Datapath.BodyGate

/-!
# Proto.CtGateProven — the DEPLOYED content-type-gated non-HTML passthrough

PROVE-WHAT-RUNS for the datapath row `ct.gate` (`DRORB_SPAN=13`, the content-type-gated
serve `Datapath.ServeGated.serveGated`).

## What runs (curl-confirmed on hbox)

The deployed gated serve mirrors the request `Content-Type` onto the response and gates
its body transform on it: `text/html` responses run the deployed html-rewrite
(`Reactor.Stage.HtmlRewrite.rewriteBytes`, which strips every `<…>` span); anything else
is a PURE PASSTHROUGH — the body is returned untouched, never tokenized. The gate
predicate/transform is `Datapath.BodyGate.gatedHtmlrewrite`, proven byte-identical to the
deployed `Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp` (`gatedHtmlrewrite_eq_stage`).

Deployed, launched `DRORB_SPAN=13 ./dataplane --bind 127.0.0.1:8100 --io blocking`; the
echo serve reflects the request `Content-Type` and gates the (echoed) body:

    $ curl -s --data-binary '<b>hi' -H 'Content-Type: application/octet-stream' \
        http://127.0.0.1:8100/echo | od -An -tx1 | tail
        ... 0d 0a 3c 62 3e 68 69          # non-HTML: body TAIL = "<b>hi", `<`/`>` PRESERVED
    $ curl -s --data-binary '<b>hi' -H 'Content-Type: text/html' \
        http://127.0.0.1:8100/echo | od -An -tx1 | tail
        ... 0d 0a 68 69                    # text/html: gate FIRES, "<b>" STRIPPED -> "hi"
    # response header echoes: `content-type: application/octet-stream` (mirrored)

## What is proven here (over the deployed gate `gatedHtmlrewrite`)

* `gate_passthrough_preserves_markup` — a NON-HTML response is returned verbatim; the
  body keeps every byte, `<` (0x3c) and `>` (0x3e) included. This is the deployed
  non-HTML case: no corruption of JSON/binary bodies.
* `gate_fires_on_html` — a `text/html` response body is rewritten exactly as the deployed
  html-rewrite (`<b>` stripped).
* `gate_correct` — the served body is `rewriteBytes` IFF the content is HTML, and the
  identity otherwise: the gate strips markup exactly when it should and never otherwise.
* `gate_octet_vs_html_differ` — non-vacuity: on the SAME `<b>hi` body the two content
  types produce DIFFERENT bodies (`<b>hi` vs `hi`), so the gate genuinely branches.
* `gate_is_deployed_stage` — the proven gate IS the deployed stage's transform.

Reuses the pure-kernel `Datapath.BodyGate` (axioms ⊆ {propext, Quot.sound}); concrete
byte facts are `decide`/`rfl` (no `native_decide`).
-/

namespace Proto.CtGateProven

open Proto (Bytes)
open Reactor (Response)
open Reactor.Stage.HtmlRewrite (rewriteBytes rewriteBytes_eq)
open Datapath.BodyGate
  (gatedHtmlrewrite isHtmlCT gatedHtmlrewrite_correct
   gatedHtmlrewrite_body_passthrough gatedHtmlrewrite_eq_stage gatedHtmlrewrite_html)

/-! ## The non-HTML response (the octet-stream wire case)

`isHtmlCT` keys on the response's `Content-Type` via `String.toUTF8`, which is
kernel-opaque (does not `rfl`/`decide`-reduce) — the same reason `HeadProven` keeps
`toUTF8` opaque. So the concrete facts here use a `Content-Type`-LESS response (which
`isHtmlCT` decides `false` by `rfl` on the empty header list — the deployed "no/`≠`
`text/html` ⇒ passthrough" branch, exactly the `application/octet-stream` curl's branch)
plus the `Content-Type`-gate correctness proven parametrically. The `<b>hi` markup body
is a byte literal, so the rewrite/passthrough effect reduces in the kernel with no
`native_decide`. -/

/-- A NON-HTML response (no `Content-Type` ⇒ `isHtmlCT = false`, the passthrough branch —
the same branch the `application/octet-stream` curl takes) whose body carries the markup
`<b>hi` (`[0x3c,0x62,0x3e,0x68,0x69]`). -/
def nonHtmlResp : Response :=
  { status := 200, reason := [], headers := [], body := [0x3c, 0x62, 0x3e, 0x68, 0x69] }

/-- `isHtmlCT` decides the non-HTML response `false` — by `rfl` (`[].find? = none`),
no `toUTF8` reduction needed. -/
theorem nonHtml_not_html : isHtmlCT nonHtmlResp.headers = false := rfl

/-! ## Passthrough preserves markup (the non-HTML wire case) -/

/-- **`gate_passthrough_preserves_markup`.** The non-HTML response is returned VERBATIM by
the deployed gate: the body is byte-identical to the request body `<b>hi`, with `<`
(0x3c) and `>` (0x3e) intact — exactly the wire tail `3c 62 3e 68 69` from the
`application/octet-stream` curl. No tokenization, no stripping. -/
theorem gate_passthrough_preserves_markup :
    (gatedHtmlrewrite nonHtmlResp).body = [0x3c, 0x62, 0x3e, 0x68, 0x69]
  ∧ (gatedHtmlrewrite nonHtmlResp).body.contains 0x3c = true
  ∧ (gatedHtmlrewrite nonHtmlResp).body.contains 0x3e = true := by
  rw [gatedHtmlrewrite_body_passthrough nonHtmlResp nonHtml_not_html]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The html branch strips markup (the text/html wire case) -/

/-- **`rewrite_strips_markup`.** The deployed html-rewrite on the byte literal `<b>hi`
strips the `<b>` tag, yielding `hi` (`[0x68,0x69]`) — the wire tail `68 69` from the
`text/html` curl. Kernel-reduced via `rewriteBytes_eq` (the reference tokenizer); no
`toUTF8`, no `native_decide`. -/
theorem rewrite_strips_markup :
    rewriteBytes [0x3c, 0x62, 0x3e, 0x68, 0x69] = [0x68, 0x69] := by
  rw [rewriteBytes_eq]; rfl

/-- **`gate_html_body`.** For any response the gate DECIDES is HTML, the served body is
exactly the deployed `rewriteBytes r.body` (the gate fires as the deployed stage does). -/
theorem gate_html_body (r : Response) (h : isHtmlCT r.headers = true) :
    (gatedHtmlrewrite r).body = rewriteBytes r.body := by
  rw [gatedHtmlrewrite_html r h]; rfl

/-! ## The gate is correct, and the two branches genuinely differ -/

/-- **`gate_correct`.** For every response the served body is `rewriteBytes r.body` IFF
the declared content is HTML, and the untouched `r.body` otherwise — the deployed gate
strips markup exactly when it should. -/
theorem gate_correct (r : Response) :
    (gatedHtmlrewrite r).body = if isHtmlCT r.headers then rewriteBytes r.body else r.body :=
  gatedHtmlrewrite_correct r

/-- **`gate_branches_differ`.** Non-vacuity: on the SAME `<b>hi` body the passthrough
(non-HTML) branch and the `rewriteBytes` (HTML) branch yield DIFFERENT bodies
(`<b>hi` ≠ `hi`) — the gate genuinely branches on `Content-Type`, so it is neither the
constant identity nor the constant strip. -/
theorem gate_branches_differ :
    (gatedHtmlrewrite nonHtmlResp).body ≠ rewriteBytes nonHtmlResp.body := by
  rw [gatedHtmlrewrite_body_passthrough nonHtmlResp nonHtml_not_html]
  show ([0x3c, 0x62, 0x3e, 0x68, 0x69] : Bytes) ≠ rewriteBytes [0x3c, 0x62, 0x3e, 0x68, 0x69]
  rw [rewrite_strips_markup]
  decide

/-- **`gate_is_deployed_stage`.** The proven gate IS the transform the deployed
`htmlrewriteStage` applies — no drift between this proof and the running pipeline. -/
theorem gate_is_deployed_stage (r : Response) :
    gatedHtmlrewrite r = Reactor.Stage.HtmlRewrite.gatedHtmlTransformResp r :=
  gatedHtmlrewrite_eq_stage r

end Proto.CtGateProven

#print axioms Proto.CtGateProven.gate_passthrough_preserves_markup
#print axioms Proto.CtGateProven.rewrite_strips_markup
#print axioms Proto.CtGateProven.gate_html_body
#print axioms Proto.CtGateProven.gate_correct
#print axioms Proto.CtGateProven.gate_branches_differ
#print axioms Proto.CtGateProven.gate_is_deployed_stage
