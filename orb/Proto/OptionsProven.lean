import Reactor.Serve
import Reactor.Deploy
import Reactor.Stage.MethodFilter

/-!
# Proto.OptionsProven — the DEPLOYED behavior for an `OPTIONS` request (ledger row `h1.options`)

**PROVE-WHAT-RUNS finding: ledger row `h1.options` ("OPTIONS + Allow (deployed)") is
FALSE-DEPLOYED** — the same class of miscredit already caught for `sse.1` / `dn.1`.
The claimed behavior (an `OPTIONS` request answered `2xx` with an `Allow:` header
advertising the supported methods, and *no body*) is **not** what the running
`drorb_serve` emits. This file proves the mechanism of the false-deployment; the
ground-truth `curl` (below, re-run by the verifier) confirms the wire.

## Ground truth (curl against the running dataplane, `--io uring`, port 9147)

```
$ curl -sS -i -X OPTIONS http://127.0.0.1:9147/
HTTP/1.1 404 Not Found
Connection: keep-alive
Strict-Transport-Security: max-age=31536000; includeSubDomains; preload
X-Frame-Options: DENY
X-Content-Type-Options: nosniff
Referrer-Policy: no-referrer
Server: drorb
x-upstream: 1572395042
x-corr: 79.80.84.73.79.78.83.32.47.…            (decimal echo of the raw request bytes)
Content-Length: 9

not found
```

`GET /` returns the byte-identical response — same `404`, same 9-byte `not found`
body, same headers — save the `x-corr` echo of the request line. The deployed serve
is **method-blind**: `Reactor.App.handle demoAppConfig` routes purely by target path
(`Route.Match.bestMatch` over `targetSegments req.target`) and never special-cases
`OPTIONS`. There is **no** `Allow:` header anywhere on the wire, and the response
**carries a body**, so BOTH requested theorems are false of the deployment:

  * `options_allow`   — FALSE: the deployed `OPTIONS` response has no `Allow` header.
  * `options_no_body` — FALSE: the deployed `OPTIONS` response has a 9-byte body.

## The mechanism (what is proven here)

The one stage that would emit an `Allow` header —
`Reactor.Stage.MethodFilter.methodFilterStage`, which answers a *disallowed* method
`405 Method Not Allowed` + `Allow: GET, POST, HEAD, OPTIONS` (RFC 9110 §10.2.1,
§15.5.6) — is proven in isolation but is **NOT wired into the deployed pipeline**
`Reactor.Deploy.deployStagesFull2`. And even that gate never emits a `2xx`+`Allow`
for `OPTIONS`: an allowed method (`OPTIONS` is on its allow-list) merely `.continue`s
to the method-blind handler, which routes by path (the `/` request lands on the
virtual-host `anyHost` catch-all `404`, exactly the wire above).

  * `deployed_omits_method_filter` — the `Allow`-carrying gate is ABSENT from the
    deployed stage list (every deployed stage has a different `name`), so its
    method-advertising logic never runs on the deployed path.
  * `methodfilter_would_advertise` / `methodfilter_advertises_options` — for the
    record, that undeployed gate DOES carry a genuine `405` + an `Allow` header
    listing the four methods (incl. `OPTIONS`). This establishes the finding is a
    real *omission* of existing, proven code — not the absence of any such code.
  * `opt_get_differ` — the `OPTIONS /` and `GET /` requests genuinely differ (distinct
    method tokens), yet the ground-truth curls show identical responses: the wire
    method-blindness is not a comparison of a request to itself.

## Not proven in-kernel (deliberately)

The wire facts (`OPTIONS /` ⇒ `404`, empty header list, 9-byte body, method-blind)
are established EMPIRICALLY by the curl above, re-run by the verifier. Proving them
in-kernel would require reducing `Reactor.App.handle` from raw request bytes, i.e.
evaluating `String.splitOnAux` (well-founded recursion) inside `targetSegments` — a
String-lemma development the codebase deliberately avoids, and one that
`native_decide` (the only shortcut) is barred by the merge gate. The finding does not
hinge on it: the row's claim is refuted by the wire + the structural omission proven
here.
-/

namespace Proto.OptionsProven

open Proto (Request)

/-! ## The concrete deployed requests (the ground-truth curl inputs, explicit bytes) -/

/-- `OPTIONS /` — method token `OPTIONS` (`[79,80,84,73,79,78,83]`), target `/`
(`[47]`). The exact shape the reactor dispatches for
`curl -X OPTIONS http://127.0.0.1:9147/`. -/
def optReqRoot : Request :=
  { method := [79, 80, 84, 73, 79, 78, 83], target := [47], version := [], headers := [] }

/-- The comparison `GET /` request — identical to `optReqRoot` EXCEPT the method token
is `GET` (`[71,69,84]`). -/
def getReqRoot : Request :=
  { optReqRoot with method := [71, 69, 84] }

/-- **`opt_get_differ`.** The two requests genuinely differ (distinct method tokens),
so the method-blindness the ground-truth curls exhibit is a real invariance, not a
request compared to itself. -/
theorem opt_get_differ : optReqRoot ≠ getReqRoot := by decide

/-! ## The `Allow`-carrying gate exists but is NOT in the deployed pipeline -/

/-- **`deployed_omits_method_filter`.** The only stage that advertises methods —
`Reactor.Stage.MethodFilter.methodFilterStage` (name `"method-filter"`) — is ABSENT
from the deployed pipeline `Reactor.Deploy.deployStagesFull2`: every deployed stage
carries a different `name`. So the `Allow`-emitting logic never runs on the deployed
path — which is why the wire (above) has no `Allow` header. -/
theorem deployed_omits_method_filter :
    ∀ s ∈ Reactor.Deploy.deployStagesFull2,
      s.name ≠ Reactor.Stage.MethodFilter.methodFilterStage.name := by
  decide

/-- **`methodfilter_would_advertise`.** For the record: the *undeployed* method gate,
had it been wired in, answers a disallowed method a genuine `405` carrying an `Allow`
header (RFC 9110 §10.2.1). The finding is thus a real *omission* — the advertising
code exists and is proven — not merely that no such code was written. -/
theorem methodfilter_would_advertise :
    Reactor.Stage.MethodFilter.methodNotAllowed.status = 405
  ∧ (Reactor.Stage.MethodFilter.allowName, Reactor.Stage.MethodFilter.allowValue)
      ∈ Reactor.Stage.MethodFilter.methodNotAllowed.headers := by
  refine ⟨rfl, ?_⟩
  simp [Reactor.Stage.MethodFilter.methodNotAllowed]

/-- **`methodfilter_advertises_options`.** The (undeployed) gate's `Allow` value is
exactly `GET, POST, HEAD, OPTIONS` — it advertises `OPTIONS` among the supported
methods. This is the header value the deployed serve would have to emit to satisfy
row `h1.options`, and pointedly does not (`deployed_omits_method_filter`). -/
theorem methodfilter_advertises_options :
    Reactor.Stage.MethodFilter.allowValue
      = Reactor.Stage.MethodFilter.strBytes "GET, POST, HEAD, OPTIONS" := rfl

/-! ## Axiom audit (fully-qualified) -/

#print axioms Proto.OptionsProven.opt_get_differ
#print axioms Proto.OptionsProven.deployed_omits_method_filter
#print axioms Proto.OptionsProven.methodfilter_would_advertise
#print axioms Proto.OptionsProven.methodfilter_advertises_options

end Proto.OptionsProven
