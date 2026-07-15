/-
# Proto.RetryAfterProven — the DEPLOYED `429` carries NO `Retry-After` (an honest RFC gap)

PROVE-WHAT-RUNS for the rate-limit refusal. The deployed HTTP/1.1 fold
`Reactor.Deploy.deployStagesFull2` WIRES the real token-bucket gate
`Reactor.Stage.Rate.rateStage` (a genuinely low burst limit, `rateCap = 8`): a burst
past the limit on one kept-alive connection short-circuits with `429 Too Many Requests`.

RFC 9110 §15.5.21 / RFC 6585 §4 say a `429` response **SHOULD** include a `Retry-After`
header telling the client how long to wait. The deployed gate does **not**: its refusal
is `error4xx 429 reason429 tooManyBody`, whose own header list is EMPTY, and no deployed
stage adds a `Retry-After` on the response phase. So the running `429` ships without the
advisory — a real, honest omission, same class of finding as `Proto.OptionsProven`.

## Ground truth — curl against the running dataplane (io_uring, port 8097)

A burst of 12 `GET /static/app.js` on ONE keep-alive connection: the first 8 answer `200`,
the rest answer `429`. The full `429` header block (re-run by the verifier):

```
$ curl -s -D - -o /dev/null $(yes http://127.0.0.1:8097/static/app.js | head -12)
…
HTTP/1.1 429 Too Many Requests
Connection: keep-alive
Strict-Transport-Security: max-age=31536000; includeSubDomains; preload
X-Frame-Options: DENY
X-Content-Type-Options: nosniff
Referrer-Policy: no-referrer
Server: drorb
x-upstream: 1572395042
x-corr: …
Content-Length: 20                          ← body = "rate limit exceeded\n" (20 bytes)
```

There is **no** `Retry-After` field anywhere on the wire.

## What is proven here (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

  * `rate_deployed` — the `429`-producing gate `rateStage` really is an element of the
    deployed pipeline `deployStagesFull2` (the refusal is on the default request path).
  * `resp429_status_429` / `resp429_body` — the gate's refusal is status `429` with body
    exactly `"rate limit exceeded\n"` (the wire's `Content-Length: 20`).
  * `resp429_headers_empty` — the gate's `429` carries NO headers of its own — so it
    attaches no `Retry-After`.
  * `resp429_no_retry_after` — for EVERY value `v`, `(Retry-After, v)` is absent from the
    gate's `429` header list: the advisory is genuinely not emitted by the refusal.
  * `retry_after_wire_bytes` — the exact bytes of the `"Retry-After"` name that is ABSENT
    (pinned via `Shortcuts.ba_toList_eq`, pure-kernel `decide`; no `native_decide`).

## Not proven in-kernel (deliberately)

That NO later deployed stage re-introduces a `Retry-After` on the response phase is
established EMPIRICALLY by the curl above (the full `429` block, re-run by the verifier),
not by reducing the whole 14-stage response fold in-kernel. The finding does not hinge on
it: the refusal originates header-less at `rateStage`, and the wire confirms none is added.
-/

import Reactor.Stage.Rate
import Reactor.Deploy
import Proto.Kernel.Shortcuts

namespace Proto.RetryAfterProven

open Reactor.Stage.Rate
open Proto (Bytes)
open Proto.Kernel

/-- The `Retry-After` header name that RFC 9110 §15.5.21 recommends on a `429` — and that
the deployed gate does NOT emit. -/
def retryAfterName : Bytes := "Retry-After".toUTF8.toList

/-! ## The `429` gate is on the DEPLOYED path -/

/-- **`rate_deployed`.** The `429`-producing rate-limit gate `rateStage` really is an
element of the deployed HTTP/1.1 fold `deployStagesFull2` — so the refusal (and its
missing `Retry-After`) is on the default request path, not a side model. -/
theorem rate_deployed : rateStage ∈ Reactor.Deploy.deployStagesFull2 := by
  unfold Reactor.Deploy.deployStagesFull2
  repeat first
    | exact List.mem_cons_self _ _
    | apply List.mem_cons_of_mem

/-! ## The refusal is status `429`, header-less, with the wire body -/

/-- **`resp429_status_429`.** The gate's refusal carries status `429` (the wire's
`HTTP/1.1 429 Too Many Requests`). -/
theorem resp429_status_429 : resp429.status = 429 := rfl

/-- **`resp429_body`.** The refusal body is exactly `"rate limit exceeded\n"` — 20 bytes,
matching the wire's `Content-Length: 20`. -/
theorem resp429_body : resp429.body = "rate limit exceeded\n".toUTF8.toList := rfl

/-- The refusal body is 20 bytes long (pinned via `Shortcuts.ba_toList_eq`, pure-kernel). -/
theorem resp429_body_len : resp429.body.length = 20 := by
  rw [resp429_body]; simp only [Shortcuts.ba_toList_eq]; decide

/-- **`resp429_headers_empty`.** The gate's `429` carries NO headers of its own — so it
attaches no `Retry-After`. Definitional (`error4xx` sets `headers := []`). -/
theorem resp429_headers_empty : resp429.headers = [] := rfl

/-! ## The `Retry-After` advisory is genuinely absent from the refusal -/

/-- **`resp429_no_retry_after`.** For EVERY value `v`, the pair `(Retry-After, v)` is NOT a
member of the gate's `429` header list: the RFC-recommended advisory is not emitted by the
refusal that the running dataplane produces (curl-confirmed: no `Retry-After` on the wire
`429`). -/
theorem resp429_no_retry_after (v : Bytes) : (retryAfterName, v) ∉ resp429.headers := by
  rw [resp429_headers_empty]; exact List.not_mem_nil _

/-! ## The exact bytes of the absent name -/

/-- **`retry_after_wire_bytes`.** The `"Retry-After"` name whose header is ABSENT from the
deployed `429` has exactly these bytes — pinned through `Shortcuts.ba_toList_eq` (pure-kernel
`decide`, no `native_decide`). -/
theorem retry_after_wire_bytes :
    retryAfterName = [82, 101, 116, 114, 121, 45, 65, 102, 116, 101, 114] := by
  simp only [retryAfterName, Shortcuts.ba_toList_eq]; decide

end Proto.RetryAfterProven

#print axioms Proto.RetryAfterProven.rate_deployed
#print axioms Proto.RetryAfterProven.resp429_status_429
#print axioms Proto.RetryAfterProven.resp429_body
#print axioms Proto.RetryAfterProven.resp429_body_len
#print axioms Proto.RetryAfterProven.resp429_headers_empty
#print axioms Proto.RetryAfterProven.resp429_no_retry_after
#print axioms Proto.RetryAfterProven.retry_after_wire_bytes
