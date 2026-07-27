import Reactor.Pipeline

/-!
# Reactor.Stage.RetryAfter — the `Retry-After` response-edge stage (RFC 9110 §10.2.3)

A byte-driving pipeline `Stage` that stamps `Retry-After` onto a `429 (Too Many
Requests)` (RFC 6585 §4) or `503 (Service Unavailable)` (RFC 9110 §15.6.4)
response — the RFC-9110 §10.2.3 back-off signal a well-behaved client reads to
decide how long to wait before retrying. The deployed rate gate
(`Reactor.Stage.Rate`) emits a bare `429` and the proxy `serviceUnavailable503`
a bare `503`; neither carries a `Retry-After`, so a client has no protocol signal
for its back-off interval. This stage closes that edge.

It is a RESPONSE-TRANSFORM stage placed at the HEAD of the deployed chain so its
`onResponse` runs OUTERMOST (last in the response onion): it therefore observes
the FINAL built status (the inner transforms are status-stable) and its stamped
header survives every inner header-map rewrite. The request phase always passes
(`.continue`), so it never gates.

## What is proven here (pure kernel; axioms ⊆ {propext, Quot.sound})

* `retryAfterStage_effect`         — the onion-effect factoring (`pipeline_stage_effect`).
* `retryAfterStage_statusStable`   — the stage never changes the built status (it
  only conditionally adds one header), so it is safe to compose inside a
  status-stable onion.
* `retryAfterStage_429_present` / `_503_present` — for ANY tail and handler whose
  inner build carries status `429` / `503`, the `Retry-After` header genuinely
  appears in the BUILT pipeline output.
* `retryAfterStage_200_absent`     — on a `200` the stage adds NOTHING (no
  spurious `Retry-After` on success): a real conditional, not an always-on stamp.
-/

namespace Reactor.Stage.RetryAfter

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)

/-- The `Retry-After` field name on the wire. -/
def retryAfterName : Bytes := "Retry-After".toUTF8.toList

/-- The deployed back-off value: `1` second (delta-seconds form, RFC 9110
§10.2.3). A conservative default a rate-limited / temporarily-unavailable client
honours; the value is a constant, not caller input. -/
def retryAfterVal : Bytes := "1".toUTF8.toList

/-- The statuses that carry a `Retry-After` back-off signal: `429` (Too Many
Requests, RFC 6585 §4) and `503` (Service Unavailable, RFC 9110 §15.6.4). -/
def needsRetryAfter (status : Nat) : Bool := status == 429 || status == 503

/-- **The `Retry-After` stage.** A response-transform: the request phase always
passes; the response phase adds `Retry-After: 1` iff the accumulated status is a
retry-signalling one (`429`/`503`), else leaves the builder untouched. -/
def retryAfterStage : Stage where
  name := "retry-after"
  onRequest := fun c => .continue c
  onResponse := fun _ b =>
    if needsRetryAfter b.acc.status then b.addHeader (retryAfterName, retryAfterVal) else b

/-- The stage factors through `pipeline_stage_effect`: its `onResponse` wraps the
tail builder (adding its header iff the tail status signals a retry). -/
theorem retryAfterStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (retryAfterStage :: rest) h c
      = (if needsRetryAfter (runPipeline rest h c).acc.status
         then (runPipeline rest h c).addHeader (retryAfterName, retryAfterVal)
         else (runPipeline rest h c)) :=
  pipeline_stage_effect retryAfterStage rest h c c rfl

/-- **Status-stable.** The stage never changes the built status — it either adds
one header (status untouched) or is the identity. So it composes safely inside a
status-stable onion (`pipeline_gate_status`). -/
theorem retryAfterStage_statusStable : Stage.statusStable retryAfterStage := by
  intro c b
  show ((if needsRetryAfter b.acc.status
          then b.addHeader (retryAfterName, retryAfterVal) else b).build).status = b.build.status
  split <;> simp [build_addHeader]

/-- **Byte-effect on a `429`.** When the inner fold builds a `429`, the
`Retry-After` header genuinely appears in the finalized pipeline output — for ANY
tail and handler. This is the deployed rate-limit response gaining its RFC-9110
back-off signal. -/
theorem retryAfterStage_429_present (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (h429 : (runPipeline rest h c).acc.status = 429) :
    (retryAfterName, retryAfterVal)
      ∈ ((runPipeline (retryAfterStage :: rest) h c).build).headers := by
  rw [retryAfterStage_effect, h429]
  simp only [needsRetryAfter, if_true, build_addHeader, Nat.reduceBEq, Bool.or_true,
    Bool.true_or, List.mem_append]
  exact Or.inr (List.mem_singleton.mpr rfl)

/-- **Byte-effect on a `503`.** The proxy `503 (Service Unavailable)` gains its
back-off signal too. -/
theorem retryAfterStage_503_present (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (h503 : (runPipeline rest h c).acc.status = 503) :
    (retryAfterName, retryAfterVal)
      ∈ ((runPipeline (retryAfterStage :: rest) h c).build).headers := by
  rw [retryAfterStage_effect, h503]
  simp only [needsRetryAfter, if_true, build_addHeader, Nat.reduceBEq, Bool.or_true,
    Bool.true_or, List.mem_append]
  exact Or.inr (List.mem_singleton.mpr rfl)

/-- **No spurious back-off on success.** On a `200` the stage adds NOTHING: the
built output is byte-identical to the inner fold's. A real conditional edge, not
an always-on stamp — a `200 OK` never tells the client to back off. -/
theorem retryAfterStage_200_absent (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (h200 : (runPipeline rest h c).acc.status = 200) :
    (runPipeline (retryAfterStage :: rest) h c).build = (runPipeline rest h c).build := by
  rw [retryAfterStage_effect, h200]
  simp [needsRetryAfter]

end Reactor.Stage.RetryAfter
