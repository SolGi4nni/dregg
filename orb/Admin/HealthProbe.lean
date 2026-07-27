/-
Admin.HealthProbe — the proven format/behavior behind the operator health probe
(`GET /healthz`, `crates/dataplane/src/admin.rs`).

The deployed dataplane answers a k8s-style probe on a SINGLE route, `/healthz`:

  * `200 OK`               with body `ok\n`        while the host is serving;
  * `503 Service Unavailable` with body `draining\n` once shutdown has begun OR
                              an operator drain is in progress.

The readiness distinction a fronting balancer / kubelet reads is carried entirely
by the STATUS CODE (200 = ready, 503 = not-ready), exactly as the Rust
`serving()` branch selects — the body is human text, the code is the signal. The
probe is a pure read of the host's `serving()` state: it never touches the
request body and never mutates host state (idempotent).

This file models the response builder faithfully to the Rust `http_response`
helper — `Content-Length` set to the actual body length, `Connection: close` —
and proves:

  * `health_probe_wellformed` — a probe response is a 200 (serving) or 503
    (draining) with HONEST framing (declared `Content-Length` = body length),
    `Connection: close`, and the body emitted verbatim as the wire suffix; the
    serving/draining branches carry exactly `ok\n` / `draining\n`;
  * `readiness_distinguishes` — the readiness signal is the status code: serving
    yields 200, draining yields 503, and 200 ≠ 503 (the two are distinguishable),
    with `statusCode = 200 ↔ serving`;
  * `health_no_side_effect` — a probe leaves host state unchanged and reads no
    request body (its output is independent of the request body), so it is
    idempotent: probing twice is the same as probing once.

Non-vacuity: a builder that declares the WRONG `Content-Length` is shown to break
honest framing, and a "readiness" that always answers 200 is shown to be unable
to signal not-ready — so both the framing and the status-code distinction are
load-bearing, not decorative.

DEPLOYED-FORMAT NOTE: the deployed route is `/healthz` (one endpoint, code-signalled
readiness), NOT three separate k8s paths `/health` `/ready` `/live`. This file
proves the format the engine actually emits.
-/

namespace Admin
namespace HealthProbe

/-! ## The response builder — a faithful model of Rust `http_response` -/

/-- The HTTP reason phrase for a status code, matching the Rust `http_response`
`match status` arms. -/
def reason (status : Nat) : String :=
  if status = 200 then "OK"
  else if status = 404 then "Not Found"
  else if status = 405 then "Method Not Allowed"
  else if status = 503 then "Service Unavailable"
  else "OK"

/-- A serialized HTTP/1.1 response, in the fields the Rust `http_response`
assembles: a status line, a `Content-Type`, a *declared* `Content-Length`, the
`Connection: close` framing flag, and the body bytes. -/
structure WireResponse where
  statusCode : Nat
  reasonPhrase : String
  contentType : String
  declaredContentLength : Nat
  connectionClose : Bool
  body : List UInt8
  deriving Repr, DecidableEq

/-- `buildResponse` mirrors `http_response(status, content_type, body)`: the
declared `Content-Length` is set to the ACTUAL body length, `Connection: close`
is always set, and the reason phrase is looked up from the status. -/
def buildResponse (status : Nat) (ct : String) (body : List UInt8) : WireResponse :=
  { statusCode := status
    reasonPhrase := reason status
    contentType := ct
    declaredContentLength := body.length
    connectionClose := true
    body := body }

/-- The response head, serialized exactly as the Rust `format!` does: status line,
`Content-Type`, `Content-Length` (the DECLARED length interpolated verbatim),
`Connection: close`, then the blank-line terminator. -/
def headBytes (r : WireResponse) : List UInt8 :=
  (s!"HTTP/1.1 {r.statusCode} {r.reasonPhrase}\r\nContent-Type: {r.contentType}\r\nContent-Length: {r.declaredContentLength}\r\nConnection: close\r\n\r\n").toUTF8.toList

/-- The full wire: the head followed by the body bytes. -/
def serialize (r : WireResponse) : List UInt8 := headBytes r ++ r.body

/-! ## The health probe response -/

/-- The probe body: `ok\n` while serving, `draining\n` once draining. -/
def healthzBody : Bool → List UInt8
  | true  => [111, 107, 10]                                  -- "ok\n"
  | false => [100, 114, 97, 105, 110, 105, 110, 103, 10]     -- "draining\n"

/-- The probe status: `200` while serving, `503` once draining — the Rust
`if serving() { 200 } else { 503 }` branch. -/
def healthzStatus : Bool → Nat
  | true  => 200
  | false => 503

/-- The full `/healthz` response for a given `serving` state. -/
def healthzResponse (serving : Bool) : WireResponse :=
  buildResponse (healthzStatus serving) "text/plain; charset=utf-8" (healthzBody serving)

/-! ## Well-formedness of the probe response -/

/-- **Honest framing.** The builder always declares a `Content-Length` equal to
the actual body length — the response is self-framing, a reader can trust the
declared length to consume exactly the body. -/
theorem buildResponse_honest_framing (status : Nat) (ct : String) (body : List UInt8) :
    (buildResponse status ct body).declaredContentLength = body.length := rfl

/-- **The body is the emitted suffix.** The serialized wire ends with the body
bytes verbatim (the head is the prefix) — nothing rewrites the body on the way
out. -/
theorem serialize_body_suffix (r : WireResponse) : ∃ pre, serialize r = pre ++ r.body :=
  ⟨headBytes r, rfl⟩

/-- **Self-framing length.** The total wire length is the head length plus the
body length: exactly the declared body count of bytes follows the head. -/
theorem serialize_length (r : WireResponse) :
    (serialize r).length = (headBytes r).length + r.body.length := by
  simp [serialize, List.length_append]

/-- **The probe response is well-formed.** For either serving state, the response
is a 200 (serving) or 503 (draining) with honest `Content-Length`, the
`Connection: close` framing, the body emitted as the wire suffix, and the exact
serving/draining body (`ok\n` / `draining\n`). -/
theorem health_probe_wellformed (serving : Bool) :
    let r := healthzResponse serving
    (r.statusCode = 200 ∨ r.statusCode = 503)
      ∧ r.declaredContentLength = r.body.length
      ∧ r.connectionClose = true
      ∧ (∃ pre, serialize r = pre ++ r.body)
      ∧ (serving = true  → r.statusCode = 200 ∧ r.body = [111, 107, 10])
      ∧ (serving = false → r.statusCode = 503
            ∧ r.body = [100, 114, 97, 105, 110, 105, 110, 103, 10]) := by
  cases serving with
  | true =>
      refine ⟨Or.inl rfl, rfl, rfl, ⟨_, rfl⟩, ?_, ?_⟩
      · intro _; exact ⟨rfl, rfl⟩
      · intro h; exact absurd h (by decide)
  | false =>
      refine ⟨Or.inr rfl, rfl, rfl, ⟨_, rfl⟩, ?_, ?_⟩
      · intro h; exact absurd h (by decide)
      · intro _; exact ⟨rfl, rfl⟩

/-! ## Readiness is carried by the status code -/

/-- **Readiness distinguishes by status code.** Serving yields 200, draining
yields 503, and 200 ≠ 503 — the status code is a genuine ready/not-ready signal a
balancer or kubelet reads. -/
theorem readiness_distinguishes :
    (healthzResponse true).statusCode = 200
      ∧ (healthzResponse false).statusCode = 503
      ∧ (healthzResponse true).statusCode ≠ (healthzResponse false).statusCode := by
  decide

/-- **Ready iff serving.** The 200 status appears exactly when the host is
serving; otherwise (draining) it is 503 — the mapping from state to readiness
code is total and faithful. -/
theorem status_iff_serving (serving : Bool) :
    (healthzResponse serving).statusCode = 200 ↔ serving = true := by
  cases serving <;> simp [healthzResponse, buildResponse, healthzStatus]

/-- The serving and draining responses are genuinely different wire responses. -/
theorem healthz_responses_differ : healthzResponse true ≠ healthzResponse false := by
  decide

/-! ## The probe has no side effect and reads no request body -/

/-- A probe as a host transition: given the host `serving` state and an arbitrary
request body, it returns the UNCHANGED state and the response — a pure read.
Mirrors the Rust handler, which computes `serving()` and never reads the request
body for `/healthz`. -/
def probe (serving : Bool) (_reqBody : List UInt8) : Bool × WireResponse :=
  (serving, healthzResponse serving)

/-- **No side effect.** A probe leaves the host `serving` state unchanged. -/
theorem probe_no_side_effect (serving : Bool) (reqBody : List UInt8) :
    (probe serving reqBody).1 = serving := rfl

/-- **Reads no request body.** The probe's output is independent of the request
body — two different request bodies yield the identical response. -/
theorem probe_ignores_request_body (serving : Bool) (b1 b2 : List UInt8) :
    probe serving b1 = probe serving b2 := rfl

/-- **Idempotent.** Because the probe neither reads the body nor mutates state,
probing twice (feeding the resulting state back in) is the same as probing once.
This is the composite `health_no_side_effect` guarantee. -/
theorem health_no_side_effect (serving : Bool) (b1 b2 : List UInt8) :
    (probe serving b1).1 = serving ∧ probe serving b1 = probe serving b2 ∧
      probe (probe serving b1).1 b2 = probe serving b1 := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Non-vacuity — mutants that violate the proven properties -/

/-- A mutant builder that declares a `Content-Length` one byte too long. -/
def buildResponseBadLen (status : Nat) (ct : String) (body : List UInt8) : WireResponse :=
  { (buildResponse status ct body) with declaredContentLength := body.length + 1 }

/-- **Non-vacuity of honest framing.** The mutant builder breaks self-framing:
its declared `Content-Length` no longer equals the body length, so a reader
would either truncate or hang waiting for a byte that never comes — the exact
failure honest framing forbids. -/
theorem buildResponseBadLen_violates_framing :
    ∃ status ct body,
      (buildResponseBadLen status ct body).declaredContentLength ≠ (body : List UInt8).length := by
  refine ⟨200, "text/plain; charset=utf-8", [111, 107, 10], ?_⟩
  decide

/-- A mutant probe status that ALWAYS answers ready (200), even while draining. -/
def brokenReadyStatus : Bool → Nat := fun _ => 200

/-- **Non-vacuity of the readiness distinction.** The always-ready mutant cannot
distinguish serving from draining — its status code is the same in both states,
so a balancer could never bleed traffic away during a drain. The real
status-code branch is load-bearing. -/
theorem brokenReadyStatus_cannot_distinguish :
    brokenReadyStatus true = brokenReadyStatus false := rfl

/-- Concretely, the real probe's serving/draining status codes DO differ where
the mutant's coincide — pinning the difference the mutant erases. -/
theorem real_vs_broken_readiness :
    healthzStatus true ≠ healthzStatus false ∧
      brokenReadyStatus true = brokenReadyStatus false := by
  exact ⟨by decide, rfl⟩

end HealthProbe
end Admin
