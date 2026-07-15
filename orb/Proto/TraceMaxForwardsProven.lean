/-
# Proto.TraceMaxForwardsProven — the DEPLOYED serve is TRACE-blind (an honest RFC gap)

PROVE-WHAT-RUNS for two related RFC 7231 method behaviors the deployed serve does NOT
implement — same class of honest finding as `Proto.OptionsProven` / `Proto.RetryAfterProven`.

`TRACE` is one of the recognized methods in the deployed front gate
`Reactor.Stage.RequestValidation.knownMethods`, so a `TRACE` request is NOT rejected `501`
(unlike an unknown method) — it clears the gate and is served by the inner serve keyed on
its request-TARGET, exactly as the same-target `GET` is. But RFC 7231 §4.3.8 says a `TRACE`
response SHOULD reflect the received request in a `message/http` body, and §5.1.2 says an
intermediary MUST act on `Max-Forwards`. The deployed serve does NEITHER: it answers a
`TRACE` with the ordinary target response and ignores `Max-Forwards` entirely.

Curl-confirmed against the deployed `dataplane` binary (io_uring, port 8097):

    $ printf 'TRACE /static/app.js HTTP/1.1\r\nHost: x\r\nMax-Forwards: 0\r\n\r\n' \
        | nc 127.0.0.1 8097
    HTTP/1.1 200 OK                               ← served as GET, NOT a TRACE echo
    …
    Content-Type: application/javascript
    Content-Length: 35                            ← the app.js body, not the echoed request

The `TRACE` is answered `200` with the SAME 35-byte `app.js` body a `GET
/static/app.js` returns — `Max-Forwards: 0` changes nothing. No echo, no decrement.

Theorems (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound} — no `native_decide`,
no `Lean.ofReduceBool`):

  * `trace_is_known_method` — `TRACE ∈ knownMethods`: the gate recognizes it (so no `501`).
  * `trace_method_wire_bytes` — the method token is exactly the 5 bytes of `"TRACE"`.
  * `deployed_trace_not_rejected` — the DEPLOYED gate `.continue`s a real `TRACE` request
    (version/method/Host all clear), so it is served, not refused — method-BLIND: the same
    request as `GET` bar the method reaches the identical inner serve.
  * `trace_get_gate_agnostic` — `TRACE` and `GET` are BOTH recognized yet distinct tokens:
    the gate treats them identically, which is exactly why the serve is method-blind.
  * `max_forwards_name_wire_bytes` — the exact bytes of the `"Max-Forwards"` request-header
    field the deployed serve IGNORES (pinned via `Shortcuts.ba_toList_eq`, pure-kernel `decide`).

## Not proven in-kernel (deliberately, per the honest-gap posture)

That NO deployed stage reads/decrements `Max-Forwards` or echoes the request is established
EMPIRICALLY by the curl above (a `TRACE … Max-Forwards: 0` returns the ordinary `200`
body), not by reducing the whole pipeline in-kernel. The in-kernel facts pin WHY: `TRACE`
is a recognized method (so it is served, not `501`ed) and the gate is method-agnostic past
the recognized set.
-/

import Reactor.Stage.RequestValidation
import Proto.Kernel.Shortcuts

namespace Proto.TraceMaxForwardsProven

open Proto (Bytes Request)
open Proto.Kernel
open Reactor.Stage.RequestValidation
  (knownMethods methodKnown versionSupported hostOk mTRACE mGET hostName httpV11
   validationStage validationStage_passes_valid)

/-! ## `TRACE` is a recognized method — so it is served, not `501`ed -/

/-- **`trace_is_known_method`.** `TRACE` is in the deployed gate's recognized-method set,
so a `TRACE` request is NOT refused `501 Not Implemented`. -/
theorem trace_is_known_method : mTRACE ∈ knownMethods := by decide

/-- **`trace_method_wire_bytes`.** The `TRACE` method token is exactly the 5 bytes of
`"TRACE"`. -/
theorem trace_method_wire_bytes : mTRACE = [84, 82, 65, 67, 69] := rfl

/-! ## The deployed gate serves a `TRACE` (method-blind) -/

/-- A concrete `TRACE /static/app.js HTTP/1.1` with a single `Host` header — a real,
gate-valid request. -/
def traceReq : Request :=
  { method := mTRACE,
    target := [47, 115, 116, 97, 116, 105, 99, 47, 97, 112, 112, 46, 106, 115],
    version := httpV11,
    headers := [(hostName, [120])] }

def traceCtx : Reactor.Pipeline.Ctx := { input := [], req := traceReq }

theorem traceReq_version_ok : versionSupported traceReq.version = true := by decide
theorem traceReq_method_ok  : methodKnown traceReq.method = true := by decide
theorem traceReq_host_ok    : hostOk traceReq = true := by decide

/-- **`deployed_trace_not_rejected`.** The DEPLOYED front gate `validationStage` — the same
gate `conformantServe` runs — `.continue`s the `TRACE` request (it clears version/method/
Host), so it is passed to the inner serve keyed on the TARGET, NOT refused. This is the
method-blindness the curl exhibits: the `TRACE` is served the same `200 app.js` a `GET`
would get, with no §4.3.8 echo. -/
theorem deployed_trace_not_rejected :
    ∃ c', validationStage.onRequest traceCtx = .continue c' :=
  ⟨_, validationStage_passes_valid traceCtx traceReq_version_ok traceReq_method_ok
        traceReq_host_ok⟩

/-- **`trace_get_gate_agnostic`.** `TRACE` and `GET` are BOTH recognized methods yet are
distinct tokens: the gate accepts both identically, so nothing downstream distinguishes a
`TRACE` from a `GET` on the same target — the root of the method-blindness. -/
theorem trace_get_gate_agnostic :
    methodKnown mTRACE = true ∧ methodKnown mGET = true ∧ mTRACE ≠ mGET := by
  refine ⟨by decide, by decide, ?_⟩
  decide

/-! ## The ignored `Max-Forwards` field -/

/-- The RFC 7231 §5.1.2 `Max-Forwards` request-header name the deployed serve ignores. -/
def maxForwardsName : Bytes := "Max-Forwards".toUTF8.toList

/-- **`max_forwards_name_wire_bytes`.** The exact bytes of the `"Max-Forwards"` field the
deployed serve neither reads nor decrements — pinned through the `Shortcuts.ba_toList_eq` bridge
(pure-kernel `decide`, no `native_decide`). Curl: `TRACE … Max-Forwards: 0` still returns
the ordinary `200` body, so the field has no effect on the wire. -/
theorem max_forwards_name_wire_bytes :
    maxForwardsName =
      [77, 97, 120, 45, 70, 111, 114, 119, 97, 114, 100, 115] := by
  simp only [maxForwardsName, Shortcuts.ba_toList_eq]; decide

end Proto.TraceMaxForwardsProven

#print axioms Proto.TraceMaxForwardsProven.trace_is_known_method
#print axioms Proto.TraceMaxForwardsProven.trace_method_wire_bytes
#print axioms Proto.TraceMaxForwardsProven.traceReq_version_ok
#print axioms Proto.TraceMaxForwardsProven.traceReq_method_ok
#print axioms Proto.TraceMaxForwardsProven.traceReq_host_ok
#print axioms Proto.TraceMaxForwardsProven.deployed_trace_not_rejected
#print axioms Proto.TraceMaxForwardsProven.trace_get_gate_agnostic
#print axioms Proto.TraceMaxForwardsProven.max_forwards_name_wire_bytes
