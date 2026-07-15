/-
# Proto.BadVersionProven — the DEPLOYED `505 HTTP Version Not Supported` rejection

PROVE-WHAT-RUNS for the RFC 7230 §2.6 / §3.1 version gate. The deployed default serve
crosses `drorb_serve_metered_conformant` = `Reactor.ServeConformant.conformantServe`, whose
front gate is the proven `Reactor.Stage.RequestValidation.validationStage`. A request whose
HTTP version token is not `HTTP/1.1` or `HTTP/1.0` is short-circuited with
`badVersionResp` — status `505`, reason `HTTP Version Not Supported`.

Curl-confirmed against the deployed `dataplane` binary (io_uring, port 8097):

    $ printf 'GET /static/app.js HTTP/9.9\r\nHost: x\r\n\r\n' | nc 127.0.0.1 8097
    HTTP/1.1 505 HTTP Version Not Supported       ← proven here (status + reason bytes)
    Connection: close                             ← the FINDING (see below)
    Date: Mon, 01 Jan 2024 00:00:00 GMT
    …

Theorems (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound} — no `native_decide`,
no `Lean.ofReduceBool`):

  * `badversion_status_505` — the deployed refusal's status is `505`.
  * `badversion_reason_wire_bytes` — its reason phrase is exactly the 26 bytes of
    `"HTTP Version Not Supported"` (pinned via the `Shortcuts.ba_toList_eq` bridge — pure-kernel
    `decide`), the phrase the wire's status line carries.
  * `badversion_no_headers` — the `505` response carries NO headers of its OWN.
  * `deployed_badversion_rejects` — a concrete `HTTP/9.9` request drives the DEPLOYED gate
    `validationStage.onRequest` to `.respond badVersionResp` (non-vacuous witness). This is
    the same `validationStage` the deployed `conformantServe` runs as its front gate, so the
    `505` on the wire IS this response, `+ Date` (the wrapper injects `Date` on the reject
    branch — see `Proto.DateHeaderProven` / `Reactor.ServeConformant.addDate`).

## The finding — `Connection: close` on the `505`, `keep-alive` on `400`/`501`

`badVersionResp.headers = []`, so the `Connection: close` on the wire is stamped NOT by the
Lean response but by the host keep-alive layer, which closes the connection ONLY on the
`505` (the version is unparseable, so the framing of any following request on the socket is
untrustworthy) while the `400 Bad Request` and `501 Not Implemented` refusals stay
`Connection: keep-alive` (curl-confirmed). The `505` rejection body itself is header-less;
the connection-close is a host framing decision layered on top.
-/

import Reactor.Stage.RequestValidation
import Proto.Kernel.Shortcuts

namespace Proto.BadVersionProven

open Proto (Bytes Request)
open Proto.Kernel
open Reactor.Stage.RequestValidation
  (badVersionResp strBytes versionSupported validationStage validationStage_rejects_bad_version)

/-! ## The deployed `505` response shape -/

/-- **`badversion_status_505`.** The deployed version-gate refusal is status `505`. -/
theorem badversion_status_505 : badVersionResp.status = 505 := rfl

/-- **`badversion_reason_wire_bytes`.** The refusal's reason phrase is exactly the 26 bytes
of `"HTTP Version Not Supported"` — pinned through the `Shortcuts.ba_toList_eq` bridge (pure-kernel
`decide`, no `native_decide`), matching the wire status line. -/
theorem badversion_reason_wire_bytes :
    badVersionResp.reason =
      [72, 84, 84, 80, 32, 86, 101, 114, 115, 105, 111, 110, 32,
       78, 111, 116, 32, 83, 117, 112, 112, 111, 114, 116, 101, 100] := by
  simp only [badVersionResp, strBytes, Shortcuts.ba_toList_eq]; decide

/-- **`badversion_no_headers`.** The `505` response carries NO headers of its own — the
wire's `Connection: close` is a host framing decision, not part of the Lean response. -/
theorem badversion_no_headers : badVersionResp.headers = [] := rfl

/-! ## The deployed gate genuinely fires on a bad version (non-vacuous witness) -/

/-- A concrete `HTTP/9.9` request — an unsupported version token. -/
def badVersionReq : Request :=
  { method := [71, 69, 84], target := [47],
    version := [72, 84, 84, 80, 47, 57, 46, 57], headers := [] }

/-- The pipeline context for that request. -/
def badVersionCtx : Reactor.Pipeline.Ctx := { input := [], req := badVersionReq }

/-- The witness version really is unsupported (`HTTP/9.9 ∉ {HTTP/1.1, HTTP/1.0}`). -/
theorem badVersionReq_unsupported : versionSupported badVersionReq.version = false := by
  decide

/-- **`deployed_badversion_rejects`.** The DEPLOYED front gate `validationStage` — the same
gate `conformantServe` runs — answers the concrete `HTTP/9.9` request with `.respond
badVersionResp`. Non-vacuous: a genuine unsupported-version request drives the `505`. -/
theorem deployed_badversion_rejects :
    validationStage.onRequest badVersionCtx = .respond badVersionResp :=
  validationStage_rejects_bad_version badVersionCtx badVersionReq_unsupported

end Proto.BadVersionProven

#print axioms Proto.BadVersionProven.badversion_status_505
#print axioms Proto.BadVersionProven.badversion_reason_wire_bytes
#print axioms Proto.BadVersionProven.badversion_no_headers
#print axioms Proto.BadVersionProven.badVersionReq_unsupported
#print axioms Proto.BadVersionProven.deployed_badversion_rejects
