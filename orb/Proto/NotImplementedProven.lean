/-
# Proto.NotImplementedProven — the DEPLOYED `501 Not Implemented` on an unknown method

PROVE-WHAT-RUNS for the RFC 7231 §4.1 method-registry gate. The deployed default serve
crosses `drorb_serve_metered_conformant` = `Reactor.ServeConformant.conformantServe`, whose
front gate is the proven `Reactor.Stage.RequestValidation.validationStage`. A request with a
recognized HTTP version but an UNRECOGNIZED method is short-circuited with
`notImplementedResp` — status `501`, reason `Not Implemented` — BEFORE it can be served as a
`GET` (the RFC 7231 §4.1 MUST NOT the wave-4 conformance probe named as B2).

Curl-confirmed against the deployed `dataplane` binary (io_uring, port 8097):

    $ printf 'FROB /static/app.js HTTP/1.1\r\nHost: x\r\n\r\n' | nc 127.0.0.1 8097
    HTTP/1.1 501 Not Implemented                  ← proven here (status + reason bytes)
    Connection: keep-alive
    Date: Mon, 01 Jan 2024 00:00:00 GMT
    …

Contrast the sibling `Proto.TraceMaxForwardsProven`: `TRACE` is a RECOGNIZED method, so it
is served (not `501`ed); `FROB` is not, so it is refused here. The gate discriminates
exactly on `knownMethods` membership.

Theorems (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound} — no `native_decide`,
no `Lean.ofReduceBool`):

  * `notimpl_status_501` — the deployed refusal's status is `501`.
  * `notimpl_reason_wire_bytes` — its reason phrase is exactly the 15 bytes of
    `"Not Implemented"` (pinned via the `Shortcuts.ba_toList_eq` bridge — pure-kernel `decide`),
    the phrase the wire's status line carries.
  * `notimpl_body_wire_bytes` — the refusal's body is exactly `"not implemented\n"`.
  * `frob_not_known` — the concrete method `"FROB"` really is unrecognized.
  * `deployed_notimpl_rejects` — a concrete recognized-version `FROB` request drives the
    DEPLOYED gate `validationStage.onRequest` to `.respond notImplementedResp` (non-vacuous).
-/

import Reactor.Stage.RequestValidation
import Proto.Kernel.Shortcuts

namespace Proto.NotImplementedProven

open Proto (Bytes Request)
open Proto.Kernel
open Reactor.Stage.RequestValidation
  (notImplementedResp strBytes versionSupported methodKnown httpV11
   validationStage validationStage_rejects_unknown_method)

/-! ## The deployed `501` response shape -/

/-- **`notimpl_status_501`.** The deployed unknown-method refusal is status `501`. -/
theorem notimpl_status_501 : notImplementedResp.status = 501 := rfl

/-- **`notimpl_reason_wire_bytes`.** The refusal's reason phrase is exactly the 15 bytes of
`"Not Implemented"` — pinned through the `Shortcuts.ba_toList_eq` bridge (pure-kernel `decide`, no
`native_decide`), matching the wire status line. -/
theorem notimpl_reason_wire_bytes :
    notImplementedResp.reason =
      [78, 111, 116, 32, 73, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100] := by
  simp only [notImplementedResp, strBytes, Shortcuts.ba_toList_eq]; decide

/-- **`notimpl_body_wire_bytes`.** The refusal's body is exactly the 16 bytes of
`"not implemented\n"`. -/
theorem notimpl_body_wire_bytes :
    notImplementedResp.body =
      [110, 111, 116, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 10] := by
  simp only [notImplementedResp, strBytes, Shortcuts.ba_toList_eq]; decide

/-! ## The deployed gate genuinely fires on an unknown method (non-vacuous witness) -/

/-- A concrete `FROB /static/app.js HTTP/1.1` request — a recognized version, unknown
method. -/
def frobReq : Request :=
  { method := [70, 82, 79, 66], target := [47],
    version := httpV11, headers := [] }

def frobCtx : Reactor.Pipeline.Ctx := { input := [], req := frobReq }

/-- The witness version is recognized (so the gate reaches the method check). -/
theorem frobReq_version_ok : versionSupported frobReq.version = true := by decide

/-- **`frob_not_known`.** The witness method `"FROB"` is NOT in the recognized set — so the
gate refuses it rather than serving it as a `GET`. -/
theorem frob_not_known : methodKnown frobReq.method = false := by decide

/-- **`deployed_notimpl_rejects`.** The DEPLOYED front gate `validationStage` — the same
gate `conformantServe` runs — answers the concrete `FROB` request with `.respond
notImplementedResp`. Non-vacuous: a genuine unknown-method request drives the `501`. -/
theorem deployed_notimpl_rejects :
    validationStage.onRequest frobCtx = .respond notImplementedResp :=
  validationStage_rejects_unknown_method frobCtx frobReq_version_ok frob_not_known

end Proto.NotImplementedProven

#print axioms Proto.NotImplementedProven.notimpl_status_501
#print axioms Proto.NotImplementedProven.notimpl_reason_wire_bytes
#print axioms Proto.NotImplementedProven.notimpl_body_wire_bytes
#print axioms Proto.NotImplementedProven.frobReq_version_ok
#print axioms Proto.NotImplementedProven.frob_not_known
#print axioms Proto.NotImplementedProven.deployed_notimpl_rejects
