/-
# Proto.StatusLine200Proven — the DEPLOYED `HTTP/1.1 200 OK` status line

PROVE-WHAT-RUNS for the RFC 7230 §3.1.2 **status line** the running dataplane emits as the
FIRST line of every `200` response. The response half of the deployed serve is proven model
code: every response byte is `Reactor.serialize resp`, whose leading line is
`Reactor.statusLine = HTTP-version SP status SP reason`. For a `200 OK` the version token is
the fixed `HTTP/1.1`, the status is `natToDec 200`, and the reason is `Reactor.App.reasonFor
200 = "OK"`. The deployed `/health` route (`.static 200 "ok"`) is answered exactly this way
by `Reactor.App.responseOfHandler`.

Curl-confirmed against the deployed `dataplane` binary (io_uring):

    $ curl -s -D - -o /dev/null http://127.0.0.1:8080/static/app.js
    HTTP/1.1 200 OK          ← proven here (version + status + reason phrase)
    …

The individual response HEADERS on a 200 are pinned by the sibling `Proto.*Proven` files
(`Date`, `Server`, `ETag`, …); NO file pinned the deployed status LINE itself — the HTTP
version token and the `OK` reason phrase were DEPLOYED-UNPROVEN. This maps ledger row
**h1.1** (HTTP/1.1 serve — request line + status line); it pins the status-line half to the
wire bytes.

Theorems (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound} — no `native_decide`,
no `Lean.ofReduceBool`):

  * `http11_wire_bytes` — the deployed HTTP-version token equals the 8 bytes of `"HTTP/1.1"`.
  * `reasonOK_wire_bytes` / `reasonFor_200_wire_bytes` — the `200` reason phrase (both the
    serializer's `reasonOK` and the app's `reasonFor 200`) is exactly the 2 bytes of `"OK"`.
  * `deployed_status_line_200` — for ANY body, the serialized status LINE of a `200 OK`
    response is exactly the bytes of `"HTTP/1.1 200 OK"` (independent of the body — a real
    ∀-quantified wire pin, matching the curl).
  * `health_status_line` — grounding it in the deployed `/health` handler
    (`responseOfHandler (.static 200 body)`): its status line is that same `HTTP/1.1 200 OK`.
-/

import Reactor.App
import Reactor.Serialize
import Proto.Kernel.Shortcuts

namespace Proto.StatusLine200Proven

open Proto (Bytes)
open Proto.Kernel

/-! ## The exact version token and reason phrase -/

/-- **`http11_wire_bytes`.** The deployed HTTP-version token `Reactor.http11` equals the 8
bytes of `"HTTP/1.1"` (connecting the serializer literal to the string bytes through the
`Shortcuts.ba_toList_eq` bridge — pure-kernel `decide`, no `native_decide`). -/
theorem http11_wire_bytes : Reactor.http11 = "HTTP/1.1".toUTF8.toList := by
  simp only [Reactor.http11, Shortcuts.ba_toList_eq]; decide

/-- **`reasonOK_wire_bytes`.** The serializer's `200` reason phrase is exactly `"OK"`. -/
theorem reasonOK_wire_bytes : Reactor.reasonOK = [79, 75] := rfl

/-- **`reasonFor_200_wire_bytes`.** The application layer's reason phrase for `200` is
exactly the 2 bytes of `"OK"` — pinned through `Shortcuts.ba_toList_eq`. -/
theorem reasonFor_200_wire_bytes : Reactor.App.reasonFor 200 = [79, 75] := by
  simp only [Reactor.App.reasonFor, Shortcuts.ba_toList_eq]; decide

/-! ## The deployed 200 status line — for ANY body -/

/-- **`deployed_status_line_200`.** For ANY body, the serialized status LINE of a `200 OK`
response (`Reactor.statusLine` over the built wire record) is exactly the bytes of
`"HTTP/1.1 200 OK"`: the fixed `HTTP/1.1` version, the `200` status rendered by `natToDec`,
and the `OK` reason. Body-independent — the status line is a constant wire prefix. -/
theorem deployed_status_line_200 (body : Bytes) :
    Reactor.statusLineOf { status := 200, reason := Reactor.App.reasonFor 200,
                           headers := [], body := body }
      = [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75] := by
  simp only [Reactor.statusLineOf, Reactor.statusLine, Reactor.build, Reactor.http11,
             Reactor.natToDec, Reactor.App.reasonFor, Shortcuts.ba_toList_eq]
  decide

/-- **`health_status_line`.** Grounding the status line in a deployed handler: the `/health`
route is `.static 200 body`, answered by `Reactor.App.responseOfHandler` as
`{status := 200, reason := reasonFor 200, …}`, whose status line is exactly
`"HTTP/1.1 200 OK"` for ANY declared body. -/
theorem health_status_line (body : Bytes) :
    Reactor.statusLineOf (Reactor.App.responseOfHandler (.static 200 body))
      = [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75] :=
  deployed_status_line_200 body

end Proto.StatusLine200Proven

#print axioms Proto.StatusLine200Proven.http11_wire_bytes
#print axioms Proto.StatusLine200Proven.reasonOK_wire_bytes
#print axioms Proto.StatusLine200Proven.reasonFor_200_wire_bytes
#print axioms Proto.StatusLine200Proven.deployed_status_line_200
#print axioms Proto.StatusLine200Proven.health_status_line
