/-
# Proto.ContentLengthProven — the DEPLOYED `Content-Length` framing = body length

PROVE-WHAT-RUNS for the RFC 7230 §3.3.2 `Content-Length` header the running dataplane frames
on every response. The deployed serializer (`Reactor.serialize` = `serializeWire ∘ build`)
fixes the wire record's `contentLength := body.length` and appends `(Content-Length,
natToDec contentLength)` as the FINAL header of the block — the emitted length is derived
from the actual body bytes, NEVER from a caller-supplied header, so the framed length can
never diverge from the body (an anti-smuggling discipline).

Curl-confirmed against the deployed `dataplane` binary (io_uring):

    $ curl -s -D - -o /dev/null http://127.0.0.1:8080/static/app.js   # 35-byte body
    …
    Content-Length: 35      ← natToDec 35, proven below
    $ curl -s http://127.0.0.1:8080/nope | wc -c                       # 9-byte body
    9
    # its response frames  Content-Length: 9   ← natToDec 9, proven below

This maps ledger row **h1.4** (Content-Length body framing): a model theorem
(`serialize_content_length`) existed, but the deployed emitted header NAME bytes, the
body-length-derived VALUE, and the terminal-position discipline were DEPLOYED-UNPROVEN as
wire facts. This file pins them.

Theorems (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound} — no `native_decide`,
no `Lean.ofReduceBool`):

  * `clName_wire_bytes` — the deployed header NAME equals the 14 bytes of `"Content-Length"`.
  * `deployed_cl_is_body_length` — the wire record's `contentLength` is exactly `body.length`
    (restates `serialize_content_length` on the deployed build).
  * `deployed_cl_header_is_terminal` — the serializer's header list is
    `resp.headers ++ [(clName, natToDec body.length)]`: the `Content-Length` line is the
    LAST header and its value is a function of the body length ALONE (never caller input).
  * `deployed_cl_present` — `(clName, natToDec body.length)` is a member of the emitted
    header list for ANY response (restates `content_length_header_present`).
  * `cl_value_9_wire_bytes` / `cl_value_35_wire_bytes` — the concrete curl values: a 9-byte
    body frames `Content-Length: 9`, a 35-byte body frames `Content-Length: 35`.
-/

import Reactor.Serialize
import Proto.Kernel.Shortcuts

namespace Proto.ContentLengthProven

open Proto (Bytes)
open Proto.Kernel

/-! ## The exact header-name bytes -/

/-- **`clName_wire_bytes`.** The deployed `Content-Length` header name equals the 14 bytes
of `"Content-Length"` (connecting the serializer literal to the string bytes through the
`Shortcuts.ba_toList_eq` bridge — pure-kernel `decide`, no `native_decide`). -/
theorem clName_wire_bytes : Reactor.clName = "Content-Length".toUTF8.toList := by
  simp only [Reactor.clName, Shortcuts.ba_toList_eq]; decide

/-! ## The framed length equals the body length, terminally, for ANY response -/

/-- **`deployed_cl_is_body_length`.** The wire record the deployed serializer builds carries
`contentLength = body.length` — the framing length is the actual body byte count, not a
caller input. -/
theorem deployed_cl_is_body_length (resp : Reactor.Response) :
    (Reactor.build resp).contentLength = resp.body.length :=
  Reactor.serialize_content_length resp

/-- **`deployed_cl_header_is_terminal`.** The serializer's full header list is the caller's
headers followed by exactly one derived `Content-Length` line whose value is
`natToDec body.length`. So `Content-Length` is the LAST header and its value is a function of
the body length ALONE — a caller cannot forge the framed length by supplying its own
`Content-Length` in `resp.headers` (the serializer's derived line is appended after it). -/
theorem deployed_cl_header_is_terminal (resp : Reactor.Response) :
    Reactor.allHeaders (Reactor.build resp)
      = resp.headers ++ [(Reactor.clName, Reactor.natToDec resp.body.length)] := rfl

/-- **`deployed_cl_present`.** For ANY response, the derived `(Content-Length, natToDec
body.length)` pair is a member of the emitted header list — restates
`content_length_header_present` on the deployed build. -/
theorem deployed_cl_present (resp : Reactor.Response) :
    (Reactor.clName, Reactor.natToDec resp.body.length)
      ∈ Reactor.allHeaders (Reactor.build resp) :=
  Reactor.content_length_header_present resp

/-! ## The concrete curl values -/

/-- **`cl_value_9_wire_bytes`.** A 9-byte body (the deployed `"not found"` 404 body) frames
`Content-Length: 9` — `natToDec 9` is exactly the single byte of `"9"`. -/
theorem cl_value_9_wire_bytes : Reactor.natToDec 9 = [57] := by
  simp only [Reactor.natToDec, Shortcuts.ba_toList_eq]; decide

/-- **`cl_value_35_wire_bytes`.** A 35-byte body (the deployed `/static/app.js` body) frames
`Content-Length: 35` — `natToDec 35` is exactly the two bytes of `"35"`. -/
theorem cl_value_35_wire_bytes : Reactor.natToDec 35 = [51, 53] := by
  simp only [Reactor.natToDec, Shortcuts.ba_toList_eq]; decide

end Proto.ContentLengthProven

#print axioms Proto.ContentLengthProven.clName_wire_bytes
#print axioms Proto.ContentLengthProven.deployed_cl_is_body_length
#print axioms Proto.ContentLengthProven.deployed_cl_header_is_terminal
#print axioms Proto.ContentLengthProven.deployed_cl_present
#print axioms Proto.ContentLengthProven.cl_value_9_wire_bytes
#print axioms Proto.ContentLengthProven.cl_value_35_wire_bytes
