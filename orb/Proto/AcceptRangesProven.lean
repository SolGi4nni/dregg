/-
# Proto.AcceptRangesProven — `Accept-Ranges: bytes` on the DEPLOYED static handler (plain 200)

PROVE-WHAT-RUNS for the range-support advertisement the running dataplane stamps on the
FULL `200 (OK)` static response — the plain `GET` (no `Range:` header) case. This is
distinct from `Proto.RangeProven`, which pins `Accept-Ranges` on the `206 Partial
Content` arm; here the server advertises range support on a NON-range request (RFC 7233
§2.3: a server MAY send `Accept-Ranges` on any response to indicate it accepts range
requests for the resource). Curl-confirmed against the deployed `dataplane` binary:

    $ curl -s -D - -o /dev/null http://127.0.0.1:8097/static/app.js
    HTTP/1.1 200 OK
    ETag: "9e983f35"
    Accept-Ranges: bytes                          ← proven here
    Content-Type: application/javascript
    …
    Content-Length: 35

The deployed default app (`Reactor.App.demoApp`, dispatched by `App.handle`) carries a
`/static` prefix route to the `staticFile` handler, and
`Reactor.App.responseOfReq req .staticFile` is DEFINITIONALLY
`StaticFile.serveDeployed (targetSegments req.target) req.headers`
(`deployed_staticFile_route`, `rfl`). For a plain `GET /static/app.js` the conditional
selection is the full `.ok`, whose `StaticFile.toResponse` adapter emits
`Accept-Ranges: bytes`. The pipeline transforms only add headers / strip hop-by-hop
fields, so the advertisement survives to the wire (curl-confirmed above; the `206`
sibling in `Proto.RangeProven` shows the same header on the range arm).

Theorems:

  * `deployed_staticFile_route` / `serve_plain_ok` — the deployed `staticFile` route IS
    `serveDeployed`, and the plain-`GET` selection is the full `.ok`.
  * `plain_get_accept_ranges` — a plain `GET /static/app.js` is served `200 (OK)` with
    `Accept-Ranges: bytes` in its headers and the real embedded body.
  * `accept_ranges_wire_bytes` — the name/value are exactly the bytes of
    `"Accept-Ranges"` / `"bytes"` (pinned via the `Shortcuts.ba_toList_eq` bridge — pure-kernel
    `decide`, no `native_decide`).
  * `accept_ranges_advertised` — for EVERY request whose selection is the full `.ok`
    serve (any headers, any body, any etag), the `Accept-Ranges: bytes` advertisement is
    emitted — the server advertises range support unconditionally on the full response,
    not only when a `Range:` header is present. Non-vacuous (`serve_plain_ok` exhibits a
    hitting request).
-/

import StaticFile
import Reactor.App
import Proto.Kernel.Shortcuts

namespace Proto.AcceptRangesProven

open StaticFile
open Proto.Kernel

/-- The served path segments for the deployed asset `/static/app.js`. -/
def assetSegs : List String := ["static", "app.js"]

/-! ## The deployed anchor: the app's `staticFile` route IS `serveDeployed` -/

/-- **`deployed_staticFile_route`.** The DEPLOYED default app's `staticFile` handler —
the one `Reactor.App.handle demoAppConfig` invokes for the `/static` prefix route — is
definitionally `StaticFile.serveDeployed` over the request's normalized target segments
and raw headers. So the theorems below, stated on `serveDeployed`, are statements about
the running dataplane's response for `/static/<file>`. -/
theorem deployed_staticFile_route (req : Proto.Request) :
    Reactor.App.responseOfReq req .staticFile
      = StaticFile.serveDeployed (Reactor.App.targetSegments req.target) req.headers := rfl

/-- The plain-`GET` selection for `/static/app.js` is the full `200 (OK)` bearing the
real body and the content entity-tag — no conditional/range narrows it. (`reqOfHeaders
[]` sets `ifNoneMatch := []`, `rangeSet := []`, `range := none`, so every conditional
gate passes to the full serve.) -/
theorem serve_plain_ok :
    serveConditional deployedConfig (reqOfHeaders []) assetSegs
      = .ok appJs (contentETag appJs) := rfl

/-! ## `plain_get_accept_ranges` — the wire response advertises range support -/

/-- **`plain_get_accept_ranges`.** A plain `GET /static/app.js` on the deployed handler is
answered `200 (OK)`, its header block contains `Accept-Ranges: bytes`, and its body is
the real embedded asset. This is the response `serveDeployed` renders — `toResponse` of
the `.ok` selection — matching the curl (`HTTP/1.1 200 OK … Accept-Ranges: bytes …`). -/
theorem plain_get_accept_ranges :
    (serveDeployed assetSegs []).status = 200
  ∧ (strBytes "Accept-Ranges", strBytes "bytes")
        ∈ (serveDeployed assetSegs []).headers
  ∧ (serveDeployed assetSegs []).body = appJs := by
  unfold serveDeployed
  rw [serve_plain_ok]
  refine ⟨rfl, ?_, rfl⟩
  simp only [toResponse]
  -- headers = [(ETag, …), (Accept-Ranges, "bytes"), (Content-Type, …)]
  exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)

/-! ## `accept_ranges_wire_bytes` — the exact bytes on the wire -/

/-- **`accept_ranges_wire_bytes`.** The `Accept-Ranges` name/value the deployed handler
emits are exactly the bytes of `"Accept-Ranges"` / `"bytes"`. Pinned to explicit byte
literals through the `Shortcuts.ba_toList_eq` bridge — pure-kernel `decide`, no `native_decide`. -/
theorem accept_ranges_wire_bytes :
    strBytes "Accept-Ranges" = [65, 99, 99, 101, 112, 116, 45, 82, 97, 110, 103, 101, 115]
  ∧ strBytes "bytes" = [98, 121, 116, 101, 115] := by
  refine ⟨?_, ?_⟩ <;> simp only [strBytes, Shortcuts.ba_toList_eq] <;> decide

/-! ## `accept_ranges_advertised` — advertised on EVERY full-serve response -/

/-- **`accept_ranges_advertised`.** For EVERY request to `/static/app.js` whose selection
is the full `200 (.ok)` serve, the emitted headers carry `Accept-Ranges: bytes` —
INDEPENDENT of the request headers and of the body content. The deployed handler
advertises range support unconditionally on the full response, not only when a `Range:`
header is present (RFC 7233 §2.3). Non-vacuous — `serve_plain_ok` exhibits a request that
actually hits this branch. -/
theorem accept_ranges_advertised (headers : List (Proto.Bytes × Proto.Bytes))
    (body : Proto.Bytes) (etag : ETag)
    (hsel : serveConditional deployedConfig (reqOfHeaders headers) assetSegs = .ok body etag) :
    (strBytes "Accept-Ranges", strBytes "bytes")
      ∈ (serveDeployed assetSegs headers).headers := by
  unfold serveDeployed
  rw [hsel]
  simp only [toResponse]
  exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)

end Proto.AcceptRangesProven

#print axioms Proto.AcceptRangesProven.deployed_staticFile_route
#print axioms Proto.AcceptRangesProven.serve_plain_ok
#print axioms Proto.AcceptRangesProven.plain_get_accept_ranges
#print axioms Proto.AcceptRangesProven.accept_ranges_wire_bytes
#print axioms Proto.AcceptRangesProven.accept_ranges_advertised
