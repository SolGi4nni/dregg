/-
# Proto.ContentTypeProven — `Content-Type: application/javascript` on the DEPLOYED static handler

PROVE-WHAT-RUNS for the response `Content-Type` the running dataplane stamps on
`/static/app.js`. Curl-confirmed against the deployed `dataplane` binary:

    $ curl -s -D - -o /dev/null http://127.0.0.1:8097/static/app.js
    HTTP/1.1 200 OK
    ETag: "9e983f35"
    Accept-Ranges: bytes
    Content-Type: application/javascript          ← proven here
    …
    Content-Length: 35

The deployed default app (`Reactor.App.demoApp`, dispatched by `App.handle`) carries a
`/static` prefix route to the `staticFile` handler, and
`Reactor.App.responseOfReq req .staticFile` is DEFINITIONALLY
`StaticFile.serveDeployed (targetSegments req.target) req.headers`
(`deployed_staticFile_route`, `rfl`). `serveDeployed` renders the
`StaticFile.serveConditional StaticFile.deployedConfig` selection onto the wire; for the
`200 (OK)` branch (`.ok`) the `StaticFile.toResponse` adapter emits
`Content-Type: application/javascript`. So the theorems below describe the EXACT
response the running dataplane emits for `/static/app.js`.

Theorems:

  * `plain_get_content_type` — a plain `GET /static/app.js` is served `200 (OK)` with
    `Content-Type: application/javascript` in its headers and the real embedded body.
  * `content_type_wire_bytes` — the value the wire carries is exactly the 22 bytes of
    `"application/javascript"` (pinned to an explicit literal via the `Shortcuts.ba_toList_eq`
    bridge — pure-kernel `decide`, no `native_decide`).
  * `content_type_is_route_not_sniffed` — the `Content-Type` is a pure function of the
    served route/resource: it is `application/javascript` for EVERY request to this asset
    regardless of the request headers, so the deployed handler declares the type from the
    route table, it does NOT content-sniff the body (this is the server-side pairing of
    the `X-Content-Type-Options: nosniff` the security-header stage stamps).
-/

import StaticFile
import Reactor.App
import Proto.Kernel.Shortcuts

namespace Proto.ContentTypeProven

open StaticFile
open Proto.Kernel

/-- The served path segments for the deployed asset `/static/app.js` — exactly what
`Reactor.App.targetSegments` yields for that request-target and what `serveDeployed`
hands to `serveConditional`. -/
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

/-! ## `plain_get_content_type` — the wire response carries the JS content type -/

/-- **`plain_get_content_type`.** A plain `GET /static/app.js` on the deployed handler
is answered `200 (OK)`, its header block contains `Content-Type:
application/javascript`, and its body is the real embedded asset. This is the response
`serveDeployed` renders — `toResponse` of the `.ok` selection — matching the curl
(`HTTP/1.1 200 OK … Content-Type: application/javascript … Content-Length: 35`). -/
theorem plain_get_content_type :
    (serveDeployed assetSegs []).status = 200
  ∧ (strBytes "Content-Type", strBytes "application/javascript")
        ∈ (serveDeployed assetSegs []).headers
  ∧ (serveDeployed assetSegs []).body = appJs := by
  unfold serveDeployed
  rw [serve_plain_ok]
  refine ⟨rfl, ?_, rfl⟩
  simp only [toResponse]
  -- headers = [(ETag, …), (Accept-Ranges, "bytes"), (Content-Type, "application/javascript")]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _))

/-! ## `content_type_wire_bytes` — the exact bytes on the wire -/

/-- **`content_type_wire_bytes`.** The `Content-Type` value the deployed handler emits is
exactly the 22 bytes of `"application/javascript"`. Pinned to an explicit byte literal
through the `Shortcuts.ba_toList_eq` bridge — pure-kernel `decide`, no `native_decide`. -/
theorem content_type_wire_bytes :
    strBytes "application/javascript"
      = [97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 47,
         106, 97, 118, 97, 115, 99, 114, 105, 112, 116] := by
  simp only [strBytes, Shortcuts.ba_toList_eq]; decide

/-! ## `content_type_is_route_not_sniffed` — the type is declared, not sniffed -/

/-- **`content_type_is_route_not_sniffed`.** For EVERY request to `/static/app.js` whose
selection is the full `200 (.ok)` serve, the emitted `Content-Type` is
`application/javascript` — INDEPENDENT of the request headers and of the body content.
The deployed handler declares the media type from the route/resource; it does not
content-sniff the payload. This is the server-side pairing of the
`X-Content-Type-Options: nosniff` the security-header stage stamps (proven in
`Proto.NoSniffProven`): the type is authoritative because it is a pure function of the
route. Non-vacuous — `serve_plain_ok` exhibits a request that actually hits this branch. -/
theorem content_type_is_route_not_sniffed (headers : List (Proto.Bytes × Proto.Bytes))
    (body : Proto.Bytes) (etag : ETag)
    (hsel : serveConditional deployedConfig (reqOfHeaders headers) assetSegs = .ok body etag) :
    (strBytes "Content-Type", strBytes "application/javascript")
      ∈ (serveDeployed assetSegs headers).headers := by
  unfold serveDeployed
  rw [hsel]
  simp only [toResponse]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _))

end Proto.ContentTypeProven

#print axioms Proto.ContentTypeProven.deployed_staticFile_route
#print axioms Proto.ContentTypeProven.serve_plain_ok
#print axioms Proto.ContentTypeProven.plain_get_content_type
#print axioms Proto.ContentTypeProven.content_type_wire_bytes
#print axioms Proto.ContentTypeProven.content_type_is_route_not_sniffed
