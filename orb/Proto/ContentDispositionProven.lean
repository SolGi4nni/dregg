/-
# Proto.ContentDispositionProven — the DEPLOYED `200` carries NO `Content-Disposition`
  (served inline; no attachment/filename directive)

PROVE-WHAT-RUNS, honest not-deployed edition (same class as `Proto.ContentLanguageProven`).
The deployed static handler answers a `200 (OK)` for `/static/app.js` with EXACTLY three
representation headers — `ETag`, `Accept-Ranges`, `Content-Type` — and no others of its own.
In particular there is NO `Content-Disposition` field: the running serve presents the asset
inline and never issues a presentation directive (RFC 6266) — no `attachment`, no suggested
`filename`. A user agent defaults to inline handling. This file proves the field absent
independent of the file served.

## Ground truth — curl against the running dataplane (io_uring)

```
$ curl -s -D - -o /dev/null http://127.0.0.1:PORT/static/app.js
HTTP/1.1 200 OK
ETag: "9e983f35"
Accept-Ranges: bytes
Content-Type: application/javascript
Strict-Transport-Security: max-age=31536000; includeSubDomains; preload
X-Frame-Options: DENY
X-Content-Type-Options: nosniff
Referrer-Policy: no-referrer
Server: drorb
x-upstream: …
Content-Length: 35
```

No `Content-Disposition` field anywhere on the wire.

## What is proven here (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

  * `deployed_staticFile_route` — the deployed `/static` route IS `serveDeployed` (`rfl`).
  * `ok_header_names` — the `200 (.ok)` arm's header NAMES are exactly
    `[ETag, Accept-Ranges, Content-Type]` — a closed three-element set (`rfl`).
  * `no_content_disposition_ok` — for ANY body/etag AND ANY value `v`,
    `(Content-Disposition, v)` is absent from the `200` header list.
  * `plain_get_status_200` / `plain_get_omits_content_disposition` — the concrete deployed
    `GET /static/app.js` is answered `200` and its headers omit `Content-Disposition`
    (non-vacuous).
  * `content_disposition_wire_bytes` — the exact bytes of the `"Content-Disposition"` name
    that is ABSENT (pinned via `Shortcuts.ba_toList_eq`, pure-kernel `decide`; no `native_decide`).
-/

import StaticFile
import Reactor.App
import Proto.Kernel.Shortcuts

namespace Proto.ContentDispositionProven

open StaticFile
open Proto.Kernel

/-- The served path segments for the deployed asset `/static/app.js`. -/
def assetSegs : List String := ["static", "app.js"]

/-- The `Content-Disposition` header name — the presentation directive the deployed handler
does NOT emit. -/
def cdName : Proto.Bytes := "Content-Disposition".toUTF8.toList

/-! ## The deployed anchor -/

/-- **`deployed_staticFile_route`.** The deployed default app's `staticFile` handler is
definitionally `StaticFile.serveDeployed` over the request's normalized target segments and
raw headers. -/
theorem deployed_staticFile_route (req : Proto.Request) :
    Reactor.App.responseOfReq req .staticFile
      = StaticFile.serveDeployed (Reactor.App.targetSegments req.target) req.headers := rfl

/-! ## The `200` header names are a closed three-element set -/

/-- **`ok_header_names`.** The `200 (.ok)` arm carries EXACTLY the header names
`[ETag, Accept-Ranges, Content-Type]` — no `Content-Disposition` among them. Definitional. -/
theorem ok_header_names (body : Proto.Bytes) (etag : ETag) :
    (toResponse (.ok body etag)).headers.map Prod.fst
      = [strBytes "ETag", strBytes "Accept-Ranges", strBytes "Content-Type"] := rfl

/-- The `"Content-Disposition"` name is not among the three `200` header names — decided on
explicit bytes through `Shortcuts.ba_toList_eq` (pure-kernel `decide`). -/
theorem cdName_notin_ok_names (body : Proto.Bytes) (etag : ETag) :
    cdName ∉ (toResponse (.ok body etag)).headers.map Prod.fst := by
  rw [ok_header_names]
  simp only [cdName, strBytes, Shortcuts.ba_toList_eq]
  decide

/-! ## The directive is genuinely absent from the deployed `200` -/

/-- **`no_content_disposition_ok`.** For ANY body/etag AND ANY value `v`, the pair
`(Content-Disposition, v)` is absent from the deployed handler's `200` header list — no
presentation directive is emitted, independent of the file served. -/
theorem no_content_disposition_ok (body : Proto.Bytes) (etag : ETag) (v : Proto.Bytes) :
    (cdName, v) ∉ (toResponse (.ok body etag)).headers := by
  intro h
  exact cdName_notin_ok_names body etag (List.mem_map_of_mem Prod.fst h)

/-! ## The concrete deployed `GET /static/app.js` (the curl witness) -/

/-- The plain-`GET` selection for `/static/app.js` is the full `200 (.ok)`. -/
theorem serve_plain_ok :
    serveConditional deployedConfig (reqOfHeaders []) assetSegs
      = .ok appJs (contentETag appJs) := rfl

/-- **`plain_get_status_200`.** The concrete deployed `GET /static/app.js` is answered
`200 (OK)` — the wire's `HTTP/1.1 200 OK`. -/
theorem plain_get_status_200 : (serveDeployed assetSegs []).status = 200 := by
  unfold serveDeployed; rw [serve_plain_ok]; rfl

/-- **`plain_get_omits_content_disposition`.** The concrete deployed `GET /static/app.js`
answer omits `Content-Disposition` for every value — non-vacuously (this request really hits
the `200` branch, matching the curl). -/
theorem plain_get_omits_content_disposition (v : Proto.Bytes) :
    (cdName, v) ∉ (serveDeployed assetSegs []).headers := by
  unfold serveDeployed
  rw [serve_plain_ok]
  exact no_content_disposition_ok appJs (contentETag appJs) v

/-! ## The exact bytes of the absent name -/

/-- **`content_disposition_wire_bytes`.** The `"Content-Disposition"` name whose header is
ABSENT from the deployed `200` has exactly these bytes — pinned through `Shortcuts.ba_toList_eq`
(pure-kernel `decide`, no `native_decide`). -/
theorem content_disposition_wire_bytes :
    cdName = [67, 111, 110, 116, 101, 110, 116, 45, 68, 105, 115, 112, 111, 115, 105, 116,
              105, 111, 110] := by
  simp only [cdName, Shortcuts.ba_toList_eq]; decide

end Proto.ContentDispositionProven

#print axioms Proto.ContentDispositionProven.deployed_staticFile_route
#print axioms Proto.ContentDispositionProven.ok_header_names
#print axioms Proto.ContentDispositionProven.cdName_notin_ok_names
#print axioms Proto.ContentDispositionProven.no_content_disposition_ok
#print axioms Proto.ContentDispositionProven.serve_plain_ok
#print axioms Proto.ContentDispositionProven.plain_get_status_200
#print axioms Proto.ContentDispositionProven.plain_get_omits_content_disposition
#print axioms Proto.ContentDispositionProven.content_disposition_wire_bytes
