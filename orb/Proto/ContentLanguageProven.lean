/-
# Proto.ContentLanguageProven — the DEPLOYED `200` carries NO `Content-Language` (no negotiation)

PROVE-WHAT-RUNS for content negotiation. The deployed static handler answers a `200 (OK)`
for `/static/app.js` with EXACTLY three representation headers — `ETag`, `Accept-Ranges`,
`Content-Type` — and no others of its own. In particular there is NO `Content-Language`
field: the running serve implements no proactive language negotiation (RFC 9110 §12.5.4 /
§8.5), so it never advertises the representation's language, and no deployed stage emits a
`Content-Language`. This is an honest not-deployed finding, same class as
`Proto.OptionsProven` — the header a naive ledger might credit is simply not on the wire.

## Ground truth — curl against the running dataplane (io_uring, port 8097)

```
$ curl -s -D - -o /dev/null http://127.0.0.1:8097/static/app.js
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

No `Content-Language` field anywhere on the wire.

## What is proven here (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

  * `deployed_staticFile_route` — the deployed `/static` route IS `serveDeployed` (`rfl`).
  * `ok_header_names` — the `200 (.ok)` arm's header NAMES are exactly
    `[ETag, Accept-Ranges, Content-Type]` — a closed three-element set (`rfl`).
  * `no_content_language_ok` — for ANY body/etag AND ANY value `v`, `(Content-Language, v)`
    is absent from the `200` header list: the representation-language advisory is never
    emitted by the deployed handler, independent of the file served.
  * `plain_get_status_200` / `plain_get_omits_content_language` — the concrete deployed
    `GET /static/app.js` is answered `200` and its headers omit `Content-Language`
    (non-vacuous: exhibits a real request that hits the branch — the curl above).
  * `content_language_wire_bytes` — the exact bytes of the `"Content-Language"` name that
    is ABSENT (pinned via `Shortcuts.ba_toList_eq`, pure-kernel `decide`; no `native_decide`).

## Not proven in-kernel (deliberately)

That NO later deployed stage (SecurityHeaders / header rewrite / …) adds a
`Content-Language` on the response phase is established EMPIRICALLY by the curl above,
re-run by the verifier. The finding does not hinge on it: the handler's `200` originates
without the field, and the wire confirms none is added.
-/

import StaticFile
import Reactor.App
import Proto.Kernel.Shortcuts

namespace Proto.ContentLanguageProven

open StaticFile
open Proto.Kernel

/-- The served path segments for the deployed asset `/static/app.js`. -/
def assetSegs : List String := ["static", "app.js"]

/-- The `Content-Language` header name — the representation-language advisory the deployed
handler does NOT emit. -/
def contentLanguageName : Proto.Bytes := "Content-Language".toUTF8.toList

/-! ## The deployed anchor -/

/-- **`deployed_staticFile_route`.** The deployed default app's `staticFile` handler is
definitionally `StaticFile.serveDeployed` over the request's normalized target segments and
raw headers — so the statements below describe the running dataplane's `/static/<file>`
response. -/
theorem deployed_staticFile_route (req : Proto.Request) :
    Reactor.App.responseOfReq req .staticFile
      = StaticFile.serveDeployed (Reactor.App.targetSegments req.target) req.headers := rfl

/-! ## The `200` header names are a closed three-element set -/

/-- **`ok_header_names`.** The `200 (.ok)` arm the deployed handler renders carries EXACTLY
the header names `[ETag, Accept-Ranges, Content-Type]` — a closed set, no
`Content-Language` among them. Definitional. -/
theorem ok_header_names (body : Proto.Bytes) (etag : ETag) :
    (toResponse (.ok body etag)).headers.map Prod.fst
      = [strBytes "ETag", strBytes "Accept-Ranges", strBytes "Content-Type"] := rfl

/-- The `"Content-Language"` name is not among the three `200` header names — decided on
explicit bytes through `Shortcuts.ba_toList_eq` (pure-kernel `decide`). -/
theorem contentLanguageName_notin_ok_names (body : Proto.Bytes) (etag : ETag) :
    contentLanguageName ∉ (toResponse (.ok body etag)).headers.map Prod.fst := by
  rw [ok_header_names]
  simp only [contentLanguageName, strBytes, Shortcuts.ba_toList_eq]
  decide

/-! ## The advisory is genuinely absent from the deployed `200` -/

/-- **`no_content_language_ok`.** For ANY body/etag AND ANY value `v`, the pair
`(Content-Language, v)` is absent from the deployed handler's `200` header list — the
representation-language advisory is never emitted, independent of the file served. -/
theorem no_content_language_ok (body : Proto.Bytes) (etag : ETag) (v : Proto.Bytes) :
    (contentLanguageName, v) ∉ (toResponse (.ok body etag)).headers := by
  intro h
  exact contentLanguageName_notin_ok_names body etag (List.mem_map_of_mem Prod.fst h)

/-! ## The concrete deployed `GET /static/app.js` (the curl witness) -/

/-- The plain-`GET` selection for `/static/app.js` is the full `200 (.ok)`. (`reqOfHeaders
[]` sets every conditional/range field empty, so the full serve is selected — `rfl`.) -/
theorem serve_plain_ok :
    serveConditional deployedConfig (reqOfHeaders []) assetSegs
      = .ok appJs (contentETag appJs) := rfl

/-- **`plain_get_status_200`.** The concrete deployed `GET /static/app.js` is answered
`200 (OK)` — the wire's `HTTP/1.1 200 OK`. -/
theorem plain_get_status_200 : (serveDeployed assetSegs []).status = 200 := by
  unfold serveDeployed; rw [serve_plain_ok]; rfl

/-- **`plain_get_omits_content_language`.** The concrete deployed `GET /static/app.js`
answer omits `Content-Language` for every value — non-vacuously (this request really hits
the `200` branch, matching the curl). -/
theorem plain_get_omits_content_language (v : Proto.Bytes) :
    (contentLanguageName, v) ∉ (serveDeployed assetSegs []).headers := by
  unfold serveDeployed
  rw [serve_plain_ok]
  exact no_content_language_ok appJs (contentETag appJs) v

/-! ## The exact bytes of the absent name -/

/-- **`content_language_wire_bytes`.** The `"Content-Language"` name whose header is ABSENT
from the deployed `200` has exactly these bytes — pinned through `Shortcuts.ba_toList_eq` (pure-kernel
`decide`, no `native_decide`). -/
theorem content_language_wire_bytes :
    contentLanguageName
      = [67, 111, 110, 116, 101, 110, 116, 45, 76, 97, 110, 103, 117, 97, 103, 101] := by
  simp only [contentLanguageName, Shortcuts.ba_toList_eq]; decide

end Proto.ContentLanguageProven

#print axioms Proto.ContentLanguageProven.deployed_staticFile_route
#print axioms Proto.ContentLanguageProven.ok_header_names
#print axioms Proto.ContentLanguageProven.contentLanguageName_notin_ok_names
#print axioms Proto.ContentLanguageProven.no_content_language_ok
#print axioms Proto.ContentLanguageProven.serve_plain_ok
#print axioms Proto.ContentLanguageProven.plain_get_status_200
#print axioms Proto.ContentLanguageProven.plain_get_omits_content_language
#print axioms Proto.ContentLanguageProven.content_language_wire_bytes
