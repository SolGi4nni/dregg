/-
# Proto.AgeProven — the DEPLOYED `200` carries NO `Age` (no shared-cache age accounting)

PROVE-WHAT-RUNS, honest not-deployed edition (same class as `Proto.ContentLanguageProven`).
The deployed static handler answers a `200 (OK)` for `/static/app.js` with EXACTLY three
representation headers — `ETag`, `Accept-Ranges`, `Content-Type` — and no others of its own.
In particular there is NO `Age` field: the running serve does not present a stored,
positive-age representation on this path, so it never stamps `Age` (RFC 9110 §5.1). A
downstream cache computing freshness sees no server-supplied age; the deployed handler makes
no age claim, and this file proves the field absent independent of the file served.

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

No `Age` field anywhere on the wire.

## What is proven here (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

  * `deployed_staticFile_route` — the deployed `/static` route IS `serveDeployed` (`rfl`).
  * `ok_header_names` — the `200 (.ok)` arm's header NAMES are exactly
    `[ETag, Accept-Ranges, Content-Type]` — a closed three-element set (`rfl`).
  * `no_age_ok` — for ANY body/etag AND ANY value `v`, `(Age, v)` is absent from the `200`
    header list.
  * `plain_get_status_200` / `plain_get_omits_age` — the concrete deployed
    `GET /static/app.js` is answered `200` and its headers omit `Age` (non-vacuous).
  * `age_wire_bytes` — the exact bytes of the `"Age"` name that is ABSENT.

RE-PROVED (2026-07-11) through the shared `Proto.Kernel.Shortcuts` kit: the private
`ba_toList_eq` copy is gone, and the deployed-route/`200`-shape facts are instantiated
from the shared factor (`deployed_staticFile_route`, `ok_header_names`, `notin_ok_of_ne`,
`serve_plain_ok`, `plain_get_status_200`, `plain_get_omits_of_ne`) — this file now only
supplies the `Age` name bytes and its three `≠`-to-the-`200`-names facts.
-/

import StaticFile
import Reactor.App
import Proto.Kernel.Shortcuts

namespace Proto.AgeProven

open StaticFile
open Proto.Kernel

/-- The served path segments for the deployed asset `/static/app.js`. -/
def assetSegs : List String := ["static", "app.js"]

/-- The `Age` header name — the shared-cache age advisory the deployed handler does NOT
emit. -/
def ageName : Proto.Bytes := "Age".toUTF8.toList

/-! ## The three `≠` facts (all this file has to supply) -/

private theorem ageName_ne_etag : ageName ≠ strBytes "ETag" := by
  simp only [ageName, StaticFile.strBytes, Shortcuts.ba_toList_eq]; decide

private theorem ageName_ne_ar : ageName ≠ strBytes "Accept-Ranges" := by
  simp only [ageName, StaticFile.strBytes, Shortcuts.ba_toList_eq]; decide

private theorem ageName_ne_ct : ageName ≠ strBytes "Content-Type" := by
  simp only [ageName, StaticFile.strBytes, Shortcuts.ba_toList_eq]; decide

/-! ## The deployed anchor (shared factor) -/

/-- **`deployed_staticFile_route`.** The deployed default app's `staticFile` handler is
definitionally `StaticFile.serveDeployed` over the request's normalized target segments and
raw headers. -/
theorem deployed_staticFile_route (req : Proto.Request) :
    Reactor.App.responseOfReq req .staticFile
      = StaticFile.serveDeployed (Reactor.App.targetSegments req.target) req.headers :=
  Shortcuts.deployed_staticFile_route req

/-! ## The `200` header names are a closed three-element set -/

/-- **`ok_header_names`.** The `200 (.ok)` arm carries EXACTLY the header names
`[ETag, Accept-Ranges, Content-Type]` — no `Age` among them. Definitional. -/
theorem ok_header_names (body : Proto.Bytes) (etag : ETag) :
    (toResponse (.ok body etag)).headers.map Prod.fst
      = [strBytes "ETag", strBytes "Accept-Ranges", strBytes "Content-Type"] :=
  Shortcuts.ok_header_names body etag

/-- The `"Age"` name is not among the three `200` header names. -/
theorem ageName_notin_ok_names (body : Proto.Bytes) (etag : ETag) :
    ageName ∉ (toResponse (.ok body etag)).headers.map Prod.fst := by
  rw [ok_header_names]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h)
  · exact ageName_ne_etag h
  · exact ageName_ne_ar h
  · exact ageName_ne_ct h

/-! ## The advisory is genuinely absent from the deployed `200` -/

/-- **`no_age_ok`.** For ANY body/etag AND ANY value `v`, the pair `(Age, v)` is absent from
the deployed handler's `200` header list — no response age is stamped, independent of the
file served. -/
theorem no_age_ok (body : Proto.Bytes) (etag : ETag) (v : Proto.Bytes) :
    (ageName, v) ∉ (toResponse (.ok body etag)).headers :=
  Shortcuts.notin_ok_of_ne ageName ageName_ne_etag ageName_ne_ar ageName_ne_ct body etag v

/-! ## The concrete deployed `GET /static/app.js` (the curl witness) -/

/-- The plain-`GET` selection for `/static/app.js` is the full `200 (.ok)`. -/
theorem serve_plain_ok :
    serveConditional deployedConfig (reqOfHeaders []) assetSegs
      = .ok appJs (contentETag appJs) :=
  Shortcuts.serve_plain_ok

/-- **`plain_get_status_200`.** The concrete deployed `GET /static/app.js` is answered
`200 (OK)` — the wire's `HTTP/1.1 200 OK`. -/
theorem plain_get_status_200 : (serveDeployed assetSegs []).status = 200 :=
  Shortcuts.plain_get_status_200

/-- **`plain_get_omits_age`.** The concrete deployed `GET /static/app.js` answer omits `Age`
for every value — non-vacuously (this request really hits the `200` branch, matching the
curl). -/
theorem plain_get_omits_age (v : Proto.Bytes) :
    (ageName, v) ∉ (serveDeployed assetSegs []).headers :=
  Shortcuts.plain_get_omits_of_ne ageName ageName_ne_etag ageName_ne_ar ageName_ne_ct v

/-! ## The exact bytes of the absent name -/

/-- **`age_wire_bytes`.** The `"Age"` name whose header is ABSENT from the deployed `200`
has exactly these bytes (pure-kernel `decide` through the shared bridge). -/
theorem age_wire_bytes : ageName = [65, 103, 101] := by
  simp only [ageName, Shortcuts.ba_toList_eq]; decide

end Proto.AgeProven

#print axioms Proto.AgeProven.deployed_staticFile_route
#print axioms Proto.AgeProven.ok_header_names
#print axioms Proto.AgeProven.ageName_notin_ok_names
#print axioms Proto.AgeProven.no_age_ok
#print axioms Proto.AgeProven.serve_plain_ok
#print axioms Proto.AgeProven.plain_get_status_200
#print axioms Proto.AgeProven.plain_get_omits_age
#print axioms Proto.AgeProven.age_wire_bytes
