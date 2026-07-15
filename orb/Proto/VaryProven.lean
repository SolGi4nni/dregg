/-
# Proto.VaryProven — the DEPLOYED `200` carries NO `Vary` (no negotiation surface advertised)

PROVE-WHAT-RUNS for content negotiation, honest not-deployed edition (same class as
`Proto.ContentLanguageProven` / `Proto.OptionsProven`). The deployed static handler answers a
`200 (OK)` for `/static/app.js` with EXACTLY three representation headers — `ETag`,
`Accept-Ranges`, `Content-Type` — and no others of its own. In particular there is NO
`Vary` field: the running serve performs no proactive negotiation, so it never advertises
which request headers a cache should key on (RFC 9110 §12.5.5). A shared cache seeing this
response may store and reuse it for all requests to the URI — the deployed handler makes no
`Vary` claim, and this file proves the field is absent independent of the file served.

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

No `Vary` field anywhere on the wire.

## What is proven here (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

  * `deployed_staticFile_route` — the deployed `/static` route IS `serveDeployed` (`rfl`).
  * `ok_header_names` — the `200 (.ok)` arm's header NAMES are exactly
    `[ETag, Accept-Ranges, Content-Type]` — a closed three-element set (`rfl`).
  * `no_vary_ok` — for ANY body/etag AND ANY value `v`, `(Vary, v)` is absent from the
    `200` header list.
  * `plain_get_status_200` / `plain_get_omits_vary` — the concrete deployed
    `GET /static/app.js` is answered `200` and its headers omit `Vary` (non-vacuous:
    exhibits the real request that hits the branch — the curl above).
  * `vary_wire_bytes` — the exact bytes of the `"Vary"` name that is ABSENT (pinned via
    `Shortcuts.ba_toList_eq`, pure-kernel `decide`; no `native_decide`).

## Not proven in-kernel (deliberately)

That NO later deployed stage adds a `Vary` on the response phase is established EMPIRICALLY
by the curl above, re-run by the verifier. The finding does not hinge on it: the handler's
`200` originates without the field, and the wire confirms none is added.
-/

import StaticFile
import Reactor.App
import Proto.Kernel.Shortcuts

namespace Proto.VaryProven

open StaticFile
open Proto.Kernel

/-- The served path segments for the deployed asset `/static/app.js`. -/
def assetSegs : List String := ["static", "app.js"]

/-- The `Vary` header name — the cache-negotiation advisory the deployed handler does NOT
emit. -/
def varyName : Proto.Bytes := "Vary".toUTF8.toList

/-! ## The deployed anchor -/

/-- **`deployed_staticFile_route`.** The deployed default app's `staticFile` handler is
definitionally `StaticFile.serveDeployed` over the request's normalized target segments and
raw headers. -/
theorem deployed_staticFile_route (req : Proto.Request) :
    Reactor.App.responseOfReq req .staticFile
      = StaticFile.serveDeployed (Reactor.App.targetSegments req.target) req.headers := rfl

/-! ## The `200` header names are a closed three-element set -/

/-- **`ok_header_names`.** The `200 (.ok)` arm carries EXACTLY the header names
`[ETag, Accept-Ranges, Content-Type]` — no `Vary` among them. Definitional. -/
theorem ok_header_names (body : Proto.Bytes) (etag : ETag) :
    (toResponse (.ok body etag)).headers.map Prod.fst
      = [strBytes "ETag", strBytes "Accept-Ranges", strBytes "Content-Type"] := rfl

/-- The `"Vary"` name is not among the three `200` header names — decided on explicit bytes
through `Shortcuts.ba_toList_eq` (pure-kernel `decide`). -/
theorem varyName_notin_ok_names (body : Proto.Bytes) (etag : ETag) :
    varyName ∉ (toResponse (.ok body etag)).headers.map Prod.fst := by
  rw [ok_header_names]
  simp only [varyName, strBytes, Shortcuts.ba_toList_eq]
  decide

/-! ## The advisory is genuinely absent from the deployed `200` -/

/-- **`no_vary_ok`.** For ANY body/etag AND ANY value `v`, the pair `(Vary, v)` is absent
from the deployed handler's `200` header list — no negotiation-cache-key is advertised,
independent of the file served. -/
theorem no_vary_ok (body : Proto.Bytes) (etag : ETag) (v : Proto.Bytes) :
    (varyName, v) ∉ (toResponse (.ok body etag)).headers := by
  intro h
  exact varyName_notin_ok_names body etag (List.mem_map_of_mem Prod.fst h)

/-! ## The concrete deployed `GET /static/app.js` (the curl witness) -/

/-- The plain-`GET` selection for `/static/app.js` is the full `200 (.ok)`. -/
theorem serve_plain_ok :
    serveConditional deployedConfig (reqOfHeaders []) assetSegs
      = .ok appJs (contentETag appJs) := rfl

/-- **`plain_get_status_200`.** The concrete deployed `GET /static/app.js` is answered
`200 (OK)` — the wire's `HTTP/1.1 200 OK`. -/
theorem plain_get_status_200 : (serveDeployed assetSegs []).status = 200 := by
  unfold serveDeployed; rw [serve_plain_ok]; rfl

/-- **`plain_get_omits_vary`.** The concrete deployed `GET /static/app.js` answer omits
`Vary` for every value — non-vacuously (this request really hits the `200` branch, matching
the curl). -/
theorem plain_get_omits_vary (v : Proto.Bytes) :
    (varyName, v) ∉ (serveDeployed assetSegs []).headers := by
  unfold serveDeployed
  rw [serve_plain_ok]
  exact no_vary_ok appJs (contentETag appJs) v

/-! ## The exact bytes of the absent name -/

/-- **`vary_wire_bytes`.** The `"Vary"` name whose header is ABSENT from the deployed `200`
has exactly these bytes — pinned through `Shortcuts.ba_toList_eq` (pure-kernel `decide`, no
`native_decide`). -/
theorem vary_wire_bytes : varyName = [86, 97, 114, 121] := by
  simp only [varyName, Shortcuts.ba_toList_eq]; decide

end Proto.VaryProven

#print axioms Proto.VaryProven.deployed_staticFile_route
#print axioms Proto.VaryProven.ok_header_names
#print axioms Proto.VaryProven.varyName_notin_ok_names
#print axioms Proto.VaryProven.no_vary_ok
#print axioms Proto.VaryProven.serve_plain_ok
#print axioms Proto.VaryProven.plain_get_status_200
#print axioms Proto.VaryProven.plain_get_omits_vary
#print axioms Proto.VaryProven.vary_wire_bytes
