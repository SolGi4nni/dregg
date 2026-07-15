/-
# Proto.StaticServeProven — the plain `200 OK` static serve on the DEPLOYED handler

PROVE-WHAT-RUNS for the deployed plain `GET /static/app.js` (no conditional / range
headers). The deployed default app (`Reactor.App.demoApp`) routes `/static` to the
`staticFile` handler, and `Reactor.App.responseOfReq req .staticFile` is DEFINITIONALLY
`StaticFile.serveDeployed (targetSegments req.target) req.headers`
(`Proto.EtagProven.deployed_staticFile_route`, `rfl`). With an EMPTY header list the
deployed header parser (`reqOfHeaders []`) short-circuits — `List.find?` over `[]` never
runs `String.splitOn` — so `serveDeployed assetSegs []` renders the FULL `200` in the
pure kernel, and these theorems describe the exact `200` the running dataplane emits.

The CURL that anchors this file (against the running `dataplane` serve):

    $ curl -s -D - http://127.0.0.1:8099/static/app.js
    HTTP/1.1 200 OK
    …
    Accept-Ranges: bytes
    Content-Type: application/javascript
    Content-Length: 35

    console.log('drorb static asset');

Theorems (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound} — no `native_decide`,
no `Lean.ofReduceBool`):
  * `deployed_static_200` — the deployed handler answers a bare `GET /static/app.js`
    with `200`, a body of exactly the 35 octets the curl carries, and the
    `Content-Type: application/javascript` + `Accept-Ranges: bytes` headers.
  * `plain_body_bytes` — those 35 body octets ARE `console.log('drorb static asset');\n`
    — octet-for-octet the curl body (`Shortcuts.ba_toList_eq` bridge; non-vacuous).
  * `deployed_static_route` — tied to the running `staticFile` route: any request whose
    normalized target is `/static/app.js` with no headers gets exactly this `200` body.
-/

import StaticFile
import Reactor.App
import Proto.EtagProven
import Proto.Kernel.Shortcuts

namespace Proto.StaticServeProven

open StaticFile
open Proto.Kernel

/-- The served path segments for `/static/app.js`. -/
def assetSegs : List String := ["static", "app.js"]

/-- The deployed `/static/app.js` body as explicit octets (35 bytes). -/
def appJsBytes : Bytes :=
  [0x63,0x6f,0x6e,0x73,0x6f,0x6c,0x65,0x2e,0x6c,0x6f,0x67,0x28,0x27,0x64,0x72,0x6f,0x72,
   0x62,0x20,0x73,0x74,0x61,0x74,0x69,0x63,0x20,0x61,0x73,0x73,0x65,0x74,0x27,0x29,0x3b,0x0a]

/-- The deployed plain-GET selection: with no request headers, `serveDeployed` renders
the full `200` (`.ok`) bearing the embedded asset and its content entity-tag. Definitional
— `reqOfHeaders []` carries no `If-None-Match`/`Range`, so no conditional/partial arm. -/
theorem serveDeployed_plain :
    serveDeployed assetSegs [] = toResponse (.ok appJs (contentETag appJs)) := rfl

/-- **`plain_body_bytes`.** The deployed `/static/app.js` body IS the 35 octets
`console.log('drorb static asset');\n` — octet-for-octet the curl body. `appJs` is
`"…".toUTF8.toList`; the `Shortcuts.ba_toList_eq` bridge makes it kernel-reduce, so this closes by
pure `decide` — no `native_decide`. -/
theorem plain_body_bytes : appJs = appJsBytes := by
  simp only [appJs, strBytes, Shortcuts.ba_toList_eq]; decide

/-- **`deployed_static_200`.** The DEPLOYED handler answers a bare `GET /static/app.js`
(no conditional/range headers) with a `200 OK` whose body is exactly the 35 octets the
curl carries, carrying `Content-Type: application/javascript` and `Accept-Ranges: bytes`
— the exact `200` the curl above observes (`Content-Length: 35` = `appJsBytes.length`). -/
theorem deployed_static_200 :
    (serveDeployed assetSegs []).status = 200
  ∧ (serveDeployed assetSegs []).body = appJsBytes
  ∧ appJsBytes.length = 35
  ∧ (strBytes "Content-Type", strBytes "application/javascript")
        ∈ (serveDeployed assetSegs []).headers
  ∧ (strBytes "Accept-Ranges", strBytes "bytes")
        ∈ (serveDeployed assetSegs []).headers := by
  refine ⟨rfl, ?_, by decide, ?_, ?_⟩
  · show (toResponse (.ok appJs (contentETag appJs))).body = appJsBytes
    exact plain_body_bytes
  · rw [serveDeployed_plain]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
  · rw [serveDeployed_plain]
    exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)

/-- **`deployed_static_route`.** Tied to the running `staticFile` route: for any request
whose normalized target is `/static/app.js` and whose header list is empty, the app's
`staticFile` response IS this `200` with body the 35 curl octets. -/
theorem deployed_static_route (req : Proto.Request)
    (htarget : Reactor.App.targetSegments req.target = assetSegs)
    (hhdr : req.headers = []) :
    (Reactor.App.responseOfReq req .staticFile).status = 200
  ∧ (Reactor.App.responseOfReq req .staticFile).body = appJsBytes := by
  rw [Proto.EtagProven.deployed_staticFile_route, htarget, hhdr]
  exact ⟨deployed_static_200.1, deployed_static_200.2.1⟩

end Proto.StaticServeProven

#print axioms Proto.StaticServeProven.serveDeployed_plain
#print axioms Proto.StaticServeProven.plain_body_bytes
#print axioms Proto.StaticServeProven.deployed_static_200
#print axioms Proto.StaticServeProven.deployed_static_route
