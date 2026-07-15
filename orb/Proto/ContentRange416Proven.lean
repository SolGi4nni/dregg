/-
# Proto.ContentRange416Proven — `Content-Range: bytes */N` on the DEPLOYED `416` arm

PROVE-WHAT-RUNS for the unsatisfiable-range refusal (RFC 7233 §4.4 / RFC 9110 §15.5.17):
when a `Range:` request asks for bytes past the end of the representation, the deployed
static handler answers `416 Range Not Satisfiable` carrying a `Content-Range: bytes */N`
header (the `*` complete-length form, `N` = the representation length) and an EMPTY body.
This is the `416` arm of `StaticFile.toResponse`, distinct from the `206` arm proven in
`Proto.RangeProven`.

## Ground truth — curl against the running dataplane (io_uring, port 8097)

```
$ curl -s -D - -o /dev/null -H 'Range: bytes=999-1000' http://127.0.0.1:8097/static/app.js
HTTP/1.1 416 Range Not Satisfiable
Connection: keep-alive
Content-Range: bytes */35                    ← proven here (N = 35 = |app.js|)
Strict-Transport-Security: …
Server: drorb
Content-Length: 0                            ← empty body
```

`app.js` is 35 bytes, so `bytes=999-1000` is entirely past the end → unsatisfiable → `416`
with the complete-length advisory `bytes */35`.

## What is proven here (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

  * `deployed_staticFile_route` — the deployed `/static` route IS `serveDeployed` (`rfl`).
  * `toResponse_416` — the `416` arm renders status `416`, a SINGLE `Content-Range:
    bytes */N` header, and an empty body, for EVERY complete length `N` (`rfl`).
  * `range_unsat_selects` — the deployed selector (`serveConditional` over the deployed
    config + real `app.js`) genuinely returns `.rangeNotSatisfiable 35` for an
    unsatisfiable single range `bytes=999-1000`: the `416` branch is REACHED, not vacuous.
  * `deployed_416` — the deployed handler's rendered `416` for that request is status
    `416`, carries `Content-Range: bytes */35`, and has an empty body — the exact wire.
  * `content_range_416_wire_bytes` — the `Content-Range` name and the `bytes */35` value
    are exactly these bytes (pinned via `Shortcuts.ba_toList_eq`, pure-kernel `decide`; no
    `native_decide`).

## Not proven in-kernel (deliberately)

That the raw wire header `Range: bytes=999-1000` PARSES to this unsatisfiable range-set is
established by the curl (the deployed parser routes through `String.splitOn`, a Lean-core
well-founded recursion that `native_decide` would be the only in-kernel shortcut for — and
the merge gate bars it). So reachability is proven here on the already-parsed `Req`
(`range_unsat_selects`), and the raw-bytes → `Req` step is the curl's job.
-/

import StaticFile
import Reactor.App
import Proto.Kernel.Shortcuts

namespace Proto.ContentRange416Proven

open StaticFile
open Proto.Kernel

/-- The served path segments for the deployed asset `/static/app.js`. -/
def assetSegs : List String := ["static", "app.js"]

/-- `app.js` is 35 bytes (pinned via `Shortcuts.ba_toList_eq`, pure-kernel) — so any range at offset
`≥ 35` is unsatisfiable. -/
theorem appJs_len : appJs.length = 35 := by
  simp only [appJs, strBytes, Shortcuts.ba_toList_eq]; decide

/-! ## The deployed anchor -/

/-- **`deployed_staticFile_route`.** The deployed default app's `staticFile` handler is
definitionally `StaticFile.serveDeployed` over the request's normalized target segments and
raw headers — so the statements below describe the running dataplane's `/static/<file>`
response. -/
theorem deployed_staticFile_route (req : Proto.Request) :
    Reactor.App.responseOfReq req .staticFile
      = StaticFile.serveDeployed (Reactor.App.targetSegments req.target) req.headers := rfl

/-! ## The `416` arm renders `Content-Range: bytes */N` + empty body -/

/-- **`toResponse_416`.** For EVERY complete length `N`, the `416` arm renders status `416`,
a SINGLE header `Content-Range: bytes */N`, and an empty body — the RFC 7233 §4.4 refusal.
Definitional. -/
theorem toResponse_416 (N : Nat) :
    toResponse (.rangeNotSatisfiable N)
      = { status := 416, reason := strBytes "Range Not Satisfiable",
          headers := [(strBytes "Content-Range", strBytes ("bytes */" ++ toString N))],
          body := [] } := rfl

/-! ## Reachability: an unsatisfiable range genuinely selects the `416` -/

/-- The already-parsed request for `Range: bytes=999-1000` — a single range wholly past the
35-byte `app.js`. (The raw-header → `Req` parse is the curl's job; see the module note.) -/
def unsatReq : Req := { target := [], rangeSet := [RangeSpec.fromTo 999 1000] }

/-- **`range_unsat_selects`.** The deployed selector `serveConditional` over the deployed
config and the real `app.js` returns `.rangeNotSatisfiable 35` for the unsatisfiable range
`bytes=999-1000`: the `416` branch is genuinely reached (not a vacuous statement about an
unreachable arm). `resolveAll 35 [999-1000] = []` (offset `999 ≥ 35`), so the range-set
resolves to no satisfiable part — RFC 7233 §2.1. -/
theorem range_unsat_selects :
    serveConditional deployedConfig unsatReq assetSegs = .rangeNotSatisfiable 35 := by
  have e : serveConditional deployedConfig unsatReq assetSegs
      = (match resolveAll appJs.length [RangeSpec.fromTo 999 1000] with
         | [] => (Resp.rangeNotSatisfiable appJs.length)
         | [(s, en)] =>
             Resp.partialContent (slice appJs s en) s en appJs.length (contentETag appJs)
         | parts => Resp.multipartRanges (mkParts appJs parts) appJs.length (contentETag appJs))
      := rfl
  rw [e, appJs_len]; rfl

/-! ## The deployed `416` for the concrete unsatisfiable request -/

/-- **`deployed_416`.** The deployed handler's rendered response for the unsatisfiable
range is status `416`, carries the `Content-Range: bytes */35` header, and has an empty
body — the exact `416` the curl observes. -/
theorem deployed_416 :
    (toResponse (serveConditional deployedConfig unsatReq assetSegs)).status = 416
  ∧ (strBytes "Content-Range", strBytes ("bytes */" ++ toString (35 : Nat)))
        ∈ (toResponse (serveConditional deployedConfig unsatReq assetSegs)).headers
  ∧ (toResponse (serveConditional deployedConfig unsatReq assetSegs)).body = [] := by
  rw [range_unsat_selects, toResponse_416]
  refine ⟨rfl, ?_, rfl⟩
  exact List.mem_cons_self _ _

/-! ## The exact deployed-wire bytes -/

/-- The `toString (35 : Nat)` the `416` renders is the digit string `"35"`. -/
theorem complete35_str : ("bytes */" ++ toString (35 : Nat)) = "bytes */35" := rfl

/-- **`content_range_416_wire_bytes`.** The `Content-Range` name and the `bytes */35` value
the deployed `416` emits are exactly these bytes — pinned through `Shortcuts.ba_toList_eq`
(pure-kernel `decide`, no `native_decide`), matching the curl `Content-Range: bytes */35`. -/
theorem content_range_416_wire_bytes :
    strBytes "Content-Range"
      = [67, 111, 110, 116, 101, 110, 116, 45, 82, 97, 110, 103, 101]
  ∧ strBytes "bytes */35" = [98, 121, 116, 101, 115, 32, 42, 47, 51, 53] := by
  refine ⟨?_, ?_⟩ <;> simp only [strBytes, Shortcuts.ba_toList_eq] <;> decide

end Proto.ContentRange416Proven

#print axioms Proto.ContentRange416Proven.appJs_len
#print axioms Proto.ContentRange416Proven.deployed_staticFile_route
#print axioms Proto.ContentRange416Proven.toResponse_416
#print axioms Proto.ContentRange416Proven.range_unsat_selects
#print axioms Proto.ContentRange416Proven.deployed_416
#print axioms Proto.ContentRange416Proven.complete35_str
#print axioms Proto.ContentRange416Proven.content_range_416_wire_bytes
