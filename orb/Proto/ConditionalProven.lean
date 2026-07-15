import StaticFile
import Reactor.App
import Proto.Kernel.Shortcuts

/-!
# Proto.ConditionalProven — `If-Modified-Since`/`304`: a REAL half-deployment finding

PROVE-WHAT-RUNS for the `If-Modified-Since` conditional (ledger row
`h1.if-modified-since`). The deployed static handler is
`StaticFile.serveDeployed` (dispatched by `Reactor.App` for `/static/<file>`,
selecting with the proven `StaticFile.serveConditional`). It DOES honor the
entity-tag conditional (`If-None-Match` → `304`), but it does **NOT** honor the
date conditional (`If-Modified-Since` → `304`) — because the deployed header
parser `StaticFile.reqOfHeaders` **structurally discards** the `If-Modified-Since`
header (HTTP-date parsing is the documented boundary, RFC 7232 §5.2). So the
date-`304` branch of `serveConditional` is dead on the deployed path, even though
the logic for it (`StaticFile.if_modified_since_304`) is proven and present.

## Ground truth — curl against the running dataplane (io_uring, port 8080)

```
$ curl -sS -i http://127.0.0.1:8080/static/app.js               # plain GET
HTTP/1.1 200 OK ; ETag: "9e983f35" ; Content-Length: 35         # (no Last-Modified)

$ curl -i -H 'If-None-Match: "9e983f35"'  …/static/app.js   →  HTTP/1.1 304 Not Modified   (honored)
$ curl -i -H 'If-Modified-Since: Wed, 21 Oct 2099 07:28:00 GMT' …/static/app.js
                                                            →  HTTP/1.1 200 OK, 35-byte body (IGNORED)
```

A far-future `If-Modified-Since` (the resource was *not* modified since 2099)
MUST be answerable `304` (RFC 7232 §3.3) — but the deployed serve returns the
full `200`. The matching-`ETag` `If-None-Match`, by contrast, IS answered `304`.
The serve even ships NO `Last-Modified` validator, so a client has nothing to
build a correct `If-Modified-Since` from.

## What is proven here (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

The FINDING (the deployed date-conditional is structurally dead):
* `reqOfHeaders_drops_ims` — for ANY inbound header list, the deployed parser
  yields `ifModifiedSince = none`. Whatever `If-Modified-Since` a client sends is
  discarded (holds by `rfl` — the field is a literal `none`).
* `ims_branch_unreachable` — hence the `If-Modified-Since`→`304` gate condition
  `ifModifiedSince304 lm (reqOfHeaders hs).ifModifiedSince` is `false` for EVERY
  client date and EVERY `Last-Modified`. The branch can never fire on the wire.
* `deployed_ims_dropped_200` — concretely, the deployed selection over the
  existing asset with a (dropped) `If-Modified-Since` resolves to `.ok` (a `200`
  with the full body), matching the wire.

The contrast (the logic EXISTS and the entity-tag half IS live — so this is a real
*omission*, not absent code):
* `deployed_ims_would_304` — had the header been parsed to a date the resource is
  not modified since (`some 0`, and `lastModified = 0`), the SAME
  `serveConditional` WOULD select `304`. So only the parse is missing.
* `deployed_inm_304` — a matching `If-None-Match` over the deployed config DOES
  select `304` (re-anchors `StaticFile.deployed_conditional_304`) — the honored
  half, matching the `"9e983f35"` curl.

The `304` byte format:
* `etag_header_name_bytes` — the `304` response's header name is exactly the ASCII
  bytes of `"ETag"` (`.toUTF8.toList` kernel-reduced via `Shortcuts.ba_toList_eq`).
* `notModified_304_empty` — `toResponse` maps a `.notModified` selection to a
  `304`-status response with an EMPTY body (RFC 7232 §4.1).
-/

namespace Proto.ConditionalProven

open StaticFile
open Proto.Kernel

/-! ## THE FINDING — the deployed parser drops `If-Modified-Since` -/

/-- **`reqOfHeaders_drops_ims`.** The deployed static header parser
`StaticFile.reqOfHeaders` yields `ifModifiedSince = none` for ANY inbound header
list — whatever `If-Modified-Since` a client sends is structurally discarded
(HTTP-date parsing is the documented RFC 7232 §5.2 boundary). Holds by `rfl`: the
field is a literal `none`. This is the root cause of the wire behavior. -/
theorem reqOfHeaders_drops_ims (hs : List (Bytes × Bytes)) :
    (reqOfHeaders hs).ifModifiedSince = none := rfl

/-- **`ims_branch_unreachable`.** Consequently the `If-Modified-Since`→`304` gate
condition is `false` on the deployed path for EVERY client date and EVERY
`Last-Modified` instant `lm`: the date-`304` branch of `serveConditional` can
never fire on the wire. -/
theorem ims_branch_unreachable (hs : List (Bytes × Bytes)) (lm : Nat) :
    ifModifiedSince304 lm (reqOfHeaders hs).ifModifiedSince = false := by
  rw [reqOfHeaders_drops_ims]; rfl

/-- **`deployed_ims_dropped_200`.** The deployed selection over the existing asset,
for a request whose `If-Modified-Since` has been dropped to `none` (the faithful
projection of ANY `If-Modified-Since` request per `reqOfHeaders_drops_ims`),
resolves to `.ok` — a `200` carrying the full body — never a `304`. This is the
`If-Modified-Since: …2099… → 200` curl. -/
theorem deployed_ims_dropped_200 :
    serveConditional deployedConfig { target := ["static", "app.js"] } ["static", "app.js"]
      = .ok appJs (contentETag appJs) := by
  simp [serveConditional, deployedConfig, staticFS, ifNoneMatchHit, ifModifiedSince304,
    ifRangeEligible]

/-- The dropped-`If-Modified-Since` response really is a `200` with the full body
(RFC-wrong: a not-modified-since request owes a `304`). -/
theorem deployed_ims_dropped_status :
    (toResponse (serveConditional deployedConfig
        { target := ["static", "app.js"] } ["static", "app.js"])).status = 200 ∧
    (toResponse (serveConditional deployedConfig
        { target := ["static", "app.js"] } ["static", "app.js"])).body = appJs := by
  rw [deployed_ims_dropped_200]; exact ⟨rfl, rfl⟩

/-! ## The CONTRAST — the logic exists (would-304), and the entity-tag half is live -/

/-- **`deployed_ims_would_304`.** Had the header been parsed to a date the resource
is not modified since (`some 0`, with the config's `lastModified = 0`), the SAME
deployed `serveConditional` WOULD select `304 (Not Modified)`. So the finding is a
pure *parse* omission — the RFC 7232 §3.3 decision logic is present and correct;
only `reqOfHeaders` never feeds it a date. -/
theorem deployed_ims_would_304 :
    serveConditional deployedConfig
        { target := ["static", "app.js"], ifModifiedSince := some 0 } ["static", "app.js"]
      = .notModified (contentETag appJs) := by
  simp [serveConditional, deployedConfig, staticFS, ifNoneMatchHit, ifModifiedSince304,
    ETag.weakMatch]

/-- **`deployed_inm_304`.** The entity-tag conditional IS honored on the deployed
config: a matching `If-None-Match` selects `304`. Re-anchors
`StaticFile.deployed_conditional_304` — this is the `If-None-Match: "9e983f35"` →
`304` curl, and it shows the deployed serve is NOT conditional-blind: only the
date validator is dropped. -/
theorem deployed_inm_304 :
    serveConditional deployedConfig
        { target := ["static", "app.js"], ifNoneMatch := [contentETag appJs] }
        ["static", "app.js"]
      = .notModified (contentETag appJs) :=
  StaticFile.deployed_conditional_304

/-! ## `304` byte format (pure kernel via `Shortcuts.ba_toList_eq`) -/

/-- **`etag_header_name_bytes`.** The header name a `304` response carries is
exactly the ASCII bytes of `"ETag"`. -/
theorem etag_header_name_bytes : strBytes "ETag" = [69, 84, 97, 103] := by
  show "ETag".toUTF8.toList = _
  rw [Shortcuts.ba_toList_eq]; decide

/-- **`notModified_304_empty`.** `toResponse` maps a `.notModified` selection to a
`304`-status response whose single header is the `"ETag"` validator (byte-exact by
`etag_header_name_bytes`) and whose body is EMPTY (RFC 7232 §4.1). -/
theorem notModified_304_empty (etag : ETag) :
    (toResponse (.notModified etag)).status = 304
  ∧ (toResponse (.notModified etag)).headers = [(strBytes "ETag", renderETag etag)]
  ∧ (toResponse (.notModified etag)).body = [] := ⟨rfl, rfl, rfl⟩

end Proto.ConditionalProven

#print axioms Proto.ConditionalProven.reqOfHeaders_drops_ims
#print axioms Proto.ConditionalProven.ims_branch_unreachable
#print axioms Proto.ConditionalProven.deployed_ims_dropped_200
#print axioms Proto.ConditionalProven.deployed_ims_dropped_status
#print axioms Proto.ConditionalProven.deployed_ims_would_304
#print axioms Proto.ConditionalProven.deployed_inm_304
#print axioms Proto.ConditionalProven.etag_header_name_bytes
#print axioms Proto.ConditionalProven.notModified_304_empty
