/-
# Proto.EtagProven — ETag / conditional-`304` behavior on the DEPLOYED static handler

PROVE-WHAT-RUNS for the ledger row `h1.etag` (ETag / conditional `304`).

The deployed default app (`Reactor.App.demoApp`, the `demoAppConfig` the running
`drorb_serve` dispatches through `App.handle`) carries a `/static` prefix route to
the `staticFile` handler, and `Reactor.App.responseOfReq req .staticFile` is
DEFINITIONALLY `StaticFile.serveDeployed (targetSegments req.target) req.headers`
(`deployed_staticFile_route`, `rfl`). `serveDeployed` renders
`StaticFile.serveConditional StaticFile.deployedConfig (reqOfHeaders headers)` onto
the wire — real embedded bytes at `/static/app.js` (`StaticFile.appJs`), a
content-hash entity-tag (`StaticFile.contentETag`, FNV-1a rendered `"…"`), and the
RFC 7232 §3.2 / §4.1 conditional selection. So the theorems below describe the
EXACT response the running dataplane emits for `/static/app.js`.

Theorems (all on the deployed `StaticFile.serveConditional StaticFile.deployedConfig`
over the served path `["static","app.js"]`, i.e. what `serveDeployed` renders):

  * `etag_304` — an `If-None-Match` carrying the current content entity-tag makes
    the precondition fail (RFC 7232 §3.2), so the rendered response is `304 (Not
    Modified)` with an EMPTY body (RFC 7232 §4.1).
  * `etag_200_mismatch` — an `If-None-Match` whose opaque tag DIFFERS from the
    current entity-tag does not match under the weak comparison function
    (RFC 7232 §2.3.2), so the full `200 (OK)` with the real body is served.
  * `etag_stable` — the entity-tag the deployed handler emits for the resource is a
    pure function of the resource content (`contentETag appJs`): it is IDENTICAL
    across any two requests, whatever their headers. This is the RFC 7232 §2.3
    validator property the deployed `curl`-then-`If-None-Match` round-trip relies
    on (a stable validator to revalidate against).

The `curl` in the lane's `ran` field re-requests the DEPLOYED endpoint: it GETs
`/static/app.js`, captures the emitted `ETag`, re-requests with that value in
`If-None-Match`, and observes the `304` — the running wire matching this proof.
-/

import StaticFile
import Reactor.App

namespace Proto.EtagProven

open StaticFile

/-- The served path segments for the deployed asset `/static/app.js` — exactly what
`Reactor.App.targetSegments` yields for that request-target and what `serveDeployed`
hands to `serveConditional`. -/
def assetSegs : List String := ["static", "app.js"]

/-- The entity-tag carried by an entity-tag-bearing response (`200`/`206`/
`multipart`/`304`); `none` for the bodies that carry no validator (`416`/`404`/
autoindex). Used to state ETag stability across requests. -/
def respETag? : Resp → Option ETag
  | .ok _ e => some e
  | .partialContent _ _ _ _ e => some e
  | .multipartRanges _ _ e => some e
  | .notModified e => some e
  | .rangeNotSatisfiable _ => none
  | .notFound => none
  | .autoindex _ => none

/-! ## The deployed anchor: the app's `staticFile` route IS `serveDeployed` -/

/-- **`deployed_staticFile_route`.** The DEPLOYED default app's `staticFile`
handler — the one `Reactor.App.handle demoAppConfig` invokes for the `/static`
prefix route — is definitionally `StaticFile.serveDeployed` over the request's
normalized target segments and raw headers. So every theorem below, stated on the
`serveConditional`/`toResponse` core `serveDeployed` renders, is a statement about
the running dataplane's response for `/static/<file>`. -/
theorem deployed_staticFile_route (req : Proto.Request) :
    Reactor.App.responseOfReq req .staticFile
      = StaticFile.serveDeployed (Reactor.App.targetSegments req.target) req.headers := rfl

/-! ## `etag_304` — matching `If-None-Match` ⇒ `304`, empty body -/

/-- **`etag_304`.** When the client's `If-None-Match` carries the current content
entity-tag (`contentETag appJs`), the deployed handler's selected-then-rendered
response for `/static/app.js` is `304 (Not Modified)` with an EMPTY body
(RFC 7232 §3.2: a matching validator fails the precondition; §4.1: a `304` carries
no content). This is the response `serveDeployed` renders — `toResponse` of the
`serveConditional` selection over `deployedConfig`. -/
theorem etag_304 :
    (toResponse (serveConditional deployedConfig
        { target := assetSegs, ifNoneMatch := [contentETag appJs] } assetSegs)).status = 304
  ∧ (toResponse (serveConditional deployedConfig
        { target := assetSegs, ifNoneMatch := [contentETag appJs] } assetSegs)).body = [] := by
  simp only [assetSegs]
  rw [deployed_conditional_304]
  exact ⟨rfl, rfl⟩

/-! ## `etag_200_mismatch` — non-matching `If-None-Match` ⇒ `200` + body -/

/-- **`etag_200_mismatch`.** An `If-None-Match` whose opaque tag DIFFERS from the
current content entity-tag does not match under the RFC 7232 §2.3.2 weak comparison
function, so the precondition holds and the deployed handler serves the full
`200 (OK)` with the real embedded body — never a `304`. Quantified over every tag
that differs, so it is the genuine mismatch direction (non-vacuous: it fails for a
handler that `304`s on a mismatch). -/
theorem etag_200_mismatch (t : ETag) (hne : t.tag ≠ (contentETag appJs).tag) :
    (toResponse (serveConditional deployedConfig
        { target := assetSegs, ifNoneMatch := [t] } assetSegs)).status = 200
  ∧ (toResponse (serveConditional deployedConfig
        { target := assetSegs, ifNoneMatch := [t] } assetSegs)).body = appJs := by
  have hnm : ifNoneMatchHit [t] (contentETag appJs) = false := by
    simp only [ifNoneMatchHit, List.any_cons, List.any_nil, Bool.or_false,
      ETag.weakMatch, beq_eq_false_iff_ne]
    exact hne
  have hserve : serveConditional deployedConfig
      { target := assetSegs, ifNoneMatch := [t] } assetSegs = .ok appJs (contentETag appJs) := by
    simp only [serveConditional, deployedConfig, staticFS, assetSegs, hnm,
      ifModifiedSince304, ifRangeEligible, Bool.false_eq_true, if_false, Bool.not_true]
  rw [hserve]
  exact ⟨rfl, rfl⟩

/-! ## `etag_stable` — the entity-tag is a pure function of the resource content -/

/-- Whenever the deployed handler's selection for `/static/app.js` carries an
entity-tag, that tag is the content hash `contentETag appJs` — independent of the
request. Every entity-tag-bearing branch of `serveConditional` over `deployedConfig`
emits `cfg.etag path = contentETag appJs`. -/
theorem cond_etag (r : Req) (e : ETag)
    (h : respETag? (serveConditional deployedConfig r assetSegs) = some e) :
    e = contentETag appJs := by
  have hfs : deployedConfig.fs assetSegs = some appJs := rfl
  have hetag : deployedConfig.etag assetSegs = contentETag appJs := rfl
  simp only [serveConditional, hfs, hetag] at h
  -- `cur` is now `contentETag appJs`; walk the conditional/range if-chain.
  split at h
  · injection h with h; exact h.symm
  · split at h
    · injection h with h; exact h.symm
    · split at h
      · injection h with h; exact h.symm
      · split at h
        · injection h with h; exact h.symm
        · split at h
          · exact absurd h (by simp [respETag?])
          · injection h with h; exact h.symm
          · injection h with h; exact h.symm

/-- **`etag_stable`.** For ANY two requests to `/static/app.js`, whenever each
selects an entity-tag-bearing response the deployed handler emits the SAME
entity-tag — namely the content hash `contentETag appJs`. The validator the client
captures from a first `GET` and replays in `If-None-Match` is therefore stable, the
precondition the RFC 7232 §2.3 round-trip (and the deployed `304` `curl`) depends
on. -/
theorem etag_stable (r1 r2 : Req) (e1 e2 : ETag)
    (h1 : respETag? (serveConditional deployedConfig r1 assetSegs) = some e1)
    (h2 : respETag? (serveConditional deployedConfig r2 assetSegs) = some e2) :
    e1 = e2 ∧ e1 = contentETag appJs :=
  ⟨(cond_etag r1 e1 h1).trans (cond_etag r2 e2 h2).symm, cond_etag r1 e1 h1⟩

/-! ## Concrete deployed witnesses (the handler actually runs, non-vacuous) -/

/-- A plain `GET /static/app.js` selects the full `200` bearing the content tag, so
`etag_stable`/`etag_200_mismatch` are populated (`respETag?` returns `some` here). -/
theorem plain_get_etag :
    respETag? (serveConditional deployedConfig { target := assetSegs } assetSegs)
      = some (contentETag appJs) := by
  have hserve : serveConditional deployedConfig { target := assetSegs } assetSegs
      = .ok appJs (contentETag appJs) := by
    simp only [serveConditional, deployedConfig, staticFS, assetSegs, ifNoneMatchHit,
      List.any_nil, ifModifiedSince304, ifRangeEligible, Bool.false_eq_true, if_false,
      Bool.not_true]
  rw [hserve]; rfl

/-- The matching `If-None-Match` path selects a `304` bearing the same content tag —
so the `304` `curl` replays exactly the validator a plain `GET` emitted. -/
theorem cond_get_etag :
    respETag? (serveConditional deployedConfig
        { target := assetSegs, ifNoneMatch := [contentETag appJs] } assetSegs)
      = some (contentETag appJs) := by
  simp only [assetSegs]
  rw [deployed_conditional_304]; rfl

end Proto.EtagProven

#print axioms Proto.EtagProven.deployed_staticFile_route
#print axioms Proto.EtagProven.etag_304
#print axioms Proto.EtagProven.etag_200_mismatch
#print axioms Proto.EtagProven.cond_etag
#print axioms Proto.EtagProven.etag_stable
#print axioms Proto.EtagProven.plain_get_etag
#print axioms Proto.EtagProven.cond_get_etag
