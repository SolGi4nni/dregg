import Reactor.Stage.RangeUnveil

/-!
# Reactor.Stage.RangeUnveilCorrect — the deployed range-unveil stage, proven GENERAL

`Reactor.Stage.RangeUnveil.rangeUnveilStage` is a member of `deployPipelineStages`
(the flat 52-stage deployed serve). Its pure decisions (`applyRange` / `carve`) and
its OFF / no-stash arms are already proven `∀` in the base module (`unveil_off_id`,
`unveil_noStash_id`, `applyRange_ifrange_mismatch_200`, `carve_multi_206`, …). But
the stage's actual FIRING behaviour — the request phase's strip-and-stash
round-tripping into the response phase's carve — was checked only on the probe's
concrete bytes: `witness_k06` / `witness_k07` / `witness_k08` call `applyRange`
directly and never exercise the stage's `onRequest → onResponse` plumbing.

This file closes that gap with GENERAL theorems (`∀` request/response satisfying the
guard, the stage produces the RFC-9110 outcome):

* `unveil_onResponse_fires` — the response-phase firing law: a stashed `Range`
  makes the stage's `onResponse` run the proven `applyRange` decision on the built
  response (the firing counterpart of `unveil_noStash_id`, which only did the
  no-stash arm).
* `unveil_stashes_range` — the request phase makes the `Range` value recoverable in
  the response phase (`stashOf (unveilCtx c) = some rv`): the stash round-trip the
  witnesses assumed but never proved.
* `unveil_onResponse_mismatch_200` — K08 (RFC 9110 §13.1.5), general: a non-matching
  `If-Range` leaves the `200` byte-identical, for EVERY built response.
* `unveil_onResponse_match_206` — K07 (RFC 9110 §13.1.5), general: a matching
  `If-Range` with a satisfiable single range carves the exact `206`.
* `unveil_onResponse_multi_206` — K06 (RFC 9110 §14.6), general: a valid multi-range
  carves the `multipart/byteranges` `206`.

All pure kernel (no `native_decide`, no `ofReduceBool`); `#print axioms` clean.
-/

namespace Reactor.Stage.RangeUnveil

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)
open Reactor.Stage.MultiRange (parseRanges lower validFor rangeValOf)
open Reactor.Stage.FramingValidation (trimOWS)

/-! ## The response-phase firing law -/

/-- **A stashed `Range` fires the carve.** When the request phase stashed a range
value, the stage's response phase runs the proven `applyRange` decision on the
built response — the firing counterpart of `unveil_noStash_id` (which covers only
the no-stash arm). General over the context and the threaded builder. -/
theorem unveil_onResponse_fires (c : Ctx) (b : ResponseBuilder) (rv : Bytes)
    (h : stashOf c = some rv) :
    rangeUnveilStage.onResponse c b = b.mapResp (applyRange (ifStashOf c) rv) := by
  show (match stashOf c with
        | some rv => b.mapResp (applyRange (ifStashOf c) rv)
        | none => b) = _
  rw [h]

/-! ## The request-phase stash round-trip -/

/-- **The unveil round-trips the `Range` value.** On an unveiling request whose
`Range` value is `rv` (and whose incoming attribute bag does not already bind the
stash key — true of every deployed context, which stashes only IP / rate keys), the
request-phase `unveilCtx` makes `rv` recoverable by the response phase's `stashOf`.
This is the load-bearing plumbing the concrete witnesses silently assumed: without
it the response-phase carve is never reached. -/
theorem unveil_stashes_range (c : Ctx) (rv : Bytes)
    (hu : unveils c.req = true)
    (hr : rangeValOf c.req = some rv)
    (hfresh : c.attrs.find? (fun kv => kv.1 == ruRangeKey) = none) :
    stashOf (unveilCtx c) = some rv := by
  unfold stashOf unveilCtx
  rw [if_pos hu]
  show ((c.attrs ++ stashPairs c.req).find? (fun kv => kv.1 == ruRangeKey)).map
        (fun kv => kv.2) = some rv
  rw [List.find?_append, hfresh, Option.none_or]
  unfold stashPairs
  rw [hr]
  simp

/-! ## The K08 / K07 / K06 outcomes, lifted to the stage `onResponse` -/

/-- **K08 (RFC 9110 §13.1.5), general.** A stashed, present, non-matching `If-Range`
against a `200` leaves the built response byte-identical — the `Range` is IGNORED
(the always-safe direction). Lifts `applyRange_ifrange_mismatch_200` through the
stage's response phase; the witness `witness_k08` is now the concrete instance of an
`∀`. -/
theorem unveil_onResponse_mismatch_200 (c : Ctx) (b : ResponseBuilder) (rv v : Bytes)
    (hstash : stashOf c = some rv) (hif : ifStashOf c = some v)
    (h200 : (b.build.status == 200) = true)
    (hm : ifRangeMatches v b.build = false) :
    (rangeUnveilStage.onResponse c b).build = b.build := by
  rw [unveil_onResponse_fires c b rv hstash, build_mapResp, hif,
      applyRange_ifrange_mismatch_200 v rv b.build h200 hm]

/-- **K07 (RFC 9110 §13.1.5), general.** A stashed, matching `If-Range` with a
satisfiable single range carves the exact `206`: the requested slice and its
`Content-Range`. Lifts `applyRange_ifrange_match_206` through the stage's response
phase; `witness_k07` is the concrete instance. -/
theorem unveil_onResponse_match_206 (c : Ctx) (b : ResponseBuilder) (rv v : Bytes)
    (r : Nat × Nat)
    (hstash : stashOf c = some rv) (hif : ifStashOf c = some v)
    (h200 : (b.build.status == 200) = true)
    (hm : ifRangeMatches v b.build = true)
    (hp : parseRanges (lower rv) = some [r])
    (hb : (decide (r.2 < b.build.body.length)) = true) :
    (rangeUnveilStage.onResponse c b).build = single206 r b.build := by
  rw [unveil_onResponse_fires c b rv hstash, build_mapResp, hif,
      applyRange_ifrange_match_206 v rv r b.build h200 hm hp hb]

/-- **K06 (RFC 9110 §14.6), general.** A stashed multi-range (no blocking
`If-Range`) that validates against the built `200` carves the `multipart/byteranges`
`206` — the SAME proven payload builder as `Reactor.Stage.MultiRange`. Lifts
`carve_multi_206` through the stage's response phase; `witness_k06` is the concrete
instance. -/
theorem unveil_onResponse_multi_206 (c : Ctx) (b : ResponseBuilder) (rv : Bytes)
    (rs : List (Nat × Nat))
    (hstash : stashOf c = some rv) (hif : ifStashOf c = none)
    (h200 : (b.build.status == 200) = true)
    (hp : parseRanges (lower rv) = some rs) (h2 : 2 ≤ rs.length)
    (hv : validFor b.build.body.length rs = true) :
    (rangeUnveilStage.onResponse c b).build = multipart206 rs b.build := by
  have hab : applyRange none rv b.build = carve rv b.build := by
    unfold applyRange
    rw [h200]
    rfl
  rw [unveil_onResponse_fires c b rv hstash, build_mapResp, hif, hab,
      carve_multi_206 rv rs b.build hp h2 hv]

/-! ## The §14.4 unsatisfiable refusal, lifted to the stage `onResponse` -/

/-- **§14.4 (RFC 9110), general.** A stashed multi-range (no blocking `If-Range`) whose
every member is unsatisfiable against the built `200` makes the stage carve the `416`, and
the refusal carries `Content-Range: bytes */complete-length` — for EVERY context and
builder. Lifts `carve_unsat_416` through the stage's response phase (the firing
counterpart of `carve_unsat_416`, which only decided the `carve` in isolation). -/
theorem unveil_onResponse_unsat_416 (c : Ctx) (b : ResponseBuilder) (rv : Bytes)
    (rs : List (Nat × Nat))
    (hstash : stashOf c = some rv) (hif : ifStashOf c = none)
    (h200 : (b.build.status == 200) = true)
    (hp : parseRanges (lower rv) = some rs) (h2 : 2 ≤ rs.length)
    (hv : validFor b.build.body.length rs = false) :
    (rangeUnveilStage.onResponse c b).build = range416 b.build
    ∧ (contentRangeName, crValUnsat b.build.body.length)
        ∈ (rangeUnveilStage.onResponse c b).build.headers := by
  have hab : applyRange none rv b.build = carve rv b.build := by
    unfold applyRange
    rw [h200]
    rfl
  have key := carve_unsat_416 rv rs b.build hp h2 hv
  have hbuild : (rangeUnveilStage.onResponse c b).build = range416 b.build := by
    rw [unveil_onResponse_fires c b rv hstash, build_mapResp, hif, hab, key.1]
  exact ⟨hbuild, hbuild ▸ key.2⟩

/-! ## The If-Range stash round-trip -/

/-- **The unveil round-trips the `If-Range` validator.** On an unveiling request whose
`If-Range` value is `v` (and whose incoming attribute bag does not already bind the
`If-Range` stash key — true of every deployed context, which stashes only IP / rate keys),
the request-phase `unveilCtx` makes the OWS-trimmed validator recoverable by the response
phase's `ifStashOf`. The `If-Range` counterpart of `unveil_stashes_range`; without it the
§13.1.5 block decision is never reached on the deployed path. -/
theorem unveil_stashes_ifrange (c : Ctx) (v : Bytes)
    (hu : unveils c.req = true)
    (hr : ifRangeValOf c.req = some v)
    (hfresh : c.attrs.find? (fun kv => kv.1 == ruIfRangeKey) = none) :
    ifStashOf (unveilCtx c) = some (trimOWS v) := by
  unfold ifStashOf unveilCtx
  rw [if_pos hu]
  show ((c.attrs ++ stashPairs c.req).find? (fun kv => kv.1 == ruIfRangeKey)).map
        (fun kv => kv.2) = some (trimOWS v)
  rw [List.find?_append, hfresh, Option.none_or]
  unfold stashPairs
  rw [hr, List.find?_append]
  cases hrng : rangeValOf c.req with
  | none => simp
  | some rv => simp [ruRangeKey, ruIfRangeKey]

end Reactor.Stage.RangeUnveil

#print axioms Reactor.Stage.RangeUnveil.unveil_onResponse_fires
#print axioms Reactor.Stage.RangeUnveil.unveil_stashes_range
#print axioms Reactor.Stage.RangeUnveil.unveil_onResponse_mismatch_200
#print axioms Reactor.Stage.RangeUnveil.unveil_onResponse_match_206
#print axioms Reactor.Stage.RangeUnveil.unveil_onResponse_multi_206

#print axioms Reactor.Stage.RangeUnveil.unveil_onResponse_unsat_416
#print axioms Reactor.Stage.RangeUnveil.unveil_stashes_ifrange
