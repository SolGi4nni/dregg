import Reactor.Pipeline

/-!
# Reactor.Stage.CacheStatus — RFC 9211 `Cache-Status` (ca.1/ca.2 residual)

RFC 9211 defines the standards-track `Cache-Status` response field a cache uses to
tell downstream recipients how it handled the request (`<cache-identity>; hit` /
`<cache-identity>; fwd=miss`, a Structured Field list). The proven cache stage
(`Reactor.Stage.Cache`, ca.1/ca.2) marks replayed responses with the LEGACY
`x-cache: HIT` indicator only; the standards-track field appears nowhere.

## Ground truth — curl against the running dataplane (blocking IO, port 8471, 2026-07-11)

```
$ curl -s -D - -o /dev/null http://127.0.0.1:8471/static/app.js   # twice
HTTP/1.1 200 OK
ETag: "9e983f35"
…
Server: drorb
Content-Length: 35        ← no Cache-Status (and no x-cache) on either fetch
```

This module adds the missing field as a response-phase `Stage` that TRANSLATES the
proven cache stage's legacy indicator into the standards-track one: a response
carrying `x-cache: HIT` gains `Cache-Status: drorb; hit`; any other response gains
`Cache-Status: drorb; fwd=miss` (this edge handled it, no stored response was
used). An upstream's own `Cache-Status` (case-insensitive) is never duplicated or
rewritten; the legacy indicator is left in place (append-only).

## What is proved (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `hitVal_shape` / `missVal_shape` — the emitted values are exactly the RFC 9211
  serialization `cache-identity "; " parameter` (`drorb; hit` / `drorb; fwd=miss`).
* `stampCS_has` — after stamping, EVERY response carries a `Cache-Status`.
* `stampCS_hit` / `stampCS_miss` — the stamped member is `hit` exactly when the
  proven cache stage's replay indicator is present, `fwd=miss` exactly otherwise.
* `stampCS_noop_present` — an upstream `Cache-Status` is never doubled/rewritten.
* `stampCS_prefix` / `stampCS_idem` — append-only; idempotent.
* `csStage_effect` / `csStage_statusStable` — the stage's byte-effect via
  `pipeline_stage_effect`; the status is never touched (safe to braid).
* `demo_hit` / `demo_miss` / `demo_upstream_kept` — concrete non-vacuous witnesses
  through the real `runPipeline` fold (the hit witness uses the exact
  `x-cache: HIT` entry the proven cache stage's `hitHdrs` emits).

Residual (named): wire into the deployed stage fold + curl through the running
socket (dataplane rebuild deferred — box-safety this session); the richer RFC 9211
parameters (`ttl`, `stored`, `collapsed`, `fwd`-reason taxonomy) once the cache
stage surfaces them.
-/

namespace Reactor.Stage.CacheStatus

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Case-insensitive field-name match -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Lowercase field-name token `"cache-status"`. -/
def csTok : Bytes := [99, 97, 99, 104, 101, 45, 115, 116, 97, 116, 117, 115]

/-- Lowercase field-name token `"x-cache"` (the proven cache stage's legacy
replay indicator name). -/
def xCacheTok : Bytes := [120, 45, 99, 97, 99, 104, 101]

/-- Is this field name `Cache-Status` (case-insensitive)? -/
def isCS (name : Bytes) : Bool := lower name == csTok

/-- The legacy indicator value `"HIT"`. -/
def hitTok : Bytes := [72, 73, 84]

/-- Is this header the legacy replay indicator `x-cache: HIT` (name
case-insensitive, value exact — the proven cache stage emits it uppercase)? -/
def isLegacyHit (nv : Bytes × Bytes) : Bool := (lower nv.1 == xCacheTok) && (nv.2 == hitTok)

/-! ## The emitted field (RFC 9211 serialization) -/

/-- The emitted field name `"Cache-Status"`. -/
def csName : Bytes := [67, 97, 99, 104, 101, 45, 83, 116, 97, 116, 117, 115]

/-- The cache-identity `"drorb"`. -/
def cacheIdentity : Bytes := [100, 114, 111, 114, 98]

/-- The hit parameter `"; hit"`. -/
def hitParam : Bytes := [59, 32, 104, 105, 116]

/-- The forward parameter `"; fwd=miss"`. -/
def fwdMissParam : Bytes := [59, 32, 102, 119, 100, 61, 109, 105, 115, 115]

/-- The emitted hit value `"drorb; hit"`. -/
def hitVal : Bytes := [100, 114, 111, 114, 98, 59, 32, 104, 105, 116]

/-- The emitted miss value `"drorb; fwd=miss"`. -/
def missVal : Bytes := [100, 114, 111, 114, 98, 59, 32, 102, 119, 100, 61, 109, 105, 115, 115]

/-- **RFC 9211 shape (hit).** `cache-identity` then the `hit` parameter. -/
theorem hitVal_shape : hitVal = cacheIdentity ++ hitParam := rfl

/-- **RFC 9211 shape (miss).** `cache-identity` then the `fwd=miss` parameter. -/
theorem missVal_shape : missVal = cacheIdentity ++ fwdMissParam := rfl

/-- The emitted name matches its own detector. -/
theorem csName_isCS : isCS csName = true := by decide

/-! ## The stamp -/

/-- Does the header list already carry a `Cache-Status` (case-insensitive)? -/
def hasCS (hs : List (Bytes × Bytes)) : Bool := hs.any (fun nv => isCS nv.1)

/-- Did the proven cache stage replay this response (legacy `x-cache: HIT`)? -/
def isHit (hs : List (Bytes × Bytes)) : Bool := hs.any isLegacyHit

/-- **Stamp `Cache-Status`.** Append `drorb; hit` on a replayed response,
`drorb; fwd=miss` otherwise — unless a `Cache-Status` is already present. -/
def stampCS (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if hasCS hs then hs
  else hs ++ [(csName, if isHit hs then hitVal else missVal)]

/-- The appended entry is seen by the detector, whatever precedes it and whichever
value was chosen. -/
theorem hasCS_append (hs : List (Bytes × Bytes)) (v : Bytes) :
    hasCS (hs ++ [(csName, v)]) = true := by
  unfold hasCS
  rw [List.any_append, List.any_cons, List.any_nil]
  have hname : isCS csName = true := by decide
  rw [hname]
  simp

/-- **Presence.** After stamping, EVERY header list carries a `Cache-Status`. -/
theorem stampCS_has (hs : List (Bytes × Bytes)) : hasCS (stampCS hs) = true := by
  unfold stampCS
  split
  · next h => exact h
  · exact hasCS_append hs _

/-- **Hit translation.** A replayed (legacy-`HIT`-bearing) header list with no
upstream `Cache-Status` gains exactly `Cache-Status: drorb; hit`. -/
theorem stampCS_hit (hs : List (Bytes × Bytes))
    (hno : hasCS hs = false) (hhit : isHit hs = true) :
    stampCS hs = hs ++ [(csName, hitVal)] := by
  unfold stampCS
  rw [hno, hhit]
  simp

/-- **Miss translation.** A non-replayed header list with no upstream
`Cache-Status` gains exactly `Cache-Status: drorb; fwd=miss`. -/
theorem stampCS_miss (hs : List (Bytes × Bytes))
    (hno : hasCS hs = false) (hmiss : isHit hs = false) :
    stampCS hs = hs ++ [(csName, missVal)] := by
  unfold stampCS
  rw [hno, hmiss]
  simp

/-- **No duplication.** A header list already carrying a `Cache-Status`
(case-insensitive) is returned UNCHANGED. -/
theorem stampCS_noop_present (hs : List (Bytes × Bytes)) (h : hasCS hs = true) :
    stampCS hs = hs := by
  unfold stampCS
  rw [h]
  simp

/-- **Append-only.** The original headers are a prefix of the stamped list (in
particular the legacy indicator is kept in place). -/
theorem stampCS_prefix (hs : List (Bytes × Bytes)) : hs <+: stampCS hs := by
  unfold stampCS
  split
  · exact List.prefix_refl hs
  · exact List.prefix_append hs _

/-- **Idempotence.** Stamping a stamped list changes nothing. -/
theorem stampCS_idem (hs : List (Bytes × Bytes)) :
    stampCS (stampCS hs) = stampCS hs :=
  stampCS_noop_present _ (stampCS_has hs)

/-! ## The stage -/

/-- **The `Cache-Status` stage.** Request phase: pass through. Response phase:
stamp the RFC 9211 field onto the finalized headers (one affine `mapResp`),
translating the proven cache stage's legacy replay indicator. Never gates. -/
def csStage : Stage where
  name := "cachestatus"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp (fun r => { r with headers := stampCS r.headers })

/-- **The byte-effect.** The stage maps `stampCS` over the finalized response's
headers, for ANY tail and handler. -/
theorem csStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (csStage :: rest) h c).build).headers
      = stampCS ((runPipeline rest h c).build).headers := by
  rw [pipeline_stage_effect csStage rest h c c rfl]
  rfl

/-- Every response through the stage carries a `Cache-Status` — the RFC 9211
handled-by-this-cache signal, discharged for ANY tail and handler. -/
theorem csStage_response_has_cs (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    hasCS ((runPipeline (csStage :: rest) h c).build).headers = true := by
  rw [csStage_effect]
  exact stampCS_has _

/-- The stage never changes the status — safe to braid into a status-stable onion. -/
theorem csStage_statusStable : csStage.statusStable := fun _ _ => rfl

/-! ## End-to-end witnesses (non-vacuous) -/

/-- The exact legacy replay indicator the proven cache stage emits
(`x-cache: HIT`, lowercase name, uppercase value — its `hitHdrs` head). -/
def legacyHit : Bytes × Bytes := ([120, 45, 99, 97, 99, 104, 101], [72, 73, 84])

/-- A replayed 200 (carries the proven cache stage's indicator). -/
def hitHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [legacyHit], body := [] }

/-- A forwarded (non-replayed) 200 — the deployed curl shape. -/
def missHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [([88], [89])], body := [] }

/-- A 200 already carrying an upstream `cache-status: up; hit` (lowercase name —
the case-insensitivity witness; value `"up; hit"`). -/
def upstreamCsHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [],
             headers := [([99, 97, 99, 104, 101, 45, 115, 116, 97, 116, 117, 115],
                          [117, 112, 59, 32, 104, 105, 116])],
             body := [] }

/-- An empty request context. -/
def demoCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- **End-to-end, hit.** A replayed response gains EXACTLY
`Cache-Status: drorb; hit`, the legacy indicator kept in place. -/
theorem demo_hit :
    ((runPipeline [csStage] hitHandler demoCtx).build).headers
      = [legacyHit, (csName, hitVal)] := by decide

/-- **End-to-end, miss.** A forwarded response gains EXACTLY
`Cache-Status: drorb; fwd=miss`. -/
theorem demo_miss :
    ((runPipeline [csStage] missHandler demoCtx).build).headers
      = [([88], [89]), (csName, missVal)] := by decide

/-- **End-to-end, no duplication.** An upstream `cache-status` (lowercase) passes
through byte-identical. -/
theorem demo_upstream_kept :
    ((runPipeline [csStage] upstreamCsHandler demoCtx).build).headers
      = [([99, 97, 99, 104, 101, 45, 115, 116, 97, 116, 117, 115],
          [117, 112, 59, 32, 104, 105, 116])] := by decide

#print axioms Reactor.Stage.CacheStatus.hitVal_shape
#print axioms Reactor.Stage.CacheStatus.missVal_shape
#print axioms Reactor.Stage.CacheStatus.stampCS_has
#print axioms Reactor.Stage.CacheStatus.stampCS_hit
#print axioms Reactor.Stage.CacheStatus.stampCS_miss
#print axioms Reactor.Stage.CacheStatus.stampCS_noop_present
#print axioms Reactor.Stage.CacheStatus.stampCS_prefix
#print axioms Reactor.Stage.CacheStatus.stampCS_idem
#print axioms Reactor.Stage.CacheStatus.csStage_effect
#print axioms Reactor.Stage.CacheStatus.csStage_response_has_cs
#print axioms Reactor.Stage.CacheStatus.csStage_statusStable
#print axioms Reactor.Stage.CacheStatus.demo_hit
#print axioms Reactor.Stage.CacheStatus.demo_miss
#print axioms Reactor.Stage.CacheStatus.demo_upstream_kept

end Reactor.Stage.CacheStatus
