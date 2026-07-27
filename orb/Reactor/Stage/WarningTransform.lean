import Reactor.Pipeline

/-!
# Reactor.Stage.WarningTransform — RFC 7234 §5.5.3 `Warning: 214` on transformed
responses (ca.1 residual / mw transformation duty)

RFC 7230 §5.7.2 and RFC 7234 §5.5.3: an intermediary that applies a transformation
to a message's representation (changing the content-coding is the canonical
example) MUST add `Warning: 214 - "Transformation Applied"` unless one already
appears. The deployed serve DOES transform — it gzips negotiated responses — and
stamps no `Warning`.

## Ground truth — curl against the running dataplane (blocking IO, port 8471, 2026-07-11)

```
$ curl -s -D - -o /dev/null -H 'Accept-Encoding: gzip' http://127.0.0.1:8471/static/app.js
HTTP/1.1 200 OK
ETag: "9e983f35"                ← the IDENTITY representation's validator, kept
Content-Type: application/javascript
Content-Encoding: gzip          ← the edge changed the coding (58 B vs 35 B identity)
…
Content-Length: 58              ← and no Warning anywhere
```

(RFC 9111 retires the `Warning` field going forward — a cache MAY drop it — but the
RFC 7234-era duty is what the reference deployment class still emits and what a
downstream 7234 cache keys `no-transform` violations on. The successor signal, `203
(Non-Authoritative Information)`, is a status rewrite and out of this stage's
append-only scope; named residual.)

This module adds the missing marker as a response-phase `Stage`: append
`Warning: 214 drorb "Transformation Applied"` to any response that carries a
`Content-Encoding` (the edge-applied coding, per the wire above) and no `Warning`
yet (both case-insensitive). Untransformed responses and responses already carrying
a `Warning` pass byte-identical.

## What is proved (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `warn214Val_shape` — the emitted value is exactly the RFC 7234 §5.5 grammar
  `warn-code SP warn-agent SP quoted warn-text` for code `214`.
* `stampWarn_marks_transform` — EVERY transformed (Content-Encoding-bearing)
  header list carries a `Warning` after the stamp.
* `stampWarn_noop_untransformed` — no `Content-Encoding` ⇒ byte-identical.
* `stampWarn_noop_present` — an existing `Warning` is never doubled.
* `stampWarn_prefix` / `stampWarn_idem` — append-only; idempotent.
* `warningStage_effect` / `warningStage_statusStable` — the stage's byte-effect via
  `pipeline_stage_effect`; the status is never touched (safe to braid).
* `demo_marks_gzip` / `demo_identity_untouched` / `demo_upstream_kept` — concrete
  non-vacuous witnesses through the real `runPipeline` fold, mirroring the curl.

Residual (named): wire into the deployed stage fold + curl through the running
socket (dataplane rebuild deferred — box-safety this session); the `203` status
rewrite; distinguishing an origin-set coding from an edge-applied one (this stage
treats a coded response as transformed, matching the deployed serve, whose origin
representations are stored identity — the curl's 35-byte `app.js`).
-/

namespace Reactor.Stage.WarningTransform

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Case-insensitive field-name match -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Lowercase field-name token `"warning"`. -/
def warnTok : Bytes := [119, 97, 114, 110, 105, 110, 103]

/-- Lowercase field-name token `"content-encoding"`. -/
def ceTok : Bytes :=
  [99, 111, 110, 116, 101, 110, 116, 45, 101, 110, 99, 111, 100, 105, 110, 103]

/-- Is this field name `Warning` (case-insensitive)? -/
def isWarning (name : Bytes) : Bool := lower name == warnTok

/-- Is this field name `Content-Encoding` (case-insensitive)? -/
def isCE (name : Bytes) : Bool := lower name == ceTok

/-! ## The emitted field (RFC 7234 §5.5 grammar) -/

/-- The emitted field name `"Warning"`. -/
def warningName : Bytes := [87, 97, 114, 110, 105, 110, 103]

/-- The warn-code `"214"` (Transformation Applied, RFC 7234 §5.5.3). -/
def warnCode : Bytes := [50, 49, 52]

/-- The warn-agent `"drorb"` (this edge's pseudonym). -/
def warnAgent : Bytes := [100, 114, 111, 114, 98]

/-- The warn-text `"Transformation Applied"` (unquoted content). -/
def warnText : Bytes :=
  [84, 114, 97, 110, 115, 102, 111, 114, 109, 97, 116, 105, 111, 110,
   32, 65, 112, 112, 108, 105, 101, 100]

/-- The emitted value `214 drorb "Transformation Applied"`. -/
def warn214Val : Bytes :=
  [50, 49, 52, 32, 100, 114, 111, 114, 98, 32,
   34, 84, 114, 97, 110, 115, 102, 111, 114, 109, 97, 116, 105, 111, 110,
   32, 65, 112, 112, 108, 105, 101, 100, 34]

/-- **RFC 7234 §5.5 grammar.** The emitted value is exactly
`warn-code SP warn-agent SP DQUOTE warn-text DQUOTE`. -/
theorem warn214Val_shape :
    warn214Val = warnCode ++ [32] ++ warnAgent ++ [32] ++ [34] ++ warnText ++ [34] := rfl

/-- The emitted name matches its own detector. -/
theorem warningName_isWarning : isWarning warningName = true := by decide

/-! ## The stamp -/

/-- Does the header list carry a `Content-Encoding` (case-insensitive) — i.e. was
the representation coded by this edge (per the deployed wire, origin
representations are identity)? -/
def isTransformed (hs : List (Bytes × Bytes)) : Bool := hs.any (fun nv => isCE nv.1)

/-- Does the header list already carry a `Warning` (case-insensitive)? -/
def hasWarning (hs : List (Bytes × Bytes)) : Bool := hs.any (fun nv => isWarning nv.1)

/-- **Stamp `Warning: 214`.** Append the transformation marker to a coded
(`Content-Encoding`-bearing) header list that has no `Warning` yet; otherwise
return the headers unchanged. -/
def stampWarn (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if isTransformed hs && !hasWarning hs then hs ++ [(warningName, warn214Val)] else hs

/-- The appended entry is seen by the detector, whatever precedes it. -/
theorem hasWarning_append (hs : List (Bytes × Bytes)) :
    hasWarning (hs ++ [(warningName, warn214Val)]) = true := by
  unfold hasWarning
  rw [List.any_append]
  have hlast : List.any [(warningName, warn214Val)] (fun nv => isWarning nv.1) = true := by
    decide
  rw [hlast, Bool.or_true]

/-- **The RFC 7234 §5.5.3 duty.** EVERY transformed header list carries a
`Warning` after the stamp — either it already had one (kept verbatim) or the `214`
was appended. -/
theorem stampWarn_marks_transform (hs : List (Bytes × Bytes))
    (h : isTransformed hs = true) : hasWarning (stampWarn hs) = true := by
  unfold stampWarn
  cases hw : hasWarning hs with
  | false => simp [h, hw, hasWarning_append]
  | true => simp [h, hw]

/-- **Untransformed ⇒ untouched.** A header list with no `Content-Encoding` is
returned byte-identical — an identity response is never decorated. -/
theorem stampWarn_noop_untransformed (hs : List (Bytes × Bytes))
    (h : isTransformed hs = false) : stampWarn hs = hs := by
  unfold stampWarn
  rw [h]
  simp

/-- **No duplication.** A header list already carrying a `Warning` is returned
UNCHANGED — an upstream's warning is never doubled or rewritten. -/
theorem stampWarn_noop_present (hs : List (Bytes × Bytes))
    (h : hasWarning hs = true) : stampWarn hs = hs := by
  unfold stampWarn
  rw [h]
  simp

/-- **Append-only.** The original headers are a prefix of the stamped list. -/
theorem stampWarn_prefix (hs : List (Bytes × Bytes)) : hs <+: stampWarn hs := by
  unfold stampWarn
  split
  · exact List.prefix_append hs _
  · exact List.prefix_refl hs

/-- **Idempotence.** Stamping a stamped list changes nothing. -/
theorem stampWarn_idem (hs : List (Bytes × Bytes)) :
    stampWarn (stampWarn hs) = stampWarn hs := by
  cases hg : (isTransformed hs && !hasWarning hs) with
  | false =>
    have hnoop : stampWarn hs = hs := by
      unfold stampWarn
      rw [hg]
      simp
    rw [hnoop]
    exact hnoop
  | true =>
    have hst : stampWarn hs = hs ++ [(warningName, warn214Val)] := by
      unfold stampWarn
      rw [hg]
      simp
    rw [hst]
    exact stampWarn_noop_present _ (hasWarning_append hs)

/-! ## The stage -/

/-- **The transformation-warning stage.** Request phase: pass through. Response
phase: stamp `Warning: 214 drorb "Transformation Applied"` onto the finalized
headers of a coded response (one affine `mapResp`). Never gates. -/
def warningStage : Stage where
  name := "warning214"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp (fun r => { r with headers := stampWarn r.headers })

/-- **The byte-effect.** The stage maps `stampWarn` over the finalized response's
headers, for ANY tail and handler. -/
theorem warningStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (warningStage :: rest) h c).build).headers
      = stampWarn ((runPipeline rest h c).build).headers := by
  rw [pipeline_stage_effect warningStage rest h c c rfl]
  rfl

/-- Every transformed response through the stage carries a `Warning` — the RFC
7234 §5.5.3 obligation, discharged for ANY tail and handler whose response is
coded. -/
theorem warningStage_response_marked (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (ht : isTransformed ((runPipeline rest h c).build).headers = true) :
    hasWarning ((runPipeline (warningStage :: rest) h c).build).headers = true := by
  rw [warningStage_effect]
  exact stampWarn_marks_transform _ ht

/-- The stage never changes the status — safe to braid into a status-stable onion. -/
theorem warningStage_statusStable : warningStage.statusStable := fun _ _ => rfl

/-! ## End-to-end witnesses (non-vacuous) -/

/-- The `Content-Encoding: gzip` entry the deployed wire showed (names/values as
bytes: `content-encoding` / `gzip`). -/
def ceGzip : Bytes × Bytes :=
  ([67, 111, 110, 116, 101, 110, 116, 45, 69, 110, 99, 111, 100, 105, 110, 103],
   [103, 122, 105, 112])

/-- A gzipped 200 — the curl-C shape (`Content-Encoding: gzip`, no Warning). -/
def gzipHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [ceGzip], body := [] }

/-- An identity 200 (no coding) — the curl-A shape. -/
def identityHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [([88], [89])], body := [] }

/-- A coded response already carrying an upstream `Warning: 110 up "stale"`-style
entry (value bytes `110 up "s"` abbreviated). -/
def upstreamWarnHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [],
             headers := [ceGzip, (warningName, [49, 49, 48, 32, 117, 112])],
             body := [] }

/-- An empty request context. -/
def demoCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- **End-to-end.** The single-stage pipeline serves the gzipped 200 with EXACTLY
the original coding header followed by the `214` marker. -/
theorem demo_marks_gzip :
    ((runPipeline [warningStage] gzipHandler demoCtx).build).headers
      = [ceGzip, (warningName, warn214Val)] := by decide

/-- **End-to-end, identity untouched.** An uncoded 200 passes byte-identical. -/
theorem demo_identity_untouched :
    ((runPipeline [warningStage] identityHandler demoCtx).build).headers
      = [([88], [89])] := by decide

/-- **End-to-end, no duplication.** A coded response already carrying an upstream
`Warning` passes byte-identical (the upstream entry preserved verbatim). -/
theorem demo_upstream_kept :
    ((runPipeline [warningStage] upstreamWarnHandler demoCtx).build).headers
      = [ceGzip, (warningName, [49, 49, 48, 32, 117, 112])] := by decide

#print axioms Reactor.Stage.WarningTransform.warn214Val_shape
#print axioms Reactor.Stage.WarningTransform.stampWarn_marks_transform
#print axioms Reactor.Stage.WarningTransform.stampWarn_noop_untransformed
#print axioms Reactor.Stage.WarningTransform.stampWarn_noop_present
#print axioms Reactor.Stage.WarningTransform.stampWarn_prefix
#print axioms Reactor.Stage.WarningTransform.stampWarn_idem
#print axioms Reactor.Stage.WarningTransform.warningStage_effect
#print axioms Reactor.Stage.WarningTransform.warningStage_response_marked
#print axioms Reactor.Stage.WarningTransform.warningStage_statusStable
#print axioms Reactor.Stage.WarningTransform.demo_marks_gzip
#print axioms Reactor.Stage.WarningTransform.demo_identity_untouched
#print axioms Reactor.Stage.WarningTransform.demo_upstream_kept

end Reactor.Stage.WarningTransform
