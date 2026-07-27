import Reactor.Pipeline
import Reactor.Stage.EarlyHints

/-!
# Reactor.Stage.LinkPreload — RFC 8288 `Link: rel=preload` stamping (rt.10 residual)

RFC 8288 (Web Linking) serializes typed links as the `Link` response header; the
`rel=preload` relation (W3C Preload) tells the client to start fetching a critical
subresource before it parses the body. The existing `Reactor.Stage.EarlyHints` lib
(rt.10, HAVE-PROVEN) derives its `103 Early Hints` interim from EXACTLY the final
response's `Link` headers — but nothing in the deployed serve ever SETS one, so the
proven 103 emitter has nothing to advertise.

## Ground truth — curl against the running dataplane (blocking IO, port 8471, 2026-07-11)

```
$ curl -s -D - -o /dev/null http://127.0.0.1:8471/static/app.js
HTTP/1.1 200 OK
ETag: "9e983f35"
Accept-Ranges: bytes
Content-Type: application/javascript
…
Server: drorb
Content-Length: 35            ← no Link, on the 200, the 404, and /health alike
```

This module adds the missing producer as a response-phase `Stage`: append
`Link: </static/app.js>; rel=preload; as=script` to `200` responses that carry no
`Link` (case-insensitive) — an upstream's own `Link` set is never duplicated or
rewritten, and non-`200`s are never decorated.

## What is proved (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `linkVal_shape` — the emitted value is exactly the RFC 8288 §3 serialization
  `"<" URI-Reference ">" ";" link-param ";" link-param`.
* `stampLink_has` — after stamping, a `200`'s header list carries a `Link`, for ANY
  Link-free header list.
* `stampLink_noop_present` / `stampLink_noop_non200` — an existing `Link`
  (case-insensitive) or a non-`200` status is returned UNCHANGED.
* `stampLink_prefix` — stamping only appends (nothing dropped/reordered/rewritten).
* `stampLink_idem` — idempotent (no double-decoration).
* `linkStage_effect` / `linkStage_statusStable` — the stage's byte-effect via
  `pipeline_stage_effect`; the status is never touched (safe to braid).
* **`stamp_feeds_early_hints`** — the composition with the PROVEN rt.10 emitter:
  the stamped entry is exactly what `EarlyHints.onlyLinks` projects, so the `103`
  interim `EarlyHints.earlyHintsEmit` builds over a stamped response advertises the
  preload (`demo_103_carries_preload`: before this stage the deployed 103 was
  provably EMPTY on the curl wire above; after it, it carries the stamp).
* `demo_stamps` / `demo_no_double` / `demo_404_untouched` — concrete non-vacuous
  witnesses through the real `runPipeline` fold.

Residual (named): wire into the deployed stage fold + curl through the running
socket (dataplane rebuild deferred — box-safety this session); a per-route preload
map (this stage carries one configured critical asset, the deployed `/static/app.js`).
-/

namespace Reactor.Stage.LinkPreload

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Case-insensitive field-name match -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Lowercase field-name token `"link"`. -/
def linkTok : Bytes := [108, 105, 110, 107]

/-- Is this field name `Link` (case-insensitive)? -/
def isLinkCI (name : Bytes) : Bool := lower name == linkTok

/-! ## The emitted field (RFC 8288 §3 serialization) -/

/-- The emitted field name — shared with the proven 103 emitter
(`Reactor.Stage.EarlyHints.linkName`, `"Link"`), so the stamped entry is BY
CONSTRUCTION what `onlyLinks` projects into the interim. -/
def linkName : Bytes := EarlyHints.linkName

/-- The configured critical asset (`"/static/app.js"` — the deployed static route's
real asset, the one the ground-truth curl fetched). -/
def uriRef : Bytes := [47, 115, 116, 97, 116, 105, 99, 47, 97, 112, 112, 46, 106, 115]

/-- The relation parameter `"; rel=preload"`. -/
def relParam : Bytes := [59, 32, 114, 101, 108, 61, 112, 114, 101, 108, 111, 97, 100]

/-- The destination parameter `"; as=script"`. -/
def asParam : Bytes := [59, 32, 97, 115, 61, 115, 99, 114, 105, 112, 116]

/-- The emitted value `"</static/app.js>; rel=preload; as=script"`. -/
def linkVal : Bytes :=
  [60, 47, 115, 116, 97, 116, 105, 99, 47, 97, 112, 112, 46, 106, 115, 62,
   59, 32, 114, 101, 108, 61, 112, 114, 101, 108, 111, 97, 100,
   59, 32, 97, 115, 61, 115, 99, 114, 105, 112, 116]

/-- **RFC 8288 §3 grammar.** The emitted value is exactly
`"<" URI-Reference ">" *( ";" link-param )` — the angle-bracketed target followed
by the `rel` and `as` parameters. -/
theorem linkVal_shape : linkVal = [60] ++ uriRef ++ [62] ++ relParam ++ asParam := rfl

/-- The emitted name matches its own case-insensitive detector. -/
theorem linkName_isLinkCI : isLinkCI linkName = true := by decide

/-- The emitted entry matches the PROVEN 103 emitter's exact-name projection
(`EarlyHints.isLink`) — the composition seam, kernel-decided. -/
theorem linkEntry_isLink : EarlyHints.isLink (linkName, linkVal) = true := by decide

/-! ## The stamp -/

/-- Does the header list already carry a `Link` (case-insensitive)? -/
def hasLink (hs : List (Bytes × Bytes)) : Bool := hs.any (fun nv => isLinkCI nv.1)

/-- **Stamp `Link`.** On a `200` with no `Link`, append the preload; otherwise
return the headers unchanged. -/
def stampLink (status : Nat) (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if status == 200 && !hasLink hs then hs ++ [(linkName, linkVal)] else hs

/-- The appended entry is seen by the detector, whatever precedes it. -/
theorem hasLink_append (hs : List (Bytes × Bytes)) :
    hasLink (hs ++ [(linkName, linkVal)]) = true := by
  unfold hasLink
  rw [List.any_append]
  have hlast : List.any [(linkName, linkVal)] (fun nv => isLinkCI nv.1) = true := by decide
  rw [hlast, Bool.or_true]

/-- **Presence.** After stamping, a Link-free `200`'s headers carry a `Link`. -/
theorem stampLink_has (hs : List (Bytes × Bytes)) (h : hasLink hs = false) :
    hasLink (stampLink 200 hs) = true := by
  unfold stampLink
  rw [h]
  simp only [beq_self_eq_true, Bool.not_false, Bool.and_true, if_true]
  exact hasLink_append hs

/-- **No duplication.** A header list already carrying a `Link` (case-insensitive)
is returned UNCHANGED — an upstream `Link` set is never doubled or rewritten. -/
theorem stampLink_noop_present (status : Nat) (hs : List (Bytes × Bytes))
    (h : hasLink hs = true) : stampLink status hs = hs := by
  unfold stampLink
  rw [h]
  simp

/-- **Scope.** A non-`200` is never decorated. -/
theorem stampLink_noop_non200 (status : Nat) (hs : List (Bytes × Bytes))
    (h : status ≠ 200) : stampLink status hs = hs := by
  unfold stampLink
  have hb : (status == 200) = false := by
    simpa using h
  rw [hb]
  simp

/-- **Append-only.** The original headers are a prefix of the stamped list. -/
theorem stampLink_prefix (status : Nat) (hs : List (Bytes × Bytes)) :
    hs <+: stampLink status hs := by
  unfold stampLink
  split
  · exact List.prefix_append hs _
  · exact List.prefix_refl hs

/-- **Idempotence.** Stamping a stamped list changes nothing. -/
theorem stampLink_idem (status : Nat) (hs : List (Bytes × Bytes)) :
    stampLink status (stampLink status hs) = stampLink status hs := by
  cases hg : (status == 200 && !hasLink hs) with
  | false =>
    have hnoop : stampLink status hs = hs := by
      unfold stampLink
      rw [hg]
      simp
    rw [hnoop]
    exact hnoop
  | true =>
    have hst : stampLink status hs = hs ++ [(linkName, linkVal)] := by
      unfold stampLink
      rw [hg]
      simp
    rw [hst]
    exact stampLink_noop_present status _ (hasLink_append hs)

/-! ## The stage -/

/-- **The `Link` preload stage.** Request phase: pass through. Response phase:
stamp the preload onto a Link-free `200`'s finalized headers (one affine
`mapResp`). Never gates. -/
def linkStage : Stage where
  name := "linkpreload"
  onRequest := fun c => .continue c
  onResponse := fun _ b =>
    b.mapResp (fun r => { r with headers := stampLink r.status r.headers })

/-- **The byte-effect.** The stage maps `stampLink` (keyed on the finalized
status) over the finalized response's headers, for ANY tail and handler. -/
theorem linkStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (linkStage :: rest) h c).build).headers
      = stampLink ((runPipeline rest h c).build).status
                  ((runPipeline rest h c).build).headers := by
  rw [pipeline_stage_effect linkStage rest h c c rfl]
  rfl

/-- The stage never changes the status — safe to braid into a status-stable onion. -/
theorem linkStage_statusStable : linkStage.statusStable := fun _ _ => rfl

/-! ## Composition with the PROVEN rt.10 emitter -/

/-- **The stamp feeds the 103.** On a Link-free `200` header list, the proven
`EarlyHints.onlyLinks` projection of the stamped headers is exactly the one
stamped preload entry — so the `103 Early Hints` interim built by the proven
`earlyHintsEmit` advertises it. (Before this stage, the deployed wire had no
`Link` anywhere — see the module-header curl — so the proven 103 was empty.) -/
theorem stamp_feeds_early_hints (hs : List (Bytes × Bytes))
    (h : EarlyHints.onlyLinks hs = []) (hno : hasLink hs = false) :
    EarlyHints.onlyLinks (stampLink 200 hs) = [(linkName, linkVal)] := by
  unfold stampLink
  rw [hno]
  simp only [beq_self_eq_true, Bool.not_false, Bool.and_true, if_true]
  unfold EarlyHints.onlyLinks at *
  rw [List.filter_append, h, List.nil_append]
  rfl

/-! ## End-to-end witnesses (non-vacuous) -/

/-- A bare 200 with one unrelated header (`X: Y`) — the deployed shape (no Link). -/
def bareHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [([88], [89])], body := [] }

/-- A 200 already carrying an upstream lowercase `link: </a>; rel=next`
(value `"</a>; rel=next"`) — the case-insensitivity witness. -/
def upstreamLinkHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [],
             headers := [([108, 105, 110, 107],
                          [60, 47, 97, 62, 59, 32, 114, 101, 108, 61, 110, 101, 120, 116])],
             body := [] }

/-- A 404 — the scope witness. -/
def notFoundHandler : Ctx → Response :=
  fun _ => { status := 404, reason := [], headers := [([88], [89])], body := [] }

/-- An empty request context. -/
def demoCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- **End-to-end.** The single-stage pipeline serves the bare 200 with EXACTLY the
original header followed by the preload `Link` — appended, nothing else touched. -/
theorem demo_stamps :
    ((runPipeline [linkStage] bareHandler demoCtx).build).headers
      = [([88], [89]), (linkName, linkVal)] := by decide

/-- **End-to-end, no duplication.** A 200 already carrying an upstream lowercase
`link` passes through byte-identical (case-insensitive detection). -/
theorem demo_no_double :
    ((runPipeline [linkStage] upstreamLinkHandler demoCtx).build).headers
      = [([108, 105, 110, 107],
          [60, 47, 97, 62, 59, 32, 114, 101, 108, 61, 110, 101, 120, 116])] := by decide

/-- **End-to-end, scope.** A 404 passes through byte-identical (never decorated). -/
theorem demo_404_untouched :
    ((runPipeline [linkStage] notFoundHandler demoCtx).build).headers
      = [([88], [89])] := by decide

/-- **End-to-end, the 103 advertises the preload.** The proven rt.10 projection of
the pipeline's built response is exactly the stamped preload — the `103 Early
Hints` interim the proven emitter builds over this response carries it (via
`EarlyHints.early_hints_103`). -/
theorem demo_103_carries_preload :
    EarlyHints.onlyLinks ((runPipeline [linkStage] bareHandler demoCtx).build).headers
      = [(linkName, linkVal)] := by decide

#print axioms Reactor.Stage.LinkPreload.linkVal_shape
#print axioms Reactor.Stage.LinkPreload.stampLink_has
#print axioms Reactor.Stage.LinkPreload.stampLink_noop_present
#print axioms Reactor.Stage.LinkPreload.stampLink_noop_non200
#print axioms Reactor.Stage.LinkPreload.stampLink_prefix
#print axioms Reactor.Stage.LinkPreload.stampLink_idem
#print axioms Reactor.Stage.LinkPreload.linkStage_effect
#print axioms Reactor.Stage.LinkPreload.linkStage_statusStable
#print axioms Reactor.Stage.LinkPreload.stamp_feeds_early_hints
#print axioms Reactor.Stage.LinkPreload.demo_stamps
#print axioms Reactor.Stage.LinkPreload.demo_no_double
#print axioms Reactor.Stage.LinkPreload.demo_404_untouched
#print axioms Reactor.Stage.LinkPreload.demo_103_carries_preload

end Reactor.Stage.LinkPreload
