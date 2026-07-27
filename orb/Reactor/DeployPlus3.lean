import Reactor.DeployPlus5
import Reactor.ServeConformant
import Reactor.Stage.RetryAfter
import Reactor.Stage.ConditionalRequest
import Reactor.Stage.VaryEncoding
import Reactor.Stage.MultiRange

/-!
# Reactor.DeployPlus3 — four more proven stages onto the extended deployed fold

Extends the `deployStagesPlus5` fold (referenced READ-ONLY — every DeployPlus2/4/5
proof stands) with four more stages, by PREPENDING them, the same pattern as the
earlier waves. List order
`[retryAfter, conditional, vary, multiRangeServe] ++ deployStagesPlus5`,
so the response onion innermost→outermost is
`deployStagesPlus5` → multi-range → vary → conditional → retry-after:

* `Reactor.Stage.RetryAfter.retryAfterStage` (HEAD — outermost): stamp
  `Retry-After: 1` onto a `429` / `503` (RFC 9110 §10.2.3) — the deployed rate
  gate's `429` gains its back-off signal.
* `Reactor.Stage.ConditionalRequest.conditionalStage`: the RFC 7232 precondition
  finisher (`If-Match` mismatch ⇒ `412`, `If-None-Match` match ⇒ `304`) applied to
  the finalized fold response. The deployed handler already discharges
  preconditions on its routes, so this layer is a PROVEN BACKSTOP: it is
  headers-transparent (`conditionalRewrite_headers`) and only ever rewrites an
  unconditioned `200`-with-`ETag` — which the deployed routes do not emit.
* `Reactor.Stage.VaryEncoding.varyStage` (NEW stage, proven in its own module):
  declare `Vary: Accept-Encoding` (RFC 9110 §12.5.5) on every response lacking a
  `Vary` — the deployed gzip stage genuinely negotiates the representation on
  `Accept-Encoding`, and no deployed response named the cache key until now.
* `mrServeStage` (built here): the DEPLOY INTEGRATION of the proven
  `Reactor.Stage.MultiRange.transform` — RFC 9110 §14.6 `multipart/byteranges`.
  The deployed fold answers a MULTI-range request with a bare `206` that blindly
  concatenates the slices (no `Content-Range`, no multipart framing — a live wire
  violation). The proven transform fires only on a full `200`, so wiring the plain
  `multiRangeStage` outside the fold would be provably inert. `mrServeStage`
  therefore STRIPS the `Range` header on a parsed multi-range request (stashing
  the original value in the ctx attribute bag, the pattern the deployed
  PROXY-protocol stage uses), letting the inner fold answer the full `200`, and
  then applies the PROVEN `transform` to that finalized response — emitting the
  genuine `multipart/byteranges` `206` with per-part `Content-Range` framing. A
  single-range request is never stripped (the deployed single-range
  `206 + Content-Range` path is already correct and stays byte-identical).

## What is proven (pure kernel — no `native_decide`, no `Lean.ofReduceBool`)

* `plus3_every_response_has_vary` — EVERY response of the NEW fold carries a
  `Vary`, for ALL contexts (including the inner folds' gate arms — the stamp is
  outermost of every gate).
* `plus3_inner_headers_prefix` — on a metered request with no `Range`, EVERY
  header the inner `deployStagesPlus5` fold finalized reaches the wire verbatim
  (as a prefix): the four added layers never disturb the deployed stamps
  (Via / Cache-Status / CORP / Permissions-Policy / Alt-Svc /
  Timing-Allow-Origin / hardened cookies / …) on this path.
* `plus3_retryAfter_429` / `_503` and the deployed-form
  `plus3_retryAfter_deployed` — a `429`/`503` fold answer carries `Retry-After`.
* `plus3_conditional_ifMatch_412` — if the inner layers finalize an unconditioned
  `200`-with-`ETag` against a failing `If-Match`, the fold answers `412`
  (the RFC 7232 §3.1 MUST, as a fold-level backstop).
* `plus3_multirange_fires` — the headline: on a parsed in-bounds multi-range
  request whose stripped inner fold answers `200`, the extended fold's response is
  a `206` whose `Content-Type` is `multipart/byteranges; boundary=drorbrange` and
  whose body IS `multipartBody`, with EVERY requested range's slice contiguous in
  the body (`plus3_multirange_slices`).
* `plus3_no_range_inner_eq` — a metered request with no `Range` never engages the
  new request-phase machinery: the inner layer byte-equals the Plus5 fold.

Export: `drorb_serve_metered_plus3` (raw) and `drorb_serve_metered_plus3_conformant`
(the RFC-conformance wrapper composed over the extended fold — the
`drorb_serve_metered_plus5_conformant` sibling, same `(peer, seq, input)` ABI), so
the host default flips by swapping the crossed symbol.

Residuals (named): `conditionalStage` is a backstop (the deployed handler already
discharges preconditions on its routes — its rewrite arms are not exercised by
today's routes); on the FIRING multi-range path the inner fold's `Content-Type`
is REPLACED by the multipart one (by design — RFC 9110 §14.6), so the
prefix-preservation theorem is scoped to the no-range path; an out-of-bounds or
malformed multi-range request is answered with the full `200` (RFC 9110 §14.2
allows ignoring `Range`), not `416`; the cookie hardener is NOT re-wired here —
`deployStagesPlus5` already carries it (with its `Set-Cookie` producer).
-/

namespace Reactor.DeployPlus3

open Reactor.Pipeline
open Reactor (Response serialize)
open Reactor.Deploy (appHandler ctxOfMetered)
open Reactor.DeployPlus2 (any_of_prefix mem_of_prefix)
open Reactor.DeployPlus5 (deployStagesPlus5)
open Reactor.Stage.RetryAfter (retryAfterStage retryAfterName retryAfterVal
  needsRetryAfter retryAfterStage_effect retryAfterStage_429_present
  retryAfterStage_503_present)
open Reactor.Stage.ConditionalRequest (conditionalStage conditionalRewrite
  conditionalStage_effect conditionalRewrite_not200 conditionalRewrite_ifMatchFails
  conditionalRewrite_noEtag conditionalRewrite_ifNoneMatch conditionalRewrite_passes
  preconditionFailedOf notModifiedOf respETag ifMatchFails ifNoneMatchMatches)
open Reactor.Stage.VaryEncoding (varyStage hasVary stampVary stampVary_prefix
  stampVary_has varyStage_effect varyStage_response_has_vary)
open Reactor.Stage.MultiRange (transform multipartBody setCt ctName mpCtVal fires
  isCt slice validFor transform_no_range transform_some transform_ct
  transform_status_206 transform_body multipart_carries_slice
  transform_single_passthrough)

/-! ## The multi-range deploy integration stage -/

/-- Attribute key stashing the original `Range` value across the request-phase
strip (the attribute-bag pattern the deployed PROXY-protocol stage uses). -/
def mrKey : String := "mr-orig-range"

/-- Strip every `Range` header (case-insensitive) from a request. -/
def stripRange (req : Proto.Request) : Proto.Request :=
  { req with
    headers := (req.headers.filter (fun nv =>
      !(Reactor.Stage.MultiRange.lower nv.1 == Reactor.Stage.MultiRange.rangeTok))) }

/-- The stripped-and-stashed context a firing multi-range request folds under. -/
def mrStash (c : Ctx) (v : Proto.Bytes) : Ctx :=
  { input := c.input
    req := stripRange c.req
    attrs := (mrKey, v) :: c.attrs }

/-- **The request transform.** On a request whose `Range` parses to TWO OR MORE
ranges: strip the `Range` header (the inner fold then answers the full `200`) and
stash the original value under `mrKey`. A single-range, absent, or unparseable
`Range` leaves the context untouched — the deployed single-range path is not
engaged. Total. -/
def mrReqCtx (c : Ctx) : Ctx :=
  match Reactor.Stage.MultiRange.rangeValOf c.req with
  | some v =>
    match Reactor.Stage.MultiRange.parseRanges (Reactor.Stage.MultiRange.lower v) with
    | some rs => if 2 ≤ rs.length then mrStash c v else c
    | none => c
  | none => c

/-- A minimal request carrying exactly the stashed `Range` value — the PROVEN
`transform`'s theorems apply to it verbatim (`rangesOf (stubReq v)` is
definitionally `parseRanges (lower v)`). -/
def stubReq (v : Proto.Bytes) : Proto.Request :=
  { headers := [(Reactor.Stage.MultiRange.rangeTok, v)] }

/-- The response-phase transform keyed on the stash: present ⇒ the PROVEN
multi-range `transform` under the stashed value; absent ⇒ the identity. -/
def mrApply (stash : Option (String × Proto.Bytes)) (r : Response) : Response :=
  match stash with
  | some p => transform (stubReq p.2) r
  | none => r

theorem mrApply_none (r : Response) : mrApply none r = r := rfl

theorem mrApply_some (p : String × Proto.Bytes) (r : Response) :
    mrApply (some p) r = transform (stubReq p.2) r := rfl

/-- **The multi-range serve stage.** Request phase: `mrReqCtx` (strip + stash on a
multi-range request; identity otherwise). Response phase: `mrApply` of the stash
on the finalized response (one affine `mapResp`). Never gates. -/
def mrServeStage : Stage where
  name := "multi-range-serve"
  onRequest := fun c => .continue (mrReqCtx c)
  onResponse := fun c b => b.mapResp (mrApply (c.attrs.find? (fun p => p.1 == mrKey)))

/-- The stage factors through `pipeline_stage_effect` at its own transformed
context — the defining onion equation. -/
theorem mrServeStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (mrServeStage :: rest) h c
      = mrServeStage.onResponse (mrReqCtx c) (runPipeline rest h (mrReqCtx c)) :=
  pipeline_stage_effect mrServeStage rest h c (mrReqCtx c) rfl

/-- The response phase, built: `mrApply` of the stash on the inner build. -/
theorem mrServe_onResponse_build (c : Ctx) (b : ResponseBuilder) :
    (mrServeStage.onResponse c b).build
      = mrApply (c.attrs.find? (fun p => p.1 == mrKey)) b.build := rfl

/-- No `Range` ⇒ the request phase is the identity. -/
theorem mrReqCtx_no_range (c : Ctx)
    (h : Reactor.Stage.MultiRange.rangeValOf c.req = none) : mrReqCtx c = c := by
  simp only [mrReqCtx, h]

/-- No stash ⇒ the response phase is the identity. -/
theorem mrServe_onResponse_id (c : Ctx) (b : ResponseBuilder)
    (h : c.attrs.find? (fun p => p.1 == mrKey) = none) :
    mrServeStage.onResponse c b = b := by
  show b.mapResp (mrApply (c.attrs.find? (fun p => p.1 == mrKey))) = b
  rw [h]
  rfl

/-- The metered context carries no stash (its two attribute keys are the
IP-filter's and the rate gate's — kernel-decided). -/
theorem metered_no_stash (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) :
    (ctxOfMetered clientIp connSeq input).attrs.find? (fun p => p.1 == mrKey)
      = none :=
  Reactor.Deploy.ctxOfMetered_find_none clientIp connSeq input mrKey
    (by decide) (by decide)

/-! ## The extended deployed chain -/

/-- **The extended deployed chain.** The four stages prepended to the exact
`deployStagesPlus5` fold — referenced read-only, so every earlier-wave proof
stands. Head placement ⇒ their `onResponse` runs OUTERMOST: `retryAfterStage`
last, then `conditionalStage`, `varyStage`, `mrServeStage`; only `mrServeStage`
transforms the request context (strip+stash), and none of the four gates, so
every deployed gate proof is untouched inner behaviour. -/
def deployStagesPlus3 : List Stage :=
  [retryAfterStage, conditionalStage, varyStage, mrServeStage]
    ++ deployStagesPlus5

/-- The built response of the extended metered fold. -/
def deployRespPlus3Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Response :=
  (runPipeline deployStagesPlus3 appHandler (ctxOfMetered clientIp connSeq input)).build

/-- The extended metered serve as wire bytes — what the
`drorb_serve_metered_plus3` export folds. -/
def servePipelinePlus3Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Proto.Bytes :=
  serialize (deployRespPlus3Metered clientIp connSeq input)

/-! ## Layer algebra — how each of the four layers moves headers -/

/-- The conditional rewrite NEVER moves headers — `304` keeps them (strips the
body), `412` keeps them (replaces the body), and every other arm is the
identity. -/
theorem conditionalRewrite_headers (req : Proto.Request) (r : Response) :
    (conditionalRewrite req r).headers = r.headers := by
  by_cases h200 : (r.status == 200) = true
  · cases hE : respETag r with
    | none => rw [conditionalRewrite_noEtag req r h200 hE]
    | some etag =>
      by_cases hm : ifMatchFails req etag = true
      · rw [conditionalRewrite_ifMatchFails req r etag h200 hE hm]; rfl
      · have hm' : ifMatchFails req etag = false := by
          revert hm; cases ifMatchFails req etag <;> simp
        by_cases hn : ifNoneMatchMatches req etag = true
        · rw [conditionalRewrite_ifNoneMatch req r etag h200 hE hm' hn]; rfl
        · have hn' : ifNoneMatchMatches req etag = false := by
            revert hn; cases ifNoneMatchMatches req etag <;> simp
          rw [conditionalRewrite_passes req r etag h200 hE hm' hn']
  · have h200' : (r.status == 200) = false := by
      revert h200; cases (r.status == 200) <;> simp
    rw [conditionalRewrite_not200 req r h200']

/-- The vary layer, built: only the headers move (through `stampVary`) — status,
reason and body are the inner fold's. -/
theorem vary_layer (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (runPipeline (varyStage :: rest) h c).build
      = { (runPipeline rest h c).build with
          headers := stampVary (((runPipeline rest h c).build).headers) } := by
  rw [pipeline_stage_effect varyStage rest h c c rfl]
  rfl

/-! ## Vary presence over the whole fold -/

/-- **Every response of the NEW fold carries a `Vary`** — for ALL contexts (so all
peer/seq/input, INCLUDING the inner folds' gate arms: the stamp runs outside every
gate). The RFC 9110 §12.5.5 negotiation declaration is now unconditional on the
deployed wire. -/
theorem plus3_every_response_has_vary (c : Ctx) :
    hasVary ((runPipeline deployStagesPlus3 appHandler c).build).headers = true := by
  have hv : hasVary ((runPipeline (varyStage :: mrServeStage :: deployStagesPlus5)
      appHandler c).build).headers = true :=
    varyStage_response_has_vary _ appHandler c
  have hcd : hasVary ((runPipeline (conditionalStage :: varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler c).build).headers = true := by
    rw [conditionalStage_effect, conditionalRewrite_headers]
    exact hv
  show hasVary ((runPipeline (retryAfterStage :: conditionalStage :: varyStage
      :: mrServeStage :: deployStagesPlus5) appHandler c).build).headers = true
  rw [retryAfterStage_effect]
  split
  · rw [build_addHeader]
    unfold Reactor.Stage.VaryEncoding.hasVary at hcd ⊢
    exact any_of_prefix _ (List.prefix_append _ _) hcd
  · exact hcd

/-! ## The no-range path preserves every inner header -/

/-- **Inner-headers preservation.** On a metered request with no `Range`, EVERY
header the inner `deployStagesPlus5` fold finalized reaches the NEW fold's wire
response verbatim, as a prefix: the multi-range layer is the identity, the vary
layer only appends, the conditional layer never moves headers, and the retry
layer only appends. So every earlier-wave stamped guarantee (Via / Cache-Status /
CORP / Permissions-Policy / Alt-Svc / Timing-Allow-Origin / hardened cookies)
holds of the NEW deployed default on this path. -/
theorem plus3_inner_headers_prefix (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes)
    (hnr : Reactor.Stage.MultiRange.rangeValOf
      (ctxOfMetered clientIp connSeq input).req = none) :
    ((runPipeline deployStagesPlus5 appHandler
        (ctxOfMetered clientIp connSeq input)).build).headers
      <+: (deployRespPlus3Metered clientIp connSeq input).headers := by
  have hmr : runPipeline (mrServeStage :: deployStagesPlus5) appHandler
        (ctxOfMetered clientIp connSeq input)
      = runPipeline deployStagesPlus5 appHandler
        (ctxOfMetered clientIp connSeq input) := by
    rw [mrServeStage_effect, mrReqCtx_no_range _ hnr]
    exact mrServe_onResponse_id _ _ (metered_no_stash clientIp connSeq input)
  have hvy : ((runPipeline deployStagesPlus5 appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers
      <+: ((runPipeline (varyStage :: mrServeStage :: deployStagesPlus5) appHandler
        (ctxOfMetered clientIp connSeq input)).build).headers := by
    rw [vary_layer, hmr]
    exact stampVary_prefix _
  have hcd : ((runPipeline (conditionalStage :: varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers
      = ((runPipeline (varyStage :: mrServeStage :: deployStagesPlus5) appHandler
        (ctxOfMetered clientIp connSeq input)).build).headers := by
    rw [conditionalStage_effect, conditionalRewrite_headers]
  show ((runPipeline deployStagesPlus5 appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers
    <+: ((runPipeline (retryAfterStage :: conditionalStage :: varyStage
      :: mrServeStage :: deployStagesPlus5) appHandler
      (ctxOfMetered clientIp connSeq input)).build).headers
  rw [retryAfterStage_effect]
  split
  · rw [build_addHeader, hcd]
    exact hvy.trans (List.prefix_append _ _)
  · rw [hcd]
    exact hvy

/-! ## Retry-After over the deployed fold -/

/-- **A `429` fold answer carries `Retry-After`** — for ANY context whose inner
(three-layer + Plus5) fold finalizes a `429` (the deployed rate gate's refusal),
the NEW fold's response carries the RFC 9110 §10.2.3 back-off header. -/
theorem plus3_retryAfter_429 (c : Ctx)
    (h429 : (runPipeline (conditionalStage :: varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler c).acc.status = 429) :
    (retryAfterName, retryAfterVal)
      ∈ ((runPipeline deployStagesPlus3 appHandler c).build).headers :=
  retryAfterStage_429_present (conditionalStage :: varyStage :: mrServeStage
    :: deployStagesPlus5) appHandler c h429

/-- The `503` sibling. -/
theorem plus3_retryAfter_503 (c : Ctx)
    (h503 : (runPipeline (conditionalStage :: varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler c).acc.status = 503) :
    (retryAfterName, retryAfterVal)
      ∈ ((runPipeline deployStagesPlus3 appHandler c).build).headers :=
  retryAfterStage_503_present (conditionalStage :: varyStage :: mrServeStage
    :: deployStagesPlus5) appHandler c h503

/-- **The deployed form.** On a metered request with no `Range` whose deployed
Plus5 fold answers `429` (the rate gate's refusal), the three added inner layers
are transparent, and the NEW fold's wire response carries `Retry-After` — the
deployed rate refusal gains its back-off signal end to end. -/
theorem plus3_retryAfter_deployed (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes)
    (hnr : Reactor.Stage.MultiRange.rangeValOf
      (ctxOfMetered clientIp connSeq input).req = none)
    (h429 : ((runPipeline deployStagesPlus5 appHandler
      (ctxOfMetered clientIp connSeq input)).build).status = 429) :
    (retryAfterName, retryAfterVal)
      ∈ (deployRespPlus3Metered clientIp connSeq input).headers := by
  have hns := metered_no_stash clientIp connSeq input
  have hmr : runPipeline (mrServeStage :: deployStagesPlus5) appHandler
        (ctxOfMetered clientIp connSeq input)
      = runPipeline deployStagesPlus5 appHandler
        (ctxOfMetered clientIp connSeq input) := by
    rw [mrServeStage_effect, mrReqCtx_no_range _ hnr]
    exact mrServe_onResponse_id _ _ hns
  have hvy : ((runPipeline (varyStage :: mrServeStage :: deployStagesPlus5)
      appHandler (ctxOfMetered clientIp connSeq input)).build).status = 429 := by
    rw [vary_layer]
    show ((runPipeline (mrServeStage :: deployStagesPlus5) appHandler
      (ctxOfMetered clientIp connSeq input)).build).status = 429
    rw [hmr]
    exact h429
  have hne : (((runPipeline (varyStage :: mrServeStage :: deployStagesPlus5)
      appHandler (ctxOfMetered clientIp connSeq input)).build).status == 200)
      = false := by
    rw [hvy]
    decide
  apply plus3_retryAfter_429
  show ((runPipeline (conditionalStage :: varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler
      (ctxOfMetered clientIp connSeq input)).build).status = 429
  rw [conditionalStage_effect, conditionalRewrite_not200 _ _ hne]
  exact hvy

/-! ## The conditional backstop over the fold -/

/-- **The RFC 7232 §3.1 backstop.** If the inner layers ever finalize an
unconditioned `200` carrying an `ETag` against a request whose `If-Match` fails,
the NEW fold answers `412 Precondition Failed` — no such `200` escapes the fold,
whatever the inner behaviour. (The deployed handler already discharges
preconditions on its routes, so this hypothesis is not satisfiable there today;
the theorem binds every future inner change.) -/
theorem plus3_conditional_ifMatch_412 (c : Ctx) (etag : Proto.Bytes)
    (h200 : (((runPipeline (varyStage :: mrServeStage :: deployStagesPlus5)
      appHandler c).build).status == 200) = true)
    (he : respETag ((runPipeline (varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler c).build) = some etag)
    (hm : ifMatchFails c.req etag = true) :
    ((runPipeline deployStagesPlus3 appHandler c).build).status = 412 := by
  have hcd : ((runPipeline (conditionalStage :: varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler c).build).status = 412 := by
    rw [conditionalStage_effect,
      conditionalRewrite_ifMatchFails c.req _ etag h200 he hm]
    rfl
  have hacc : (runPipeline (conditionalStage :: varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler c).acc.status = 412 := hcd
  have h412 : needsRetryAfter 412 = false := by decide
  show ((runPipeline (retryAfterStage :: conditionalStage :: varyStage
      :: mrServeStage :: deployStagesPlus5) appHandler c).build).status = 412
  rw [retryAfterStage_effect, hacc, h412]
  simp only [Bool.false_eq_true, if_false]
  exact hcd

/-! ## The multi-range integration, proven end to end -/

/-- `rangesOf` of the stub is definitionally the parse of the stashed value. -/
theorem rangesOf_stub (v : Proto.Bytes) :
    Reactor.Stage.MultiRange.rangesOf (stubReq v)
      = Reactor.Stage.MultiRange.parseRanges (Reactor.Stage.MultiRange.lower v) := rfl

/-- On a parsed multi-range request the request phase strips and stashes. -/
theorem mrReqCtx_fires (c : Ctx) (v : Proto.Bytes) (rs : List (Nat × Nat))
    (hv : Reactor.Stage.MultiRange.rangeValOf c.req = some v)
    (hrs : Reactor.Stage.MultiRange.parseRanges (Reactor.Stage.MultiRange.lower v)
      = some rs)
    (hlen : 2 ≤ rs.length) :
    mrReqCtx c = mrStash c v := by
  simp only [mrReqCtx, hv, hrs, if_pos hlen]

/-- The stripped context's stash is found immediately. -/
theorem stash_found (c : Ctx) (v : Proto.Bytes) :
    (mrStash c v).attrs.find? (fun p => p.1 == mrKey) = some (mrKey, v) := rfl

/-- The inner fold's finalized response on the STRIPPED context — what the proven
transform reads. -/
def mrInner (c : Ctx) (v : Proto.Bytes) : Response :=
  (runPipeline deployStagesPlus5 appHandler (mrStash c v)).build

/-- The multi-range layer, built, on a firing request: EXACTLY the proven
`transform` of the stripped inner fold. -/
theorem mr_layer_fires (c : Ctx) (v : Proto.Bytes) (rs : List (Nat × Nat))
    (hv : Reactor.Stage.MultiRange.rangeValOf c.req = some v)
    (hrs : Reactor.Stage.MultiRange.parseRanges (Reactor.Stage.MultiRange.lower v)
      = some rs)
    (hlen : 2 ≤ rs.length) :
    ((runPipeline (mrServeStage :: deployStagesPlus5) appHandler c).build)
      = transform (stubReq v) (mrInner c v) := by
  rw [mrServeStage_effect, mrServe_onResponse_build,
    mrReqCtx_fires c v rs hv hrs hlen, stash_found, mrApply_some]
  rfl

/-- **The headline: the NEW fold serves genuine `multipart/byteranges`.** On a
request whose `Range` parses to `2 ≤` ranges (`hv`/`hrs`/`hlen`), when the
STRIPPED inner deployed fold answers the full `200` with every range in bounds
(`hfire` — the `fires` condition of the proven transform), the NEW fold's
response is a `206` carrying the
`multipart/byteranges; boundary=drorbrange` `Content-Type` whose body IS the
proven `multipartBody` framing of the inner body — per-part `Content-Range`
headers, terminated boundary. The deployed blind-concatenation wire violation is
closed by construction. -/
theorem plus3_multirange_fires (c : Ctx) (v : Proto.Bytes) (rs : List (Nat × Nat))
    (hv : Reactor.Stage.MultiRange.rangeValOf c.req = some v)
    (hrs : Reactor.Stage.MultiRange.parseRanges (Reactor.Stage.MultiRange.lower v)
      = some rs)
    (hlen : 2 ≤ rs.length)
    (hfire : fires rs (mrInner c v) = true) :
    ((runPipeline deployStagesPlus3 appHandler c).build).status = 206
      ∧ (ctName, mpCtVal)
          ∈ ((runPipeline deployStagesPlus3 appHandler c).build).headers
      ∧ ((runPipeline deployStagesPlus3 appHandler c).build).body
          = multipartBody (mrInner c v).body rs := by
  have hstub : Reactor.Stage.MultiRange.rangesOf (stubReq v) = some rs := by
    rw [rangesOf_stub]; exact hrs
  have hmr := mr_layer_fires c v rs hv hrs hlen
  have hst : ((runPipeline (mrServeStage :: deployStagesPlus5) appHandler
      c).build).status = 206 := by
    rw [hmr]; exact transform_status_206 _ _ rs hstub hfire
  have hhd : ((runPipeline (mrServeStage :: deployStagesPlus5) appHandler
      c).build).headers = setCt (mrInner c v).headers := by
    rw [hmr]; exact transform_ct _ _ rs hstub hfire
  have hbd : ((runPipeline (mrServeStage :: deployStagesPlus5) appHandler
      c).build).body = multipartBody (mrInner c v).body rs := by
    rw [hmr]; exact transform_body _ _ rs hstub hfire
  have hvy := vary_layer (mrServeStage :: deployStagesPlus5) appHandler c
  have hvyst : ((runPipeline (varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler c).build).status = 206 := by
    rw [hvy]; exact hst
  have hne206 : (((runPipeline (varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler c).build).status == 200) = false := by
    rw [hvyst]
    decide
  have hcd : (runPipeline (conditionalStage :: varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler c).build
      = (runPipeline (varyStage :: mrServeStage :: deployStagesPlus5)
          appHandler c).build := by
    rw [conditionalStage_effect, conditionalRewrite_not200 _ _ hne206]
  have hacc : (runPipeline (conditionalStage :: varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler c).acc.status = 206 := by
    show ((runPipeline (conditionalStage :: varyStage :: mrServeStage
      :: deployStagesPlus5) appHandler c).build).status = 206
    rw [hcd]; exact hvyst
  have h206 : needsRetryAfter 206 = false := by decide
  have hout : runPipeline (retryAfterStage :: conditionalStage :: varyStage
      :: mrServeStage :: deployStagesPlus5) appHandler c
      = runPipeline (conditionalStage :: varyStage :: mrServeStage
          :: deployStagesPlus5) appHandler c := by
    rw [retryAfterStage_effect, hacc, h206]
    simp only [Bool.false_eq_true, if_false]
  refine ⟨?_, ?_, ?_⟩
  · show ((runPipeline (retryAfterStage :: conditionalStage :: varyStage
      :: mrServeStage :: deployStagesPlus5) appHandler c).build).status = 206
    rw [hout, hcd]; exact hvyst
  · show (ctName, mpCtVal) ∈ ((runPipeline (retryAfterStage :: conditionalStage
      :: varyStage :: mrServeStage :: deployStagesPlus5) appHandler
      c).build).headers
    rw [hout, hcd, hvy]
    show (ctName, mpCtVal) ∈ stampVary (((runPipeline (mrServeStage
      :: deployStagesPlus5) appHandler c).build).headers)
    apply mem_of_prefix (stampVary_prefix _)
    rw [hhd]
    unfold Reactor.Stage.MultiRange.setCt
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · show ((runPipeline (retryAfterStage :: conditionalStage :: varyStage
      :: mrServeStage :: deployStagesPlus5) appHandler c).build).body
      = multipartBody (mrInner c v).body rs
    rw [hout, hcd, hvy]
    exact hbd

/-- **Slice exactness on the served body.** Under the firing hypotheses, EVERY
requested range's slice sits contiguously in the NEW fold's served body — the
inherited `multipart_carries_slice` composed through the fold. -/
theorem plus3_multirange_slices (c : Ctx) (v : Proto.Bytes) (rs : List (Nat × Nat))
    (p : Nat × Nat)
    (hv : Reactor.Stage.MultiRange.rangeValOf c.req = some v)
    (hrs : Reactor.Stage.MultiRange.parseRanges (Reactor.Stage.MultiRange.lower v)
      = some rs)
    (hlen : 2 ≤ rs.length)
    (hfire : fires rs (mrInner c v) = true)
    (hp : p ∈ rs) :
    ∃ pre post,
      ((runPipeline deployStagesPlus3 appHandler c).build).body
        = pre ++ slice (mrInner c v).body p ++ post := by
  obtain ⟨_h1, _h2, hbody⟩ := plus3_multirange_fires c v rs hv hrs hlen hfire
  rw [hbody]
  exact multipart_carries_slice (mrInner c v).body rs p hp

/-- **No-range transparency.** A metered request with no `Range` header runs the
NEW fold's inner layer to the EXACT Plus5 builder — the deployed single-range and
plain paths are untouched by the request-phase machinery. -/
theorem plus3_no_range_inner_eq (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes)
    (hnr : Reactor.Stage.MultiRange.rangeValOf
      (ctxOfMetered clientIp connSeq input).req = none) :
    runPipeline (mrServeStage :: deployStagesPlus5) appHandler
        (ctxOfMetered clientIp connSeq input)
      = runPipeline deployStagesPlus5 appHandler
          (ctxOfMetered clientIp connSeq input) := by
  rw [mrServeStage_effect, mrReqCtx_no_range _ hnr]
  exact mrServe_onResponse_id _ _ (metered_no_stash clientIp connSeq input)

/-! ## The exports -/

/-- **The extended metered serve seam** (`drorb_serve_metered_plus3`): the
`drorb_serve_metered_plus5` ABI sibling over `deployStagesPlus3`. -/
@[export drorb_serve_metered_plus3]
def drorbServeMeteredPlus3 (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  ByteArray.mk (servePipelinePlus3Metered peer.toList seq.toNat input.toList).toArray

/-- The export is definitionally the extended pipeline (totality: a plain `def`). -/
theorem drorbServeMeteredPlus3_serves (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    drorbServeMeteredPlus3 peer seq input
      = ByteArray.mk
          (servePipelinePlus3Metered peer.toList seq.toNat input.toList).toArray := rfl

section Conformant

open Reactor.ServeConformant (conformantServe respBytesRaw acceptedRaw injectDate
  mkCtx reqBytes mk_toArray_toList addDate missingHostInput stripBody afterBlank
  hasConditional conformant_head_no_body conformant_rejects_missingHost)
open Reactor.Stage.RequestValidation (validationStage badRequestResp)
open Reactor.Stage.StrictValidation (strictStage)
open Reactor.Stage.FramingValidation (framingValidationStage)

/-- **The conformant extended serve** (`drorb_serve_metered_plus3_conformant`):
the proven RFC-conformance wrapper over the NEW fold — the
`drorb_serve_metered_plus5_conformant` sibling, same `(peer, seq, input)` ABI, so
the host default flips by swapping the crossed symbol. -/
@[export drorb_serve_metered_plus3_conformant]
def drorbServeMeteredPlus3Conformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  conformantServe (fun i => drorbServeMeteredPlus3 peer seq i) input

/-- The export is definitionally the conformance wrapper over the NEW fold. -/
theorem drorbServeMeteredPlus3Conformant_serves (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    drorbServeMeteredPlus3Conformant peer seq input
      = conformantServe (fun i => drorbServeMeteredPlus3 peer seq i) input := rfl

/-- **The accepted path serves THE proven extended fold.** On a request that
parses, passes both gates, keeps its origin-form target and carries no
precondition header, the wrapper's raw response bytes are the `Date`-injected
serialization of `deployRespPlus3Metered` — the exact `Response` every theorem
above is stated over. -/
theorem plus3Conformant_accept_serves_fold (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) (req : Proto.Request) (c' c'' : Reactor.Pipeline.Ctx)
    (hp : Proto.RequestSerialize.parse (reqBytes input) = some req)
    (hr : strictStage.onRequest (mkCtx input req) = .continue c')
    (hf : framingValidationStage.onRequest c' = .continue c'')
    (htgt : c''.req.target = req.target)
    (hnc : hasConditional req = false) :
    respBytesRaw (fun i => drorbServeMeteredPlus3 peer seq i) input
      = injectDate (serialize
          (deployRespPlus3Metered peer.toList seq.toNat input.toList)) := by
  have hraw : respBytesRaw (fun i => drorbServeMeteredPlus3 peer seq i) input
      = injectDate (drorbServeMeteredPlus3 peer seq input).toList := by
    simp only [respBytesRaw, hp, hr, hf, htgt, beq_self_eq_true, if_true,
      acceptedRaw, hnc, Bool.false_eq_true, if_false]
  rw [hraw, drorbServeMeteredPlus3_serves, mk_toArray_toList]
  unfold servePipelinePlus3Metered
  rfl

/-- **B1 on the extended conformant default** — a `HEAD` response carries no body
octets, for ANY request bytes. -/
theorem plus3Conformant_head_no_body (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    afterBlank (stripBody
      (respBytesRaw (fun i => drorbServeMeteredPlus3 peer seq i) input)) = [] :=
  conformant_head_no_body _ input

/-- **C1 on the extended conformant default** — a REAL missing-Host request is
refused `400` before the fold is consulted. -/
theorem plus3Conformant_rejects_missingHost (peer : ByteArray) (seq : UInt64) :
    respBytesRaw (fun i => drorbServeMeteredPlus3 peer seq i) missingHostInput
      = serialize (addDate badRequestResp) :=
  conformant_rejects_missingHost _

end Conformant

#print axioms plus3_every_response_has_vary
#print axioms plus3_inner_headers_prefix
#print axioms plus3_retryAfter_429
#print axioms plus3_retryAfter_503
#print axioms plus3_retryAfter_deployed
#print axioms plus3_conditional_ifMatch_412
#print axioms plus3_multirange_fires
#print axioms plus3_multirange_slices
#print axioms plus3_no_range_inner_eq
#print axioms drorbServeMeteredPlus3_serves
#print axioms drorbServeMeteredPlus3Conformant_serves
#print axioms plus3Conformant_accept_serves_fold
#print axioms plus3Conformant_head_no_body
#print axioms plus3Conformant_rejects_missingHost

end Reactor.DeployPlus3
