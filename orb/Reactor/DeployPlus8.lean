import Reactor.DeployPlus6
import Reactor.DeployPlus3
import Reactor.Stage.VaryEncoding
import Reactor.Stage.UriTooLong
import Reactor.Stage.NotAcceptable
import Proto.Kernel.Shortcuts

/-!
# Reactor.DeployPlus8 — one proven-inert stage un-inerted + two missing
refusal surfaces built, onto the DEFAULT serve

Extends the EXACT `Reactor.DeployPlus6.deployStagesPlus6` fold the running
default serves — referenced read-only, so every existing deployed proof stands.

NUMBERING NOTE (honest): `DeployPlus7` is reserved for the in-flight
range/date wave (`RangeUnveil` / `DateCondition` / the cache-bypass seam,
owned by a parallel workstream whose fold has not landed); this module extends
`deployStagesPlus6` DIRECTLY (the `DeployPlus3`-extends-plus5 sparse-numbering
precedent) and re-parents onto that fold by changing one import and one
open when it lands — every theorem here is stated against the inner fold
opaquely plus one status-preservation lemma.

## Un-inerted (proven-in-isolation, never deployed until now)

* **`Reactor.Stage.VaryEncoding.varyStage`, `/bulk`-excluded (`varyGate8`)** —
  the negotiation cache key: the deployed gzip stage genuinely negotiates the
  representation on `Accept-Encoding` on EVERY fold route, and (wire capture
  2026-07-13, default serve) `/health` and `/login` answer `200` with NO
  `Vary` — precisely the shared-cache corruption RFC 9110 §12.5.5 names. The
  stamp runs OUTERMOST (outside every gate — the fold-wide discipline of the
  stage's own `varyStage_response_has_vary`), excluded only on the `/bulk`
  datapath target so the dense-arm bytes are untouched (the exclusion is the
  named residual; `/bulk` is the one deployed route left unnamed).

## Built (the reference has them; the engine had NOTHING)

* **`Reactor.Stage.UriTooLong`** — the `414 (URI Too Long)` refusal (RFC 9110
  §15.5.13) at a 2048-octet target budget. Wire today: a 3000-octet target is
  mis-answered `404`. (Verified FIRABLE on this host: an over-budget target is
  not a cacheable-route shape, so it crosses the metered fold; the budget sits
  far under the head/parse caps, unlike the withdrawn declared-size `413`.)
* **`Reactor.Stage.NotAcceptable`** — the language `406`: `GET /welcome` whose
  `Accept-Language` scores EVERY served representation `q=0` is refused `406`
  with the available tags listed (RFC 9110 §12.5.4 / §15.5.7) — closing the
  plus6 wave's named residual (wire today: served the default `200`).

## Un-inert candidates examined and WITHDRAWN (honest — each verified against
the live default serve before rejection)

* `Reactor.Stage.CacheControl.cacheControlStage` and the static-scoped date
  stamp: their whole scope is `GET /static/…`, and under the deployed default
  (`DRORB_EFFECT_SEAM=1`) every such request is answered by the effect-seam
  cache lane (`interp::should_handle` → `serveStep`), never by this fold —
  proven-inert-in-place theater, the withdrawn-`BodyLimit` class. The static
  surface belongs to the seam's own lane (`cache bypass`, owned elsewhere).
* `Reactor.Stage.Compress.compressStage`: its `encode` is a one-byte
  codec-tag MODEL (`codecTag enc :: body`), not the RFC 7932/1951 container —
  deploying it would stamp a `Content-Encoding` the body does not satisfy (a
  wire LIE breaking every real client). Stays a kernel model.
* `Reactor.DeployPlus3.retryAfterStage`: no `429`/`503` is producible on this
  host (the deployed high-limit bucket ALWAYS admits — `rateHigh_admits`; the
  conn-limit `503` is braided, default-off). Cannot fire.
* `Reactor.DeployPlus3.conditionalStage`: a backstop whose firing hypothesis
  (an unconditioned `200`-with-`ETag` from the fold) no deployed route
  satisfies. Cannot fire.
* `Reactor.DeployPlus3.mrServeStage`: superseded by the plus7 wave's
  `RangeUnveil` (which owns the strip-and-carve on the range surface).

## Stage geometry

`deployStagesPlus8` puts the `Vary` stamp OUTERMOST (outside every gate — a
refusal carries the cache key too), then the two request gates (`414`, `406`),
then the EXACT `deployStagesPlus6` fold (read-only). Gate refusals still
traverse the entire deployed response onion via the gate-carries-transforms
semantics.

## Composition theorems (pure kernel — no `native_decide`, no `ofReduceBool`)

* `plus8_collapse` — **the conservation theorem**: on the `/bulk` datapath
  target, under budget and off the negotiated route, the plus8 response IS the
  plus6 response, byte-for-byte; the dense-arm identity chains it with the
  plus6 conservation theorem to the plus5 fold.
* `plus8_vary` — EVERY non-`/bulk` response of the extended fold carries a
  `Vary`, for ALL contexts (gate arms included — the stamp is outermost).
* `plus8_414` / `plus8_406` — each refusal's status reaches the wire through
  the whole response onion (the inner transforms never rewrite a
  non-`200`).
* Concrete non-vacuous witnesses by kernel `decide`; build-time whole-fold
  `#guard`s (the dense-twin discipline) for the end-to-end shapes.

## Deployment

`drorb_serve_metered_plus8` / `drorb_serve_metered_plus8_conformant` — the
extended metered serve and its RFC-conformant wrapper (same ABI as the plus6
pair). The host's default crossing reaches this fold through the dense twin
(`Datapath.DenseStampsPlus8`) — default-on, NOT behind any env lever.

Named residuals (honest): the `Vary` stamp excludes the `/bulk` datapath
target; the two new gates sit ahead of the metered IP-filter/rate gates and of
the plus6/plus7 gates (the established wave precedent — an input on two edges
is answered by the OUTER gate; on this host the framing seam refuses the
overlapping smuggling shapes before the fold).
-/

namespace Reactor.DeployPlus8

open Reactor.Pipeline
open Reactor (Response serialize)
open Reactor.Deploy (appHandler ctxOf ctxOfMetered)
open Reactor.DeployPlus5 (deployRespPlus5Of)

open Reactor.DeployPlus6 (deployStagesPlus6 deployRespPlus6Of ctxOfShape
  plus5_statusStable multiRange_status_at methodGate6 methodGate6_statusStable)
open Reactor.Stage.ContentLanguage (langStampStage welcomeGateStage
  langStamp_statusStable welcomeGate_statusStable)
open Reactor.Stage.Dashboard (dashTypeStage dashGateStage
  dashTypeStage_statusStable dashGate_statusStable)
open Reactor.Stage.ClTeGuard (clTeGuardStage clTeGuardStage_statusStable)
open Reactor.Stage.VaryEncoding (varyStage stampVary hasVary stampVary_has
  stampVary_prefix varyStage_statusStable varyName aeVal isVary)
open Reactor.Stage.UriTooLong (uriTooLongStage uriTooLongResp overCap
  uriGate_fires uriGate_passes uriGate_onResponse_id uriGate_statusStable
  overCap_empty)
open Reactor.Stage.NotAcceptable (naGateStage notAcceptableResp naGate_fires
  naGate_passes naGate_onResponse_id naGate_statusStable fires_off_welcome
  naBody)
open Reactor.Stage.ContentLanguage (welcomeTarget)
open Reactor.Stage.Dashboard (dashTarget)
open Reactor.Stage.ClTeGuard (clTeConflict)
open Reactor.Stage.MethodFilter (isAllowed)
open Reactor.Stage.MultiRange (rangesOf)
open Reactor.ServeConformant (conformantServe)

/-! ## The `/bulk`-excluded `Vary` stage -/

/-- The dense datapath target's segments (`/bulk`). -/
def bulkSegs : List String := ["bulk"]

/-- Is the request the `/bulk` datapath target? -/
def isBulkTarget (c : Ctx) : Bool :=
  Reactor.App.targetSegments c.req.target == bulkSegs

/-- **The `/bulk`-excluded `Vary: Accept-Encoding` stamp.** Everywhere but the
dense datapath target it is EXACTLY the proven `varyStage` response phase; on
`/bulk` the identity — the dense-arm bytes are untouched (the dense-arm
identity rides this exclusion). -/
def varyGate8 : Stage where
  name := "vary-encoding-nonbulk"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if isBulkTarget c then b else varyStage.onResponse c b

theorem varyGate8_statusStable : Stage.statusStable varyGate8 := by
  intro c b
  show ((if isBulkTarget c then b else varyStage.onResponse c b).build).status
    = b.build.status
  split
  · rfl
  · exact varyStage_statusStable c b

theorem varyGate8_noop_bulk (c : Ctx) (b : ResponseBuilder)
    (hb : isBulkTarget c = true) : varyGate8.onResponse c b = b := by
  show (if isBulkTarget c then b else varyStage.onResponse c b) = b
  rw [hb]
  rfl

theorem varyGate8_stamps (c : Ctx) (b : ResponseBuilder)
    (hnb : isBulkTarget c = false) :
    varyGate8.onResponse c b = varyStage.onResponse c b := by
  show (if isBulkTarget c then b else varyStage.onResponse c b) = _
  rw [hnb]
  rfl

/-- The datapath-target fact in `Bool` form, from the arm's `Prop` equality
(the dense twin's hook — no kernel string reduction involved). -/
theorem isBulkTarget_of_segs (c : Ctx)
    (h : Reactor.App.targetSegments c.req.target = bulkSegs) :
    isBulkTarget c = true := by
  unfold isBulkTarget
  rw [h]
  simp

/-! ## The extended deployed chain -/

/-- **The extended deployed chain.** The `Vary` stamp outermost (outside every
gate), the two refusal gates, then the EXACT `deployStagesPlus6` fold
(read-only). -/
def deployStagesPlus8 : List Stage :=
  varyGate8 :: uriTooLongStage :: naGateStage :: deployStagesPlus6

/-- The built response of the extended fold on a directly-supplied context. -/
def deployRespPlus8Of (c : Ctx) : Response :=
  (runPipeline deployStagesPlus8 appHandler c).build

/-- The built response of the extended METERED fold. -/
def deployRespPlus8Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Response :=
  (runPipeline deployStagesPlus8 appHandler
    (ctxOfMetered clientIp connSeq input)).build

/-- The extended metered serve as wire bytes. -/
def servePipelinePlus8Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Proto.Bytes :=
  serialize (deployRespPlus8Metered clientIp connSeq input)

/-! ## The conservation theorems -/

/-- **The conservation/collapse theorem.** On the `/bulk` datapath target,
under budget and off the negotiated route: the plus8 response IS the plus6
response, byte-for-byte. -/
theorem plus8_collapse (c : Ctx)
    (hb : isBulkTarget c = true)
    (hlen : overCap c.req = false)
    (hw : ¬ c.req.target = welcomeTarget) :
    deployRespPlus8Of c = deployRespPlus6Of c := by
  show (runPipeline (varyGate8 :: uriTooLongStage :: naGateStage ::
      deployStagesPlus6) appHandler c).build = _
  rw [pipeline_stage_effect varyGate8 _ appHandler c c rfl,
      pipeline_stage_effect uriTooLongStage _ appHandler c c
        (uriGate_passes c hlen),
      pipeline_stage_effect naGateStage _ appHandler c c
        (naGate_passes c (fires_off_welcome c hw)),
      uriGate_onResponse_id, naGate_onResponse_id,
      varyGate8_noop_bulk c _ hb]
  rfl

/-! ## The Vary guarantee -/

/-- **EVERY non-`/bulk` response of the extended fold carries a `Vary`** — for
ALL contexts, gate arms included (the stamp is outermost of every gate). The
RFC 9110 §12.5.5 negotiation declaration is now deployed on the whole
non-datapath wire. -/
theorem plus8_vary (c : Ctx) (hnb : isBulkTarget c = false) :
    hasVary (deployRespPlus8Of c).headers = true := by
  show hasVary ((runPipeline (varyGate8 :: uriTooLongStage :: naGateStage ::
      deployStagesPlus6) appHandler c).build).headers = true
  rw [pipeline_stage_effect varyGate8 _ appHandler c c rfl,
      varyGate8_stamps c _ hnb]
  show hasVary (stampVary ((runPipeline (uriTooLongStage :: naGateStage ::
      deployStagesPlus6) appHandler c).build).headers) = true
  exact stampVary_has _

/-! ## The gate refusals reach the wire -/

/-- The plus6 fold under its own outermost multipart transform (definitional
split). -/
def rest6 : List Stage :=
  langStampStage :: dashTypeStage :: clTeGuardStage :: methodGate6 ::
    welcomeGateStage :: dashGateStage :: Reactor.DeployPlus5.deployStagesPlus5

theorem plus6_split : deployStagesPlus6
    = Reactor.Stage.MultiRange.multiRangeStage :: rest6 := rfl

/-- Every stage under the plus6 multipart transform is status-stable. -/
theorem rest6_statusStable : ∀ s ∈ rest6, Stage.statusStable s := by
  intro s hs
  simp only [rest6, List.mem_cons] at hs
  rcases hs with h|h|h|h|h|h|hs
  · subst h; exact langStamp_statusStable
  · subst h; exact dashTypeStage_statusStable
  · subst h; exact clTeGuardStage_statusStable
  · subst h; exact methodGate6_statusStable
  · subst h; exact welcomeGate_statusStable
  · subst h; exact dashGate_statusStable
  · exact plus5_statusStable s hs

/-- **A non-`200` seed keeps its status through the WHOLE inner response
onion** (the multipart transform never rewrites a non-`200`; everything under
it is status-stable). -/
theorem runResp_inner_status (c : Ctx) (b : ResponseBuilder)
    (hne : (b.build.status == 200) = false) :
    ((runResp deployStagesPlus6 c b).build).status = b.build.status := by
  rw [plus6_split, runResp_cons]
  have hin : ((runResp rest6 c b).build).status = b.build.status :=
    runResp_build_status rest6 c b rest6_statusStable
  rw [multiRange_status_at c _ (by rw [hin]; exact hne), hin]

/-- **The `414` reaches the wire** through the entire deployed response onion
(RFC 9110 §15.5.13, deployed). -/
theorem plus8_414 (c : Ctx)
    (hover : overCap c.req = true) :
    (deployRespPlus8Of c).status = 414 := by
  show ((runPipeline (varyGate8 :: uriTooLongStage :: naGateStage ::
      deployStagesPlus6) appHandler c).build).status = 414
  rw [pipeline_stage_effect varyGate8 _ appHandler c c rfl,
      pipeline_gate_short_circuits uriTooLongStage _ appHandler c
        uriTooLongResp (uriGate_fires c hover)]
  have hin : ((runResp (naGateStage :: deployStagesPlus6) c
      (ResponseBuilder.ofResponse uriTooLongResp)).build).status = 414 := by
    rw [runResp_cons, naGate_onResponse_id,
        runResp_inner_status c _ (by decide)]
    rfl
  exact (varyGate8_statusStable c _).trans hin

/-- **The `406` reaches the wire** through the entire deployed response onion
(RFC 9110 §15.5.7, deployed). -/
theorem plus8_406 (c : Ctx)
    (hlen : overCap c.req = false)
    (hfire : Reactor.Stage.NotAcceptable.fires c = true) :
    (deployRespPlus8Of c).status = 406 := by
  show ((runPipeline (varyGate8 :: uriTooLongStage :: naGateStage ::
      deployStagesPlus6) appHandler c).build).status = 406
  rw [pipeline_stage_effect varyGate8 _ appHandler c c rfl,
      pipeline_stage_effect uriTooLongStage _ appHandler c c
        (uriGate_passes c hlen),
      pipeline_gate_short_circuits naGateStage _ appHandler c
        notAcceptableResp (naGate_fires c hfire),
      uriGate_onResponse_id]
  have hin : ((runResp deployStagesPlus6 c
      (ResponseBuilder.ofResponse notAcceptableResp)).build).status = 406 := by
    rw [runResp_inner_status c _ (by decide)]
    rfl
  exact (varyGate8_statusStable c _).trans hin

/-! ## Kernel witnesses (non-vacuous) -/

/-- A 2500-octet request target — refused `414` on the deployed fold. -/
def longCtx : Ctx := ctxOfShape [71, 69, 84] (List.replicate 2500 97) []

theorem witness_414 : (deployRespPlus8Of longCtx).status = 414 :=
  plus8_414 _
    (by show decide (Reactor.Stage.UriTooLong.targetCap
          < (List.replicate 2500 (97 : UInt8)).length) = true
        rw [List.length_replicate]
        rfl)

/-- `GET /welcome` scoring every served representation `q=0` — refused `406`
(`Accept-Language` = `[65,99,…]`, value `de;q=0, en;q=0, fr;q=0`). -/
def q0Ctx8 : Ctx := ctxOfShape [71, 69, 84] welcomeTarget
  [([65, 99, 99, 101, 112, 116, 45, 76, 97, 110, 103, 117, 97, 103, 101],
    [100, 101, 59, 113, 61, 48, 44, 32, 101, 110, 59, 113, 61, 48, 44, 32,
     102, 114, 59, 113, 61, 48])]

theorem witness_406 : (deployRespPlus8Of q0Ctx8).status = 406 :=
  plus8_406 _ (by decide) (by decide)

/-- `GET /health` — a non-`/bulk` route: the deployed answer now names the
negotiation cache key (checked end to end by the `#guard`s below; the
`targetSegments` string machinery does not kernel-reduce, so the concrete
witness is the build-time whole-fold check, and the KERNEL fact is the general
`plus8_vary`). -/
def healthCtx8 : Ctx :=
  ctxOfShape [71, 69, 84] [47, 104, 101, 97, 108, 116, 104] []

/-! ## Build-time whole-fold checks (the dense-twin `#guard` discipline). -/

/-- An off-edges probe (`GET /bulk`). -/
def bulkCtx8 : Ctx := ctxOfShape [71, 69, 84] [47, 98, 117, 108, 107] []

-- The refusals and the stamp fire end to end…
#guard (deployRespPlus8Of longCtx).status == 414
#guard (deployRespPlus8Of q0Ctx8).status == 406
#guard hasVary (deployRespPlus8Of healthCtx8).headers
-- …the inner fold genuinely lacked the key (the stamp closes a REAL gap)…
#guard !(hasVary (deployRespPlus6Of healthCtx8).headers)
-- …no double stamp…
#guard ((deployRespPlus8Of healthCtx8).headers.filter
        (fun nv => isVary nv.1)).length == 1
-- …and on the `/bulk` datapath target the fold is BYTE-IDENTICAL to plus6.
#guard serialize (deployRespPlus8Of bulkCtx8)
        == serialize (deployRespPlus6Of bulkCtx8)

/-! ## The exports (the DEFAULT crossing reaches this fold via the dense twin) -/

/-- **The extended metered serve seam** (`drorb_serve_metered_plus8`) — the
`drorb_serve_metered_plus6` ABI sibling over `deployStagesPlus8`. -/
@[export drorb_serve_metered_plus8]
def drorbServeMeteredPlus8 (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  ByteArray.mk (servePipelinePlus8Metered peer.toList seq.toNat
    input.toList).toArray

/-- What the export folds is definitionally the extended pipeline. -/
theorem drorbServeMeteredPlus8_serves (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    drorbServeMeteredPlus8 peer seq input
      = ByteArray.mk (servePipelinePlus8Metered peer.toList seq.toNat
          input.toList).toArray := rfl

/-- **The extended metered serve, RFC-conformant**
(`drorb_serve_metered_plus8_conformant`): the proven conformance wrapper over
`deployStagesPlus8`. Same `(peer, seq, input)` ABI as the plus6 sibling. -/
@[export drorb_serve_metered_plus8_conformant]
def drorbServeMeteredPlus8Conformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  conformantServe (fun i => drorbServeMeteredPlus8 peer seq i) input

/-- The export is definitionally the conformance wrapper over the extended
fold. -/
theorem drorbServeMeteredPlus8Conformant_serves (peer : ByteArray)
    (seq : UInt64) (input : ByteArray) :
    drorbServeMeteredPlus8Conformant peer seq input
      = conformantServe (fun i => drorbServeMeteredPlus8 peer seq i) input := rfl

end Reactor.DeployPlus8

#print axioms Reactor.DeployPlus8.plus8_collapse
#print axioms Reactor.DeployPlus8.plus8_vary
#print axioms Reactor.DeployPlus8.plus8_414
#print axioms Reactor.DeployPlus8.plus8_406
#print axioms Reactor.DeployPlus8.witness_414
#print axioms Reactor.DeployPlus8.witness_406
#print axioms Reactor.DeployPlus8.drorbServeMeteredPlus8Conformant_serves
