import Datapath.DenseStamps
import Reactor.DeployPlus5

/-!
# Datapath.DenseStampsPlus5 — the DENSE `/bulk` arm for the DEPLOYED default
(the plus5-conformant fold)

`Datapath.DenseStamps` closed the `/bulk` body-cliff at the PLUS2 rung: its dense
head carries the nine edge stamps and is proven byte-identical to
`drorbServeMeteredPlus2Conformant`. But the deployed DEFAULT has since moved TWO
rungs further out: with no env levers the host crosses
`drorb_serve_metered_plus5_conformant` — `deployStagesPlus4`'s three edges
(`Timing-Allow-Origin` on every response, `Content-Location` on static GETs, the
`Max-Forwards` OPTIONS gate) and `deployStagesPlus5`'s four
(the `Set-Cookie` hardener + the three scoped route gates: `GET /login`,
`GET /events`, `GET /app/…`) layered over the plus2 fold. So the plus2-dense twin
is NOT byte-identical to the deployed default (its `/bulk` head lacks the
`Timing-Allow-Origin` stamp), and the default's `/bulk` response still re-crossed
the 1 MiB body as a `List` cons-spine.

This module closes the cliff AT THE DEPLOYED RUNG, by construction:

* `OffEdges` — the decidable request-level conjuncts under which every plus4/plus5
  addition is transparent on the wire except the two outermost pure header maps:
  non-`OPTIONS`/`TRACE` (the `Max-Forwards` gate passes), non-static target (no
  `Content-Location`), target none of `/login`/`/events`/`/app/…` (the three route
  gates pass, the two media-type stamps and the cookie stamp are no-ops).
* `plus5_build_stamped` — on a preamble-free ctx off the edges, the plus5 fold's
  BUILT response is the plus2 stamp chain (`DenseStamps.stampResp`) followed by
  `stampTAO` and the `hardenHeader` map — three PURE header transforms over the
  deployed `deployStagesFull2` build.
* `denseHeadBytesIdxPlus5` — **the deployed-default dense `/bulk` head**: the
  proven index-native dense head with `stampHeaders`, then `stampTAO`, then
  `.map hardenHeader` folded over its header block — O(head) work, never the
  body. The hardener map is APPLIED in the head render (byte-identity needs no
  "no `Set-Cookie` in the block" argument — the head computes the same function).
* `serveMeteredPlus5HeadIdx` / `…_eq` — the deployed-rung metered serve with the
  dense arm, and **the byte-identity**: for EVERY `(peer, seq, input)` it equals
  `drorbServeMeteredPlus5`.
* `serveMeteredPlus5HeadIdxConformant` / `…_eq` — the SAME proven conformance
  wrapper, byte-identical to the deployed default
  `drorbServeMeteredPlus5Conformant` for EVERY `(peer, seq, input)`.

The `/bulk` arm's compute path has NO `toList`: the guard is ONE index-native head
parse (`parseIndexNative` off the borrowed window) + decidable probes on the
parsed (head-sized) request, the head render is the flat block + the three stamp
chains, the body is one native `ByteArray` append of the cached 1 MiB constant.

Residuals (named): the guard's parsed `Proto.Request` fields are `List`-typed
(head-sized — `IndexParse`'s standing residual); `/health` and every off-arm route
fall back to the extended `List` fold (no cliff — small bodies); the conformance
WRAPPER's request-side parse still views the (size-gated, small) request as a
`List`, and its response post-processing copies the response (the fused
single-copy post-processor stays a separate rung).
-/

namespace Datapath.DenseStampsPlus5

open Proto (Bytes)
open Reactor (Response serialize)
open Reactor.Pipeline (Ctx runPipeline pipeline_stage_effect ResponseBuilder
  build_mapResp)
open Reactor.Deploy
open Reactor.DeployPlus4 (deployStagesPlus4 plus4_transparent)
open Reactor.DeployPlus5 (deployStagesPlus5 drorbServeMeteredPlus5
  drorbServeMeteredPlus5Conformant servePipelinePlus5Metered)
open Reactor.Stage.TimingAllowOrigin (stampTAO)
open Reactor.Stage.MaxForwards (isOPTIONS isTRACE)
open Reactor.Stage.ContentLocation (isStaticGet staticPrefix getMethod)
open Reactor.Stage.CookieSecure (cookieSecureStage hardenHeader)
open Reactor.Stage.SessionCookie (sessionGateStage setCookieStage loginTarget
  sessionGate_passes setCookieStage_noop)
open Reactor.Stage.SseServe (sseGateStage sseHeadStage eventsTarget
  sseGate_passes sseHeadStage_noop)
open Reactor.Stage.SpaServe (spaGateStage spaTypeStage spaPrefix
  spaGate_passes spaTypeStage_noop)
open Reactor.Stage.ProxyProtocol (recoverClient clientKey)
open Datapath.DenseHead (renderHead denseHeadersBlock serialize_eq_head_body
  renderHead_eq_headBytes)
open Datapath.SpanBytes (full full_wf read_eq_denote denote_full parseIndexNative
  parseIndexNative_refines)
open Datapath.ServeDenseIdx (ReqArm corrValB corrValB_eq uvBulk uv_arm
  deploySubs_dispatch bulkArm_of_reqArm healthReq bulkGzipReq)
open Datapath.ServeDenseReal (BulkArm denseOut_eq bulkDemoReq bulkDemoReqAnyHost
  appHandler_bulk builtScalars denseHeadersUnknown)
open Datapath.ServeDenseFullReal (bulkBodyDense)
open Datapath.ServeHeadIdx (noPreambleB noPreambleB_sound echoPostReq oldReq)
open Datapath.ServeMeteredHeadIdx (ipGateB rateGateB ctxAddr_metered
  rate_admits_metered ipfilterStage_pass_admit full2_reduces_unknown_pass
  innerFold_ctxOfMetered cleanPeer blockedPeer)
open Datapath.DenseStamps (stampResp stampHeaders stampResp_200
  plus2_build_stamped meteredAttrs_no_client preambledReq headHas
  serveMeteredPlus2HeadIdx)
open Reactor.ServeConformant (ba_toList_eq ba_toList_length)

/-! ## 1. The off-edges request conjuncts (decidable, head-sized) -/

/-- **The off-edges conjuncts.** The decidable request-level facts under which the
six plus4/plus5 request-phase additions all PASS and the response-phase additions
collapse to the two pure header maps (`stampTAO`, `.map hardenHeader`):
non-`OPTIONS`/`TRACE` method, non-static-prefix target, target none of the three
scoped routes. Every probe reads the (head-sized) parsed request, never the body. -/
def OffEdges (req : Proto.Request) : Prop :=
  (isOPTIONS req || isTRACE req) = false
  ∧ staticPrefix.isPrefixOf req.target = false
  ∧ ¬ (req.target = loginTarget)
  ∧ ¬ (req.target = eventsTarget)
  ∧ spaPrefix.isPrefixOf req.target = false

instance (req : Proto.Request) : Decidable (OffEdges req) := by
  unfold OffEdges; infer_instance

/-! ## 2. The extended fold IS the three pure header maps over the deployed fold
(preamble-free, off the edges) -/

/-- **The plus5 fold as three pure header transforms.** With no recoverable
preamble, no stashed client attr, and the request off the plus4/plus5 edges, the
deployed-default fold's BUILT response is the plus2 stamp chain (`stampResp`),
then `stampTAO`, then the `hardenHeader` map, over the deployed
`deployStagesFull2` build — nothing else moves. -/
theorem plus5_build_stamped (c : Ctx)
    (hrec : recoverClient c.input = none)
    (hfind : c.attrs.find? (fun p => p.1 == clientKey) = none)
    (hmeth : (isOPTIONS c.req || isTRACE c.req) = false)
    (hns : isStaticGet c = false)
    (hlog : ¬ c.req.target = loginTarget)
    (hev : ¬ c.req.target = eventsTarget)
    (hpre : spaPrefix.isPrefixOf c.req.target = false) :
    (runPipeline deployStagesPlus5 appHandler c).build
      = { stampResp ((runPipeline deployStagesFull2 appHandler c).build) with
          headers :=
            (stampTAO (stampResp ((runPipeline deployStagesFull2 appHandler
              c).build)).headers).map hardenHeader } := by
  have hout : (runPipeline deployStagesPlus5 appHandler c).build
      = ((runPipeline deployStagesPlus4 appHandler c).mapResp
          (fun r => { r with headers := r.headers.map hardenHeader })).build := by
    show (runPipeline (cookieSecureStage :: setCookieStage :: sseHeadStage
        :: spaTypeStage :: sseGateStage :: spaGateStage :: sessionGateStage
        :: deployStagesPlus4) appHandler c).build = _
    rw [pipeline_stage_effect cookieSecureStage _ appHandler c c rfl,
        setCookieStage_noop _ appHandler c hlog,
        sseHeadStage_noop _ appHandler c hev,
        spaTypeStage_noop _ appHandler c hpre,
        pipeline_stage_effect sseGateStage _ appHandler c c (sseGate_passes c hev),
        pipeline_stage_effect spaGateStage _ appHandler c c (spaGate_passes c hpre),
        pipeline_stage_effect sessionGateStage _ appHandler c c
          (sessionGate_passes c hlog)]
    rfl
  rw [hout, build_mapResp, plus4_transparent c hmeth hns,
      plus2_build_stamped c hrec hfind]

/-! ## 3. The deployed-default dense `/bulk` head -/

/-- **THE DEPLOYED-DEFAULT DENSE HEAD** — the proven index-native dense `/bulk`
head with the FULL deployed stamp pipeline folded over its header block:
`stampHeaders` (the nine plus2 edges), then `stampTAO`, then the `hardenHeader`
map — all O(head) work over the small header list, rendered with the dense body
LENGTH, never the body bytes, and NO `toList` of the input. -/
def denseHeadBytesIdxPlus5 (input : ByteArray) : Bytes :=
  renderHead 200 (Reactor.App.reasonFor 200)
    ((stampTAO (stampHeaders
        (denseHeadersBlock [] uvBulk (corrValB input)).denote)).map hardenHeader)
    Reactor.App.bulkSize

/-! ## 4. The index-decided deployed-rung arm guard -/

/-- **The deployed-rung dense-arm guard.** Size gates by `input.size` (O(1) field
reads), the head parse by `parseIndexNative` (index probes off the borrowed
window), the `/bulk`-arm conjuncts AND the off-edges conjuncts decided on the
parsed (head-sized) request. NO `input.toList`, NO `deploySubs` on the deciding
path. -/
def armB5 (input : ByteArray) : Bool :=
  decide (0 < input.size)
    && decide (¬ input.size > deployConfig.maxHeaderBytes)
    && (match parseIndexNative (full input) with
        | .request _ req _ => decide (ReqArm req ∧ OffEdges req)
        | _ => false)

/-- **Guard soundness, surfaced at the dispatch.** A firing guard yields the
dispatched request together with its `/bulk`-arm and off-edges conjuncts — the
same parse-refinement + dispatch bridge `denseArmB_sound` crosses. -/
theorem armB5_dispatch (input : ByteArray) (h : armB5 input = true) :
    ∃ req rest, deploySubs input.toList = .dispatch req :: rest
      ∧ ReqArm req ∧ OffEdges req := by
  unfold armB5 at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hsz, hlen⟩, harm⟩ := h
  have hread : (full input).read = input.toList := by
    rw [read_eq_denote _ (full_wf _), denote_full, ← ba_toList_eq]
  cases hpo : parseIndexNative (full input) with
  | request n req ka =>
    rw [hpo] at harm
    obtain ⟨harm', hoff⟩ := of_decide_eq_true harm
    have hparse : Reactor.Config.h1ParseFn input.toList = .request n req ka := by
      rw [← hread, ← parseIndexNative_refines _ (full_wf _), hpo]
    have hlen' : ¬ input.toList.length > deployConfig.maxHeaderBytes := by
      rw [ba_toList_length]; exact of_decide_eq_true hlen
    have hne : input.toList.isEmpty = false := by
      have hpos : 0 < input.toList.length := by
        rw [ba_toList_length]; exact of_decide_eq_true hsz
      cases hl : input.toList with
      | nil => rw [hl] at hpos; exact absurd hpos (by simp)
      | cons a t => rfl
    obtain ⟨rest, hsub⟩ := deploySubs_dispatch input.toList n req ka hlen' hne hparse
    exact ⟨req, rest, hsub, harm', hoff⟩
  | reject n resp => rw [hpo] at harm; exact absurd harm (by simp)
  | incomplete => rw [hpo] at harm; exact absurd harm (by simp)
  | error => rw [hpo] at harm; exact absurd harm (by simp)

/-- On a firing guard the deployed-default dense head is the deployed dense head
under the full stamp pipeline — the same scalar collapse (`corrValB_eq` +
`uv_arm`) as the plus2 head, under the two further maps. -/
theorem denseHeadBytesIdxPlus5_eq (input : ByteArray) (h : armB5 input = true) :
    denseHeadBytesIdxPlus5 input
      = renderHead 200 (Reactor.App.reasonFor 200)
          ((stampTAO (stampHeaders (denseHeadersBlock []
            (upstreamVal (deployPlan (deploySubs input.toList)))
            (corrVal input.toList)).denote)).map hardenHeader)
          Reactor.App.bulkSize := by
  obtain ⟨req, rest, hsub, harm, _⟩ := armB5_dispatch input h
  obtain ⟨_, _, _, _, _, _, _, _, hseg, _, _⟩ := harm
  unfold denseHeadBytesIdxPlus5
  rw [corrValB_eq, uv_arm input.toList req rest hsub hseg]

/-! ## 5. The dense arm equals the deployed-default metered fold on `/bulk` -/

set_option maxHeartbeats 1600000 in
/-- The wire bytes of the fully-stamped `200`: the head rendered over the stamped
headers, followed by the unchanged body. Stated at a GENERIC response so every
record-collapse step happens on small neutral terms. -/
theorem serialize_stamped5 (r : Response) (h : r.status = 200) :
    serialize { stampResp r with
        headers := (stampTAO (stampResp r).headers).map hardenHeader }
      = renderHead 200 r.reason
          ((stampTAO (stampHeaders r.headers)).map hardenHeader)
          r.body.length ++ r.body := by
  rw [stampResp_200 r h]
  show serialize { r with
      headers := (stampTAO (stampHeaders r.headers)).map hardenHeader } = _
  rw [serialize_eq_head_body, ← renderHead_eq_headBytes]
  show renderHead r.status r.reason
      ((stampTAO (stampHeaders r.headers)).map hardenHeader)
      r.body.length ++ r.body = _
  rw [h]

/-- **The deployed-default dense `/bulk` assembly is byte-identical to the
extended metered fold.** On a firing guard with both metered gates admitting and
a preamble-free input, `stamped head ++ dense 1 MiB body` equals
`serialize (deployRespPlus5Metered …)` — the deployed default's exact wire bytes.
NO 1 MiB `List` on the compute path. -/
theorem plus5DenseArm_eq (peer : ByteArray) (seq : UInt64) (input : ByteArray)
    (h : armB5 input = true) (hip : ipGateB peer = true)
    (hrate : rateGateB seq.toNat = true) (hnp : noPreambleB input = true) :
    ByteArray.mk (denseHeadBytesIdxPlus5 input).toArray ++ bulkBodyDense
      = ByteArray.mk (servePipelinePlus5Metered peer.toList seq.toNat
          input.toList).toArray := by
  obtain ⟨req, rest, hsub, harm, hoff⟩ := armB5_dispatch input h
  have hreq : (ctxOf input.toList).req = req := ctxOf_req input.toList req rest hsub
  have harm' : BulkArm (ctxOf input.toList) :=
    bulkArm_of_reqArm input.toList req hreq harm
  obtain ⟨hadmin, hpriv, hrate0, hredir, htrav, hpol, hgz, hcors, hseg, hna, hnb⟩ := harm'
  obtain ⟨hmeth5, hstat5, hlog5, hev5, hpre5⟩ := hoff
  -- the metered gates admit at the metered ctx
  have hip_m : Reactor.Stage.IpFilter.deployAdmits
      (Reactor.Stage.IpFilter.ctxAddr
        (ctxOfMetered peer.toList seq.toNat input.toList)) = true := by
    rw [ctxAddr_metered]; exact hip
  have hrate_m : Reactor.Stage.Rate.admits
      (ctxOfMetered peer.toList seq.toNat input.toList) = true := by
    rw [rate_admits_metered]; exact hrate
  -- the metered deployed fold collapses to the bare deployed fold on the arm
  have hin : (ctxOfMetered peer.toList seq.toNat input.toList).input
      = (ctxOf input.toList).input := rfl
  have hkey : runPipeline deployStagesFull2 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)
      = runPipeline deployStagesFull2 appHandler (ctxOf input.toList) := by
    rw [full2_reduces_unknown_pass (ctxOfMetered peer.toList seq.toNat input.toList)
          hadmin hpriv (ipfilterStage_pass_admit _ hip_m) hrate_m hredir htrav hpol,
        full2_reduces_unknown (ctxOf input.toList) hadmin hpriv rfl hrate0 hredir
          htrav hpol,
        innerFold_ctxOfMetered peer.toList seq.toNat input.toList, hin]
  -- the request facts at the metered ctx (its req IS the dispatched req)
  have hreqm : (ctxOfMetered peer.toList seq.toNat input.toList).req = req := hreq
  have hmeth : (isOPTIONS (ctxOfMetered peer.toList seq.toNat input.toList).req
      || isTRACE (ctxOfMetered peer.toList seq.toNat input.toList).req) = false := by
    rw [hreqm]; exact hmeth5
  have hns : isStaticGet (ctxOfMetered peer.toList seq.toNat input.toList) = false := by
    show ((ctxOfMetered peer.toList seq.toNat input.toList).req.method == getMethod
        && staticPrefix.isPrefixOf
            (ctxOfMetered peer.toList seq.toNat input.toList).req.target) = false
    rw [hreqm, hstat5, Bool.and_false]
  have hlog : ¬ (ctxOfMetered peer.toList seq.toNat input.toList).req.target
      = loginTarget := by rw [hreqm]; exact hlog5
  have hev : ¬ (ctxOfMetered peer.toList seq.toNat input.toList).req.target
      = eventsTarget := by rw [hreqm]; exact hev5
  have hpre : spaPrefix.isPrefixOf
      (ctxOfMetered peer.toList seq.toNat input.toList).req.target = false := by
    rw [hreqm]; exact hpre5
  -- the whole extended prefix collapses to the three pure header maps
  have hrec : recoverClient
      (ctxOfMetered peer.toList seq.toNat input.toList).input = none :=
    noPreambleB_sound input hnp
  have h1 : (runPipeline deployStagesPlus5 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build
      = { stampResp ((runPipeline deployStagesFull2 appHandler
            (ctxOf input.toList)).build) with
          headers :=
            (stampTAO (stampResp ((runPipeline deployStagesFull2 appHandler
              (ctxOf input.toList)).build)).headers).map hardenHeader } := by
    rw [plus5_build_stamped _ hrec
          (meteredAttrs_no_client peer.toList seq.toNat input.toList)
          hmeth hns hlog hev hpre, hkey]
  -- the bare built response on the arm: scalars + the dense header block
  have happ := appHandler_bulk (ctxOf input.toList) hseg hna hnb
  obtain ⟨hst, hrs, hbd⟩ := builtScalars (ctxOf input.toList) hadmin hpriv rfl
    hrate0 hredir htrav hpol hgz hcors happ
  have hhdr := denseHeadersUnknown (ctxOf input.toList) hadmin hpriv rfl
    hrate0 hredir htrav hpol hgz hcors
  have hAheaders : (appHandler (ctxOf input.toList)).headers = [] := by rw [happ]
  have hinput : (ctxOf input.toList).input = input.toList := rfl
  -- the wire bytes of the deployed-default fold, as stamped head ++ body
  have hlist : servePipelinePlus5Metered peer.toList seq.toNat input.toList
      = denseHeadBytesIdxPlus5 input ++ Reactor.App.bulkBody := by
    show serialize ((runPipeline deployStagesPlus5 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build) = _
    rw [h1, serialize_stamped5 _ hst]
    rw [hrs, hbd, Reactor.App.bulkBody_length,
        show ((runPipeline deployStagesFull2 appHandler (ctxOf input.toList)).build).headers
          = (denseHeadersBlock []
              (upstreamVal (deployPlan (deploySubs input.toList)))
              (corrVal input.toList)).denote from by
            rw [← hhdr, hAheaders, hinput],
        denseHeadBytesIdxPlus5_eq input h]
  calc ByteArray.mk (denseHeadBytesIdxPlus5 input).toArray ++ bulkBodyDense
      = ByteArray.mk (denseHeadBytesIdxPlus5 input ++ Reactor.App.bulkBody).toArray :=
        denseOut_eq _
    _ = ByteArray.mk (servePipelinePlus5Metered peer.toList seq.toNat
          input.toList).toArray := by rw [hlist]

/-! ## 6. THE SERVE — the deployed-rung metered serve with the dense `/bulk` arm -/

/-- **The dense-stamped deployed-rung metered serve.** Metered gates on the host
scalars, the O(1) preamble probe, ONE index-native head parse deciding the
`/bulk`-arm + off-edges conjuncts, the arm emitted as
`fully-stamped dense head ++ dense 1 MiB body`. Everything else — off-arm routes,
on-edge requests (`OPTIONS`/`TRACE`, static, `/login`, `/events`, `/app/…`),
refused gates, preambled inputs, unparsable heads — is the deployed-default
metered `List` fold verbatim. -/
def serveMeteredPlus5HeadIdx (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  if armB5 input && ipGateB peer && rateGateB seq.toNat && noPreambleB input then
    ByteArray.mk (denseHeadBytesIdxPlus5 input).toArray ++ bulkBodyDense
  else drorbServeMeteredPlus5 peer seq input

/-- **THE BYTE-IDENTITY.** For EVERY `(peer, seq, input)` the deployed-rung
dense-stamped serve produces the IDENTICAL bytes to the deployed-default metered
fold (`drorbServeMeteredPlus5`): a firing guard implies the dense assembly equals
the fold (`plus5DenseArm_eq`); everywhere else it IS the fold. -/
theorem serveMeteredPlus5HeadIdx_eq (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    serveMeteredPlus5HeadIdx peer seq input
      = drorbServeMeteredPlus5 peer seq input := by
  unfold serveMeteredPlus5HeadIdx
  cases hg : armB5 input && ipGateB peer && rateGateB seq.toNat
      && noPreambleB input with
  | false => rw [if_neg Bool.false_ne_true]
  | true =>
    rw [if_pos rfl]
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨harm, hip⟩, hrate⟩, hnp⟩ := hg
    exact plus5DenseArm_eq peer seq input harm hip hrate hnp

/-! ## 7. The RFC-conformant wrapper — the seam the deployed DEFAULT crosses -/

/-- **`drorb_serve_metered_plus5_dense_conformant`** — the deployed default's
conformance wrapper (431-gate → validation/framing gates → inner → `Date` splice
→ scrub → `HEAD`-strip) around the deployed-rung dense-stamped serve. Same
`(peer, seq, input)` ABI as `drorb_serve_metered_plus5_conformant`. -/
-- EXPORT MOVED (2026-07-13): the host default symbol
-- drorb_serve_metered_plus5_dense_conformant is now exported by
-- Datapath.DenseStampsPlus6 (the plus6 fold with the same dense /bulk arm);
-- this def and every theorem below stand unchanged as the plus5 rung.
def serveMeteredPlus5HeadIdxConformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  Reactor.ServeConformant.conformantServe
    (fun i => serveMeteredPlus5HeadIdx peer seq i) input

/-- **The wrapper preserves the byte-identity**: the dense-stamped conformant
serve equals the deployed default `drorbServeMeteredPlus5Conformant` for EVERY
`(peer, seq, input)` — the inners are equal as functions, and the wrapper is a
function of its inner. -/
theorem serveMeteredPlus5HeadIdxConformant_eq (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    serveMeteredPlus5HeadIdxConformant peer seq input
      = drorbServeMeteredPlus5Conformant peer seq input := by
  unfold serveMeteredPlus5HeadIdxConformant
    Reactor.DeployPlus5.drorbServeMeteredPlus5Conformant
  rw [show (fun i => serveMeteredPlus5HeadIdx peer seq i)
        = (fun i => drorbServeMeteredPlus5 peer seq i) from
      funext (serveMeteredPlus5HeadIdx_eq peer seq)]

/-! ## 8. Non-vacuity — the arm genuinely fires, the on-edge shapes genuinely
refuse, byte-identical to the deployed fold and default on every shape. -/

/-- `OPTIONS /bulk` at hop-limit zero — ON-edge (the `Max-Forwards` gate answers
`204` through the fold); the dense guard must refuse. -/
def optionsBulkReq : ByteArray :=
  "OPTIONS /bulk HTTP/1.1\r\nHost: x\r\nMax-Forwards: 0\r\n\r\n".toUTF8

/-- `GET /login` — ON-edge (the session route gate fires); the guard must refuse. -/
def loginReq : ByteArray := "GET /login HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

/-- `GET /events` — ON-edge (the SSE route gate fires); the guard must refuse. -/
def eventsReq : ByteArray := "GET /events HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

/-- `GET /app/dash` — ON-edge (the SPA prefix gate fires); the guard must refuse. -/
def appReq : ByteArray := "GET /app/dash HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

-- The dense guard genuinely fires on the real `/bulk` request…
#guard armB5 bulkDemoReq && ipGateB cleanPeer && rateGateB 0 && noPreambleB bulkDemoReq
-- …and genuinely refuses every on-edge shape.
#guard !(armB5 optionsBulkReq)
#guard !(armB5 loginReq)
#guard !(armB5 eventsReq)
#guard !(armB5 appReq)
-- Byte-identity to the deployed-default metered fold on every shape: on-arm (two
-- hosts), off-arm, on-edge (all four), gate-refused (blocked peer, exhausted
-- sequence), preambled.
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 0 bulkDemoReq).data.toList
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 bulkDemoReqAnyHost).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 0 bulkDemoReqAnyHost).data.toList
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 healthReq).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 0 healthReq).data.toList
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 bulkGzipReq).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 0 bulkGzipReq).data.toList
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 echoPostReq).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 0 echoPostReq).data.toList
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 oldReq).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 0 oldReq).data.toList
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 optionsBulkReq).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 0 optionsBulkReq).data.toList
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 loginReq).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 0 loginReq).data.toList
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 eventsReq).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 0 eventsReq).data.toList
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 appReq).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 0 appReq).data.toList
#guard (serveMeteredPlus5HeadIdx blockedPeer 0 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus5 blockedPeer 0 bulkDemoReq).data.toList
#guard (serveMeteredPlus5HeadIdx cleanPeer 8 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 8 bulkDemoReq).data.toList
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 preambledReq).data.toList
        == (drorbServeMeteredPlus5 cleanPeer 0 preambledReq).data.toList
-- The dense arm fires (1 MiB body), the refusals refuse, and the deployed-rung
-- stamped head is STRICTLY longer than the plus2-rung stamped head (the
-- `Timing-Allow-Origin` edge is really there).
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 bulkDemoReq).size > 1048576
#guard (serveMeteredPlus5HeadIdx blockedPeer 0 bulkDemoReq).size < 1024
#guard (serveMeteredPlus5HeadIdx cleanPeer 8 bulkDemoReq).size < 1024
#guard (serveMeteredPlus5HeadIdx cleanPeer 0 bulkDemoReq).size
        > (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReq).size
-- The deployed edges are genuinely in the served HEAD.
#guard headHas "Timing-Allow-Origin".toUTF8.toList
        (serveMeteredPlus5HeadIdx cleanPeer 0 bulkDemoReq)
#guard headHas "Alt-Svc".toUTF8.toList (serveMeteredPlus5HeadIdx cleanPeer 0 bulkDemoReq)
#guard headHas "Permissions-Policy".toUTF8.toList
        (serveMeteredPlus5HeadIdx cleanPeer 0 bulkDemoReq)
#guard headHas "Via".toUTF8.toList (serveMeteredPlus5HeadIdx cleanPeer 0 bulkDemoReq)
#guard headHas "Cache-Status".toUTF8.toList
        (serveMeteredPlus5HeadIdx cleanPeer 0 bulkDemoReq)
#guard headHas "Cache-Control".toUTF8.toList
        (serveMeteredPlus5HeadIdx cleanPeer 0 bulkDemoReq)
-- Through the conformance wrapper: byte-identical to the deployed default, on-arm
-- (still > 1 MiB — the dense arm survives the wrapper) and on the reject shapes.
#guard (serveMeteredPlus5HeadIdxConformant cleanPeer 0 bulkDemoReqAnyHost).data.toList
        == (drorbServeMeteredPlus5Conformant cleanPeer 0 bulkDemoReqAnyHost).data.toList
#guard (serveMeteredPlus5HeadIdxConformant cleanPeer 0 bulkDemoReqAnyHost).size > 1048576
#guard (serveMeteredPlus5HeadIdxConformant cleanPeer 0
          ("HEAD /bulk HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8)).data.toList
        == (drorbServeMeteredPlus5Conformant cleanPeer 0
          ("HEAD /bulk HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8)).data.toList
#guard (serveMeteredPlus5HeadIdxConformant cleanPeer 0
          ("GET /bulk HTTP/1.1\r\n\r\n".toUTF8)).data.toList
        == (drorbServeMeteredPlus5Conformant cleanPeer 0
          ("GET /bulk HTTP/1.1\r\n\r\n".toUTF8)).data.toList

/-! ## 9. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms plus5_build_stamped
#print axioms plus5DenseArm_eq
#print axioms serveMeteredPlus5HeadIdx_eq
#print axioms serveMeteredPlus5HeadIdxConformant_eq

end Datapath.DenseStampsPlus5
