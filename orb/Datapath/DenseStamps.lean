import Datapath.ServeMeteredHeadIdx
import Reactor.DeployPlus2Conformant

/-!
# Datapath.DenseStamps — the DENSE `/bulk` arm for the nine-edge deployed default

The deployed default serve is the RFC-conformance wrapper over the EXTENDED
metered fold (`drorbServeMeteredPlus2Conformant` — the nine proven edge stamps:
Alt-Svc / Permissions-Policy / Cross-Origin-Resource-Policy / Via / Cache-Status /
Warning-transform / Link-preload / client-recovery / stale-while-revalidate,
prepended to the deployed stages). That flip re-opened the body-cliff on ONE
route: the extended fold's `/bulk` response differs from the plain fold's by the
stamped edge headers, so the proven dense `/bulk` bypass no longer byte-matched
and the 1 MiB body re-crossed as a `List UInt8` cons-spine on every `/bulk` hit
of the default deployment.

This module closes it BY CONSTRUCTION: the dense head itself carries the stamps.

* `stampHeaders` — the eight edge stamps that fire on a 200-response header list
  (`stampCc` → `stampLink` → `stampWarn` → `stampCS` → `stampVia` → `stampCorp` →
  `stampPP` → `stampAlt`, the extended fold's exact inside-out response order)
  as ONE pure function of the small header list — O(head), never the body.
* `denseHeadBytesIdxPlus2` — **the stamped dense `/bulk` head**: the proven
  index-native dense head (`denseHeadBytesIdx`'s render) with `stampHeaders`
  folded over its header block. Everything the extended fold adds to the `/bulk`
  response happens INSIDE the head render; the 1 MiB body stays the dense
  constant `bulkBodyDense`.
* `serveMeteredPlus2HeadIdx` — the extended metered serve with the dense arm:
  metered gates on the host scalars, ONE index-native head parse, the `/bulk`
  arm emitting `stamped head ++ dense body`, the O(1) `noPreambleB` probe
  discharging the client-recovery stage (the only input-reading stage of the
  nine). Off-arm (or refused gate, or preambled input) it IS the extended
  `List` fold verbatim.
* `serveMeteredPlus2HeadIdx_eq` — **the byte-identity**: for EVERY
  `(peer, seq, input)` the dense-stamped serve equals `drorbServeMeteredPlus2`.
* `serveMeteredPlus2HeadIdxConformant` / `…_eq` — the SAME proven conformance
  wrapper around it, byte-identical to the deployed default
  `drorbServeMeteredPlus2Conformant` for EVERY `(peer, seq, input)`.

The `/bulk` arm's compute path has NO `toList` anywhere: guard by index probes
(`gateB`/`bulkIdxB` off the borrowed window, `ipGateB`/`rateGateB` on the host
scalars, `noPreambleB` one byte read), head by `renderHead` over the flat block
with the stamp chain, body by one native `ByteArray` append of the cached 1 MiB
constant.

Residuals (named): the `/health` route is NOT given a stamped dense arm here (its
body is 2 bytes — no cliff; it falls back to the extended fold); the conformance
WRAPPER's request-side parse still views the (size-gated, small) request as a
`List` (`reqBytes` — the standing wrapper residual, unchanged by this module);
the wrapper's response post-processing copies the response twice (the fused
single-copy post-processor is a separate, orthogonal rung).
-/

namespace Datapath.DenseStamps

open Proto (Bytes)
open Reactor (Response serialize)
open Reactor.Pipeline (Ctx runPipeline pipeline_stage_effect ResponseBuilder)
open Reactor.Deploy
open Reactor.DeployPlus2 (deployStagesPlus2 servePipelinePlus2Metered
  drorbServeMeteredPlus2 drorbServeMeteredPlus2Conformant)
open Reactor.Stage.StaleWhileRevalidate (swrStage applyCc stampCc)
open Reactor.Stage.ProxyProtocol (proxyProtoStage recoverClient clientKey xffName
  proxyProtoStage_passthrough)
open Reactor.Stage.LinkPreload (linkStage stampLink)
open Reactor.Stage.WarningTransform (warningStage stampWarn)
open Reactor.Stage.CacheStatus (csStage stampCS)
open Reactor.Stage.Via (viaStage stampVia)
open Reactor.Stage.CrossOriginResource (corpStage stampCorp)
open Reactor.Stage.PermissionsPolicy (ppStage stampPP)
open Reactor.Stage.AltSvc (altStage stampAlt)
open Datapath.DenseHead (renderHead denseHeadersBlock serialize_eq_head_body
  renderHead_eq_headBytes)
open Datapath.SpanBytes (full parseArr spanArr)
open Datapath.HeadIdx (bulkIdxB)
open Datapath.ServeDenseIdx (denseArmB denseArmB_sound denseArmB_dispatch
  corrValB corrValB_eq uvBulk uv_arm healthReq bulkGzipReq bulkCorsReq)
open Datapath.ServeDenseReal (denseOut_eq bulkDemoReq bulkDemoReqAnyHost
  appHandler_bulk builtScalars denseHeadersUnknown)
open Datapath.ServeDenseFullReal (bulkBodyDense)
open Datapath.ServeHeadIdx (gateB bulkArmOf denseArmB_headIdx noPreambleB
  noPreambleB_sound echoPostReq oldReq)
open Datapath.ServeMeteredHeadIdx (ipGateB rateGateB ctxAddr_metered
  rate_admits_metered ipfilterStage_pass_admit full2_reduces_unknown_pass
  innerFold_ctxOfMetered cleanPeer blockedPeer serveMeteredHeadIdx)

/-! ## 1. The stamp chain as a pure head transform -/

/-- **The response-level effect of the nine-edge prefix** (preamble-free ctx):
the stale-while-revalidate `Cache-Control` apply, then the seven append-only
stamps in the extended fold's exact inside-out response order. -/
def stampResp (r : Response) : Response :=
  let r1 := applyCc r
  let r2 := { r1 with headers := stampLink r1.status r1.headers }
  let r3 := { r2 with headers := stampWarn r2.headers }
  let r4 := { r3 with headers := stampCS r3.headers }
  let r5 := { r4 with headers := stampVia r4.headers }
  let r6 := { r5 with headers := stampCorp r5.headers }
  let r7 := { r6 with headers := stampPP r6.headers }
  { r7 with headers := stampAlt r7.headers }

/-- **The stamp chain on a `200` header list** — the whole nine-edge header
effect as ONE pure function of the (small) header list: O(head) name probes and
tail appends, no status re-read, no body. -/
def stampHeaders (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  stampAlt (stampPP (stampCorp (stampVia (stampCS (stampWarn (stampLink 200
    (stampCc hs)))))))

/-- On a `200` response the response-level stamp chain is exactly the header
chain — status, reason and body are untouched. -/
theorem stampResp_200 (r : Response) (h : r.status = 200) :
    stampResp r = { r with headers := stampHeaders r.headers } := by
  unfold stampResp stampHeaders applyCc
  rw [h]
  rfl

/-- The wire bytes of a stamped `200`: the head rendered over the stamped
headers, followed by the unchanged body. Stated at a GENERIC response so every
record-collapse step happens on small neutral terms. -/
theorem serialize_stampResp (r : Response) (h : r.status = 200) :
    serialize (stampResp r)
      = renderHead 200 r.reason (stampHeaders r.headers) r.body.length
          ++ r.body := by
  rw [stampResp_200 r h, serialize_eq_head_body, ← renderHead_eq_headBytes]
  show renderHead r.status r.reason (stampHeaders r.headers) r.body.length
      ++ r.body = _
  rw [h]

/-! ## 2. The extended fold IS the stamp chain over the deployed fold
(preamble-free) -/

/-- With no recoverable preamble in the raw bytes and no stashed client attr,
the extended fold's BUILT response is `stampResp` of the deployed fold's built
response — all nine prepended stages pass the request phase unchanged, and the
response phase is the pure stamp chain. -/
theorem plus2_build_stamped (c : Ctx)
    (hrec : recoverClient c.input = none)
    (hfind : c.attrs.find? (fun p => p.1 == clientKey) = none) :
    (runPipeline deployStagesPlus2 appHandler c).build
      = stampResp ((runPipeline deployStagesFull2 appHandler c).build) := by
  show (runPipeline (altStage :: ppStage :: corpStage :: viaStage :: csStage
      :: warningStage :: linkStage :: proxyProtoStage :: swrStage
      :: deployStagesFull2) appHandler c).build = _
  rw [pipeline_stage_effect altStage _ appHandler c c rfl,
      pipeline_stage_effect ppStage _ appHandler c c rfl,
      pipeline_stage_effect corpStage _ appHandler c c rfl,
      pipeline_stage_effect viaStage _ appHandler c c rfl,
      pipeline_stage_effect csStage _ appHandler c c rfl,
      pipeline_stage_effect warningStage _ appHandler c c rfl,
      pipeline_stage_effect linkStage _ appHandler c c rfl,
      pipeline_stage_effect proxyProtoStage _ appHandler c c
        (proxyProtoStage_passthrough c hrec),
      pipeline_stage_effect swrStage _ appHandler c c rfl]
  have hpx : ∀ b : ResponseBuilder, proxyProtoStage.onResponse c b = b := by
    intro b
    show (match c.attrs.find? (fun p => p.1 == clientKey) with
          | some p => b.addHeader (xffName, p.2)
          | none => b) = b
    rw [hfind]
  rw [hpx]
  rfl

/-- The metered ctx stashes exactly the two metered keys — neither is the
client-recovery key, so the recovery stage's response phase finds nothing. -/
theorem meteredAttrs_no_client (peer : Bytes) (seq : Nat) (input : Bytes) :
    (ctxOfMetered peer seq input).attrs.find?
      (fun p => p.1 == clientKey) = none := by
  show List.find? _ [(Reactor.Stage.IpFilter.clientIpKey, peer),
        (Reactor.Stage.Rate.seqKey, List.replicate seq (0 : UInt8))] = none
  have h1 : (Reactor.Stage.IpFilter.clientIpKey == clientKey) = false := by decide
  have h2 : (Reactor.Stage.Rate.seqKey == clientKey) = false := by decide
  simp [List.find?, h1, h2]

/-! ## 3. The stamped dense `/bulk` head -/

/-- **THE STAMPED DENSE HEAD** — the proven index-native dense `/bulk` head with
the nine-edge stamp chain folded over its header block: constant `x-upstream`
(`uvBulk`), index-native `x-corr` (`corrValB`), the flat header fold, then
`stampHeaders` (O(head) appends) — rendered with the dense body LENGTH, never
the body bytes, and NO `toList` of the input. -/
def denseHeadBytesIdxPlus2 (input : ByteArray) : Bytes :=
  renderHead 200 (Reactor.App.reasonFor 200)
    (stampHeaders (denseHeadersBlock [] uvBulk (corrValB input)).denote)
    Reactor.App.bulkSize

/-- On a firing guard the stamped index-native head is the stamped deployed
dense head — the same scalar collapse (`corrValB_eq` + `uv_arm`) as the
unstamped head, under the stamp chain. -/
theorem denseHeadBytesIdxPlus2_eq (input : ByteArray) (h : denseArmB input = true) :
    denseHeadBytesIdxPlus2 input
      = renderHead 200 (Reactor.App.reasonFor 200)
          (stampHeaders (denseHeadersBlock []
            (upstreamVal (deployPlan (deploySubs input.toList)))
            (corrVal input.toList)).denote)
          Reactor.App.bulkSize := by
  obtain ⟨req, rest, hsub, harm⟩ := denseArmB_dispatch input h
  obtain ⟨_, _, _, _, _, _, _, _, hseg, _, _⟩ := harm
  unfold denseHeadBytesIdxPlus2
  rw [corrValB_eq, uv_arm input.toList req rest hsub hseg]

/-! ## 4. The dense arm equals the extended metered fold on `/bulk` -/

/-- **The stamped dense `/bulk` assembly is byte-identical to the extended
metered fold.** On a firing dense guard with both metered gates admitting and a
preamble-free input, `stamped head ++ dense 1 MiB body` equals
`serialize (deployRespPlus2Metered …)` — the extended fold's exact wire bytes:
the nine stages collapse to `stampResp` (`plus2_build_stamped`), the metered
fold collapses to the bare fold under the admitted gates, and the bare built
response is the proven dense head + body. NO 1 MiB `List` on the compute path. -/
theorem plus2DenseArm_eq (peer : ByteArray) (seq : UInt64) (input : ByteArray)
    (h : denseArmB input = true) (hip : ipGateB peer = true)
    (hrate : rateGateB seq.toNat = true) (hnp : noPreambleB input = true) :
    ByteArray.mk (denseHeadBytesIdxPlus2 input).toArray ++ bulkBodyDense
      = ByteArray.mk (servePipelinePlus2Metered peer.toList seq.toNat
          input.toList).toArray := by
  have harm := denseArmB_sound input h
  obtain ⟨hadmin, hpriv, hrate0, hredir, htrav, hpol, hgz, hcors, hseg, hna, hnb⟩ := harm
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
        full2_reduces_unknown (ctxOf input.toList) hadmin hpriv rfl hrate0 hredir htrav hpol,
        innerFold_ctxOfMetered peer.toList seq.toNat input.toList, hin]
  -- the nine-stage prefix collapses to the pure stamp chain
  have hrec : recoverClient
      (ctxOfMetered peer.toList seq.toNat input.toList).input = none :=
    noPreambleB_sound input hnp
  have h1 : (runPipeline deployStagesPlus2 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build
      = stampResp ((runPipeline deployStagesFull2 appHandler
          (ctxOf input.toList)).build) := by
    rw [plus2_build_stamped _ hrec
          (meteredAttrs_no_client peer.toList seq.toNat input.toList), hkey]
  -- the bare built response on the arm: scalars + the dense header block
  have happ := appHandler_bulk (ctxOf input.toList) hseg hna hnb
  obtain ⟨hst, hrs, hbd⟩ := builtScalars (ctxOf input.toList) hadmin hpriv rfl
    hrate0 hredir htrav hpol hgz hcors happ
  have hhdr := denseHeadersUnknown (ctxOf input.toList) hadmin hpriv rfl
    hrate0 hredir htrav hpol hgz hcors
  have hAheaders : (appHandler (ctxOf input.toList)).headers = [] := by rw [happ]
  have hinput : (ctxOf input.toList).input = input.toList := rfl
  -- the wire bytes of the extended fold, as stamped head ++ body
  have hlist : servePipelinePlus2Metered peer.toList seq.toNat input.toList
      = denseHeadBytesIdxPlus2 input ++ Reactor.App.bulkBody := by
    show serialize ((runPipeline deployStagesPlus2 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build) = _
    rw [h1, serialize_stampResp _ hst]
    rw [hrs, hbd, Reactor.App.bulkBody_length,
        show ((runPipeline deployStagesFull2 appHandler (ctxOf input.toList)).build).headers
          = (denseHeadersBlock []
              (upstreamVal (deployPlan (deploySubs input.toList)))
              (corrVal input.toList)).denote from by
            rw [← hhdr, hAheaders, hinput],
        denseHeadBytesIdxPlus2_eq input h]
  calc ByteArray.mk (denseHeadBytesIdxPlus2 input).toArray ++ bulkBodyDense
      = ByteArray.mk (denseHeadBytesIdxPlus2 input ++ Reactor.App.bulkBody).toArray :=
        denseOut_eq _
    _ = ByteArray.mk (servePipelinePlus2Metered peer.toList seq.toNat
          input.toList).toArray := by rw [hlist]

/-! ## 5. THE SERVE — the nine-edge metered serve with the dense `/bulk` arm -/

/-- **The dense-stamped extended metered serve.** Metered gates on the host
scalars, the O(1) preamble probe, ONE index-native head parse, the `/bulk` arm
decided by index probes and emitted as `stamped dense head ++ dense 1 MiB body`.
Everything else — off-arm routes, refused gates, preambled inputs, unparsable
heads — is the extended metered `List` fold verbatim. -/
def serveMeteredPlus2HeadIdx (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  if gateB input && ipGateB peer && rateGateB seq.toNat && noPreambleB input then
    match parseArr (spanArr (full input)) with
    | .complete areq =>
        if bulkIdxB areq then
          ByteArray.mk (denseHeadBytesIdxPlus2 input).toArray ++ bulkBodyDense
        else drorbServeMeteredPlus2 peer seq input
    | _ => drorbServeMeteredPlus2 peer seq input
  else drorbServeMeteredPlus2 peer seq input

/-- **THE BYTE-IDENTITY.** For EVERY `(peer, seq, input)` the dense-stamped
serve produces the IDENTICAL bytes to the extended metered fold
(`drorbServeMeteredPlus2`): a firing guard implies the deployed dense arm
(`denseArmB_headIdx`), where the stamped dense assembly equals the extended
fold (`plus2DenseArm_eq`); everywhere else it IS the extended fold. -/
theorem serveMeteredPlus2HeadIdx_eq (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    serveMeteredPlus2HeadIdx peer seq input
      = drorbServeMeteredPlus2 peer seq input := by
  unfold serveMeteredPlus2HeadIdx
  cases hg : gateB input && ipGateB peer && rateGateB seq.toNat
      && noPreambleB input with
  | false => rw [if_neg Bool.false_ne_true]
  | true =>
    rw [if_pos rfl]
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨hgate, hip⟩, hrate⟩, hnp⟩ := hg
    cases hp : parseArr (spanArr (full input)) with
    | complete areq =>
      show (if bulkIdxB areq then
              ByteArray.mk (denseHeadBytesIdxPlus2 input).toArray ++ bulkBodyDense
            else drorbServeMeteredPlus2 peer seq input)
          = drorbServeMeteredPlus2 peer seq input
      by_cases hb : bulkIdxB areq = true
      · rw [if_pos hb]
        have hdense : denseArmB input = true := by
          rw [denseArmB_headIdx, hgate, hp, Bool.true_and]
          exact hb
        exact plus2DenseArm_eq peer seq input hdense hip hrate hnp
      · rw [if_neg hb]
    | incomplete => rfl
    | error e d => rfl

/-! ## 6. The RFC-conformant wrapper (retired export) -/

/-- **A retired dense-stamped conformance wrapper** (formerly the C export
`drorb_serve_metered_plus2_dense_conformant`) — the conformance wrapper
(431-gate → validation/framing gates → inner → `Date` splice → scrub →
`HEAD`-strip) around the dense-stamped extended serve. RETIRED experimental seam — the `@[export]` was removed in the consolidation, so this def is no longer a host crossing; it is retained only for the byte-identity derivation chain. The single deployed default is `drorb_serve_pipeline_conformant`. -/
def serveMeteredPlus2HeadIdxConformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  Reactor.ServeConformant.conformantServe
    (fun i => serveMeteredPlus2HeadIdx peer seq i) input

/-- **The wrapper preserves the byte-identity**: the dense-stamped conformant
serve equals the deployed default `drorbServeMeteredPlus2Conformant` for EVERY
`(peer, seq, input)` — the inners are equal as functions, and the wrapper is a
function of its inner. -/
theorem serveMeteredPlus2HeadIdxConformant_eq (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    serveMeteredPlus2HeadIdxConformant peer seq input
      = drorbServeMeteredPlus2Conformant peer seq input := by
  unfold serveMeteredPlus2HeadIdxConformant
    Reactor.DeployPlus2.drorbServeMeteredPlus2Conformant
  rw [show (fun i => serveMeteredPlus2HeadIdx peer seq i)
        = (fun i => drorbServeMeteredPlus2 peer seq i) from
      funext (serveMeteredPlus2HeadIdx_eq peer seq)]

/-! ## 7. Non-vacuity — the stamped dense arm genuinely fires, byte-identical
to the extended fold and the deployed conformant default on every shape. -/

/-- A preambled connection input — the probe refuses; falls back to the fold. -/
def preambledReq : ByteArray :=
  "PROXY TCP4 192.168.1.1 10.0.0.1 12345 80\r\nGET /bulk HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

-- The dense guard genuinely fires on the real `/bulk` request.
#guard gateB bulkDemoReq && ipGateB cleanPeer && rateGateB 0 && noPreambleB bulkDemoReq
        && bulkArmOf (parseArr (spanArr (full bulkDemoReq)))
-- Byte-identity to the extended metered fold on every shape: on-arm (two hosts),
-- off-arm, gate-refused (blocked peer, exhausted sequence), preambled.
#guard (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus2 cleanPeer 0 bulkDemoReq).data.toList
#guard (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReqAnyHost).data.toList
        == (drorbServeMeteredPlus2 cleanPeer 0 bulkDemoReqAnyHost).data.toList
#guard (serveMeteredPlus2HeadIdx cleanPeer 0 healthReq).data.toList
        == (drorbServeMeteredPlus2 cleanPeer 0 healthReq).data.toList
#guard (serveMeteredPlus2HeadIdx cleanPeer 0 bulkGzipReq).data.toList
        == (drorbServeMeteredPlus2 cleanPeer 0 bulkGzipReq).data.toList
#guard (serveMeteredPlus2HeadIdx cleanPeer 0 echoPostReq).data.toList
        == (drorbServeMeteredPlus2 cleanPeer 0 echoPostReq).data.toList
#guard (serveMeteredPlus2HeadIdx cleanPeer 0 oldReq).data.toList
        == (drorbServeMeteredPlus2 cleanPeer 0 oldReq).data.toList
#guard (serveMeteredPlus2HeadIdx blockedPeer 0 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus2 blockedPeer 0 bulkDemoReq).data.toList
#guard (serveMeteredPlus2HeadIdx cleanPeer 8 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus2 cleanPeer 8 bulkDemoReq).data.toList
#guard (serveMeteredPlus2HeadIdx cleanPeer 0 preambledReq).data.toList
        == (drorbServeMeteredPlus2 cleanPeer 0 preambledReq).data.toList
-- The dense arm fires (1 MiB body), the refusals refuse, and the stamped head is
-- STRICTLY longer than the unstamped dense head (the nine edges are really there).
#guard (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReq).size > 1048576
#guard (serveMeteredPlus2HeadIdx blockedPeer 0 bulkDemoReq).size < 1024
#guard (serveMeteredPlus2HeadIdx cleanPeer 8 bulkDemoReq).size < 1024
#guard (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReq).size
        > (serveMeteredHeadIdx cleanPeer 0 bulkDemoReq).size
-- The stamped names are genuinely in the served HEAD (scan the first 2000 bytes).
def headHas (pat : Bytes) (bs : ByteArray) : Bool :=
  let head := bs.data.toList.take 2000
  (List.range head.length).any (fun i => pat.isPrefixOf (head.drop i))

#guard headHas "Alt-Svc".toUTF8.toList (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReq)
#guard headHas "Permissions-Policy".toUTF8.toList (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReq)
#guard headHas "Cross-Origin-Resource-Policy".toUTF8.toList (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReq)
#guard headHas "Via".toUTF8.toList (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReq)
#guard headHas "Cache-Status".toUTF8.toList (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReq)
#guard headHas "Link".toUTF8.toList (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReq)
#guard headHas "Cache-Control".toUTF8.toList (serveMeteredPlus2HeadIdx cleanPeer 0 bulkDemoReq)
-- Through the conformance wrapper: byte-identical to the deployed default, on-arm
-- (still > 1 MiB — the dense arm survives the wrapper) and on the reject shapes.
#guard (serveMeteredPlus2HeadIdxConformant cleanPeer 0 bulkDemoReqAnyHost).data.toList
        == (drorbServeMeteredPlus2Conformant cleanPeer 0 bulkDemoReqAnyHost).data.toList
#guard (serveMeteredPlus2HeadIdxConformant cleanPeer 0 bulkDemoReqAnyHost).size > 1048576
#guard (serveMeteredPlus2HeadIdxConformant cleanPeer 0
          ("HEAD /bulk HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8)).data.toList
        == (drorbServeMeteredPlus2Conformant cleanPeer 0
          ("HEAD /bulk HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8)).data.toList
#guard (serveMeteredPlus2HeadIdxConformant cleanPeer 0
          ("GET /bulk HTTP/1.1\r\n\r\n".toUTF8)).data.toList
        == (drorbServeMeteredPlus2Conformant cleanPeer 0
          ("GET /bulk HTTP/1.1\r\n\r\n".toUTF8)).data.toList

/-! ## 8. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms plus2_build_stamped
#print axioms plus2DenseArm_eq
#print axioms serveMeteredPlus2HeadIdx_eq
#print axioms serveMeteredPlus2HeadIdxConformant_eq

end Datapath.DenseStamps
