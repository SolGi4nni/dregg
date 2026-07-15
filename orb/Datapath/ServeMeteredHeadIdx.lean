import Datapath.ServeHeadIdx
import Reactor.ServeConformant

/-!
# Datapath.ServeMeteredHeadIdx — the METERED serve with an index-native arm decision

The deployed METERED default (`drorb_serve_metered_dense_conformant` and the
empty-config divert of `drorb_serve_metered_cfg_conformant`) decides its dense
`/bulk` arm by `Reactor.Deploy.BulkArmMetered` — a decidable `Prop` whose every
conjunct evaluates over `ctxOf input.toList` / `ctxOfMetered peer seq input.toList`:
the whole request head is `List`-parsed (twice: once for `BulkArm`, once to build
the metered ctx the two gate conjuncts read), and `List.replicate seq 0` is consed
just so the rate gate can take its `length`. The non-metered default already
crosses `serveHeadIdx` (parse-once, index-native); this module closes the SAME
residual on the metered seam:

* the two METERED gates are decided directly on the host-supplied scalars —
  `ipGateB` on the encoded peer address (never through a ctx), `rateGateB` on the
  sequence count as a `Nat` (no `List.replicate`, no attr-bag lookup);
* ONE index-native head parse (`parseArr` off the borrowed window), off which BOTH
  dense arms are decided by `Datapath.HeadIdx.bulkIdxB`/`healthIdxB` — header
  names compared by index probes, values/target resolved only on demand;
* the arm bodies are the PROVEN dense emitters (`denseHeadBytesIdx`/
  `healthHeadBytesIdx` + the dense bodies) — and the `/health` arm is now ALSO
  dense on the metered path (the metered `List` fold previously answered it);
* off both arms (or with a refusing gate) it is the deployed metered `List` fold
  verbatim (`servePipelineFull2Metered`) — the 403/429 refusals and every other
  route are byte-identical by construction. That off-arm fold still re-parses,
  which is the standing off-arm residual, not this module's scope.

`serveMeteredHeadIdx_eq` proves byte-identity to the deployed metered fold —
`ByteArray.mk (servePipelineFull2Metered peer.toList seq.toNat input.toList).toArray`,
the exact body of the deployed metered serve seam — for EVERY `(peer, seq, input)`.
`serveMeteredHeadIdxConformant` wraps it in the SAME proven RFC-conformance stages
the deployed metered default crosses, with the equality lifted through the wrapper.
-/

namespace Datapath.ServeMeteredHeadIdx

open Proto (Bytes)
open Reactor.Pipeline (Ctx runPipeline)
open Reactor.Deploy
open Datapath.SpanBytes (full parseArr spanArr)
open Datapath.HeadIdx (bulkIdxB healthIdxB)
open Datapath.ServeDenseReal (BulkArm denseArm_eq bulkDemoReq)
open Datapath.ServeDenseIdx (denseArmB healthArmB denseArmB_sound healthArmB_sound
  denseHeadBytesIdx healthHeadBytesIdx healthBodyDense denseHeadBytesIdx_eq
  healthHeadBytesIdx_eq healthArm_eq HealthArm healthReq bulkGzipReq)
open Datapath.ServeDenseFullReal (bulkBodyDense)
open Datapath.ServeHeadIdx (gateB bulkArmOf healthArmOf denseArmB_headIdx
  healthArmB_headIdx echoPostReq oldReq)

/-! ## 1. The metered gates, decided on the host scalars — no ctx, no head parse -/

/-- **The IP-filter gate on the encoded peer directly.** The deployed admission
decision (`deployAdmits`, deny `10.0.0.0/8` / default-admit) over the decoded
accept address — O(address) work on the ≤129 host-supplied peer bytes, never
touching the request. -/
def ipGateB (peer : ByteArray) : Bool :=
  Reactor.Stage.IpFilter.deployAdmits (Reactor.Stage.IpFilter.decodeAddr peer.toList)

/-- **The rate gate on the sequence count directly.** The real token-bucket
decision (`Rate.tryAdmit` after refill) on the reconstructed standing bucket —
`rateCap - seq` tokens — with NO `List.replicate seq 0` cons and no attr-bag
lookup. -/
def rateGateB (seq : Nat) : Bool :=
  (_root_.Rate.tryAdmit (_root_.Rate.refill 0
    { tokens := Reactor.Stage.Rate.rateCap - seq, last := 0,
      cap := Reactor.Stage.Rate.rateCap, rate := Reactor.Stage.Rate.rateRate })).2

/-- The metered ctx's decided address IS the decoded peer: `ctxOfMetered` stashes
the peer under `clientIpKey` at the head of the attr bag. -/
theorem ctxAddr_metered (peer : Bytes) (seq : Nat) (input : Bytes) :
    Reactor.Stage.IpFilter.ctxAddr (ctxOfMetered peer seq input)
      = Reactor.Stage.IpFilter.decodeAddr peer := rfl

/-- The metered ctx's standing sequence IS the supplied count: the `seqKey` attr
is `List.replicate seq 0`, whose length is `seq`. -/
theorem seqOf_metered (peer : Bytes) (seq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.seqOf (ctxOfMetered peer seq input) = seq := by
  show (List.replicate seq (0 : UInt8)).length = seq
  exact List.length_replicate ..

/-- **The rate gate decides exactly the metered ctx's admission.** -/
theorem rate_admits_metered (peer : Bytes) (seq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.admits (ctxOfMetered peer seq input) = rateGateB seq := by
  unfold Reactor.Stage.Rate.admits Reactor.Stage.Rate.bucketOf rateGateB
  rw [seqOf_metered]

/-! ## 2. The metered gate-pass reductions (the admitted-arm bridge)

These mirror the deployed metered `/bulk` bridge: with both gates admitting, the
metered thirteen-stage fold collapses to the bare fold — the metered attrs feed
only the two now-transparent gates. Restated here (rather than imported) because
they live downstream of this module in the export root. -/

/-- `ipfilterStage` request phase `.continue`s unchanged when the deployed ruleset
admits the ctx's address — the admitted-arm pass witness for a ctx that DOES carry
an accept peer. -/
theorem ipfilterStage_pass_admit (c : Ctx)
    (h : Reactor.Stage.IpFilter.deployAdmits (Reactor.Stage.IpFilter.ctxAddr c) = true) :
    Reactor.Stage.IpFilter.ipfilterStage.onRequest c = .continue c := by
  simp only [Reactor.Stage.IpFilter.ipfilterStage, h]

/-- **The admitted-arm reduction, parametric over the IP-filter pass witness.**
Identical to `full2_reduces_unknown`, but the IP-filter step is supplied as a
hypothesis rather than derived from a missing `client.ip` attr — so it fires for a
metered ctx (accept peer present and ADMITTED). The fold collapses to the five
inner response transforms threaded through the outer deploy header rewrite. -/
theorem full2_reduces_unknown_pass (c : Ctx)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hippass : Reactor.Stage.IpFilter.ipfilterStage.onRequest c = .continue c)
    (hrate : Reactor.Stage.Rate.admits c = true)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hpol : policyReserved c.req = false) :
    runPipeline deployStagesFull2 appHandler c
      = (runPipeline full2InnerStages appHandler c).mapResp
          (Reactor.Lifecycle.rewriteResp
            (deployProg (deployPlan (deploySubs c.input)) c.input)) := by
  show runPipeline (jwtAdminStage :: Reactor.Stage.BasicAuth.basicStage
      :: Reactor.Stage.IpFilter.ipfilterStage :: Reactor.Stage.Rate.rateStage
      :: cacheEmptyStage :: Reactor.Stage.Redirect.redirectStage :: traversalStage
      :: policyStage :: headerRewriteStage :: full2InnerStages) appHandler c = _
  rw [Reactor.Pipeline.pipeline_stage_effect jwtAdminStage _ appHandler c c (jwtAdminStage_pass c hadmin),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.BasicAuth.basicStage _ appHandler c c
        (Reactor.Stage.BasicAuth.basicStage_pass c hpriv),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.IpFilter.ipfilterStage _ appHandler c c
        hippass,
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.Rate.rateStage _ appHandler c c
        (Reactor.Stage.Rate.rateStage_onReq_continue c hrate),
      Reactor.Pipeline.pipeline_stage_effect cacheEmptyStage _ appHandler c c (cacheEmptyStage_pass c),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.Redirect.redirectStage _ appHandler c c
        (redirectStage_pass c hredir),
      Reactor.Pipeline.pipeline_stage_effect traversalStage _ appHandler c c (traversalStage_pass c htrav),
      Reactor.Pipeline.pipeline_stage_effect policyStage _ appHandler c c (policyStage_pass_unknown c hpol),
      Reactor.Pipeline.pipeline_stage_effect headerRewriteStage _ appHandler c c rfl]
  simp only [jwtAdminStage, Reactor.Stage.BasicAuth.basicStage,
    Reactor.Stage.IpFilter.ipfilterStage, Reactor.Stage.Rate.rateStage, cacheEmptyStage,
    Reactor.Stage.Cache.mkStage, Reactor.Stage.Redirect.redirectStage, traversalStage,
    policyStage, headerRewriteStage]

/-- The inner response-transform fold is insensitive to the metered attrs: the
five `full2InnerStages` pass the request phase and their response phase reads only
`c.req`/`c.input`, and `ctxOfMetered` differs from `ctxOf` ONLY in `.attrs`. -/
theorem innerFold_ctxOfMetered (peer : Bytes) (seq : Nat) (input : Bytes) :
    runPipeline full2InnerStages appHandler (ctxOfMetered peer seq input)
      = runPipeline full2InnerStages appHandler (ctxOf input) := rfl

/-- **The metered bridge on the `/bulk` arm.** With the arm holding on the bare
ctx and BOTH metered gates admitting, the metered fold emits the SAME bytes as the
bare fold — the metered attrs feed only the two now-transparent gates. -/
theorem meteredFold_bulk_eq (peer : Bytes) (seq : Nat) (input : Bytes)
    (harm : BulkArm (ctxOf input))
    (hip_m : Reactor.Stage.IpFilter.deployAdmits
        (Reactor.Stage.IpFilter.ctxAddr (ctxOfMetered peer seq input)) = true)
    (hrate_m : Reactor.Stage.Rate.admits (ctxOfMetered peer seq input) = true) :
    servePipelineFull2Metered peer seq input = servePipelineFull2 input := by
  obtain ⟨hadmin, hpriv, hrate0, hredir, htrav, hpol, _hgz, _hcors, _hseg, _hna, _hnb⟩ := harm
  have hin : (ctxOfMetered peer seq input).input = (ctxOf input).input := rfl
  have key : runPipeline deployStagesFull2 appHandler (ctxOfMetered peer seq input)
           = runPipeline deployStagesFull2 appHandler (ctxOf input) := by
    rw [full2_reduces_unknown_pass (ctxOfMetered peer seq input) hadmin hpriv
          (ipfilterStage_pass_admit _ hip_m) hrate_m hredir htrav hpol,
        full2_reduces_unknown (ctxOf input) hadmin hpriv rfl hrate0 hredir htrav hpol,
        innerFold_ctxOfMetered peer seq input, hin]
  unfold servePipelineFull2Metered servePipelineFull2
  rw [key]

/-- **The metered bridge on the `/health` arm** — the same collapse for the second
dense route (which the deployed metered serve previously answered through the
`List` fold; this is what lets the metered serve emit it densely). -/
theorem meteredFold_health_eq (peer : Bytes) (seq : Nat) (input : Bytes)
    (harm : HealthArm (ctxOf input))
    (hip_m : Reactor.Stage.IpFilter.deployAdmits
        (Reactor.Stage.IpFilter.ctxAddr (ctxOfMetered peer seq input)) = true)
    (hrate_m : Reactor.Stage.Rate.admits (ctxOfMetered peer seq input) = true) :
    servePipelineFull2Metered peer seq input = servePipelineFull2 input := by
  obtain ⟨hadmin, hpriv, hrate0, hredir, htrav, hpol, _hgz, _hcors, _hseg⟩ := harm
  have hin : (ctxOfMetered peer seq input).input = (ctxOf input).input := rfl
  have key : runPipeline deployStagesFull2 appHandler (ctxOfMetered peer seq input)
           = runPipeline deployStagesFull2 appHandler (ctxOf input) := by
    rw [full2_reduces_unknown_pass (ctxOfMetered peer seq input) hadmin hpriv
          (ipfilterStage_pass_admit _ hip_m) hrate_m hredir htrav hpol,
        full2_reduces_unknown (ctxOf input) hadmin hpriv rfl hrate0 hredir htrav hpol,
        innerFold_ctxOfMetered peer seq input, hin]
  unfold servePipelineFull2Metered servePipelineFull2
  rw [key]

/-! ## 3. THE METERED SERVE — gates on scalars, ONE head read, arms index-decided -/

/-- The deployed metered `List` fold as a `ByteArray` serve — the exact body of
the deployed metered serve seam (the byte-identity target and the off-arm
fallback). -/
def meteredFoldServe (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  ByteArray.mk (servePipelineFull2Metered peer.toList seq.toNat input.toList).toArray

/-- **The index-native-head METERED serve.** The two metered gates decided on the
host scalars (`ipGateB`/`rateGateB` — no ctx, no replicate), then ONE index-native
head parse (`parseArr` — spans into the flat window), off which BOTH dense arms
are decided (`bulkIdxB`/`healthIdxB`). The `/bulk` arm emits the proven dense head
+ dense 1 MiB body, the `/health` arm the dense head + constant body; a refusing
gate or an off-arm request falls back to the deployed metered `List` fold verbatim
(where the 403/429 refusals are produced by the in-fold gate stages, unchanged). -/
@[export drorb_serve_metered_head_idx]
def serveMeteredHeadIdx (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  if gateB input && ipGateB peer && rateGateB seq.toNat then
    match parseArr (spanArr (full input)) with
    | .complete areq =>
        if bulkIdxB areq then
          ByteArray.mk (denseHeadBytesIdx input).toArray ++ bulkBodyDense
        else if healthIdxB areq then
          ByteArray.mk (healthHeadBytesIdx input).toArray ++ healthBodyDense
        else
          meteredFoldServe peer seq input
    | _ => meteredFoldServe peer seq input
  else
    meteredFoldServe peer seq input

/-- **THE BYTE-IDENTITY.** For EVERY `(peer, seq, input)`, the index-native
metered serve produces the IDENTICAL bytes to the deployed metered fold: a firing
`/bulk` (resp. `/health`) guard implies the deployed arm (`denseArmB_sound` /
`healthArmB_sound`, through the shared parse via `denseArmB_headIdx` /
`healthArmB_headIdx`), where the dense emission equals the bare fold (`denseArm_eq`
/ `healthArm_eq`) and the bare fold equals the metered fold under the admitted
gates (`meteredFold_bulk_eq` / `meteredFold_health_eq`, keyed by `ctxAddr_metered`
/ `rate_admits_metered`); everywhere else it IS the metered fold. -/
theorem serveMeteredHeadIdx_eq (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    serveMeteredHeadIdx peer seq input = meteredFoldServe peer seq input := by
  unfold serveMeteredHeadIdx
  cases hg : gateB input && ipGateB peer && rateGateB seq.toNat with
  | false => rw [if_neg Bool.false_ne_true]
  | true =>
    rw [if_pos rfl]
    rw [Bool.and_eq_true, Bool.and_eq_true] at hg
    obtain ⟨⟨hgate, hip⟩, hrate⟩ := hg
    have hip_m : Reactor.Stage.IpFilter.deployAdmits
        (Reactor.Stage.IpFilter.ctxAddr
          (ctxOfMetered peer.toList seq.toNat input.toList)) = true := by
      rw [ctxAddr_metered]; exact hip
    have hrate_m : Reactor.Stage.Rate.admits
        (ctxOfMetered peer.toList seq.toNat input.toList) = true := by
      rw [rate_admits_metered]; exact hrate
    cases hp : parseArr (spanArr (full input)) with
    | complete areq =>
      show (if bulkIdxB areq then
              ByteArray.mk (denseHeadBytesIdx input).toArray ++ bulkBodyDense
            else if healthIdxB areq then
              ByteArray.mk (healthHeadBytesIdx input).toArray ++ healthBodyDense
            else meteredFoldServe peer seq input) = meteredFoldServe peer seq input
      by_cases hb : bulkIdxB areq = true
      · rw [if_pos hb]
        have hdense : denseArmB input = true := by
          rw [denseArmB_headIdx, hgate, hp, Bool.true_and]
          exact hb
        rw [denseHeadBytesIdx_eq input hdense,
            denseArm_eq input (denseArmB_sound input hdense)]
        unfold meteredFoldServe
        rw [meteredFold_bulk_eq peer.toList seq.toNat input.toList
              (denseArmB_sound input hdense) hip_m hrate_m]
      · rw [if_neg hb]
        by_cases hh : healthIdxB areq = true
        · rw [if_pos hh]
          have hhealth : healthArmB input = true := by
            rw [healthArmB_headIdx, hgate, hp, Bool.true_and]
            exact hh
          rw [healthHeadBytesIdx_eq input hhealth,
              healthArm_eq input (healthArmB_sound input hhealth)]
          unfold meteredFoldServe
          rw [meteredFold_health_eq peer.toList seq.toNat input.toList
                (healthArmB_sound input hhealth) hip_m hrate_m]
        · rw [if_neg hh]
    | incomplete => rfl
    | error e d => rfl

/-! ## 4. The RFC-conformant wrapper — the seam the metered default crosses -/

/-- **`drorb_serve_metered_head_idx_conformant`** — the RFC-conformant
INDEX-NATIVE metered serve: the SAME proven `conformantServe` stages
(validation C1/C2/B2/G1/C3 → the inner serve → `Date` F1 / `HEAD`-strip B1)
wrapped around `serveMeteredHeadIdx peer seq`. Same `(peer, seq, input)` ABI as
the deployed metered-conformant serves; `input` is the raw HTTP/1.1 request. -/
@[export drorb_serve_metered_head_idx_conformant]
def serveMeteredHeadIdxConformant (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  Reactor.ServeConformant.conformantServe (fun i => serveMeteredHeadIdx peer seq i) input

/-- **The conformant wrapper preserves the byte-identity.** The inner serves are
equal as FUNCTIONS (`serveMeteredHeadIdx_eq`, funext), and `conformantServe` is a
function OF its inner — so the index-native metered-conformant serve is
byte-identical to `conformantServe` over the deployed metered fold (which is the
deployed metered-conformant default, definitionally). -/
theorem serveMeteredHeadIdxConformant_eq (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    serveMeteredHeadIdxConformant peer seq input
      = Reactor.ServeConformant.conformantServe
          (fun i => meteredFoldServe peer seq i) input := by
  unfold serveMeteredHeadIdxConformant
  have hf : (fun i => serveMeteredHeadIdx peer seq i)
          = (fun i => meteredFoldServe peer seq i) := by
    funext i; exact serveMeteredHeadIdx_eq peer seq i
  rw [hf]

/-- **B1 on the index-native metered-conformant serve** — after the wrapper's
`HEAD`-strip the response carries NO body octets, for ANY request bytes
(instantiating the parametric, non-vacuous `conformant_head_no_body`). -/
theorem serveMeteredHeadIdxConformant_head_no_body
    (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    Reactor.ServeConformant.afterBlank
      (Reactor.ServeConformant.stripBody
        (Reactor.ServeConformant.respBytesRaw
          (fun i => serveMeteredHeadIdx peer seq i) input)) = [] :=
  Reactor.ServeConformant.conformant_head_no_body _ input

/-- **C1 on the index-native metered-conformant serve** — a REAL missing-Host
request is rejected as the dated `400` WITHOUT consulting the inner serve. -/
theorem serveMeteredHeadIdxConformant_rejects_missingHost (peer : ByteArray) (seq : UInt64) :
    Reactor.ServeConformant.respBytesRaw (fun i => serveMeteredHeadIdx peer seq i)
        Reactor.ServeConformant.missingHostInput
      = Reactor.serialize (Reactor.ServeConformant.addDate
          Reactor.Stage.RequestValidation.badRequestResp) :=
  Reactor.ServeConformant.conformant_rejects_missingHost _

/-! ## 5. Non-vacuity — the gates and arms genuinely fire (and refuse), and the
serve is byte-identical to the deployed metered fold on every shape: on-arm (both
routes), gate-refused (blocked peer, exhausted sequence), off-arm, malformed. -/

/-- A clean accept peer (loopback-class, admitted by the deployed ruleset). -/
def cleanPeer : ByteArray :=
  ByteArray.mk (Reactor.Stage.IpFilter.encodeAddr Reactor.Stage.IpFilter.cleanClient).toArray

/-- A blocked accept peer (inside the denied `/8`). -/
def blockedPeer : ByteArray :=
  ByteArray.mk (Reactor.Stage.IpFilter.encodeAddr Reactor.Stage.IpFilter.blockedClient).toArray

-- The scalar gates decide exactly as deployed: admit clean, refuse blocked;
-- admit under the cap, refuse at it.
#guard ipGateB cleanPeer
#guard !(ipGateB blockedPeer)
#guard rateGateB 0 && rateGateB 7
#guard !(rateGateB 8)
-- The index-decided `/bulk` arm genuinely fires through the shared parse.
#guard gateB bulkDemoReq && ipGateB cleanPeer && rateGateB 0
        && bulkArmOf (parseArr (spanArr (full bulkDemoReq)))
-- Byte-identity to the deployed metered fold on every shape.
#guard (serveMeteredHeadIdx cleanPeer 0 bulkDemoReq).data.toList
        == (meteredFoldServe cleanPeer 0 bulkDemoReq).data.toList
#guard (serveMeteredHeadIdx cleanPeer 0 healthReq).data.toList
        == (meteredFoldServe cleanPeer 0 healthReq).data.toList
#guard (serveMeteredHeadIdx cleanPeer 0 bulkGzipReq).data.toList
        == (meteredFoldServe cleanPeer 0 bulkGzipReq).data.toList
#guard (serveMeteredHeadIdx cleanPeer 0 echoPostReq).data.toList
        == (meteredFoldServe cleanPeer 0 echoPostReq).data.toList
#guard (serveMeteredHeadIdx cleanPeer 0 oldReq).data.toList
        == (meteredFoldServe cleanPeer 0 oldReq).data.toList
#guard (serveMeteredHeadIdx blockedPeer 0 bulkDemoReq).data.toList
        == (meteredFoldServe blockedPeer 0 bulkDemoReq).data.toList
#guard (serveMeteredHeadIdx cleanPeer 8 bulkDemoReq).data.toList
        == (meteredFoldServe cleanPeer 8 bulkDemoReq).data.toList
-- The dense arms genuinely fire: 1 MiB bulk body, tiny health body; the refusals
-- genuinely refuse (no 1 MiB body on the blocked/exhausted paths).
#guard (serveMeteredHeadIdx cleanPeer 0 bulkDemoReq).size > 1048576
#guard (serveMeteredHeadIdx cleanPeer 0 healthReq).size > 2
#guard (serveMeteredHeadIdx blockedPeer 0 bulkDemoReq).size < 1024
#guard (serveMeteredHeadIdx cleanPeer 8 bulkDemoReq).size < 1024

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms rate_admits_metered
#print axioms meteredFold_bulk_eq
#print axioms meteredFold_health_eq
#print axioms serveMeteredHeadIdx_eq
#print axioms serveMeteredHeadIdxConformant_eq
#print axioms serveMeteredHeadIdxConformant_head_no_body
#print axioms serveMeteredHeadIdxConformant_rejects_missingHost

end Datapath.ServeMeteredHeadIdx
