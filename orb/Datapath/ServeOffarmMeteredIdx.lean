import Datapath.ServeOffarmIdx
import Datapath.ServeMeteredHeadIdx

/-!
# Datapath.ServeOffarmMeteredIdx — the METERED serve with the off-arm densified

`Datapath.ServeMeteredHeadIdx.serveMeteredHeadIdx` decides the metered gates on
the host scalars and the `/bulk`/`/health` arms index-natively — but its OFF-ARM
still falls to the metered `List` fold (`servePipelineFull2Metered`, its named
standing residual): a catch-all `404`, a vhost answer, or a glob hit on the
metered seam still consed `input.toList` twice. This module lifts the four
constant-body off-arm routes (`Datapath.ServeOffarmIdx`) onto the metered seam:

* the metered gates stay the scalar decisions (`ipGateB`/`rateGateB` — no ctx,
  no `List.replicate`);
* ONE index-native head parse, off which ALL SIX dense arms are decided;
* the admitted-arm metered bridge is generalized (`meteredFold_gates_eq`): with
  both metered gates admitting and the six request-level gate conjuncts (which
  EVERY dense arm carries), the metered fold collapses to the bare fold — so
  each off-arm route's proven bare-fold byte-identity transfers.

`serveOffarmMeteredIdx_eq` proves byte-identity to the deployed metered fold for
EVERY `(peer, seq, input)`; the conformant wrapper carries it through the same
proven RFC stages the deployed metered default crosses.
-/

namespace Datapath.ServeOffarmMeteredIdx

open Proto (Bytes)
open Reactor.Pipeline (Ctx runPipeline)
open Reactor.Deploy
open Reactor.Config (protoReqOf)
open Datapath.SpanBytes (full parseArr spanArr)
open Datapath.HeadIdx (bulkIdxB healthIdxB)
open Datapath.ServeDenseReal (denseArm_eq bulkDemoReq)
open Datapath.ServeDenseIdx (denseHeadBytesIdx healthHeadBytesIdx healthBodyDense
  denseHeadBytesIdx_eq healthHeadBytesIdx_eq healthArm_eq denseArmB_sound
  healthArmB_sound healthReq bulkGzipReq)
open Datapath.ServeDenseFullReal (bulkBodyDense)
open Datapath.ServeHeadIdx (gateB denseArmB_headIdx healthArmB_headIdx echoPostReq oldReq)
open Datapath.ServeMeteredHeadIdx (ipGateB rateGateB ctxAddr_metered rate_admits_metered
  ipfilterStage_pass_admit full2_reduces_unknown_pass innerFold_ctxOfMetered
  meteredFoldServe meteredFold_bulk_eq meteredFold_health_eq cleanPeer blockedPeer)
open Datapath.OffarmApp (notFoundBodyDense vhostABodyDense vhostBBodyDense globBodyDense)
open Datapath.OffarmArms
open Datapath.ServeOffarmIdx (notFoundHeadIdx vhostAHeadIdx vhostBHeadIdx globHeadIdx
  notFoundArm_eq vhostAArm_eq vhostBArm_eq globArm_eq parseArr_dispatch
  nfReq vaReq vbReq globDemoReq nfGzipReq staticReq armFires)

/-! ## 1. The admitted-arm metered bridge, generalized to the gate conjuncts

`meteredFold_bulk_eq`/`meteredFold_health_eq` are route-pinned. Every dense arm
carries the SAME six request-level gate conjuncts, and those (plus the two
admitting metered gates) are all the collapse needs — so this is the ONE bridge
all four new arms cross. -/

/-- With both metered gates admitting and the six gate conjuncts holding on the
bare ctx, the metered fold emits the SAME bytes as the bare fold. -/
theorem meteredFold_gates_eq (peer : Bytes) (seq : Nat) (input : Bytes)
    (hadmin : isAdminPath (ctxOf input).req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath (ctxOf input).req = false)
    (hrate0 : Reactor.Stage.Rate.admits (ctxOf input) = true)
    (hredir : ¬ ((ctxOf input).req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes (ctxOf input).req = false)
    (hpol : policyReserved (ctxOf input).req = false)
    (hip_m : Reactor.Stage.IpFilter.deployAdmits
        (Reactor.Stage.IpFilter.ctxAddr (ctxOfMetered peer seq input)) = true)
    (hrate_m : Reactor.Stage.Rate.admits (ctxOfMetered peer seq input) = true) :
    servePipelineFull2Metered peer seq input = servePipelineFull2 input := by
  have hin : (ctxOfMetered peer seq input).input = (ctxOf input).input := rfl
  have key : runPipeline deployStagesFull2 appHandler (ctxOfMetered peer seq input)
           = runPipeline deployStagesFull2 appHandler (ctxOf input) := by
    rw [full2_reduces_unknown_pass (ctxOfMetered peer seq input) hadmin hpriv
          (ipfilterStage_pass_admit _ hip_m) hrate_m hredir htrav hpol,
        full2_reduces_unknown (ctxOf input) hadmin hpriv rfl hrate0 hredir htrav hpol,
        innerFold_ctxOfMetered peer seq input, hin]
  unfold servePipelineFull2Metered servePipelineFull2
  rw [key]

/-! ## 2. THE METERED SERVE — gates on scalars, ONE head read, SIX dense arms -/

/-- **The off-arm-densified METERED serve.** The metered gates on the host
scalars, one index-native head parse, six dense arms (`/bulk`, `/health`, the
two exact vhosts, the glob, the catch-all `404`); a refusing gate or a genuinely
non-dense request falls back to the deployed metered `List` fold verbatim (where
the 403/429 refusals are produced by the in-fold gate stages, unchanged). -/
@[export drorb_serve_offarm_metered_idx]
def serveOffarmMeteredIdx (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  if gateB input && ipGateB peer && rateGateB seq.toNat then
    match parseArr (spanArr (full input)) with
    | .complete areq =>
        if bulkIdxB areq then
          ByteArray.mk (denseHeadBytesIdx input).toArray ++ bulkBodyDense
        else if healthIdxB areq then
          ByteArray.mk (healthHeadBytesIdx input).toArray ++ healthBodyDense
        else if vhostAIdxB areq then
          ByteArray.mk (vhostAHeadIdx input).toArray ++ vhostABodyDense
        else if vhostBIdxB areq then
          ByteArray.mk (vhostBHeadIdx input).toArray ++ vhostBBodyDense
        else if globIdxB areq then
          ByteArray.mk (globHeadIdx input).toArray ++ globBodyDense
        else if notFoundIdxB areq then
          ByteArray.mk (notFoundHeadIdx input).toArray ++ notFoundBodyDense
        else
          meteredFoldServe peer seq input
    | _ => meteredFoldServe peer seq input
  else
    meteredFoldServe peer seq input

/-! ## 3. The byte-identity -/

/-- **THE BYTE-IDENTITY.** For EVERY `(peer, seq, input)`, the off-arm-densified
metered serve produces the IDENTICAL bytes to the deployed metered fold: each
firing arm implies the deployed arm, whose dense emission equals the bare fold
(the proven arm equalities), and the bare fold equals the metered fold under the
admitting gates (`meteredFold_gates_eq` for the four new arms; the pinned
bridges for `/bulk`/`/health`). -/
theorem serveOffarmMeteredIdx_eq (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    serveOffarmMeteredIdx peer seq input = meteredFoldServe peer seq input := by
  unfold serveOffarmMeteredIdx
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
            else if vhostAIdxB areq then
              ByteArray.mk (vhostAHeadIdx input).toArray ++ vhostABodyDense
            else if vhostBIdxB areq then
              ByteArray.mk (vhostBHeadIdx input).toArray ++ vhostBBodyDense
            else if globIdxB areq then
              ByteArray.mk (globHeadIdx input).toArray ++ globBodyDense
            else if notFoundIdxB areq then
              ByteArray.mk (notFoundHeadIdx input).toArray ++ notFoundBodyDense
            else meteredFoldServe peer seq input) = meteredFoldServe peer seq input
      by_cases hb : bulkIdxB areq = true
      · rw [if_pos hb]
        have hdense : Datapath.ServeDenseIdx.denseArmB input = true := by
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
          have hhealth : Datapath.ServeDenseIdx.healthArmB input = true := by
            rw [healthArmB_headIdx, hgate, hp, Bool.true_and]
            exact hh
          rw [healthHeadBytesIdx_eq input hhealth,
              healthArm_eq input (healthArmB_sound input hhealth)]
          unfold meteredFoldServe
          rw [meteredFold_health_eq peer.toList seq.toNat input.toList
                (healthArmB_sound input hhealth) hip_m hrate_m]
        · rw [if_neg hh]
          by_cases hva : vhostAIdxB areq = true
          · rw [if_pos hva]
            obtain ⟨rest, hsub⟩ := parseArr_dispatch input areq hgate hp
            obtain ⟨hadmin, hpriv, hrate0, hredir, htrav, hpol, _, _, _, _, _, _⟩ :
                VhostAArm (ctxOf input.toList) :=
              vhostAArm_of_req input.toList (protoReqOf areq) (ctxOf_req _ _ _ hsub)
                ((vhostAIdxB_iff areq).mp hva)
            rw [vhostAArm_eq input areq hgate hp hva]
            unfold meteredFoldServe
            rw [meteredFold_gates_eq peer.toList seq.toNat input.toList
                  hadmin hpriv hrate0 hredir htrav hpol hip_m hrate_m]
          · rw [if_neg hva]
            by_cases hvb : vhostBIdxB areq = true
            · rw [if_pos hvb]
              obtain ⟨rest, hsub⟩ := parseArr_dispatch input areq hgate hp
              obtain ⟨hadmin, hpriv, hrate0, hredir, htrav, hpol, _, _, _, _, _, _⟩ :
                  VhostBArm (ctxOf input.toList) :=
                vhostBArm_of_req input.toList (protoReqOf areq) (ctxOf_req _ _ _ hsub)
                  ((vhostBIdxB_iff areq).mp hvb)
              rw [vhostBArm_eq input areq hgate hp hvb]
              unfold meteredFoldServe
              rw [meteredFold_gates_eq peer.toList seq.toNat input.toList
                    hadmin hpriv hrate0 hredir htrav hpol hip_m hrate_m]
            · rw [if_neg hvb]
              by_cases hgl : globIdxB areq = true
              · rw [if_pos hgl]
                obtain ⟨rest, hsub⟩ := parseArr_dispatch input areq hgate hp
                obtain ⟨hadmin, hpriv, hrate0, hredir, htrav, hpol,
                    _, _, _, _, _, _, _, _⟩ :
                    GlobArm (ctxOf input.toList) :=
                  globArm_of_req input.toList (protoReqOf areq) (ctxOf_req _ _ _ hsub)
                    ((globIdxB_iff areq).mp hgl)
                rw [globArm_eq input areq hgate hp hgl]
                unfold meteredFoldServe
                rw [meteredFold_gates_eq peer.toList seq.toNat input.toList
                      hadmin hpriv hrate0 hredir htrav hpol hip_m hrate_m]
              · rw [if_neg hgl]
                by_cases hnf : notFoundIdxB areq = true
                · rw [if_pos hnf]
                  obtain ⟨rest, hsub⟩ := parseArr_dispatch input areq hgate hp
                  obtain ⟨hadmin, hpriv, hrate0, hredir, htrav, hpol,
                      _, _, _, _, _, _, _, _, _⟩ :
                      NotFoundArm (ctxOf input.toList) :=
                    notFoundArm_of_req input.toList (protoReqOf areq) (ctxOf_req _ _ _ hsub)
                      ((notFoundIdxB_iff areq).mp hnf)
                  rw [notFoundArm_eq input areq hgate hp hnf]
                  unfold meteredFoldServe
                  rw [meteredFold_gates_eq peer.toList seq.toNat input.toList
                        hadmin hpriv hrate0 hredir htrav hpol hip_m hrate_m]
                · rw [if_neg hnf]
    | incomplete => rfl
    | error e d => rfl

/-! ## 4. The RFC-conformant wrapper — the seam the metered default crosses -/

/-- **`drorb_serve_offarm_metered_idx_conformant`** — the SAME proven
`conformantServe` stages wrapped around the off-arm-densified metered serve.
Same `(peer, seq, input)` ABI as the deployed metered-conformant serves. -/
@[export drorb_serve_offarm_metered_idx_conformant]
def serveOffarmMeteredIdxConformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  Reactor.ServeConformant.conformantServe (fun i => serveOffarmMeteredIdx peer seq i) input

/-- The conformant wrapper preserves the byte-identity (funext through the
wrapper). -/
theorem serveOffarmMeteredIdxConformant_eq (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    serveOffarmMeteredIdxConformant peer seq input
      = Reactor.ServeConformant.conformantServe
          (fun i => meteredFoldServe peer seq i) input := by
  unfold serveOffarmMeteredIdxConformant
  have hf : (fun i => serveOffarmMeteredIdx peer seq i)
          = (fun i => meteredFoldServe peer seq i) := by
    funext i; exact serveOffarmMeteredIdx_eq peer seq i
  rw [hf]

/-! ## 5. Non-vacuity — the new arms fire (and the refusals refuse) on the
metered seam, byte-identical to the deployed metered fold on every shape. -/

-- Byte-identity to the deployed metered fold: the four new dense arms...
#guard (serveOffarmMeteredIdx cleanPeer 0 nfReq).data.toList
        == (meteredFoldServe cleanPeer 0 nfReq).data.toList
#guard (serveOffarmMeteredIdx cleanPeer 0 vaReq).data.toList
        == (meteredFoldServe cleanPeer 0 vaReq).data.toList
#guard (serveOffarmMeteredIdx cleanPeer 0 vbReq).data.toList
        == (meteredFoldServe cleanPeer 0 vbReq).data.toList
#guard (serveOffarmMeteredIdx cleanPeer 0 globDemoReq).data.toList
        == (meteredFoldServe cleanPeer 0 globDemoReq).data.toList
-- ...the two existing dense arms and the honest fallbacks...
#guard (serveOffarmMeteredIdx cleanPeer 0 bulkDemoReq).data.toList
        == (meteredFoldServe cleanPeer 0 bulkDemoReq).data.toList
#guard (serveOffarmMeteredIdx cleanPeer 0 healthReq).data.toList
        == (meteredFoldServe cleanPeer 0 healthReq).data.toList
#guard (serveOffarmMeteredIdx cleanPeer 0 nfGzipReq).data.toList
        == (meteredFoldServe cleanPeer 0 nfGzipReq).data.toList
#guard (serveOffarmMeteredIdx cleanPeer 0 staticReq).data.toList
        == (meteredFoldServe cleanPeer 0 staticReq).data.toList
#guard (serveOffarmMeteredIdx cleanPeer 0 oldReq).data.toList
        == (meteredFoldServe cleanPeer 0 oldReq).data.toList
#guard (serveOffarmMeteredIdx cleanPeer 0 echoPostReq).data.toList
        == (meteredFoldServe cleanPeer 0 echoPostReq).data.toList
-- ...and the gate refusals (blocked peer, exhausted sequence) on a miss.
#guard (serveOffarmMeteredIdx blockedPeer 0 nfReq).data.toList
        == (meteredFoldServe blockedPeer 0 nfReq).data.toList
#guard (serveOffarmMeteredIdx cleanPeer 8 nfReq).data.toList
        == (meteredFoldServe cleanPeer 8 nfReq).data.toList
-- The dense 404 genuinely fires on the metered seam (small answer, admitted
-- gates); the refusals genuinely refuse.
#guard (serveOffarmMeteredIdx cleanPeer 0 nfReq).size < 1024
#guard (serveOffarmMeteredIdx blockedPeer 0 nfReq).size < 1024

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms meteredFold_gates_eq
#print axioms serveOffarmMeteredIdx_eq
#print axioms serveOffarmMeteredIdxConformant_eq

end Datapath.ServeOffarmMeteredIdx
