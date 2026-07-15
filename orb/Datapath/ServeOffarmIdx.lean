import Datapath.OffarmArms
import Datapath.ServeHeadIdx

/-!
# Datapath.ServeOffarmIdx — the serve with the OFF-ARM densified

`Datapath.ServeHeadIdx.serveHeadIdx` decides `/bulk` and `/health` index-natively
and emits them densely — but its OFF-ARM (everything else) still falls to
`servePipelineFull2 input.toList`: the WHOLE input is materialized as a cons-list
and the `List` fold re-parses it, for routes whose answers are CONSTANTS. This
module densifies the four constant-body off-arm routes:

* the **catch-all `404`** — the by-far most common off-arm answer (every scanner
  probe, every typo) previously consed the whole input twice to say "not found";
* the **two exact virtual hosts** (`a.example` / `b.example`) — decided by the
  index-native host compare (`hostEqIdx`), never through `protoReqOf`;
* the **assets glob route** — decided by the real `pathMatch` on the once-resolved
  target segments.

Each new arm: ONE shared index-native head parse (`parseArr` — the same single
parse `serveHeadIdx` introduced), the arm decided on the arena head
(`Datapath.OffarmArms`), the head rendered from the proven flat header fold with
the CONSTANT `x-upstream` (`uvDefault`) and the index-native `x-corr`
(`corrValB`), and the CONSTANT dense body bulk-appended. NO `input.toList`, NO
`deploySubs`, NO `protoReqOf` on any deciding or emitting path of the six dense
arms.

`serveOffarmIdx_refines` proves byte-identity to
`Datapath.ServeFlatFull.deployedServeRef` (= `Dataplane.drorbServe`) for EVERY
input: each firing guard implies the deployed arm (the parse refinement + the
dispatch bridge), where the dense emission is proven equal to the deployed
`List` fold (`constArm_eq` for the four new arms; the existing `/bulk`/`/health`
identities for the old two).

## Honest residual (what still falls to the `List` fold)

* `/static/⋯` — the request-aware conditioned FILE answer (ETag/`Range`/
  conditional branches on real file bytes): index-decidable in principle, but its
  response is not a constant and needs its own head/body equality — NOT done here;
* `/cgi-bin/⋯` — the CGI answer (script-derived);
* the GATED answers (the `401`/`403`/`404`/`429` refusals of the admin, basic-auth,
  traversal, policy, and metered gates), the `308` redirect, the gzip and CORS
  transform arms, warm-cache hits, and the h2c engine;
* the metered/cfg-route serves' off-arm (`servePipelineFull2Metered` and the
  config-instantiated fold) — the same four routes could be lifted onto the
  metered seam via `ServeMeteredHeadIdx`'s gate bridges, not done here.
-/

namespace Datapath.ServeOffarmIdx

open Proto (Bytes)
open Reactor.Deploy
open Reactor.Config (protoReqOf)
open Reactor.ServeConformant (ba_toList_eq ba_toList_length)
open Datapath.SpanBytes (full full_wf parseArr spanArr parseIndexNative
  parseIndexNative_refines read_eq_denote denote_full)
open Datapath.DenseHead (renderHead denseHeadersBlock)
open Datapath.ServeDenseIdx (corrValB corrValB_eq deploySubs_dispatch
  denseHeadBytesIdx healthHeadBytesIdx healthBodyDense healthBody
  denseHeadBytesIdx_eq healthHeadBytesIdx_eq healthArm_eq
  denseArmB_sound healthArmB_sound hasH2PrefaceB hasH2PrefaceB_eq
  healthReq bulkGzipReq)
open Datapath.ServeDenseReal (denseArm_eq bulkDemoReq bulkDemoReqAnyHost)
open Datapath.ServeDenseFullReal (bulkBodyDense)
open Datapath.HeadIdx (bulkIdxB healthIdxB)
open Datapath.ServeHeadIdx (gateB denseArmB_headIdx healthArmB_headIdx
  echoPostReq oldReq bulkHeadReq)
open Datapath.OffarmApp (notFoundBody notFoundBodyDense notFoundBodyDense_toList
  vhostABody vhostABodyDense vhostABodyDense_toList
  vhostBBody vhostBBodyDense vhostBBodyDense_toList
  globBody globBodyDense globBodyDense_toList
  rewriteBytes_notFoundBody rewriteBytes_vhostABody rewriteBytes_vhostBBody
  rewriteBytes_globBody uvDefault uv_dispatch constArm_eq
  appHandler_notFound appHandler_vhostA appHandler_vhostB appHandler_glob)
open Datapath.OffarmArms

/-! ## 1. The dispatch bridge off the SHARED parse

Every dense-arm byte-identity needs `deploySubs input.toList = .dispatch req :: _`
for the head the index-native parse produced. This discharges it ONCE, from the
in-budget gate and the shared `parseArr` outcome — each arm then only decodes its
own guard. -/

/-- A gated, completely-parsed head IS the deployed dispatch: the deployed
submissions open with `.dispatch (protoReqOf areq)`. -/
theorem parseArr_dispatch (input : ByteArray) (areq : Arena.Parse.Request)
    (hg : gateB input = true)
    (hp : parseArr (spanArr (full input)) = .complete areq) :
    ∃ rest, deploySubs input.toList = .dispatch (protoReqOf areq) :: rest := by
  unfold Datapath.ServeHeadIdx.gateB at hg
  rw [Bool.and_eq_true] at hg
  obtain ⟨hsz, hlen⟩ := hg
  have hread : (full input).read = input.toList := by
    rw [read_eq_denote _ (full_wf _), denote_full, ← ba_toList_eq]
  have hparse : Reactor.Config.h1ParseFn input.toList
      = .request areq.consumed (protoReqOf areq)
          (Reactor.Config.deriveKeepAlive (protoReqOf areq).headers) := by
    rw [← hread, ← parseIndexNative_refines _ (full_wf _)]
    show Reactor.Config.arenaToProto (parseArr (spanArr (full input))) = _
    rw [hp]
    rfl
  have hlen' : ¬ input.toList.length > deployConfig.maxHeaderBytes := by
    rw [ba_toList_length]; exact of_decide_eq_true hlen
  have hne : input.toList.isEmpty = false := by
    have hpos : 0 < input.toList.length := by
      rw [ba_toList_length]; exact of_decide_eq_true hsz
    cases hl : input.toList with
    | nil => rw [hl] at hpos; exact absurd hpos (by simp)
    | cons a t => rfl
  exact deploySubs_dispatch input.toList areq.consumed (protoReqOf areq)
    (Reactor.Config.deriveKeepAlive (protoReqOf areq).headers) hlen' hne hparse

/-! ## 2. The four dense heads — constant `x-upstream`, index-native `x-corr` -/

/-- The dense catch-all `404` head — NO `input.toList`. -/
def notFoundHeadIdx (input : ByteArray) : Bytes :=
  renderHead 404 (Reactor.App.reasonFor 404)
    (denseHeadersBlock [] uvDefault (corrValB input)).denote notFoundBody.length

/-- The dense `a.example` head — NO `input.toList`. -/
def vhostAHeadIdx (input : ByteArray) : Bytes :=
  renderHead 200 (Reactor.App.reasonFor 200)
    (denseHeadersBlock [] uvDefault (corrValB input)).denote vhostABody.length

/-- The dense `b.example` head — NO `input.toList`. -/
def vhostBHeadIdx (input : ByteArray) : Bytes :=
  renderHead 200 (Reactor.App.reasonFor 200)
    (denseHeadersBlock [] uvDefault (corrValB input)).denote vhostBBody.length

/-- The dense glob-route head — NO `input.toList`. -/
def globHeadIdx (input : ByteArray) : Bytes :=
  renderHead 200 (Reactor.App.reasonFor 200)
    (denseHeadersBlock [] uvDefault (corrValB input)).denote globBody.length

/-! ## 3. The four arm byte-identities -/

/-- **The `404` arm equality.** A firing index guard implies the deployed arm
(through the shared parse + the dispatch bridge), where the dense emission is
the deployed `List` fold's bytes (`constArm_eq` instantiated at the `404`
answer, the scalar collapse by `uv_dispatch`/`corrValB_eq`). -/
theorem notFoundArm_eq (input : ByteArray) (areq : Arena.Parse.Request)
    (hg : gateB input = true)
    (hp : parseArr (spanArr (full input)) = .complete areq)
    (hx : notFoundIdxB areq = true) :
    ByteArray.mk (notFoundHeadIdx input).toArray ++ notFoundBodyDense
      = ByteArray.mk (servePipelineFull2 input.toList).toArray := by
  obtain ⟨rest, hsub⟩ := parseArr_dispatch input areq hg hp
  have harm : NotFoundArm (ctxOf input.toList) :=
    notFoundArm_of_req input.toList (protoReqOf areq) (ctxOf_req _ _ _ hsub)
      ((notFoundIdxB_iff areq).mp hx)
  obtain ⟨hadmin, hpriv, hrate, hredir, htrav, hpol, hgz, hcors,
    hnh, hns, hnc, hng, hnbk, hna, hnb⟩ := harm
  have happ := appHandler_notFound (ctxOf input.toList) hnh hns hnc hng hnbk hna hnb
  have hhead : notFoundHeadIdx input
      = renderHead 404 (Reactor.App.reasonFor 404)
          (denseHeadersBlock []
            (upstreamVal (deployPlan (deploySubs input.toList)))
            (corrVal input.toList)).denote notFoundBody.length := by
    unfold notFoundHeadIdx
    rw [corrValB_eq, uv_dispatch input.toList _ rest hsub]
  rw [hhead]
  exact constArm_eq input.toList 404 (Reactor.App.reasonFor 404) notFoundBody
    notFoundBodyDense notFoundBodyDense_toList hadmin hpriv hrate hredir htrav hpol
    hgz hcors happ rewriteBytes_notFoundBody

/-- **The `a.example` arm equality.** -/
theorem vhostAArm_eq (input : ByteArray) (areq : Arena.Parse.Request)
    (hg : gateB input = true)
    (hp : parseArr (spanArr (full input)) = .complete areq)
    (hx : vhostAIdxB areq = true) :
    ByteArray.mk (vhostAHeadIdx input).toArray ++ vhostABodyDense
      = ByteArray.mk (servePipelineFull2 input.toList).toArray := by
  obtain ⟨rest, hsub⟩ := parseArr_dispatch input areq hg hp
  have harm : VhostAArm (ctxOf input.toList) :=
    vhostAArm_of_req input.toList (protoReqOf areq) (ctxOf_req _ _ _ hsub)
      ((vhostAIdxB_iff areq).mp hx)
  obtain ⟨hadmin, hpriv, hrate, hredir, htrav, hpol, hgz, hcors, hnh, hns, hnc, hva⟩ := harm
  have happ := appHandler_vhostA (ctxOf input.toList) hnh hns hnc hva
  have hhead : vhostAHeadIdx input
      = renderHead 200 (Reactor.App.reasonFor 200)
          (denseHeadersBlock []
            (upstreamVal (deployPlan (deploySubs input.toList)))
            (corrVal input.toList)).denote vhostABody.length := by
    unfold vhostAHeadIdx
    rw [corrValB_eq, uv_dispatch input.toList _ rest hsub]
  rw [hhead]
  exact constArm_eq input.toList 200 (Reactor.App.reasonFor 200) vhostABody
    vhostABodyDense vhostABodyDense_toList hadmin hpriv hrate hredir htrav hpol
    hgz hcors happ rewriteBytes_vhostABody

/-- **The `b.example` arm equality.** -/
theorem vhostBArm_eq (input : ByteArray) (areq : Arena.Parse.Request)
    (hg : gateB input = true)
    (hp : parseArr (spanArr (full input)) = .complete areq)
    (hx : vhostBIdxB areq = true) :
    ByteArray.mk (vhostBHeadIdx input).toArray ++ vhostBBodyDense
      = ByteArray.mk (servePipelineFull2 input.toList).toArray := by
  obtain ⟨rest, hsub⟩ := parseArr_dispatch input areq hg hp
  have harm : VhostBArm (ctxOf input.toList) :=
    vhostBArm_of_req input.toList (protoReqOf areq) (ctxOf_req _ _ _ hsub)
      ((vhostBIdxB_iff areq).mp hx)
  obtain ⟨hadmin, hpriv, hrate, hredir, htrav, hpol, hgz, hcors, hnh, hns, hnc, hvb⟩ := harm
  have happ := appHandler_vhostB (ctxOf input.toList) hnh hns hnc hvb
  have hhead : vhostBHeadIdx input
      = renderHead 200 (Reactor.App.reasonFor 200)
          (denseHeadersBlock []
            (upstreamVal (deployPlan (deploySubs input.toList)))
            (corrVal input.toList)).denote vhostBBody.length := by
    unfold vhostBHeadIdx
    rw [corrValB_eq, uv_dispatch input.toList _ rest hsub]
  rw [hhead]
  exact constArm_eq input.toList 200 (Reactor.App.reasonFor 200) vhostBBody
    vhostBBodyDense vhostBBodyDense_toList hadmin hpriv hrate hredir htrav hpol
    hgz hcors happ rewriteBytes_vhostBBody

/-- **The glob arm equality.** -/
theorem globArm_eq (input : ByteArray) (areq : Arena.Parse.Request)
    (hg : gateB input = true)
    (hp : parseArr (spanArr (full input)) = .complete areq)
    (hx : globIdxB areq = true) :
    ByteArray.mk (globHeadIdx input).toArray ++ globBodyDense
      = ByteArray.mk (servePipelineFull2 input.toList).toArray := by
  obtain ⟨rest, hsub⟩ := parseArr_dispatch input areq hg hp
  have harm : GlobArm (ctxOf input.toList) :=
    globArm_of_req input.toList (protoReqOf areq) (ctxOf_req _ _ _ hsub)
      ((globIdxB_iff areq).mp hx)
  obtain ⟨hadmin, hpriv, hrate, hredir, htrav, hpol, hgz, hcors,
    hnh, hns, hnc, hgm, hna, hnb⟩ := harm
  have happ := appHandler_glob (ctxOf input.toList) hnh hns hnc hgm hna hnb
  have hhead : globHeadIdx input
      = renderHead 200 (Reactor.App.reasonFor 200)
          (denseHeadersBlock []
            (upstreamVal (deployPlan (deploySubs input.toList)))
            (corrVal input.toList)).denote globBody.length := by
    unfold globHeadIdx
    rw [corrValB_eq, uv_dispatch input.toList _ rest hsub]
  rw [hhead]
  exact constArm_eq input.toList 200 (Reactor.App.reasonFor 200) globBody
    globBodyDense globBodyDense_toList hadmin hpriv hrate hredir htrav hpol
    hgz hcors happ rewriteBytes_globBody

/-! ## 4. THE SERVE — six dense arms off ONE index-native head read -/

/-- **The off-arm-densified serve.** The h2c fork by index probes; the in-budget
gate by O(1) field reads; ONE index-native head parse; then SIX dense arms decided
on the arena head — `/bulk`, `/health` (the existing proven emitters), the two
exact vhosts, the assets glob, and the catch-all `404` (the new constant-body
emitters). Only a request that is genuinely none of these (a real `/static` or
`/cgi-bin` hit, a gate refusal, a redirect, a gzip/CORS-transformed answer, a
parse reject) falls back to the deployed `List` fold. -/
@[export drorb_serve_offarm_idx]
def serveOffarmIdx (input : ByteArray) : ByteArray :=
  if hasH2PrefaceB input then
    ByteArray.mk (Reactor.H2Ingress.serveH2c input.toList).toArray
  else if gateB input then
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
          ByteArray.mk (servePipelineFull2 input.toList).toArray
    | _ => ByteArray.mk (servePipelineFull2 input.toList).toArray
  else
    ByteArray.mk (servePipelineFull2 input.toList).toArray

/-- **THE BYTE-IDENTITY.** For EVERY input, the off-arm-densified serve produces
the IDENTICAL bytes to the deployed serve
(`Datapath.ServeFlatFull.deployedServeRef` = `Dataplane.drorbServe`). -/
theorem serveOffarmIdx_refines (input : ByteArray) :
    serveOffarmIdx input = Datapath.ServeFlatFull.deployedServeRef input := by
  unfold serveOffarmIdx Datapath.ServeFlatFull.deployedServeRef
  rw [hasH2PrefaceB_eq]
  by_cases h2 : Reactor.Ingress.hasH2Preface input.toList
  · simp only [h2, if_true]
  · simp only [h2, Bool.false_eq_true, if_false]
    cases hg : gateB input with
    | false => rw [if_neg Bool.false_ne_true]
    | true =>
      rw [if_pos rfl]
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
              else ByteArray.mk (servePipelineFull2 input.toList).toArray)
            = ByteArray.mk (servePipelineFull2 input.toList).toArray
        by_cases hb : bulkIdxB areq = true
        · rw [if_pos hb]
          have hdense : Datapath.ServeDenseIdx.denseArmB input = true := by
            rw [denseArmB_headIdx, hg, hp, Bool.true_and]
            exact hb
          rw [denseHeadBytesIdx_eq input hdense]
          exact denseArm_eq input (denseArmB_sound input hdense)
        · rw [if_neg hb]
          by_cases hh : healthIdxB areq = true
          · rw [if_pos hh]
            have hhealth : Datapath.ServeDenseIdx.healthArmB input = true := by
              rw [healthArmB_headIdx, hg, hp, Bool.true_and]
              exact hh
            rw [healthHeadBytesIdx_eq input hhealth]
            exact healthArm_eq input (healthArmB_sound input hhealth)
          · rw [if_neg hh]
            by_cases hva : vhostAIdxB areq = true
            · rw [if_pos hva]
              exact vhostAArm_eq input areq hg hp hva
            · rw [if_neg hva]
              by_cases hvb : vhostBIdxB areq = true
              · rw [if_pos hvb]
                exact vhostBArm_eq input areq hg hp hvb
              · rw [if_neg hvb]
                by_cases hgl : globIdxB areq = true
                · rw [if_pos hgl]
                  exact globArm_eq input areq hg hp hgl
                · rw [if_neg hgl]
                  by_cases hnf : notFoundIdxB areq = true
                  · rw [if_pos hnf]
                    exact notFoundArm_eq input areq hg hp hnf
                  · rw [if_neg hnf]
      | incomplete => rfl
      | error e d => rfl

/-! ## 5. Non-vacuity — every new arm FIRES on a real request (and refuses the
neighbouring shapes), and the serve is byte-identical to the deployed serve on
every shape: the four new arms, the two old arms, gated/redirect/static/cgi
off-arm fallbacks, and malformed input. -/

/-- A miss — no author route, no vhost, no glob, no `/bulk`: the catch-all. -/
def nfReq : ByteArray := "GET /nope HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

/-- Any path under the `a.example` authority: the vhost-a catch-all. -/
def vaReq : ByteArray := "GET /anything HTTP/1.1\r\nHost: a.example\r\n\r\n".toUTF8

/-- The root path under the `b.example` authority: the vhost-b catch-all. -/
def vbReq : ByteArray := "GET / HTTP/1.1\r\nHost: b.example\r\n\r\n".toUTF8

/-- An assets-glob hit under a non-vhost authority. -/
def globDemoReq : ByteArray :=
  "GET /health/assets/app.js HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

/-- A gzip-accepting miss — the gzip transform arm must answer (fallback). -/
def nfGzipReq : ByteArray :=
  "GET /nope HTTP/1.1\r\nHost: x\r\nAccept-Encoding: gzip\r\n\r\n".toUTF8

/-- A `/static` hit — the request-aware file answer (fallback, named residual). -/
def staticReq : ByteArray := "GET /static/hello.txt HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

/-- The guard helper the non-vacuity checks probe an arm through: the SAME gate +
single shared parse the serve runs. -/
def armFires (f : Arena.Parse.Request → Bool) (input : ByteArray) : Bool :=
  gateB input
    && (match parseArr (spanArr (full input)) with
        | .complete areq => f areq
        | _ => false)

-- The four new arms genuinely FIRE, index-decided, on their real requests.
#guard armFires notFoundIdxB nfReq
#guard armFires vhostAIdxB vaReq
#guard armFires vhostBIdxB vbReq
#guard armFires globIdxB globDemoReq
-- ...and REFUSE the neighbouring shapes.
#guard !(armFires notFoundIdxB healthReq)
#guard !(armFires notFoundIdxB bulkDemoReq)
#guard !(armFires notFoundIdxB vaReq)
#guard !(armFires notFoundIdxB globDemoReq)
#guard !(armFires notFoundIdxB nfGzipReq)
#guard !(armFires notFoundIdxB staticReq)
#guard !(armFires notFoundIdxB oldReq)
#guard !(armFires vhostAIdxB nfReq)
#guard !(armFires vhostAIdxB vbReq)
#guard !(armFires vhostBIdxB vaReq)
#guard !(armFires globIdxB healthReq)
#guard !(armFires globIdxB nfReq)
-- The serve is byte-identical to the deployed serve on EVERY shape: the four
-- new dense arms...
#guard (serveOffarmIdx nfReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef nfReq).data.toList
#guard (serveOffarmIdx vaReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef vaReq).data.toList
#guard (serveOffarmIdx vbReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef vbReq).data.toList
#guard (serveOffarmIdx globDemoReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef globDemoReq).data.toList
-- ...the two existing dense arms...
#guard (serveOffarmIdx bulkDemoReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkDemoReq).data.toList
#guard (serveOffarmIdx bulkDemoReqAnyHost).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkDemoReqAnyHost).data.toList
#guard (serveOffarmIdx bulkHeadReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkHeadReq).data.toList
#guard (serveOffarmIdx healthReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef healthReq).data.toList
-- ...and the honest fallbacks (transform arms, redirect, static, cgi-shape, POST).
#guard (serveOffarmIdx nfGzipReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef nfGzipReq).data.toList
#guard (serveOffarmIdx bulkGzipReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef bulkGzipReq).data.toList
#guard (serveOffarmIdx oldReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef oldReq).data.toList
#guard (serveOffarmIdx staticReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef staticReq).data.toList
#guard (serveOffarmIdx echoPostReq).data.toList
        == (Datapath.ServeFlatFull.deployedServeRef echoPostReq).data.toList
-- The dense answers genuinely carry their bodies (404 stays small; the vhost and
-- glob answers are 200s with their constant bodies; bulk stays 1 MiB).
#guard (serveOffarmIdx nfReq).size < 1024
#guard (serveOffarmIdx bulkDemoReq).size > 1048576

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms parseArr_dispatch
#print axioms notFoundArm_eq
#print axioms vhostAArm_eq
#print axioms vhostBArm_eq
#print axioms globArm_eq
#print axioms serveOffarmIdx_refines

end Datapath.ServeOffarmIdx
