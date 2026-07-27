/-
# Proto.RateDeployedProven — the DEPLOYED rate-limit `429` SERVED end-to-end (ledger mw.6)

PROVE-WHAT-RUNS for the deployed token-bucket refusal. `Reactor.Stage.Rate.rateStage` (a
CONFIGURED per-connection burst limit, `defaultBurstCap = 512` by default) is
WIRED into the deployed HTTP/1.1 metered fold
`Reactor.Deploy.deployStagesFull2` (stage 4), and the running dataplane threads the
per-connection request sequence into that fold via `Reactor.Deploy.servePipelineFull2Metered`
(the `drorb_serve_metered` ABI, `seq` under the `rate-seq` attr). A connection that has
already spent its burst (`defaultBurstCap` requests, no elapsed clock) has an empty bucket, so the REAL `Rate.tryAdmit` rejects
and the gate answers `429`.

The PRIOR deployed evidence (`RetryAfterProven`) was only MEMBERSHIP (`rateStage ∈
deployStagesFull2`) + the refusal SHAPE (`resp429.status = 429`). This file closes the honest
gap: the ASSEMBLED fourteen-stage fold — every prefix gate (`jwtAdminStage`, `basicStage`,
`ipfilterStage`) genuinely PASSING — BUILDS status `429` for an over-limit connection,
through the whole status-stable response onion. Same bar the JWT gate already met
(`Reactor.Deploy.servePipelineFull2_admin_status_401`).

The CURL that anchors this file — a burst of `> burst-cap` requests on ONE keep-alive
connection to the running dataplane; the first `burst-cap` answer `200`, the rest `429`:

    $ ( for i in $(seq 1 12); do printf 'GET / HTTP/1.1\r\nHost: x\r\nConnection: keep-alive\r\n\r\n'; done ) \
        | nc 127.0.0.1 8099 | grep -c '429 Too Many Requests'
    4

Theorems (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound}):
  * `deployed_rate_429` — parametric: for ANY ctx whose request is neither `/admin` nor
    `/private` (the JWT + Basic gates pass), whose client is admitted (the IP-filter gate
    passes), and whose reconstructed bucket is over the limit, the built deployStagesFull2
    response has status `429`.
  * `throttled_serves_429` — the concrete non-vacuous witness: a real `GET /` from an
    admitted loopback peer whose connection has already spent its burst is SERVED
    `429` through the whole deployed fold.
  * `metered_rate_429` — tied to the deployed metered serve FUNCTION: supplying an admitted
    peer and a per-connection sequence of `defaultBurstCap` (the `rate-seq` attr the accept path
    stashes) builds the `429`, for any request bytes parsing to a non-admin/non-private
    target.
-/

import Reactor.Deploy
import Reactor.BraidCalculus

namespace Proto.RateDeployedProven

open Reactor.Pipeline (Ctx Stage StageStep runPipeline)
open Reactor.Deploy
  (deployStagesFull2 appHandler jwtAdminStage jwtAdminStage_pass isAdminPath
   deployStagesFull2_statusStable)
open Reactor.Stage.Rate
  (rateStage resp429 admits rateStage_onReq_respond seqKey defaultBurstCap)
open Reactor.Stage.IpFilter
  (ipfilterStage forbidden403 deployAdmits ctxAddr cleanClient clientIpKey encodeAddr decodeAddr
   decode_encode_clean deployAdmits_clean)
open Reactor.BraidCalculus (Transparent braid_gate cons_transparent nil_transparent)

/-- The IP-filter gate PASSES (`.continue`) on an ADMITTED client address — the admitted-arm
analogue of `Reactor.Deploy.ipfilterStage_pass'` for a ctx that DOES carry an accept peer
(the deployed metered path). Proven inline from the gate's definition. -/
theorem ipfilterStage_pass_clean {c : Ctx} (h : deployAdmits (ctxAddr c) = true) :
    ipfilterStage.onRequest c = .continue c := by
  show (match deployAdmits (ctxAddr c) with
        | true  => StageStep.continue c
        | false => StageStep.respond forbidden403) = _
  rw [h]

/-- The response-transform TAIL of `deployStagesFull2` after the rate gate (stages 5..14).
Every member is status-stable. Written out so the gate decomposition
`deployStagesFull2 = [jwt, basic, ipfilter] ++ rate :: rateTail` is `rfl`. -/
def rateTail : List Stage :=
  [ Reactor.Deploy.cacheEmptyStage
  , Reactor.Stage.Redirect.redirectStage
  , Reactor.Deploy.traversalStage
  , Reactor.Deploy.policyStage
  , Reactor.Deploy.headerRewriteStage
  , Reactor.Deploy.deployCorsStage
  , Reactor.Stage.Gzip.gzipStage
  , Reactor.Stage.HtmlRewrite.htmlrewriteStage
  , Reactor.Stage.SecurityHeaders.securityheadersStage
  , Reactor.Stage.Header.headerStage ]

/-- `deployStagesFull2` factors as the three passing prefix gates, the rate gate, and the
response-transform tail — definitionally. -/
theorem deployStagesFull2_rate_split :
    deployStagesFull2
      = [jwtAdminStage, Reactor.Stage.BasicAuth.basicStage, Reactor.Stage.IpFilter.ipfilterStage]
          ++ rateStage :: rateTail :=
  rfl

/-- Every tail stage is status-stable (each is a member of `deployStagesFull2`). -/
theorem rateTail_statusStable : ∀ t ∈ rateTail, Stage.statusStable t := by
  intro t ht
  exact deployStagesFull2_statusStable t
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht))))

/-- **`deployed_rate_429` — the deployed fold serves `429` over the limit.** For any ctx
whose request is neither `/admin` (JWT passes) nor `/private` (Basic passes), whose client is
admitted (IP-filter passes), and whose reconstructed token bucket is empty (`admits c =
false`), the fully assembled `deployStagesFull2` response has status exactly `429`: the three
prefix gates fire `.continue` (transparent — their `onResponse` is the identity), the rate
gate short-circuits with `resp429`, and that `429` survives the ten status-stable response
transforms. -/
theorem deployed_rate_429 (c : Ctx)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hadmit : deployAdmits (ctxAddr c) = true)
    (hover : admits c = false) :
    ((runPipeline deployStagesFull2 appHandler c).build).status = 429 := by
  have hpref : ∀ X ∈ [jwtAdminStage, Reactor.Stage.BasicAuth.basicStage,
      Reactor.Stage.IpFilter.ipfilterStage], Transparent X c :=
    cons_transparent ⟨jwtAdminStage_pass c hadmin, fun _ => rfl⟩
      (cons_transparent ⟨Reactor.Stage.BasicAuth.basicStage_pass c hpriv, fun _ => rfl⟩
        (cons_transparent ⟨ipfilterStage_pass_clean hadmit, fun _ => rfl⟩
          (nil_transparent c)))
  have h := braid_gate [jwtAdminStage, Reactor.Stage.BasicAuth.basicStage,
      Reactor.Stage.IpFilter.ipfilterStage] rateStage rateTail appHandler c resp429
    hpref (rateStage_onReq_respond c hover) rateTail_statusStable
  exact h.trans rfl

/-! ## The concrete, non-vacuous witness -/

/-- A real `GET /` request — neither `/admin` nor `/private`. -/
def demoGetReq : Proto.Request :=
  { method := [71, 69, 84], target := [47] }

/-- Its deployed serve context: an admitted loopback peer under `client.ip`, and a
per-connection sequence of `defaultBurstCap` already-served requests under `rate-seq` (the empty
bucket) — exactly the two accept-path attributes the metered fold reads. -/
def throttledCtx : Ctx :=
  { input := [], req := demoGetReq,
    attrs := [ (clientIpKey, encodeAddr cleanClient)
             , (seqKey, Reactor.Stage.ConnLimit.encodeCap defaultBurstCap) ] }

/-- The witness peer IS admitted by the deployed admission decision (loopback, outside the
deny CIDR). -/
theorem throttledCtx_admitted : deployAdmits (ctxAddr throttledCtx) = true := by
  have : ctxAddr throttledCtx = cleanClient := by
    show decodeAddr (encodeAddr cleanClient) = cleanClient
    exact decode_encode_clean
  rw [this]; exact deployAdmits_clean

/-- The witness connection's bucket is over the limit — the REAL `Rate.tryAdmit` rejects. -/
theorem throttledCtx_over : admits throttledCtx = false := by decide

/-- **`throttled_serves_429` — non-vacuous.** The concrete `GET /` from an admitted peer
whose connection has already spent its burst is served `429` through the entire
deployed fourteen-stage fold. -/
theorem throttled_serves_429 :
    ((runPipeline deployStagesFull2 appHandler throttledCtx).build).status = 429 :=
  deployed_rate_429 throttledCtx (by decide) (by decide)
    throttledCtx_admitted throttledCtx_over

/-! ## Tied to the deployed metered serve function -/

/-- **`metered_rate_429` — the deployed metered serve builds the `429`.** The running
dataplane serves via `servePipelineFull2Metered peer seq input`, folding `deployStagesFull2`
over `ctxOfMetered peer seq input` (per-connection sequence stashed under `rate-seq` as a
positional word). For an admitted peer and a sequence of `defaultBurstCap` (the bucket empty)
and request bytes parsing to a non-admin/non-private target, the built metered response has
status `429` — the deployed rate gate firing on the real per-connection sequence. -/
theorem metered_rate_429 (input : Proto.Bytes)
    (hadmin : isAdminPath
      (Reactor.Deploy.ctxOfMetered (encodeAddr cleanClient) defaultBurstCap input).req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath
      (Reactor.Deploy.ctxOfMetered (encodeAddr cleanClient) defaultBurstCap input).req = false) :
    ((runPipeline deployStagesFull2 appHandler
        (Reactor.Deploy.ctxOfMetered (encodeAddr cleanClient) defaultBurstCap input)).build).status
      = 429 := by
  refine deployed_rate_429 _ hadmin hpriv ?_ ?_
  · show deployAdmits (ctxAddr
      (Reactor.Deploy.ctxOfMetered (encodeAddr cleanClient) defaultBurstCap input)) = true
    have : ctxAddr (Reactor.Deploy.ctxOfMetered (encodeAddr cleanClient) defaultBurstCap input)
        = cleanClient := by
      show decodeAddr (encodeAddr cleanClient) = cleanClient
      exact decode_encode_clean
    rw [this]; exact deployAdmits_clean
  · -- The metered ctx's gate reading is the DEFAULT burst pair against the packed
    -- scalar's two fields (`rateAdmits_ctxOfMetered`), and a connection that has
    -- already spent `defaultBurstCap` requests with no elapsed clock has an empty
    -- bucket — the REAL `Rate.tryAdmit` refuses.
    show admits (Reactor.Deploy.ctxOfMetered (encodeAddr cleanClient)
      defaultBurstCap input) = false
    rw [Reactor.Deploy.rateAdmits_ctxOfMetered]
    decide

#print axioms deployed_rate_429
#print axioms throttled_serves_429
#print axioms metered_rate_429

end Proto.RateDeployedProven
