/-
# Proto.IpFilterDeployedProven — the DEPLOYED IP allow/deny `403` SERVED end-to-end (ledger mw.14)

PROVE-WHAT-RUNS for the deployed IP-filter refusal. `Reactor.Stage.IpFilter.ipfilterStage`
is WIRED into the deployed HTTP/1.1 metered fold `Reactor.Deploy.deployStagesFull2`
(stage 3), and the running dataplane threads the accepted peer address into that fold via
`Reactor.Deploy.servePipelineFull2Metered` (the `drorb_serve_metered` ABI the io_uring /
blocking accept path crosses, peer in scope). A client inside the deployed deny block
`10.0.0.0/8` is refused with a `403` through the REAL deny-precedence admission decision
(`IpFilter.permits` over `deployRuleset`).

The PRIOR deployed evidence (`RetryAfterProven`-style) was only MEMBERSHIP
(`ipfilterStage ∈ deployStagesFull2`) + the refusal SHAPE (`forbidden403.status = 403`).
This file closes the honest gap: the ASSEMBLED fourteen-stage fold — every prefix gate
(`jwtAdminStage`, `basicStage`) genuinely PASSING — BUILDS status `403` for a blocked
peer, through the whole status-stable response onion. This is the same bar the JWT gate
already met (`Reactor.Deploy.servePipelineFull2_admin_status_401`); here it is met for the
IP-filter gate on the metered deployed path.

The CURL that anchors the ADMIT side (a real accepted loopback peer — outside the deny
CIDR — is served normally, so the gate is not fail-closed on real traffic):

    $ curl -s -o /dev/null -w '%{http_code}\n' http://127.0.0.1:8099/
    200

The deny side fires for a source inside `10.0.0.0/8` (the deployed `deployRuleset` deny
block); it is proven here over the real admission machine (a `10.x` source cannot be
curled from an off-net host, so the wire anchor is the admit path + the proof of the deny).

Theorems (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound}):
  * `deployed_ipfilter_403` — parametric: for ANY ctx whose request is neither an `/admin`
    path nor a `/private` path (so the two prefix gates PASS) and whose client address is
    rejected by the deployed admission decision, the built deployStagesFull2 response has
    status `403`.
  * `blocked_serves_403` — the concrete non-vacuous witness: a real `GET /` from
    `10.0.0.0` (inside the deny CIDR) is SERVED `403` through the whole deployed fold.
  * `metered_ipfilter_403` — tied to the deployed metered serve FUNCTION
    (`servePipelineFull2Metered`'s fold, keyed by `ctxOfMetered`): supplying the blocked
    peer under the accept-path `client.ip` attr builds the `403`, for any per-connection
    sequence and any request bytes parsing to a non-admin/non-private target.
-/

import Reactor.Deploy
import Reactor.BraidCalculus

namespace Proto.IpFilterDeployedProven

open Reactor.Pipeline (Ctx Stage runPipeline)
open Reactor.Deploy
  (deployStagesFull2 appHandler jwtAdminStage jwtAdminStage_pass isAdminPath
   deployStagesFull2_statusStable ctxOfMetered)
open Reactor.Stage.IpFilter
  (ipfilterStage forbidden403 deployAdmits ctxAddr blockedClient clientIpKey encodeAddr
   decodeAddr decode_encode_blocked deployAdmits_blocked)
open Reactor.BraidCalculus (Transparent braid_gate cons_transparent nil_transparent)

/-- The response-transform TAIL of `deployStagesFull2` after the IP-filter gate (stages
4..14). Every member is status-stable (`deployStagesFull2_statusStable`). Written out so the
gate decomposition `deployStagesFull2 = [jwt, basic] ++ ipfilter :: ipfilterTail` is `rfl`. -/
def ipfilterTail : List Stage :=
  [ Reactor.Stage.Rate.rateStage
  , Reactor.Deploy.cacheEmptyStage
  , Reactor.Stage.Redirect.redirectStage
  , Reactor.Deploy.traversalStage
  , Reactor.Deploy.policyStage
  , Reactor.Deploy.headerRewriteStage
  , Reactor.Deploy.deployCorsStage
  , Reactor.Stage.Gzip.gzipStage
  , Reactor.Stage.HtmlRewrite.htmlrewriteStage
  , Reactor.Stage.SecurityHeaders.securityheadersStage
  , Reactor.Stage.Header.headerStage ]

/-- `deployStagesFull2` factors as the two passing prefix gates, the IP-filter gate, and
the response-transform tail — definitionally. -/
theorem deployStagesFull2_ipfilter_split :
    deployStagesFull2
      = [jwtAdminStage, Reactor.Stage.BasicAuth.basicStage] ++ ipfilterStage :: ipfilterTail :=
  rfl

/-- Every tail stage is status-stable (each is a member of `deployStagesFull2`). -/
theorem ipfilterTail_statusStable : ∀ t ∈ ipfilterTail, Stage.statusStable t := by
  intro t ht
  exact deployStagesFull2_statusStable t
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)))

/-- The IP-filter gate `.respond`s the `403` on a rejected address. -/
theorem ipfilterStage_denies {c : Ctx} (h : deployAdmits (ctxAddr c) = false) :
    ipfilterStage.onRequest c = .respond forbidden403 := by
  simp only [ipfilterStage, h]

/-- **`deployed_ipfilter_403` — the deployed fold serves `403` for a rejected peer.**
For any ctx whose request is neither `/admin` (JWT gate passes) nor `/private` (Basic gate
passes) and whose client address the deployed admission decision REJECTS, the fully
assembled `deployStagesFull2` response has status exactly `403`: the two prefix gates fire
`.continue` (transparent — their `onResponse` is the identity), the IP-filter gate
short-circuits with `forbidden403`, and that `403` survives the eleven status-stable
response transforms. -/
theorem deployed_ipfilter_403 (c : Ctx)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hdeny : deployAdmits (ctxAddr c) = false) :
    ((runPipeline deployStagesFull2 appHandler c).build).status = 403 := by
  have hpref : ∀ X ∈ [jwtAdminStage, Reactor.Stage.BasicAuth.basicStage], Transparent X c :=
    cons_transparent ⟨jwtAdminStage_pass c hadmin, fun _ => rfl⟩
      (cons_transparent ⟨Reactor.Stage.BasicAuth.basicStage_pass c hpriv, fun _ => rfl⟩
        (nil_transparent c))
  have h := braid_gate [jwtAdminStage, Reactor.Stage.BasicAuth.basicStage] ipfilterStage
    ipfilterTail appHandler c forbidden403 hpref (ipfilterStage_denies hdeny)
    ipfilterTail_statusStable
  exact h.trans rfl

/-! ## The concrete, non-vacuous witness -/

/-- A real `GET /` request — neither an `/admin` nor a `/private` target, so both prefix
gates pass. -/
def demoGetReq : Proto.Request :=
  { method := [71, 69, 84], target := [47] }

/-- Its deployed serve context, carrying the blocked peer under the accept-path
`client.ip` attribute exactly as the metered accept path stashes it. -/
def blockedGetCtx : Ctx :=
  { input := [], req := demoGetReq, attrs := [(clientIpKey, encodeAddr blockedClient)] }

/-- The witness client address IS rejected by the deployed admission decision — the REAL
`10.0.0.0/8` deny-precedence path, on the address decoded from the stashed accept bytes. -/
theorem blockedGetCtx_denied : deployAdmits (ctxAddr blockedGetCtx) = false := by
  have : ctxAddr blockedGetCtx = blockedClient := by
    show decodeAddr (encodeAddr blockedClient) = blockedClient
    exact decode_encode_blocked
  rw [this]; exact deployAdmits_blocked

/-- **`blocked_serves_403` — non-vacuous.** The concrete `GET /` from `10.0.0.0` is served
`403` through the entire deployed fourteen-stage fold. -/
theorem blocked_serves_403 :
    ((runPipeline deployStagesFull2 appHandler blockedGetCtx).build).status = 403 :=
  deployed_ipfilter_403 blockedGetCtx (by decide) (by decide) blockedGetCtx_denied

/-! ## Tied to the deployed metered serve function -/

/-- **`metered_ipfilter_403` — the deployed metered serve builds the `403`.** The running
dataplane serves via `servePipelineFull2Metered peer seq input`, which folds
`deployStagesFull2` over `ctxOfMetered peer seq input` (peer stashed under `client.ip`,
per-connection sequence under `rate-seq`). For a peer inside the deny CIDR (`encodeAddr
blockedClient`) and request bytes parsing to a non-admin/non-private target, the built
metered response has status `403` — the deployed IP-filter gate firing on the real accept
peer, for ANY per-connection sequence and ANY such request. -/
theorem metered_ipfilter_403 (input : Proto.Bytes) (connSeq : Nat)
    (hadmin : isAdminPath (ctxOfMetered (encodeAddr blockedClient) connSeq input).req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath
              (ctxOfMetered (encodeAddr blockedClient) connSeq input).req = false) :
    ((runPipeline deployStagesFull2 appHandler
        (ctxOfMetered (encodeAddr blockedClient) connSeq input)).build).status = 403 := by
  refine deployed_ipfilter_403 _ hadmin hpriv ?_
  show deployAdmits (ctxAddr (ctxOfMetered (encodeAddr blockedClient) connSeq input)) = false
  have : ctxAddr (ctxOfMetered (encodeAddr blockedClient) connSeq input) = blockedClient := by
    show decodeAddr (encodeAddr blockedClient) = blockedClient
    exact decode_encode_blocked
  rw [this]; exact deployAdmits_blocked

#print axioms deployed_ipfilter_403
#print axioms blocked_serves_403
#print axioms metered_ipfilter_403

end Proto.IpFilterDeployedProven
