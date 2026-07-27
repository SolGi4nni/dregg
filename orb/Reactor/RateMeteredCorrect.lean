import Reactor.Deploy

/-!
# Reactor.RateMeteredCorrect — the DEPLOYED metered rate gate returns `429`

The deployed dataplane hot path is `drorb_serve_metered`
(`Reactor.Deploy.servePipelineFull2Metered`), whose whole decision is the
fourteen-stage `Reactor.Deploy.deployStagesFull2` fold run over
`Reactor.Deploy.ctxOfMetered clientIp connSeq input` — the context carrying the
accept peer address (under `IpFilter.clientIpKey`) and the per-connection request
index (under `Rate.seqKey`).

`Reactor.Deploy.full2_admin_status_401` already proves the JWT gate (position 1)
fires `401` through this exact fold. The token-bucket rate gate
(`Reactor.Stage.Rate.rateStage`, position 4) had strong theorems
only over a *generic* `rateStage :: rest` pipeline — never over the real
`deployStagesFull2` fold the deployed metered serve runs. This module closes that:
it proves that on an over-limit request that clears the three preceding gates
(JWT off `/admin`, basic-auth off `/private`, IP-filter admits), the built response
of the WHOLE deployed fold has status `429`, the short-circuit carried through the
status-stable inner response onion (positions 5–14). No behaviour change — a pure
proof of the path `drorb_serve_metered` already runs.
-/

namespace Reactor.RateMeteredCorrect

open Reactor.Deploy
open Reactor.Pipeline (Ctx Stage StageStep runPipeline pipeline_stage_effect pipeline_gate_status)

/-- The ten stages after the rate gate in `deployStagesFull2` (positions 5–14):
cache, redirect, traversal, policy, the deploy header rewrite, CORS, gzip, the
markup rewrite, the security-header set, and the hop-strip/`Server` stage. This is
the response onion the `429` short-circuit is threaded through. -/
def full2AfterRate : List Stage :=
  [ cacheEmptyStage
  , Reactor.Stage.Redirect.redirectStage
  , traversalStage
  , policyStage
  , headerRewriteStage
  , deployCorsStage
  , Reactor.Stage.Gzip.gzipStage
  , Reactor.Stage.HtmlRewrite.htmlrewriteStage
  , Reactor.Stage.SecurityHeaders.securityheadersStage
  , Reactor.Stage.Header.headerStage ]

/-- `deployStagesFull2` is the three passing gates, then the rate gate, then the
inner response onion. -/
theorem deployStagesFull2_eq_rate :
    deployStagesFull2 = jwtAdminStage :: Reactor.Stage.BasicAuth.basicStage
      :: Reactor.Stage.IpFilter.ipfilterStage :: Reactor.Stage.Rate.rateStage
      :: full2AfterRate := rfl

/-- Every stage after the rate gate is in `deployStagesFull2`. -/
theorem full2AfterRate_sub : ∀ s ∈ full2AfterRate, s ∈ deployStagesFull2 := by
  intro s hs
  rw [deployStagesFull2_eq_rate]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs)))

/-- Every stage after the rate gate is status-stable (from
`deployStagesFull2_statusStable`), so threading the `429` through them adds headers
/ rewrites the body only — the status stays `429`. -/
theorem full2AfterRate_statusStable : ∀ s ∈ full2AfterRate, Stage.statusStable s :=
  fun s hs => deployStagesFull2_statusStable s (full2AfterRate_sub s hs)

/-- **The deployed metered rate gate fires `429` through the full fold.** For any
context that clears the JWT gate (off `/admin`), the basic-auth gate (off
`/private`), and the IP-filter (its client address is admitted), and that the REAL
token bucket rejects (`Rate.admits c = false`), the built response of the WHOLE
`deployStagesFull2` fold — the exact fold `drorb_serve_metered` runs — has status
`429`. The three preceding gates pass (`onResponse` identity, so the status peels
through them); the rate gate short-circuits; the inner onion (positions 5–14) is
status-stable so the `429` is preserved to the built response. -/
theorem full2_rate_gate_status (c : Ctx)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hip : Reactor.Stage.IpFilter.deployAdmits (Reactor.Stage.IpFilter.ctxAddr c) = true)
    (hover : Reactor.Stage.Rate.admits c = false) :
    ((runPipeline deployStagesFull2 appHandler c).build).status = 429 := by
  have hipc : Reactor.Stage.IpFilter.ipfilterStage.onRequest c = StageStep.continue c := by
    show (match Reactor.Stage.IpFilter.deployAdmits (Reactor.Stage.IpFilter.ctxAddr c) with
          | true  => StageStep.continue c
          | false => StageStep.respond Reactor.Stage.IpFilter.forbidden403) = _
    rw [hip]
  have hrate : Reactor.Stage.Rate.rateStage.onRequest c
      = StageStep.respond Reactor.Stage.Rate.resp429 :=
    Reactor.Stage.Rate.rateStage_onReq_respond c hover
  rw [deployStagesFull2_eq_rate,
      pipeline_stage_effect jwtAdminStage _ appHandler c c (jwtAdminStage_pass c hadmin),
      jwtAdminStage_statusStable c _,
      pipeline_stage_effect Reactor.Stage.BasicAuth.basicStage _ appHandler c c
        (Reactor.Stage.BasicAuth.basicStage_pass c hpriv),
      basicStage_statusStable c _,
      pipeline_stage_effect Reactor.Stage.IpFilter.ipfilterStage _ appHandler c c hipc,
      ipfilterStage_statusStable c _]
  exact (pipeline_gate_status Reactor.Stage.Rate.rateStage full2AfterRate appHandler c
    Reactor.Stage.Rate.resp429 hrate full2AfterRate_statusStable).trans
    Reactor.Stage.Rate.resp429_status

/-! ## The deployed metered serve — a clean accept peer, over the rate limit -/

/-- The accept-peer bytes for a clean (loopback `127.0.0.0`) client — the kind of
peer the dataplane actually accepts, encoded exactly as the metered accept path
stashes it under `IpFilter.clientIpKey`. -/
def cleanIp : Proto.Bytes :=
  Reactor.Stage.IpFilter.encodeAddr Reactor.Stage.IpFilter.cleanClient

/-- **The deployed metered serve emits `429` on an over-limit connection.** For a
clean accept peer whose connection has already spent its DEFAULT burst
(`Rate.defaultBurstCap` = 512 requests on one connection)
(so the token bucket is empty), the built response of the deployed metered fold
(`deployStagesFull2` over `ctxOfMetered cleanIp defaultBurstCap input` — the value
`drorb_serve_metered` runs) has status `429`, provided the request is not an
`/admin` (JWT) or `/private` (basic-auth) surface. The IP-admit and over-limit
facts are discharged by the kernel (they read only the metered attribute bag). -/
theorem servePipelineFull2Metered_over_429 (input : Proto.Bytes)
    (hadmin : isAdminPath (ctxOfMetered cleanIp Reactor.Stage.Rate.defaultBurstCap input).req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath
      (ctxOfMetered cleanIp Reactor.Stage.Rate.defaultBurstCap input).req = false) :
    ((runPipeline deployStagesFull2 appHandler
        (ctxOfMetered cleanIp Reactor.Stage.Rate.defaultBurstCap input)).build).status = 429 :=
  full2_rate_gate_status _ hadmin hpriv (by rfl)
    (by rw [rateAdmits_ctxOfMetered]; decide)

/-- **A concrete non-vacuous witness on the deployed metered context.** With the
empty request (a valid deployed dispatch — target `/`, not `/admin`/`/private`), a
clean accept peer, and the connection over the rate cap, the deployed metered fold
serves `429`. -/
theorem servePipelineFull2Metered_empty_over_429 :
    ((runPipeline deployStagesFull2 appHandler
        (ctxOfMetered cleanIp Reactor.Stage.Rate.defaultBurstCap [])).build).status = 429 :=
  servePipelineFull2Metered_over_429 [] (by decide) (by decide)

/-! ## ★ THE PER-CONNECTION BURST GATE FIRES AT THE **CONFIGURED** POINT

The theorems above are stated over the DEFAULT burst parameters, because the plain
metered context carries no configured ones. These are the restatements over the
OPERATOR'S values — the DoS-metered context (`Reactor.Deploy.ctxOfMeteredConn`) carries
`burst-cap` and `burst-refill` through the shared attribute-bag word codec, and the
deployed fold's per-connection token bucket decides on THOSE.

This is what the retired module constants `rateCap := 8` / `rateRate := 1` could not
say: there was no configured value to state a theorem over. `knob_moves_the_gate_metered`
below exhibits ONE connection depletion at which two different configured capacities
disagree on the DEPLOYED context, so the decision provably follows the configuration and
not a literal. -/

/-- **The deployed fold serves `429` at the CONFIGURED burst point.** For a request that
clears the JWT, basic-auth and IP gates, on a connection whose standing request count has
reached the operator's `burst-cap` with no elapsed clock to refill it, the built response
of the whole `deployStagesFull2` fold over the DoS-metered context has status `429`.
Stated over an ARBITRARY live capacity and refill rate (any pair the host can cross), so
the refusal point is the CONFIGURED one. -/
theorem burstCap_fires_metered (clientIp : Proto.Bytes)
    (connSeq active span cap rateCount rateLimit burstCap burstRate : Nat)
    (input : Proto.Bytes)
    (hadmin : isAdminPath (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input).req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input).req = false)
    (hip : Reactor.Stage.IpFilter.deployAdmits
      (Reactor.Stage.IpFilter.ctxAddr (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)) = true)
    (hbc : burstCap < 2 ^ 64) (hbr : burstRate < 2 ^ 64) (hpos : 0 < burstCap)
    (hclock : Reactor.Stage.Rate.clockOfPacked connSeq = 0)
    (hover : burstCap <= Reactor.Stage.Rate.countOfPacked connSeq) :
    ((runPipeline deployStagesFull2 appHandler (ctxOfMeteredConn clientIp connSeq active span cap rateCount rateLimit burstCap burstRate input)).build).status = 429 :=
  full2_rate_gate_status _ hadmin hpriv hip (by
    rw [Reactor.Deploy.rateAdmits_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ hbc hbr, hclock]
    exact Reactor.Stage.Rate.admitsAt_saturates_at_zero _ _ hpos hover)

/-- **A browser-shaped burst is ADMITTED by the deployed gate under the DEFAULTS.**
Fifty requests already served on ONE keep-alive/HTTP-2 connection — one page load — with
no elapsed clock: the deployed per-connection gate passes it. This is the case a default
drorb answered `429` to at request NINE. -/
theorem browserBurst_admitted_metered (clientIp : Proto.Bytes)
    (active span cap rateCount rateLimit : Nat) (input : Proto.Bytes) :
    Reactor.Stage.Rate.admits
        (ctxOfMeteredConn clientIp 50 active span cap rateCount rateLimit
          Reactor.Stage.Rate.defaultBurstCap Reactor.Stage.Rate.defaultBurstRate input)
      = true := by
  rw [Reactor.Deploy.rateAdmits_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  decide

/-- …and the gate is therefore TRANSPARENT on that burst: the fold with the rate stage in
front of any tail emits exactly the tail's bytes. The browser burst is not merely "not
refused" — the stage contributes nothing to the response. -/
theorem browserBurst_passes_metered (rest : List Stage) (h : Ctx -> Response)
    (clientIp : Proto.Bytes) (active span cap rateCount rateLimit : Nat)
    (input : Proto.Bytes) :
    runPipeline (Reactor.Stage.Rate.rateStage :: rest) h
        (ctxOfMeteredConn clientIp 50 active span cap rateCount rateLimit
          Reactor.Stage.Rate.defaultBurstCap Reactor.Stage.Rate.defaultBurstRate input)
      = runPipeline rest h
        (ctxOfMeteredConn clientIp 50 active span cap rateCount rateLimit
          Reactor.Stage.Rate.defaultBurstCap Reactor.Stage.Rate.defaultBurstRate input) :=
  Reactor.Stage.Rate.rateStage_pass rest h _
    (browserBurst_admitted_metered clientIp active span cap rateCount rateLimit input)

/-- **★ THE KNOB MOVES THE DEPLOYED GATE.** At the SAME eight requests already served on
one connection and the SAME zero elapsed clock, the DEPLOYED context under a configured
`burst-cap` of `8` is REFUSED and under `16` is ADMITTED. Under the retired hardcoded `8`
both were refused, and no directive could change that — this pair is the bug, closed. -/
theorem knob_moves_the_gate_metered (clientIp : Proto.Bytes)
    (active span cap rateCount rateLimit : Nat) (input : Proto.Bytes) :
    Reactor.Stage.Rate.admits
        (ctxOfMeteredConn clientIp 8 active span cap rateCount rateLimit 8 1 input) = false
    /\ Reactor.Stage.Rate.admits
        (ctxOfMeteredConn clientIp 8 active span cap rateCount rateLimit 16 1 input) = true := by
  constructor
  · rw [Reactor.Deploy.rateAdmits_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _
      (by decide) (by decide)]
    decide
  · rw [Reactor.Deploy.rateAdmits_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _
      (by decide) (by decide)]
    decide

/-- **A configured `burst-cap 0` DISABLES the deployed gate** — the reading
`max-connections 0` and `rate-limit 0` already have. Even a connection a million requests
deep is admitted. -/
theorem knob_zero_disables_metered (clientIp : Proto.Bytes)
    (active span cap rateCount rateLimit : Nat) (input : Proto.Bytes) :
    Reactor.Stage.Rate.admits
        (ctxOfMeteredConn clientIp 1000000 active span cap rateCount rateLimit 0 0 input)
      = true := by
  rw [Reactor.Deploy.rateAdmits_ctxOfMeteredConn _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  decide

#print axioms burstCap_fires_metered
#print axioms browserBurst_admitted_metered
#print axioms browserBurst_passes_metered
#print axioms knob_moves_the_gate_metered
#print axioms knob_zero_disables_metered

#print axioms full2_rate_gate_status
#print axioms servePipelineFull2Metered_over_429
#print axioms servePipelineFull2Metered_empty_over_429

end Reactor.RateMeteredCorrect
