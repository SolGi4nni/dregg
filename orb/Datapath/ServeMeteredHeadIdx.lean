import Datapath.ServeHeadIdx
import Reactor.ServeConformant

/-!
# Datapath.ServeMeteredHeadIdx — the METERED serve with an index-native arm decision

The deployed METERED default (`drorb_serve_metered_dense_conformant` and the
empty-config divert of `drorb_serve_metered_cfg_conformant`) decides its dense
`/bulk` arm by `Reactor.Deploy.BulkArmMetered` — a decidable `Prop` whose every
conjunct evaluates over `ctxOf input.toList` / `ctxOfMetered peer seq input.toList`:
the whole request head is `List`-parsed (twice: once for `BulkArm`, once to build
the metered ctx the two gate conjuncts read), and a `List.replicate` of zero bytes
is consed just so the rate gate can take its `length`. The non-metered default already
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


/-- **The rate gate on the packed sequence scalar directly.** The real time-based
token-bucket decision (`Reactor.Stage.Rate.admitsAt`, the proven `Rate.refill` /
`Rate.tryAdmit` transition) with no attr-bag lookup at all. The host packs the
per-connection request count into the low 32 bits (`countOfPacked`) and the monotonic
elapsed-seconds clock into the high bits (`clockOfPacked`); the bucket starts with
`cap - count` standing tokens and is refilled to the clock, so an over-limit
connection recovers as time advances.

This is the DEFAULT-configuration decision, and deliberately so: it decides the dense
`/bulk` arm, which is keyed on `ctxOfMetered` — the context that carries no configured
burst parameters and therefore reads `defaultBurstCap` / `defaultBurstRate`
(`rate_admits_metered` below is the equality that makes that exact). The
operator-configured burst parameters ride the DoS-metered context
(`Reactor.Deploy.ctxOfMeteredConn`) and are decided by the same `admitsAt` there
(`Reactor.Deploy.rateAdmits_ctxOfMeteredConn`). -/
def rateGateB (seq : Nat) : Bool :=
  Reactor.Stage.Rate.admitsAt Reactor.Stage.Rate.defaultBurstCap
    Reactor.Stage.Rate.defaultBurstRate
    (Reactor.Stage.Rate.countOfPacked seq)
    (Reactor.Stage.Rate.clockOfPacked seq)

/-- The metered ctx's decided address IS the decoded peer: `ctxOfMetered` stashes
the peer under `clientIpKey` at the head of the attr bag. -/
theorem ctxAddr_metered (peer : Bytes) (seq : Nat) (input : Bytes) :
    Reactor.Stage.IpFilter.ctxAddr (ctxOfMetered peer seq input)
      = Reactor.Stage.IpFilter.decodeAddr peer := rfl


/-- The metered ctx's standing request count is EXACTLY the packed low field. The
reading is a positional eight-byte word in the shared attribute-bag codec, not the
unary byte-run it used to be, so the count needs no clamp: the packed low field is
under `2^32` and the word round-trips it exactly at every count
(`Reactor.Stage.Rate.countOfPacked_lt64`). -/
theorem seqOf_metered (peer : Bytes) (seq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.seqOf (ctxOfMetered peer seq input)
      = Reactor.Stage.Rate.countOfPacked seq :=
  Reactor.Deploy.seqOf_ctxOfMetered peer seq input

/-- The metered ctx's standing clock is the packed high field CLAMPED at the default
burst capacity, so the positional word is exact for every clock a long-lived
connection can reach. The clamp is INERT
(`Reactor.Stage.Rate.admitsAt_clock_clamp`): once the elapsed time would credit a full
capacity there is nothing further to credit. -/
theorem clockOf_metered (peer : Bytes) (seq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.clockOf (ctxOfMetered peer seq input)
      = min (Reactor.Stage.Rate.clockOfPacked seq) Reactor.Stage.Rate.defaultBurstCap :=
  Reactor.Deploy.clockOf_ctxOfMetered peer seq input

/-- The metered ctx carries NO configured burst capacity, so the gate reads the
DEFAULT — the no-regression fact the dense arm relies on. -/
theorem burstCapOf_metered (peer : Bytes) (seq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.burstCapOf (ctxOfMetered peer seq input)
      = Reactor.Stage.Rate.defaultBurstCap :=
  Reactor.Deploy.burstCapOf_ctxOfMetered peer seq input

/-- The metered ctx carries NO configured refill rate, so the gate reads the DEFAULT. -/
theorem burstRateOf_metered (peer : Bytes) (seq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.burstRateOf (ctxOfMetered peer seq input)
      = Reactor.Stage.Rate.defaultBurstRate :=
  Reactor.Deploy.burstRateOf_ctxOfMetered peer seq input

/-! ## 1a. Clock-clamp inertness — the theorem that JUSTIFIES the stored reading

The metered ctx stores both per-connection readings as POSITIONAL eight-byte words in
the ONE shared attribute-bag codec. The COUNT needs no clamp (the packed low field is
under `2^32`). The CLOCK is unbounded in the packed high field, so it is stored
clamped at the capacity — and that clamp is made a REAL THEOREM rather than left to a
test: once the elapsed time would credit a full capacity there is nothing further to
credit, so the clamped reading and the raw one decide identically, for every capacity,
refill rate and count (`Reactor.Stage.Rate.admitsAt_clock_clamp`).

This replaces the old count-cap inertness lemma, whose purpose was to justify an
`O(cap)` UNARY allocation of the count. That allocation is gone: the count is eight
bytes at every value, so there is no count cap left to justify. -/

/-- **CLOCK-CLAMP INERTNESS on the deployed scalar gate.** Clamping the packed
elapsed-seconds clock at the burst capacity changes NO verdict, for EVERY packed
scalar — so the reading the metered ctx stores decides exactly as the raw one. -/
theorem rateGateB_clock_clamp (seq : Nat) :
    Reactor.Stage.Rate.admitsAt Reactor.Stage.Rate.defaultBurstCap
      Reactor.Stage.Rate.defaultBurstRate
      (Reactor.Stage.Rate.countOfPacked seq)
      (min (Reactor.Stage.Rate.clockOfPacked seq) Reactor.Stage.Rate.defaultBurstCap)
      = rateGateB seq :=
  Reactor.Stage.Rate.admitsAt_clock_clamp _ _ _ _

/-- **The rate gate decides exactly the metered ctx's admission.** The ctx carries no
configured burst parameters, so it reads the DEFAULTS; its count is the packed low
field verbatim and its clock is the packed high field clamped inertly — so the ctx's
verdict is the decision on the raw, unclamped packed scalar, for EVERY `seq`. -/
theorem rate_admits_metered (peer : Bytes) (seq : Nat) (input : Bytes) :
    Reactor.Stage.Rate.admits (ctxOfMetered peer seq input) = rateGateB seq :=
  Reactor.Deploy.rateAdmits_ctxOfMetered peer seq input

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

#guard rateGateB 0 && rateGateB 511
#guard !(rateGateB 512)
-- TIME RECOVERY (impossible at `rateRate = 0`): the exhausted connection (low field 8,
-- clock 0) is refused, but the SAME saturated count with the packed clock advanced by
-- >= 1 second (high field) is ADMITTED again -- the `429 -> wait -> 200` recovery, decided
-- by the REAL `Rate.refill`; the clock rides the LOW-field-preserving high bits.
#guard rateGateB (512 + Reactor.Stage.Rate.packWidth)
#guard rateGateB (512 + 3 * Reactor.Stage.Rate.packWidth)
#guard !(rateGateB 512) && rateGateB (512 + Reactor.Stage.Rate.packWidth)
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
#guard (serveMeteredHeadIdx cleanPeer 512 bulkDemoReq).data.toList
        == (meteredFoldServe cleanPeer 512 bulkDemoReq).data.toList
-- The dense arms genuinely fire: 1 MiB bulk body, tiny health body; the refusals
-- genuinely refuse (no 1 MiB body on the blocked/exhausted paths).
#guard (serveMeteredHeadIdx cleanPeer 0 bulkDemoReq).size > 1048576
#guard (serveMeteredHeadIdx cleanPeer 0 healthReq).size > 2

#guard (serveMeteredHeadIdx blockedPeer 0 bulkDemoReq).size < 1024
#guard (serveMeteredHeadIdx cleanPeer 512 bulkDemoReq).size < 1024
-- SERVE-LEVEL time recovery: the exhausted connection (low field 8, clock 0) refuses the
-- bulk body, but the SAME count with the packed clock advanced one second (512 + 2^32)
-- serves the full 1 MiB body again -- the deployed limiter recovering over time.
#guard (serveMeteredHeadIdx cleanPeer 4294967808 bulkDemoReq).size > 1048576
#guard (serveMeteredHeadIdx cleanPeer 4294967808 bulkDemoReq).data.toList
        == (meteredFoldServe cleanPeer 4294967808 bulkDemoReq).data.toList
-- Clock-clamp inertness genuinely collapses large clocks onto a real decision: an
-- exhausted count with a huge clock and the same count with the clock clamped at the
-- capacity both ADMIT (the recovery), while the same count at clock 0 REFUSES -- so
-- the collapse is not a degenerate always-admit.
#guard rateGateB (512 + 10000 * Reactor.Stage.Rate.packWidth)
        == rateGateB (512 + 512 * Reactor.Stage.Rate.packWidth)
#guard rateGateB (512 + 10000 * Reactor.Stage.Rate.packWidth) && !(rateGateB 512)
-- Below the capacity the count is preserved verbatim and admits.
#guard rateGateB 3 && rateGateB 500 && !(rateGateB 513)

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/


#print axioms seqOf_metered
#print axioms clockOf_metered
#print axioms rateGateB_clock_clamp
#print axioms rate_admits_metered
#print axioms meteredFold_bulk_eq
#print axioms meteredFold_health_eq
#print axioms serveMeteredHeadIdx_eq
#print axioms serveMeteredHeadIdxConformant_eq
#print axioms serveMeteredHeadIdxConformant_head_no_body
#print axioms serveMeteredHeadIdxConformant_rejects_missingHost

end Datapath.ServeMeteredHeadIdx
