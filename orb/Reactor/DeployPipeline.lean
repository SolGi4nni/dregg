import Datapath.DenseStampsPlus8
import Reactor.ServeConformant
import Reactor.Stage.RangeUnveil
import Reactor.Stage.CacheControl
import Reactor.Stage.ModifiedSince
import Reactor.Stage.AssetExpires
import Reactor.Stage.AssetImmutable

/-!
# Reactor.DeployPipeline — the ONE consolidated deployed pipeline

The deployed default serve was assembled by a CHAIN of extension folds spread
across six files: `deployStagesFull2` (base) was wrapped by `deployStagesPlus2`,
then `…Plus4`, `…Plus5`, `…Plus6`, `…Plus8`, each defined as `newEdges ++
priorList` in its own module. The running list was therefore only visible by
mentally unrolling six `::`/`++` splices across six files — the confusing chain
the debt-paydown targets.

This module states that SAME list ONCE, FLAT: `deployPipelineStages` is the full
ordered registry, outermost stage first. Each entry is a fully-qualified
reference to the stage's OWN proof module (it is proven and imported, never
inlined here) — so the pipeline GROWS by adding one line + one import, with no
giant file to recompile and no fold-of-folds to unroll.

## This wave — the range / freshness layer (RFC 9110 §14, RFC 9111 §5)

Two proven stages are appended OUTERMOST of the plus8 onion, closing three RFC
cases the deployed serve still violated, my-hand verified against the running
default serve:

  * `Reactor.Stage.RangeUnveil.rangeUnveilStage` — the two mishandled range
    shapes (multi-range `206`, `If-Range`) unveiled on the handler's full `200`
    (RFC 9110 §13.1.5 / §14.2 — closes K06 multi-range and K08 If-Range non-match).
  * `Reactor.Stage.CacheControl.cacheControlStage` — the origin freshness
    directive `public, max-age=3600` on a cacheable static `200`
    (RFC 9111 §5.2 — closes N01).

### Named residual — the date conditionals (J09 / J11) are NOT deployed here

`Reactor.Stage.DateCondition.dateCondStage` (with `Reactor.Stage.ModifiedSince`'s
`Last-Modified` stamp) closes J09 / J11 (`If-Modified-Since` ⇒ `304`,
`If-Unmodified-Since` ⇒ `412`) at the KERNEL level, and does so on a plain fold.
It is deliberately NOT deployed into this inner pipeline, because
`Reactor.ServeConformant.conformantServe` — the RFC wrapper the host default
crosses — STRIPS `If-None-Match` / `If-Match` from the request before invoking
the inner serve (`stripCondReq`, so its own ETag `conditionalRewrite` is the sole
precondition authority). A date-conditional stage inside the inner fold therefore
CANNOT see a present `If-None-Match` and cannot honour the §13.2.2 precedence
(`If-None-Match` beats `If-Modified-Since`): it would answer `304` for the
J12 shape (`If-None-Match` non-match + far-future `If-Modified-Since`), which MUST
be `200`. My-hand verification (`rfc_conformance_full.py`) confirmed deploying it
here REGRESSES J12. The correct home for the date conditionals is
`conformantServe`'s conditional finisher (`condRewriteBytes` / `conditionalRewrite`),
which sees the un-stripped request and already owns the ETag precedence — a
change in `Reactor.ServeConformant`, out of this lane. J09 / J11 stay open until
then.

## The dense `/bulk` fast path is preserved (the perf lever)

The dense fast path is now taken for the LITERAL `/bulk` datapath shape ALONE
(`newStagesOffB` = `armB8 input && !unveils && !isStaticGet`). A non-`/bulk`
dynamic request (`GET /`, a `404`, `/health`, `/welcome`, …) no longer enters the
dense arm — it flows through the FULL consolidated `List` fold, so every outermost
registry stage runs on it. This is the breadth un-inert: the broad predecessor
condition (`!unveils && !isStaticGet` alone) routed ALL such traffic into the
plus8 fold, structurally barring any outermost stage that is not inert on general
dynamic requests. `newStages_collapse` proves the two range/freshness stages
collapse to the identity under the off-facts (still true on the `/bulk` shape), so
the dense-arm bytes stay byte-identical (`serveMeteredPipelineDenseIdx_eq`), and
the deployed OUTPUT is unchanged — the fold and the fast path agree on `/bulk`.
-/

namespace Reactor.DeployPipeline

open Proto (Bytes)
open Reactor (Response serialize)
open Reactor.Pipeline (Ctx Stage StageStep runPipeline pipeline_cons)
open Reactor.Deploy (appHandler ctxOfMetered ctxOf)
open Reactor.ServeConformant (conformantServe)
open Reactor.DeployPlus8 (deployStagesPlus8 drorbServeMeteredPlus8
  servePipelinePlus8Metered deployRespPlus8Of)
open Datapath.DenseStampsPlus8 (serveMeteredPlus8HeadIdx serveMeteredPlus8HeadIdx_eq armB8)

/-- **THE consolidated deployed pipeline** — the full ordered stage registry the
running default folds, flat in one list, outermost stage first. The two
range/freshness stages of this wave are prepended OUTERMOST; the remaining
forty-three entries are the plus8 onion stated flat (definitionally
`deployStagesPlus8`, so every existing proof about the deployed fold transfers to
the tail via `deployPipelineStages_tail_eq`). -/
def deployPipelineStages : List Stage :=
  -- this wave: range unveil (outermost) → static freshness
  [ Reactor.Stage.RangeUnveil.rangeUnveilStage
  , Reactor.Stage.CacheControl.cacheControlStage
  -- this wave: the static-asset validation / caching completeness stamps
  -- (Last-Modified validator, Expires absolute date, Cache-Control: immutable),
  -- each the identity off the cacheable static surface (so the dense `/bulk`
  -- arm stays byte-identical).
  , Reactor.Stage.ModifiedSince.lmStampStage
  , Reactor.Stage.AssetExpires.assetExpiresStage
  , Reactor.Stage.AssetImmutable.assetImmutableStage
  -- plus8 edges (outermost of the tail): Vary stamp, then the 414 / 406 gates
  , Reactor.DeployPlus8.varyGate8
  , Reactor.Stage.UriTooLong.uriTooLongStage
  , Reactor.Stage.NotAcceptable.naGateStage
  -- plus6 edges: multi-range 206, language stamp, dashboard type, CL/TE guard,
  -- method gate, welcome/dashboard route gates
  , Reactor.Stage.MultiRange.multiRangeStage
  , Reactor.Stage.ContentLanguage.langStampStage
  , Reactor.Stage.Dashboard.dashTypeStage
  , Reactor.Stage.ClTeGuard.clTeGuardStage
  , Reactor.DeployPlus6.methodGate6
  , Reactor.Stage.ContentLanguage.welcomeGateStage
  , Reactor.Stage.Dashboard.dashGateStage
  -- plus5 layer: cookie hardening, session set-cookie, SSE + SPA heads/gates
  , Reactor.Stage.CookieSecure.cookieSecureStage
  , Reactor.Stage.SessionCookie.setCookieStage
  , Reactor.Stage.SseServe.sseHeadStage
  , Reactor.Stage.SpaServe.spaTypeStage
  , Reactor.Stage.SseServe.sseGateStage
  , Reactor.Stage.SpaServe.spaGateStage
  , Reactor.Stage.SessionCookie.sessionGateStage
  -- plus4 layer: Timing-Allow-Origin, Content-Location, Max-Forwards hop gate
  , Reactor.Stage.TimingAllowOrigin.taoStage
  , Reactor.Stage.ContentLocation.contentLocationStage
  , Reactor.Stage.MaxForwards.mfStage
  -- plus2 layer: the nine response-stamp edges
  , Reactor.Stage.AltSvc.altStage
  , Reactor.Stage.PermissionsPolicy.ppStage
  , Reactor.Stage.CrossOriginResource.corpStage
  , Reactor.Stage.Via.viaStage
  , Reactor.Stage.CacheStatus.csStage
  , Reactor.Stage.WarningTransform.warningStage
  , Reactor.Stage.LinkPreload.linkStage
  , Reactor.Stage.ProxyProtocol.proxyProtoStage
  , Reactor.Stage.StaleWhileRevalidate.swrStage
  -- base serve (deployStagesFull2): auth, gates, route, transform, headers
  , Reactor.Deploy.jwtAdminStage
  , Reactor.Stage.BasicAuth.basicStage
  , Reactor.Stage.IpFilter.ipfilterStage
  , Reactor.Stage.Rate.rateStage
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

/-- **The consolidation identity for the tail.** Dropping the five outermost
stages (range unveil, cache-control freshness, and this wave's Last-Modified /
Expires / immutable static-asset stamps), the flat registry tail IS the deployed
`deployStagesPlus8` onion, definitionally. Every proof about the deployed fold
therefore transfers to the tail. -/
theorem deployPipelineStages_tail_eq :
    deployPipelineStages.drop 5 = Reactor.DeployPlus8.deployStagesPlus8 := rfl

/-- The consolidated registry is exactly forty-eight stages (43 plus8 + 5 new:
range unveil, cache-control freshness, Last-Modified, Expires, immutable). -/
theorem deployPipelineStages_length : deployPipelineStages.length = 48 := rfl

/-! ## The consolidated serve (folds the full registry, new stages included) -/

/-- The built response of the consolidated fold on a directly-supplied context. -/
def deployPipelineRespOf (c : Ctx) : Response :=
  (runPipeline deployPipelineStages appHandler c).build

/-- The consolidated metered serve as wire bytes: the flat-registry fold over the
connection-aware peer/seq context the dataplane threads in. -/
def servePipelineMetered (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Bytes :=
  serialize ((runPipeline deployPipelineStages appHandler
    (ctxOfMetered clientIp connSeq input)).build)

/-- The consolidated metered serve at the host ABI (`ByteArray → UInt64 →
ByteArray`). -/
def drorbServePipelineMetered (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  ByteArray.mk (servePipelineMetered peer.toList seq.toNat input.toList).toArray

/-! ## The new-stage collapse — the outermost stamps are the identity off their surface -/

/-- **The dense-arm off-condition — narrowed to the LITERAL `/bulk` dense shape.**
Three conjuncts, each load-bearing:

  * `armB8 input` — the request IS the dense `/bulk` datapath shape (the
    index-native `/bulk`-arm guard). THIS is the narrowing: a non-`/bulk` dynamic
    request (`GET /`, a `404`, `/health`, `/welcome`, …) fails this conjunct and so
    leaves the dense fast path for the FULL consolidated fold — every outermost
    registry stage runs on it. The broad predecessor (`!unveils && !isStaticGet`
    alone) swallowed ALL such traffic into the plus8 fold, structurally barring any
    outermost stage that is not inert on general dynamic requests.
  * `!unveils req` and `!isStaticGet` — the two facts the new-stage collapse needs
    (`newStages_collapse`): the outermost range/freshness stamps are the identity
    exactly here. NOT implied by `armB8`: a `/bulk` request bearing a MALFORMED
    `Range` + `If-Range` parses to `rangesOf = none` (so it passes `OffEdges6`,
    firing `armB8`) yet has `unveils = true`; this conjunct genuinely excludes it,
    so it crosses the full fold and range-unveil fires.

Decided on the parsed request of the raw input (attribute-independent, so it
agrees with the metered context). -/
def newStagesOffB (input : ByteArray) : Bool :=
  armB8 input
    && !Reactor.Stage.RangeUnveil.unveils (ctxOf input.toList).req
    && !Reactor.Stage.CacheControl.isStaticGet (ctxOf input.toList)

/-- **The two new stages collapse to the identity on the fold** when the request
carries no range and is not a static `GET` (and the context has no stashed
range). Each stage passes the request phase and is builder-identical on the
response phase under its off-fact — so the consolidated fold equals the plus8
fold, builder-for-builder. -/
theorem newStages_collapse (c : Ctx)
    (hu : Reactor.Stage.RangeUnveil.unveils c.req = false)
    (hs : Reactor.Stage.CacheControl.isStaticGet c = false)
    (hstash : Reactor.Stage.RangeUnveil.stashOf c = none) :
    runPipeline deployPipelineStages appHandler c
      = runPipeline Reactor.DeployPlus8.deployStagesPlus8 appHandler c := by
  -- generic peel: a stage whose request phase continues on `c` and whose
  -- response phase is `c`-identical drops off the front of the fold.
  have peel : ∀ (s : Stage) (rest : List Stage),
      s.onRequest c = StageStep.continue c → (∀ b, s.onResponse c b = b) →
      runPipeline (s :: rest) appHandler c = runPipeline rest appHandler c := by
    intro s rest hReq hResp
    rw [pipeline_cons, hReq]
    exact hResp _
  -- cacheControl's response phase is builder-identical off the static surface
  have hccResp : ∀ b, Reactor.Stage.CacheControl.cacheControlStage.onResponse c b = b := by
    intro b
    show (if b.acc.status == 200 && Reactor.Stage.CacheControl.isStaticGet c
          then b.addHeader (Reactor.Stage.CacheControl.cacheControlName,
                            Reactor.Stage.CacheControl.cacheControlVal)
          else b) = b
    rw [hs]; simp
  -- the three static-asset stamps of this wave are each the identity off static
  have hlmResp : ∀ b, Reactor.Stage.ModifiedSince.lmStampStage.onResponse c b = b :=
    fun b => Reactor.Stage.ModifiedSince.lmStamp_noop_nonstatic c b hs
  have hexpResp : ∀ b, Reactor.Stage.AssetExpires.assetExpiresStage.onResponse c b = b :=
    fun b => Reactor.Stage.AssetExpires.assetExpiresStage_resp_off_static c b hs
  have himmResp : ∀ b, Reactor.Stage.AssetImmutable.assetImmutableStage.onResponse c b = b :=
    fun b => Reactor.Stage.AssetImmutable.assetImmutableStage_resp_off_static c b hs
  show runPipeline (Reactor.Stage.RangeUnveil.rangeUnveilStage
      :: Reactor.Stage.CacheControl.cacheControlStage
      :: Reactor.Stage.ModifiedSince.lmStampStage
      :: Reactor.Stage.AssetExpires.assetExpiresStage
      :: Reactor.Stage.AssetImmutable.assetImmutableStage
      :: Reactor.DeployPlus8.deployStagesPlus8) appHandler c
    = runPipeline Reactor.DeployPlus8.deployStagesPlus8 appHandler c
  rw [peel _ _ (Reactor.Stage.RangeUnveil.unveil_off_id c hu)
        (fun b => Reactor.Stage.RangeUnveil.unveil_noStash_id c b hstash),
      peel _ _ rfl hccResp,
      peel _ _ rfl hlmResp,
      peel _ _ rfl hexpResp,
      peel _ _ rfl himmResp]

/-- The stashed-range slot of a metered context is empty (its attribute bag holds
only the client IP and rate sequence — never the range-unveil key). -/
theorem stashOf_ctxOfMetered (clientIp : Bytes) (connSeq : Nat) (input : Bytes) :
    Reactor.Stage.RangeUnveil.stashOf (ctxOfMetered clientIp connSeq input) = none := by
  simp [Reactor.Stage.RangeUnveil.stashOf, ctxOfMetered,
        Reactor.Stage.RangeUnveil.ruRangeKey,
        Reactor.Stage.IpFilter.clientIpKey, Reactor.Stage.Rate.seqKey]

/-- **On the dense-arm off-condition, the consolidated fold IS the plus8 fold.**
The two new stages are the identity there (`newStages_collapse`), so their serve
bytes agree — this is the bridge that keeps the dense `/bulk` arm byte-identical. -/
theorem drorbServePipelineMetered_eq_plus8_off (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) (hoff : newStagesOffB input = true) :
    drorbServePipelineMetered peer seq input
      = drorbServeMeteredPlus8 peer seq input := by
  simp only [newStagesOffB, Bool.and_eq_true, Bool.not_eq_true'] at hoff
  obtain ⟨⟨_harm8, hu⟩, hstatic⟩ := hoff
  show ByteArray.mk (servePipelineMetered peer.toList seq.toNat input.toList).toArray
      = ByteArray.mk (servePipelinePlus8Metered peer.toList seq.toNat input.toList).toArray
  have hbuild : (runPipeline deployPipelineStages appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build
      = (runPipeline Reactor.DeployPlus8.deployStagesPlus8 appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build := by
    rw [newStages_collapse (ctxOfMetered peer.toList seq.toNat input.toList)
          hu hstatic
          (stashOf_ctxOfMetered peer.toList seq.toNat input.toList)]
  show ByteArray.mk (serialize ((runPipeline deployPipelineStages appHandler
        (ctxOfMetered peer.toList seq.toNat input.toList)).build)).toArray = _
  rw [hbuild]
  rfl

/-! ## The re-homed deployed default — dense `/bulk` arm, consolidated fold elsewhere -/

/-- **The consolidated dense-arm metered serve.** On the dense-arm off-condition
(no range, not a static GET — the `/bulk` datapath shape) it reuses the plus8
dense assembly verbatim (`serveMeteredPlus8HeadIdx`, which itself fires the dense
`/bulk` bytes or falls to the plus8 fold); on every other shape it is the
consolidated fold, which applies the two new stages. -/
def serveMeteredPipelineDenseIdx (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  if newStagesOffB input then
    serveMeteredPlus8HeadIdx peer seq input
  else
    drorbServePipelineMetered peer seq input

/-- **Byte-identity to the consolidated fold.** For EVERY `(peer, seq, input)` the
dense-arm serve equals the plain consolidated fold `drorbServePipelineMetered`: on
the off-condition the dense assembly is the plus8 fold
(`serveMeteredPlus8HeadIdx_eq`) which is the consolidated fold there
(`drorbServePipelineMetered_eq_plus8_off`); off the condition it IS the fold. -/
theorem serveMeteredPipelineDenseIdx_eq (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    serveMeteredPipelineDenseIdx peer seq input
      = drorbServePipelineMetered peer seq input := by
  unfold serveMeteredPipelineDenseIdx
  cases hoff : newStagesOffB input with
  | false => rw [if_neg Bool.false_ne_true]
  | true =>
    rw [if_pos rfl]
    rw [serveMeteredPlus8HeadIdx_eq,
        ← drorbServePipelineMetered_eq_plus8_off peer seq input hoff]

/-- **The consolidated default metered serve BODY.** The RFC-conformance wrapper
(`conformantServe`) over the consolidated dense-arm serve: the `/bulk` arm emits
the fully-stamped dense head + the dense 1 MiB body with no per-byte `List` cons;
every other shape is the consolidated `List` fold, which now applies the
range / freshness stages of this wave.

HOST-SYMBOL NOTE (honest): this def is NOT exported directly. The single host
serve symbol is `drorb_serve_pipeline_conformant`
(`Dataplane.drorbServePipelineConformant`), which is definitionally this function
— so the deployed default IS this serve, by construction. The retired
`plus5`-named C export has been removed (no dead symbol remains). -/
def serveMeteredPipelineConformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  conformantServe (fun i => serveMeteredPipelineDenseIdx peer seq i) input

/-- **The consolidation's core claim: the deployed executable = the conformance
wrapper over the consolidated registry fold.** The dense arm is byte-identical to
the plain consolidated fold (`serveMeteredPipelineDenseIdx_eq`), so the bytes the
host emits are exactly the consolidated pipeline's bytes, conformance-wrapped. -/
theorem serveMeteredPipelineConformant_eq_stages (peer : ByteArray)
    (seq : UInt64) (input : ByteArray) :
    serveMeteredPipelineConformant peer seq input
      = conformantServe (fun i => drorbServePipelineMetered peer seq i) input := by
  show conformantServe (fun i => serveMeteredPipelineDenseIdx peer seq i) input
    = conformantServe (fun i => drorbServePipelineMetered peer seq i) input
  have h : (fun i => serveMeteredPipelineDenseIdx peer seq i)
         = (fun i => drorbServePipelineMetered peer seq i) := by
    funext i; exact serveMeteredPipelineDenseIdx_eq peer seq i
  rw [h]

/-! ## Non-vacuity — the narrowed off-condition routes `/bulk` dense, dynamic full -/

/-- A plain dynamic `GET /` (root): not `/bulk`, no range, not a static asset. -/
def rootReq : ByteArray := "GET / HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

/-- A `404` dynamic shape (`GET /nope`): not `/bulk`, no range, not static. -/
def notFoundReq : ByteArray := "GET /nope HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

-- The dense fast path STILL fires on the real `/bulk` datapath shape…
#guard newStagesOffB Datapath.ServeDenseReal.bulkDemoReq = true
-- …while a non-`/bulk` dynamic request now LEAVES the dense arm for the full
-- consolidated fold — so every outermost registry stage runs on it.
#guard newStagesOffB rootReq = false
#guard newStagesOffB notFoundReq = false

end Reactor.DeployPipeline

#print axioms Reactor.DeployPipeline.newStages_collapse
#print axioms Reactor.DeployPipeline.drorbServePipelineMetered_eq_plus8_off
#print axioms Reactor.DeployPipeline.serveMeteredPipelineDenseIdx_eq
#print axioms Reactor.DeployPipeline.serveMeteredPipelineConformant_eq_stages
#print axioms Reactor.DeployPipeline.deployPipelineStages_length
