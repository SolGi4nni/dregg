import Reactor.DeployPlus2
import Reactor.ServeConformant
import Reactor.Stage.TimingAllowOrigin
import Reactor.Stage.MaxForwards
import Reactor.Stage.ContentLocation
import Proto.Kernel.Shortcuts

/-!
# Reactor.DeployPlus4 — three more edges onto the deployed default
(`Timing-Allow-Origin` / `Content-Location` / `Max-Forwards`)

Extends the CURRENT deployed default — the RFC-conformant EXTENDED metered fold
`Reactor.DeployPlus2.deployStagesPlus2` (nine proven edges over
`deployStagesFull2`, served through `conformantServe`) — with three further
proven stages, by PREPENDING them, so `deployStagesPlus2` is referenced
read-only and every existing deployed proof stands:

* `Reactor.Stage.TimingAllowOrigin.taoStage` (HEAD — outermost response): stamp
  `Timing-Allow-Origin: *` (W3C Resource Timing) on every response lacking one —
  cross-origin consumers' RUM telemetry sees real network phase timings.
* `Reactor.Stage.ContentLocation.contentLocationStage`: stamp
  `Content-Location: <target>` (RFC 9110 §8.7) onto a `200` static-asset
  answer, naming the returned representation's URI — the previously
  proven-but-inert leaf, now deployed.
* `Reactor.Stage.MaxForwards.mfStage`: RFC 9110 §7.6.2 — `OPTIONS` at
  `Max-Forwards: 0` is answered by THIS hop (`204` + `Allow`, the §9.3.7
  final-recipient answer) instead of being routed method-blind; a forwardable
  `OPTIONS`/`TRACE` continues with the hop count decremented.

Response order innermost→outermost:
`deployStagesFull2` → nine plus2 edges → max-forwards → content-location →
timing-allow-origin.

## Theorems (pure kernel — NO `native_decide`; axioms ⊆ {propext,
Classical.choice, Quot.sound})

* `plus4_headers_eq` — the extended fold's finalized headers are EXACTLY
  `stampTAO` over the inner fold's (the composition spine).
* `plus4_every_response_has_tao` — EVERY response of the extended metered fold
  carries `Timing-Allow-Origin`, for ALL peer/seq/input (gate refusals included).
* `plus4_options_mf0_204` / `plus4Metered_options_mf0_204` — an `OPTIONS` request
  at hop-limit zero is answered `204` through the WHOLE extended fold (the
  §7.6.2 MUST, composed via `deployStagesPlus2_statusStable` — every inner
  response phase is status-stable, `proxyProtoStage`'s proven here).
* `plus4_content_location_static` / `plus4Metered_content_location_static` — when
  the inner deployed fold answers a static GET with `200`, the extended fold's
  response carries `(Content-Location, <target>)`; the `OPTIONS`/`TRACE`
  scoping is DERIVED from `isStaticGet` through the
  `Proto.Kernel.Shortcuts.toUTF8_toList_ascii` bridge (`getMethod_bytes`).
* `plus4_transparent` — off the three edges' firing conditions (non-`OPTIONS`/
  `TRACE`, non-static), the extended fold's response IS the deployed plus2
  response with exactly the `Timing-Allow-Origin` stamp appended — the
  conformance-preservation equation.
* `plus4Conformant_accept_serves_fold` / `plus4Conformant_head_no_body` /
  `plus4Conformant_rejects_missingHost` — the conformance wrapper composed over
  the extended fold (the `DeployPlus2Conformant` theorems re-established at the
  plus4 inner).

Export: `drorb_serve_metered_plus4` (the raw extended fold) and
`drorb_serve_metered_plus4_conformant` (the wrapper over it — THE deployed
default; `DRORB_PLUS4=0` reverts to the plus2-conformant fold).

Residuals (named): `Allow`-header survival through the inner response onion is
witnessed on the wire (curl), not kernel-stated — the header-map rewrite's
preservation lemma is the missing piece; the decremented `Max-Forwards` has no
deployed forwarding consumer yet; `TRACE` termination (§9.3.8 echo) is not
implemented; the wrapper's REJECT arms (400/431/501) answer before the fold, so
those responses carry `Date` but not the stamped edges.
-/

namespace Reactor.DeployPlus4

open Reactor.Pipeline
open Reactor (Response serialize)
open Reactor.Deploy (deployStagesFull2 appHandler ctxOfMetered
  deployStagesFull2_statusStable)
open Reactor.DeployPlus2 (deployStagesPlus2 deployRespPlus2Metered
  mem_of_prefix any_of_prefix)
open Reactor.ServeConformant (conformantServe respBytesRaw acceptedRaw injectDate
  mkCtx reqBytes mk_toArray_toList addDate missingHostInput stripBody afterBlank
  hasConditional conformant_head_no_body conformant_rejects_missingHost)
open Reactor.Stage.RequestValidation (validationStage badRequestResp)
open Reactor.Stage.StrictValidation (strictStage)
open Reactor.Stage.FramingValidation (framingValidationStage)
open Reactor.Stage.TimingAllowOrigin (taoStage hasTAO stampTAO stampTAO_prefix
  stampTAO_has taoStage_effect taoStage_statusStable taoStage_response_has_tao)
open Reactor.Stage.MaxForwards (mfStage mfContinueCtx optionsResp isOPTIONS isTRACE
  mfZero mfStage_gates mfStage_passthrough mfStage_statusStable
  mfStage_gate_status optionsResp_status optionsResp_has_allow)
open Reactor.Stage.ContentLocation (contentLocationStage contentLocationName
  canonicalResourcePath
  isStaticGet contentLocationStage_statusStable contentLocationStage_preserves_status
  contentLocationStage_static200_present contentLocationStage_nonstatic_absent)
open Reactor.Stage.AltSvc (altStage altStage_statusStable)
open Reactor.Stage.PermissionsPolicy (ppStage ppStage_statusStable)
open Reactor.Stage.CrossOriginResource (corpStage corpStage_statusStable)
open Reactor.Stage.Via (viaStage viaStage_statusStable)
open Reactor.Stage.CacheStatus (csStage csStage_statusStable)
open Reactor.Stage.WarningTransform (warningStage warningStage_statusStable)
open Reactor.Stage.LinkPreload (linkStage linkStage_statusStable)
open Reactor.Stage.ProxyProtocol (proxyProtoStage clientKey xffName)
open Reactor.Stage.StaleWhileRevalidate (swrStage swrStage_statusStable)

/-- **The extended deployed chain.** The three edges prepended to the exact
`deployStagesPlus2` fold the deployed default serves — head placement, so their
`onResponse` runs OUTERMOST and none of the plus2/deployed gate proofs move. -/
def deployStagesPlus4 : List Stage :=
  taoStage :: contentLocationStage :: mfStage :: deployStagesPlus2

/-- The built response of the extended METERED fold — the peer/seq context the
dataplane threads in. -/
def deployRespPlus4Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Response :=
  (runPipeline deployStagesPlus4 appHandler (ctxOfMetered clientIp connSeq input)).build

/-- The extended metered serve as wire bytes. -/
def servePipelinePlus4Metered (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) : Proto.Bytes :=
  serialize (deployRespPlus4Metered clientIp connSeq input)

/-! ## Status stability of the inner chain -/

/-- `proxyProtoStage`'s response phase (the conditional `X-Forwarded-For` append)
never touches the status. -/
theorem proxyProtoStage_statusStable : Stage.statusStable proxyProtoStage := by
  intro c b
  have h : ∀ (o : Option (String × Proto.Bytes)),
      ((match o with
        | some p => b.addHeader (xffName, p.2)
        | none => b).build).status = b.build.status := by
    intro o; cases o <;> rfl
  exact h (c.attrs.find? (fun p => p.1 == clientKey))

/-- **Every response phase below the three edges is status-stable** — the nine
plus2 edges (stamps) and the whole deployed fold. This is what carries a gate's
status through the onion. -/
theorem deployStagesPlus2_statusStable :
    ∀ s ∈ deployStagesPlus2, Stage.statusStable s := by
  intro s hs
  rw [show deployStagesPlus2
      = altStage :: ppStage :: corpStage :: viaStage :: csStage :: warningStage
        :: linkStage :: proxyProtoStage :: swrStage :: deployStagesFull2 from rfl] at hs
  simp only [List.mem_cons] at hs
  rcases hs with h|h|h|h|h|h|h|h|h|h
  · rw [h]; exact altStage_statusStable
  · rw [h]; exact ppStage_statusStable
  · rw [h]; exact corpStage_statusStable
  · rw [h]; exact viaStage_statusStable
  · rw [h]; exact csStage_statusStable
  · rw [h]; exact warningStage_statusStable
  · rw [h]; exact linkStage_statusStable
  · rw [h]; exact proxyProtoStage_statusStable
  · rw [h]; exact swrStage_statusStable
  · exact deployStagesFull2_statusStable s h

/-- The whole extended chain is status-stable in its response phase — exported
for any further extension to stack on. -/
theorem deployStagesPlus4_statusStable :
    ∀ s ∈ deployStagesPlus4, Stage.statusStable s := by
  intro s hs
  rw [show deployStagesPlus4
      = taoStage :: contentLocationStage :: mfStage :: deployStagesPlus2 from rfl] at hs
  simp only [List.mem_cons] at hs
  rcases hs with h|h|h|h
  · rw [h]; exact taoStage_statusStable
  · rw [h]; exact contentLocationStage_statusStable
  · rw [h]; exact mfStage_statusStable
  · exact deployStagesPlus2_statusStable s h

/-! ## The composition spine -/

/-- The finalized INNER response at the point the outermost stamp sees it. -/
def innerResp4 (clientIp : Proto.Bytes) (connSeq : Nat) (input : Proto.Bytes) : Response :=
  (runPipeline (contentLocationStage :: mfStage :: deployStagesPlus2) appHandler
    (ctxOfMetered clientIp connSeq input)).build

/-- **The composition spine.** The extended fold's finalized headers are EXACTLY
`stampTAO` over the inner fold's headers. -/
theorem plus4_headers_eq (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) :
    (deployRespPlus4Metered clientIp connSeq input).headers
      = stampTAO (innerResp4 clientIp connSeq input).headers :=
  taoStage_effect (contentLocationStage :: mfStage :: deployStagesPlus2) appHandler _

/-- **Presence, everywhere.** EVERY response of the extended metered fold carries
`Timing-Allow-Origin` — for ALL peer/seq/input, gate refusals included. -/
theorem plus4_every_response_has_tao (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes) :
    hasTAO (deployRespPlus4Metered clientIp connSeq input).headers = true :=
  taoStage_response_has_tao _ appHandler _

/-! ## Max-Forwards: the hop-limit termination through the whole fold -/

/-- **§7.6.2, composed.** An `OPTIONS` request at `Max-Forwards: 0` is answered
`204` through the WHOLE extended fold — for ANY context satisfying the guards. -/
theorem plus4_options_mf0_204 (c : Ctx) (hopt : isOPTIONS c.req = true)
    (hz : mfZero c.req = true) :
    ((runPipeline deployStagesPlus4 appHandler c).build).status = 204 := by
  have h1 : runPipeline deployStagesPlus4 appHandler c
      = taoStage.onResponse c
          (runPipeline (contentLocationStage :: mfStage :: deployStagesPlus2)
            appHandler c) :=
    pipeline_stage_effect taoStage _ appHandler c c rfl
  rw [h1, taoStage_statusStable c _]
  show ((runPipeline (contentLocationStage :: mfStage :: deployStagesPlus2)
        appHandler c).acc).status = 204
  rw [contentLocationStage_preserves_status _ appHandler c]
  show ((runPipeline (mfStage :: deployStagesPlus2) appHandler c).build).status = 204
  exact mfStage_gate_status c deployStagesPlus2 appHandler hopt hz
    deployStagesPlus2_statusStable

/-- The metered instance: the deployed peer/seq context. -/
theorem plus4Metered_options_mf0_204 (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes)
    (hopt : isOPTIONS (ctxOfMetered clientIp connSeq input).req = true)
    (hz : mfZero (ctxOfMetered clientIp connSeq input).req = true) :
    (deployRespPlus4Metered clientIp connSeq input).status = 204 :=
  plus4_options_mf0_204 _ hopt hz

/-! ## Content-Location: the representation pointer on the deployed static 200 -/

/-- `ContentLocation.getMethod`'s wire bytes, derived through the
`Proto.Kernel.Shortcuts` ASCII bridge (the definition goes through the
WF-recursive `String.toUTF8`, which the kernel cannot reduce directly). -/
theorem getMethod_bytes :
    Reactor.Stage.ContentLocation.getMethod = [71, 69, 84] := by
  show ("GET".toUTF8.toList : Proto.Bytes) = _
  rw [Proto.Kernel.Shortcuts.toUTF8_toList_ascii "GET" (by decide)]
  decide

/-- A static GET is neither `OPTIONS` nor `TRACE` — the Max-Forwards stage is
byte-transparent on the static surface (derived, not hypothesized). -/
theorem staticGet_not_scoped {c : Ctx} (h : isStaticGet c = true) :
    (isOPTIONS c.req || isTRACE c.req) = false := by
  have hm : (c.req.method == Reactor.Stage.ContentLocation.getMethod) = true := by
    unfold Reactor.Stage.ContentLocation.isStaticGet at h
    exact ((Bool.and_eq_true _ _).mp h).1
  have hmeq : c.req.method = [71, 69, 84] := by
    have hbe := eq_of_beq hm
    rw [hbe, getMethod_bytes]
  unfold Reactor.Stage.MaxForwards.isOPTIONS Reactor.Stage.MaxForwards.isTRACE
  rw [hmeq]
  decide

/-- **RFC 9110 §8.7, composed.** When the inner deployed plus2 fold answers a
static GET with `200`, the extended fold's response carries
`(Content-Location, <canonical resource path>)` — the SERVER-CHOSEN representation
URI (query-stripped, normalized), never reflected request input, on the wire. -/
theorem plus4_content_location_static (c : Ctx)
    (hstatic : isStaticGet c = true)
    (h200 : ((runPipeline deployStagesPlus2 appHandler c).build).status = 200) :
    (contentLocationName, canonicalResourcePath c.req.target)
      ∈ ((runPipeline deployStagesPlus4 appHandler c).build).headers := by
  have hmeth := staticGet_not_scoped hstatic
  have h1 : runPipeline deployStagesPlus4 appHandler c
      = taoStage.onResponse c
          (runPipeline (contentLocationStage :: mfStage :: deployStagesPlus2)
            appHandler c) :=
    pipeline_stage_effect taoStage _ appHandler c c rfl
  have hmf : runPipeline (mfStage :: deployStagesPlus2) appHandler c
      = runPipeline deployStagesPlus2 appHandler c := by
    rw [pipeline_stage_effect mfStage deployStagesPlus2 appHandler c c
      (mfStage_passthrough c hmeth)]
    rfl
  have hcl : (contentLocationName, canonicalResourcePath c.req.target)
      ∈ ((runPipeline (contentLocationStage :: mfStage :: deployStagesPlus2)
          appHandler c).build).headers := by
    apply contentLocationStage_static200_present (mfStage :: deployStagesPlus2)
      appHandler c _ hstatic
    show ((runPipeline (mfStage :: deployStagesPlus2) appHandler c).build).status = 200
    rw [hmf]
    exact h200
  rw [h1]
  show (contentLocationName, canonicalResourcePath c.req.target)
      ∈ stampTAO (((runPipeline (contentLocationStage :: mfStage :: deployStagesPlus2)
          appHandler c).build).headers)
  exact mem_of_prefix (stampTAO_prefix _) hcl

/-- The metered instance: when the deployed plus2 fold's response is a static-GET
`200`, the plus4 default's response names the representation. -/
theorem plus4Metered_content_location_static (clientIp : Proto.Bytes) (connSeq : Nat)
    (input : Proto.Bytes)
    (hstatic : isStaticGet (ctxOfMetered clientIp connSeq input) = true)
    (h200 : (deployRespPlus2Metered clientIp connSeq input).status = 200) :
    (contentLocationName,
        canonicalResourcePath (ctxOfMetered clientIp connSeq input).req.target)
      ∈ (deployRespPlus4Metered clientIp connSeq input).headers :=
  plus4_content_location_static _ hstatic h200

/-! ## Transparency — the conformance-preservation equation -/

/-- **Off the edges' firing conditions the fold is the deployed fold plus exactly
the timing stamp.** For a non-`OPTIONS`/`TRACE`, non-static request the extended
fold's response IS the deployed plus2 response with `stampTAO` on its headers —
nothing else moves (status, reason, body all equal). -/
theorem plus4_transparent (c : Ctx)
    (hmeth : (isOPTIONS c.req || isTRACE c.req) = false)
    (hns : isStaticGet c = false) :
    (runPipeline deployStagesPlus4 appHandler c).build
      = { (runPipeline deployStagesPlus2 appHandler c).build with
          headers := stampTAO ((runPipeline deployStagesPlus2 appHandler c).build).headers } := by
  have h1 : runPipeline deployStagesPlus4 appHandler c
      = taoStage.onResponse c
          (runPipeline (contentLocationStage :: mfStage :: deployStagesPlus2)
            appHandler c) :=
    pipeline_stage_effect taoStage _ appHandler c c rfl
  have h2 : (runPipeline (contentLocationStage :: mfStage :: deployStagesPlus2)
        appHandler c).build
      = (runPipeline (mfStage :: deployStagesPlus2) appHandler c).build :=
    contentLocationStage_nonstatic_absent _ appHandler c hns
  have hmf : runPipeline (mfStage :: deployStagesPlus2) appHandler c
      = runPipeline deployStagesPlus2 appHandler c := by
    rw [pipeline_stage_effect mfStage deployStagesPlus2 appHandler c c
      (mfStage_passthrough c hmeth)]
    rfl
  rw [h1]
  show { (runPipeline (contentLocationStage :: mfStage :: deployStagesPlus2)
          appHandler c).build with
         headers := stampTAO ((runPipeline (contentLocationStage :: mfStage
          :: deployStagesPlus2) appHandler c).build).headers } = _
  rw [h2, hmf]

/-! ## The exports -/

/-- **The extended metered serve seam** (`drorb_serve_metered_plus4`) — the
`drorb_serve_metered` ABI sibling over `deployStagesPlus4`. -/
def drorbServeMeteredPlus4 (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  ByteArray.mk (servePipelinePlus4Metered peer.toList seq.toNat input.toList).toArray

/-- What the export folds is definitionally the extended pipeline (totality: a
plain `def`). -/
theorem drorbServeMeteredPlus4_serves (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    drorbServeMeteredPlus4 peer seq input
      = ByteArray.mk (servePipelinePlus4Metered peer.toList seq.toNat input.toList).toArray :=
  rfl

/-- **A retired conformance-wrapped extended metered serve** (formerly the C
export `drorb_serve_metered_plus4_conformant`): the proven conformance wrapper
over the extended metered fold `deployStagesPlus4`. RETIRED experimental seam — the `@[export]` was removed in the consolidation, so this def is no longer a host crossing; it is retained only for the byte-identity derivation chain. The single deployed default is `drorb_serve_pipeline_conformant`. -/
def drorbServeMeteredPlus4Conformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  conformantServe (fun i => drorbServeMeteredPlus4 peer seq i) input

/-- The export is definitionally the conformance wrapper over the extended fold. -/
theorem drorbServeMeteredPlus4Conformant_serves (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    drorbServeMeteredPlus4Conformant peer seq input
      = conformantServe (fun i => drorbServeMeteredPlus4 peer seq i) input := rfl

/-- **The accepted path serves THE proven extended fold.** For a request that
parses, PASSES both wrapper gates, keeps its origin-form target, and carries no
precondition header, the wrapper's raw response bytes are the `Date`-injected
serialization of `deployRespPlus4Metered` — the exact `Response` every plus4
composition/presence theorem is stated over. -/
theorem plus4Conformant_accept_serves_fold (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) (req : Proto.Request) (c' c'' : Reactor.Pipeline.Ctx)
    (hp : Proto.RequestSerialize.parse (reqBytes input) = some req)
    (hr : strictStage.onRequest (mkCtx input req) = .continue c')
    (hf : framingValidationStage.onRequest c' = .continue c'')
    (htgt : c''.req.target = req.target)
    (hnc : hasConditional req = false) :
    respBytesRaw (fun i => drorbServeMeteredPlus4 peer seq i) input
      = injectDate (serialize
          (deployRespPlus4Metered peer.toList seq.toNat input.toList)) := by
  have hraw : respBytesRaw (fun i => drorbServeMeteredPlus4 peer seq i) input
      = injectDate (drorbServeMeteredPlus4 peer seq input).toList := by
    simp only [respBytesRaw, hp, hr, hf, htgt, beq_self_eq_true, if_true, acceptedRaw,
      hnc, Bool.false_eq_true, if_false]
  rw [hraw, drorbServeMeteredPlus4_serves, mk_toArray_toList]
  unfold servePipelinePlus4Metered
  rfl

/-- **B1, on the deployed extended default.** After the wrapper's `HEAD`-strip the
response carries NO body octets — for ANY request bytes. -/
theorem plus4Conformant_head_no_body (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    afterBlank (stripBody
      (respBytesRaw (fun i => drorbServeMeteredPlus4 peer seq i) input)) = [] :=
  conformant_head_no_body _ input

/-- **C1, on the deployed extended default.** The wrapper rejects a REAL
missing-Host request as a `400` WITHOUT consulting the extended fold. -/
theorem plus4Conformant_rejects_missingHost (peer : ByteArray) (seq : UInt64) :
    respBytesRaw (fun i => drorbServeMeteredPlus4 peer seq i) missingHostInput
      = serialize (addDate badRequestResp) :=
  conformant_rejects_missingHost _

#print axioms proxyProtoStage_statusStable
#print axioms deployStagesPlus2_statusStable
#print axioms deployStagesPlus4_statusStable
#print axioms plus4_headers_eq
#print axioms plus4_every_response_has_tao
#print axioms plus4_options_mf0_204
#print axioms plus4Metered_options_mf0_204
#print axioms getMethod_bytes
#print axioms staticGet_not_scoped
#print axioms plus4_content_location_static
#print axioms plus4Metered_content_location_static
#print axioms plus4_transparent
#print axioms drorbServeMeteredPlus4_serves
#print axioms drorbServeMeteredPlus4Conformant_serves
#print axioms plus4Conformant_accept_serves_fold
#print axioms plus4Conformant_head_no_body
#print axioms plus4Conformant_rejects_missingHost

end Reactor.DeployPlus4
