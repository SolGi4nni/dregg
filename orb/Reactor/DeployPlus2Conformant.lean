import Reactor.DeployPlus2
import Reactor.ServeConformant

/-!
# Reactor.DeployPlus2Conformant — the RFC-conformant EXTENDED metered serve (deployed default)

Composes the proven RFC-conformance wrapper
(`Reactor.ServeConformant.conformantServe`: request-head 431 limit → parse →
validation gate (C1/C2/B2/G1/C3) → framing gate (L1/J2/M1) → inner serve →
`Date` splice (F1) → `x-corr` scrub (N2) → `HEAD`-strip (B1)) over the EXTENDED
metered fold `Reactor.DeployPlus2.deployStagesPlus2` — the nine proven edge stages
(Alt-Svc / Permissions-Policy / Cross-Origin-Resource-Policy / Via / Cache-Status /
Warning-transform / Link-preload / PROXY-protocol recovery / stale-while-revalidate)
prepended to the deployed `deployStagesFull2`.

This module is the DEFAULT FLIP: the host's metered default serve now crosses
`drorb_serve_metered_plus2_conformant` (unset `DRORB_PLUS2`), so every default
response carries the stamped edge headers AND every conformance edge still holds —
the nine edges move from proven-behind-a-lever to deployed-by-default.

Theorems (pure kernel — axioms ⊆ {propext, Classical.choice, Quot.sound}):

* `plus2Conformant_accept_serves_fold` — on an accepted request (parse ✓,
  validation ✓, framing ✓, origin-form target, no precondition) the wrapper's raw
  response bytes are EXACTLY `injectDate (serialize (deployRespPlus2Metered …))`:
  the deployed default consults THE proven extended fold, so every DeployPlus2
  presence theorem (`plus2_every_response_has_via`,
  `plus2_every_response_has_cache_status`, `plus3_every_response_has_corp` /
  `…_pp` / `…_alt`, `plus2_cacheControl`, `plus2_linkPreload`, `plus2_warning`)
  governs the deployed default's accepted responses.
* `plus2Conformant_head_no_body` (B1) and `plus2Conformant_rejects_missingHost`
  (C1) — the parametric conformance gates instantiated at the extended inner
  (both non-vacuous by construction in `Reactor.ServeConformant`).
* `drorbServeMeteredPlus2Conformant_serves` — the export is definitionally the
  wrapper over the extended fold (totality: a plain `def`).

Residuals (named):

* The wrapper's REJECT arms (400/431/501) answer before the fold, so those
  responses carry `Date` but NOT the nine edge headers.
* A PROXY-preambled input fails the validation gate before `proxyProtoStage` can
  read it, so the client-recovery stage is wired but INERT on the conformant
  default; `DRORB_PLUS2=raw` keeps the unwrapped extended fold for preambled
  deployments (the `plus2_xff` theorems govern that lever path).
* The `/bulk` dense-arm bypass is NOT composed here (the extended fold's `/bulk`
  response differs by the stamped headers, so the dense head bypass no longer
  byte-matches): the 1 MiB arm re-crosses as a `List` — the body-cliff returns on
  that one route under the new default; `DRORB_PLUS2=0` keeps the dense fold
  without the nine edges.
-/

namespace Reactor.DeployPlus2

open Reactor (serialize)
open Reactor.ServeConformant (conformantServe respBytesRaw acceptedRaw injectDate
  mkCtx reqBytes mk_toArray_toList addDate missingHostInput stripBody afterBlank
  hasConditional conformant_head_no_body conformant_rejects_missingHost)
open Reactor.Stage.RequestValidation (validationStage badRequestResp)
open Reactor.Stage.StrictValidation (strictStage)
open Reactor.Stage.FramingValidation (framingValidationStage)

/-- **A retired conformance-wrapped extended metered serve** (formerly the C
export `drorb_serve_metered_plus2_conformant`): the proven conformance wrapper
over the extended metered fold `deployStagesPlus2`. RETIRED experimental seam — the `@[export]` was removed in the consolidation, so this def is no longer a host crossing; it is retained only for the byte-identity derivation chain. The single deployed default is `drorb_serve_pipeline_conformant`. -/
def drorbServeMeteredPlus2Conformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  conformantServe (fun i => drorbServeMeteredPlus2 peer seq i) input

/-- The export is definitionally the conformance wrapper over the extended fold
(totality: a plain `def`). -/
theorem drorbServeMeteredPlus2Conformant_serves (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    drorbServeMeteredPlus2Conformant peer seq input
      = conformantServe (fun i => drorbServeMeteredPlus2 peer seq i) input := rfl

/-- **The accepted path serves THE proven extended fold.** For a request that
parses, PASSES both gates, keeps its origin-form target, and carries no
precondition header, the wrapper's raw response bytes are the `Date`-injected
serialization of `deployRespPlus2Metered` — the exact Response every DeployPlus2
composition/presence theorem is stated over. -/
theorem plus2Conformant_accept_serves_fold (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) (req : Proto.Request) (c' c'' : Reactor.Pipeline.Ctx)
    (hp : Proto.RequestSerialize.parse (reqBytes input) = some req)
    (hr : strictStage.onRequest (mkCtx input req) = .continue c')
    (hf : framingValidationStage.onRequest c' = .continue c'')
    (htgt : c''.req.target = req.target)
    (hnc : hasConditional req = false) :
    respBytesRaw (fun i => drorbServeMeteredPlus2 peer seq i) input
      = injectDate (serialize
          (deployRespPlus2Metered peer.toList seq.toNat input.toList)) := by
  have hraw : respBytesRaw (fun i => drorbServeMeteredPlus2 peer seq i) input
      = injectDate (drorbServeMeteredPlus2 peer seq input).toList := by
    simp only [respBytesRaw, hp, hr, hf, htgt, beq_self_eq_true, if_true, acceptedRaw,
      hnc, Bool.false_eq_true, if_false]
  rw [hraw, drorbServeMeteredPlus2_serves, mk_toArray_toList]
  unfold servePipelinePlus2Metered
  rfl

/-- **B1, on the deployed extended default.** After the wrapper's `HEAD`-strip the
response carries NO body octets — for ANY request bytes (the parametric,
non-vacuous `conformant_head_no_body` at the extended inner). -/
theorem plus2Conformant_head_no_body (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    afterBlank (stripBody
      (respBytesRaw (fun i => drorbServeMeteredPlus2 peer seq i) input)) = [] :=
  conformant_head_no_body _ input

/-- **C1, on the deployed extended default.** The wrapper rejects a REAL
missing-Host request as `serialize (addDate badRequestResp)` — a `400` — WITHOUT
consulting the extended fold. -/
theorem plus2Conformant_rejects_missingHost (peer : ByteArray) (seq : UInt64) :
    respBytesRaw (fun i => drorbServeMeteredPlus2 peer seq i) missingHostInput
      = serialize (addDate badRequestResp) :=
  conformant_rejects_missingHost _

#print axioms drorbServeMeteredPlus2Conformant_serves
#print axioms plus2Conformant_accept_serves_fold
#print axioms plus2Conformant_head_no_body
#print axioms plus2Conformant_rejects_missingHost

end Reactor.DeployPlus2
